//! Incremental Drive backups. SQLite work always runs outside the UI/runtime threads.
use oauth2::{
    AuthUrl, AuthorizationCode, ClientId, ClientSecret, CsrfToken, PkceCodeChallenge, RedirectUrl,
    RefreshToken, Scope, TokenResponse, TokenUrl, basic::BasicClient,
};
use rusqlite::{Connection, OptionalExtension, params, types::Value as SqlValue};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::TcpListener,
    sync::mpsc,
};

type Error = Box<dyn std::error::Error + Send + Sync>;
type Result<T> = std::result::Result<T, Error>;
const API: &str = "https://www.googleapis.com/drive/v3/files";
const INTERVAL: Duration = Duration::from_secs(600);

#[derive(Clone, Copy, Debug)]
pub enum Dataset {
    Cantos,
    Biblias,
}
impl Dataset {
    fn name(self) -> &'static str {
        match self {
            Self::Cantos => "cantos",
            Self::Biblias => "biblias",
        }
    }
    fn tables(self) -> &'static [&'static str] {
        match self {
            Self::Cantos => &["cantos", "diapositivas", "favoritos"],
            Self::Biblias => &["versiones", "versiculos"],
        }
    }
    fn sql(self) -> &'static str {
        match self {
            Self::Cantos => include_str!("../migrations/cantos_sync.sql"),
            Self::Biblias => include_str!("../migrations/biblias_sync.sql"),
        }
    }
}

fn columns(conn: &Connection, table: &str) -> rusqlite::Result<Vec<String>> {
    let mut stmt = conn.prepare(&format!("PRAGMA table_info({table})"))?;
    stmt.query_map([], |r| r.get(1))?.collect()
}

/// Only install seed data when the local file does not exist. Never replace user data.
pub fn prepare_local_file(path: &Path, seed: &Path) -> std::io::Result<()> {
    if path.try_exists()? {
        return Ok(());
    }
    let mut source = std::fs::File::open(seed)?;
    match std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
    {
        Ok(mut destination) => {
            std::io::copy(&mut source, &mut destination)?;
            destination.sync_all()
        }
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => Ok(()),
        Err(e) => Err(e),
    }
}

/// Add missing schema elements atomically, including partially migrated databases.
/// rusqlite rolls the transaction back on any error before commit().
pub fn migrate(conn: &mut Connection, dataset: Dataset) -> rusqlite::Result<()> {
    let tx = conn.transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
    let had_changes: bool = tx.query_row(
        "SELECT EXISTS(SELECT 1 FROM sqlite_master WHERE type='table' AND name='sync_changes')",
        [],
        |r| r.get(0),
    )?;
    let had_versions: bool = tx.query_row(
        "SELECT EXISTS(SELECT 1 FROM sqlite_master WHERE type='table' AND name='sync_versions')",
        [],
        |r| r.get(0),
    )?;
    // The prefix only creates auxiliary tables/indexes, before installing triggers.
    let sql = dataset.sql();
    let prefix = sql.split("CREATE TRIGGER").next().unwrap_or(sql);
    tx.execute_batch(prefix)?;
    let metadata = columns(&tx, "sync_metadata")?;
    for (name, definition) in [
        ("id", "INTEGER NOT NULL DEFAULT 1"),
        ("last_sync_timestamp", "INTEGER NOT NULL DEFAULT 0"),
        ("clock", "INTEGER NOT NULL DEFAULT 1"),
        ("suppress", "INTEGER NOT NULL DEFAULT 0"),
        ("remote_folder", "TEXT NOT NULL DEFAULT ''"),
        ("local_instance", "TEXT NOT NULL DEFAULT ''"),
    ] {
        if !metadata.iter().any(|c| c == name) {
            tx.execute_batch(&format!(
                "ALTER TABLE sync_metadata ADD COLUMN {name} {definition}"
            ))?;
        }
    }
    tx.execute_batch(
        "CREATE UNIQUE INDEX IF NOT EXISTS sync_metadata_id ON sync_metadata(id);
        INSERT OR IGNORE INTO sync_metadata(id) VALUES(1);
        UPDATE sync_metadata SET last_sync_timestamp=COALESCE(last_sync_timestamp,0),
            clock=COALESCE(clock,1), suppress=COALESCE(suppress,0),
            local_instance=CASE WHEN local_instance='' OR local_instance IS NULL
                THEN lower(hex(randomblob(16))) ELSE local_instance END WHERE id=1;",
    )?;
    if matches!(dataset, Dataset::Cantos) {
        tx.execute_batch(
            "CREATE TABLE IF NOT EXISTS favoritos (
            id INTEGER PRIMARY KEY AUTOINCREMENT, tipo TEXT NOT NULL DEFAULT 'canto',
            ref_id INTEGER NOT NULL DEFAULT 0, referencia TEXT NOT NULL DEFAULT '',
            titulo TEXT NOT NULL DEFAULT '', version TEXT NOT NULL DEFAULT '');",
        )?;
        if !columns(&tx, "favoritos")?.iter().any(|c| c == "version") {
            tx.execute_batch("ALTER TABLE favoritos ADD COLUMN version TEXT NOT NULL DEFAULT ''")?;
        }
    }
    let now: i64 = tx.query_row(
        "SELECT CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)",
        [],
        |r| r.get(0),
    )?;
    let mut baselines = Vec::new();
    for table in dataset.tables() {
        let current = columns(&tx, table)?;
        if current.is_empty() {
            return Err(rusqlite::Error::InvalidQuery);
        }
        let new_timestamp = !current.iter().any(|c| c == "updated_at");
        let new_deleted = !current.iter().any(|c| c == "is_deleted");
        if new_timestamp {
            // ADD COLUMN cannot use CURRENT_TIMESTAMP as its default in SQLite.
            tx.execute_batch(&format!(
                "ALTER TABLE {table} ADD COLUMN updated_at TIMESTAMP NOT NULL DEFAULT 0"
            ))?;
            tx.execute(&format!("UPDATE {table} SET updated_at=?1"), [now])?;
        }
        if new_deleted {
            tx.execute_batch(&format!("ALTER TABLE {table} ADD COLUMN is_deleted INTEGER NOT NULL DEFAULT 0 CHECK(is_deleted IN (0,1))"))?;
        }
        if new_timestamp || new_deleted || !had_changes || !had_versions {
            baselines.push((*table, new_timestamp));
        }
    }
    // Triggers are installed after all required columns exist.
    tx.execute_batch(sql)?;
    for (table, new_timestamp) in baselines {
        tx.execute(
            &format!(
                "UPDATE sync_metadata SET clock=MAX(clock+1,last_sync_timestamp+1,?1,
            COALESCE((SELECT MAX(updated_at) FROM {table}),0)) WHERE id=1"
            ),
            [now],
        )?;
        let fields = columns(&tx, table)?
            .iter()
            .map(|c| format!("'{c}',{c}"))
            .collect::<Vec<_>>()
            .join(",");
        tx.execute_batch(&format!("INSERT INTO sync_changes
            SELECT (SELECT clock FROM sync_metadata WHERE id=1), '{table}', id, json_object({fields}) FROM {table};"))?;
        // Untouched installation/migration rows may accept a backup from another device,
        // even when that backup predates this device's migration time.
        let version = if new_timestamp { "0" } else { "updated_at" };
        tx.execute_batch(&format!(
            "INSERT INTO sync_versions(table_name,record_id,timestamp)
            SELECT '{table}',id,{version} FROM {table} WHERE true
            ON CONFLICT(table_name,record_id) DO NOTHING;"
        ))?;
    }
    tx.commit()
}

fn open(path: &Path, dataset: Dataset) -> Result<Connection> {
    // Never silently create a missing/replaced application database.
    let mut conn = Connection::open_with_flags(path, rusqlite::OpenFlags::SQLITE_OPEN_READ_WRITE)?;
    conn.busy_timeout(Duration::from_secs(5))?;
    migrate(&mut conn, dataset)?;
    Ok(conn)
}

#[derive(Debug, Serialize, Deserialize)]
struct Change {
    table: String,
    row: BTreeMap<String, Value>,
}
#[derive(Debug, Serialize, Deserialize)]
struct Delta {
    source: String,
    format: u32,
    dataset: String,
    from: i64,
    through: i64,
    changes: Vec<Change>,
}
#[cfg(test)]
fn snapshot(path: &Path, dataset: Dataset) -> Result<Delta> {
    snapshot_for(path, dataset, None)
}
fn snapshot_for(path: &Path, dataset: Dataset, folder: Option<&str>) -> Result<Delta> {
    let mut conn = open(path, dataset)?;
    let tx = conn.transaction()?;
    let (mut from, through, remote, source): (i64, i64, String, String) = tx.query_row(
        "SELECT last_sync_timestamp,clock,remote_folder,local_instance FROM sync_metadata WHERE id=1",
        [],
        |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?)),
    )?;
    let changes = if folder.is_some_and(|f| f != remote) {
        from = 0;
        let mut changes = Vec::new();
        for table in dataset.tables() {
            let columns: Vec<String> = {
                let mut stmt = tx.prepare(&format!("PRAGMA table_info({table})"))?;
                stmt.query_map([], |r| r.get(1))?
                    .collect::<rusqlite::Result<_>>()?
            };
            let fields = columns
                .iter()
                .map(|c| format!("'{c}',{c}"))
                .collect::<Vec<_>>()
                .join(",");
            let sql = format!("SELECT json_object({fields}) FROM {table}");
            let mut stmt = tx.prepare(&sql)?;
            for payload in stmt.query_map([], |r| r.get::<_, String>(0))? {
                changes.push(Change {
                    table: (*table).into(),
                    row: serde_json::from_str(&payload?)?,
                });
            }
            let sql = format!(
                "SELECT record_id,timestamp FROM sync_versions WHERE table_name=?1 AND NOT EXISTS(SELECT 1 FROM {table} WHERE id=record_id)"
            );
            let mut stmt = tx.prepare(&sql)?;
            for row in
                stmt.query_map([table], |r| Ok((r.get::<_, i64>(0)?, r.get::<_, i64>(1)?)))?
            {
                let (id, timestamp) = row?;
                changes.push(Change {
                    table: (*table).into(),
                    row: serde_json::from_value(
                        json!({"id":id,"updated_at":timestamp,"is_deleted":1}),
                    )?,
                });
            }
        }
        changes
    } else {
        let mut stmt = tx.prepare("SELECT table_name,payload FROM sync_changes WHERE timestamp>?1 AND timestamp<=?2 ORDER BY timestamp,rowid")?;
        let rows = stmt.query_map(params![from, through], |r| {
            Ok((r.get::<_, String>(0)?, r.get::<_, String>(1)?))
        })?;
        let mut changes = Vec::new();
        for row in rows {
            let (table, payload) = row?;
            changes.push(Change {
                table,
                row: serde_json::from_str(&payload)?,
            });
        }
        changes
    };
    tx.commit()?;
    Ok(Delta {
        source,
        format: 1,
        dataset: dataset.name().into(),
        from,
        through,
        changes,
    })
}
#[cfg(test)]
fn acknowledge(path: &Path, dataset: Dataset, through: i64) -> Result<()> {
    let source: String = open(path, dataset)?.query_row(
        "SELECT local_instance FROM sync_metadata WHERE id=1",
        [],
        |r| r.get(0),
    )?;
    acknowledge_for(path, dataset, through, "", &source)
}
fn acknowledge_for(
    path: &Path,
    dataset: Dataset,
    through: i64,
    folder: &str,
    source: &str,
) -> Result<()> {
    let mut conn = open(path, dataset)?;
    let tx = conn.transaction()?;
    let valid: bool = tx.query_row(
        "SELECT local_instance=?1 AND clock>=?2 FROM sync_metadata WHERE id=1",
        params![source, through],
        |r| r.get(0),
    )?;
    if !valid {
        return Err(
            "La base fue reemplazada durante la subida; se conservaron los cambios pendientes"
                .into(),
        );
    }
    tx.execute(
        "UPDATE sync_metadata SET last_sync_timestamp=?1,remote_folder=?2 WHERE id=1",
        params![through, folder],
    )?;
    tx.execute("DELETE FROM sync_changes WHERE timestamp<=?1", [through])?;
    tx.commit()?;
    Ok(())
}
fn number(row: &BTreeMap<String, Value>, key: &str) -> Result<i64> {
    row.get(key)
        .and_then(Value::as_i64)
        .ok_or_else(|| format!("Campo inválido: {key}").into())
}
fn merge(path: &Path, dataset: Dataset, deltas: Vec<Delta>) -> Result<usize> {
    let mut conn = open(path, dataset)?;
    let tx = conn.transaction()?;
    tx.execute("UPDATE sync_metadata SET suppress=1 WHERE id=1", [])?;
    let mut count = 0;
    for delta in deltas {
        if delta.format != 1 || delta.dataset != dataset.name() {
            return Err("Formato de respaldo incompatible".into());
        }
        for change in delta.changes {
            if !dataset.tables().contains(&change.table.as_str()) {
                return Err("Tabla desconocida en respaldo".into());
            }
            let id = number(&change.row, "id")?;
            let stamp = number(&change.row, "updated_at")?;
            if id <= 0 || stamp < 1 {
                return Err("ID o timestamp inválido".into());
            }
            let deleted = match change.row.get("is_deleted") {
                Some(Value::Bool(v)) => *v,
                Some(v) if v.as_i64() == Some(0) => false,
                Some(v) if v.as_i64() == Some(1) => true,
                _ => return Err("is_deleted inválido".into()),
            };
            let local: Option<i64> = tx
                .query_row(
                    "SELECT timestamp FROM sync_versions WHERE table_name=?1 AND record_id=?2",
                    params![change.table, id],
                    |r| r.get(0),
                )
                .optional()?;
            if local.is_some_and(|v| v > stamp || (v == stamp && stamp != 1)) {
                continue;
            }
            if deleted {
                tx.execute(&format!("DELETE FROM {} WHERE id=?1", change.table), [id])?;
            } else {
                // Validate every column before constructing identifiers from downloaded JSON.
                let columns: Vec<String> = {
                    let mut stmt = tx.prepare(&format!("PRAGMA table_info({})", change.table))?;
                    stmt.query_map([], |r| r.get(1))?
                        .collect::<rusqlite::Result<_>>()?
                };
                if change.row.len() != columns.len()
                    || columns.iter().any(|c| !change.row.contains_key(c))
                {
                    return Err("Columnas incompatibles en respaldo".into());
                }
                // Legacy rows all start at 1. Restore different legacy content even
                // on a freshly installed target, while keeping replays idempotent.
                if local == Some(1) && stamp == 1 {
                    let fields = columns
                        .iter()
                        .map(|c| format!("'{c}',{c}"))
                        .collect::<Vec<_>>()
                        .join(",");
                    let current: Option<String> = tx
                        .query_row(
                            &format!(
                                "SELECT json_object({fields}) FROM {} WHERE id=?1",
                                change.table
                            ),
                            [id],
                            |r| r.get(0),
                        )
                        .optional()?;
                    let mut normalized = change.row.clone();
                    normalized.insert("is_deleted".into(), json!(0));
                    if current
                        .map(|v| serde_json::from_str::<Value>(&v))
                        .transpose()?
                        == Some(serde_json::to_value(normalized)?)
                    {
                        continue;
                    }
                }
                let values: Vec<SqlValue> = columns
                    .iter()
                    .map(|c| match &change.row[c] {
                        Value::Null => Ok(SqlValue::Null),
                        Value::String(s) => Ok(SqlValue::Text(s.clone())),
                        Value::Bool(b) => Ok(SqlValue::Integer(i64::from(*b))),
                        Value::Number(n) => {
                            n.as_i64().map(SqlValue::Integer).ok_or("Número inválido")
                        }
                        _ => Err("Valor SQLite inválido"),
                    })
                    .collect::<std::result::Result<_, _>>()?;
                let updates = columns
                    .iter()
                    .filter(|c| c.as_str() != "id")
                    .map(|c| format!("{c}=excluded.{c}"))
                    .collect::<Vec<_>>()
                    .join(",");
                let sql = format!(
                    "INSERT INTO {} ({}) VALUES ({}) ON CONFLICT(id) DO UPDATE SET {}",
                    change.table,
                    columns.join(","),
                    vec!["?"; columns.len()].join(","),
                    updates
                );
                tx.execute(&sql, rusqlite::params_from_iter(values))?;
            }
            // An accepted restore supersedes pending older local payloads, including
            // the migration baseline dated later than an older remote backup.
            tx.execute(
                "DELETE FROM sync_changes WHERE table_name=?1 AND record_id=?2",
                params![change.table, id],
            )?;
            tx.execute("INSERT INTO sync_versions VALUES(?1,?2,?3) ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp",params![change.table,id,stamp])?;
            tx.execute(
                "UPDATE sync_metadata SET clock=MAX(clock,?1) WHERE id=1",
                [stamp],
            )?;
            count += 1;
        }
    }
    let has_broken_references = tx
        .prepare("PRAGMA foreign_key_check")?
        .query([])?
        .next()?
        .is_some();
    if has_broken_references {
        return Err("La restauración contiene referencias inválidas entre tablas".into());
    }
    tx.execute("UPDATE sync_metadata SET suppress=0 WHERE id=1", [])?;
    tx.commit()?;
    Ok(count)
}

#[derive(Deserialize)]
struct DriveFile {
    id: String,
    name: String,
}
#[derive(Deserialize)]
struct FileList {
    files: Vec<DriveFile>,
    #[serde(rename = "nextPageToken")]
    next: Option<String>,
}
struct Drive {
    config: GoogleOAuthConfig,
    http: reqwest::Client,
    access: String,
    refresh: Option<String>,
    expires: Instant,
}
impl Drive {
    async fn login(dir: &Path, report: &(impl Fn(Status) + Sync)) -> Result<Self> {
        let dir = dir.to_path_buf();
        let config = tokio::task::spawn_blocking(move || load_google_config(&dir)).await??;
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let redirect = format!(
            "http://127.0.0.1:{}/oauth2/callback",
            listener.local_addr()?.port()
        );
        let client = oauth_client(&config)?.set_redirect_uri(RedirectUrl::new(redirect.clone())?);
        let (challenge, verifier) = PkceCodeChallenge::new_random_sha256();
        let (url, state) = client
            .authorize_url(CsrfToken::new_random)
            .add_scope(Scope::new(
                "https://www.googleapis.com/auth/drive.file".into(),
            ))
            .set_pkce_challenge(challenge)
            .add_extra_param("access_type", "offline")
            .add_extra_param("prompt", "select_account consent")
            .url();
        tokio::task::spawn_blocking(move || webbrowser::open(url.as_str())).await??;
        let code = tokio::time::timeout(Duration::from_secs(180), async {
            loop {
                let (mut socket,_) = listener.accept().await?;
                let mut buffer = Vec::new();
                loop {
                    let mut chunk = [0;1024];
                    let n = tokio::time::timeout(Duration::from_secs(5),socket.read(&mut chunk)).await??;
                    if n==0 { break; }
                    buffer.extend_from_slice(&chunk[..n]);
                    if buffer.windows(4).any(|s| s==b"\r\n\r\n") || buffer.len()>8192 { break; }
                }
                let request = String::from_utf8_lossy(&buffer);
                let target = request.lines().next().and_then(|l|l.split_whitespace().nth(1)).unwrap_or("");
                let parsed = reqwest::Url::parse(&format!("http://127.0.0.1{target}"))?;
                let pairs: BTreeMap<_,_> = parsed.query_pairs().into_owned().collect();
                let valid = parsed.path()=="/oauth2/callback" && pairs.get("state").is_some_and(|s|CsrfToken::new(s.clone())==state);
                if !valid {
                    socket.write_all(b"HTTP/1.1 400 Bad Request\r\nConnection: close\r\nContent-Length: 0\r\n\r\n").await?;
                    continue;
                }
                socket.write_all(b"HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Type: text/plain; charset=utf-8\r\n\r\nPuede cerrar esta ventana y volver a ReadyShow.").await?;
                if let Some(error) = pairs.get("error") { return Err(authorization_error(error).into()); }
                return pairs.get("code").cloned().ok_or_else(|| -> Error { "Google no autorizó el acceso".into() });
            }
        }).await.map_err(|_| "El navegador no devolvió la autorización a ReadyShow en 3 minutos. Vuelve a iniciar sesión, acepta el permiso de Drive y espera la página que indica que puedes volver a ReadyShow")??;
        status(
            report,
            "Autorización recibida. Conectando con Google...",
            true,
            false,
            false,
        );
        let http = reqwest::Client::builder()
            .redirect(reqwest::redirect::Policy::none())
            .timeout(Duration::from_secs(120))
            .build()?;
        let token = client
            .exchange_code(AuthorizationCode::new(code))
            .set_pkce_verifier(verifier)
            .request_async(&http)
            .await
            .map_err(|_| "No se pudo obtener el token OAuth")?;
        Ok(Self {
            config,
            http,
            access: token.access_token().secret().clone(),
            refresh: token.refresh_token().map(|t| t.secret().clone()),
            expires: Instant::now() + token.expires_in().unwrap_or(Duration::from_secs(3600)),
        })
    }
    async fn token(&mut self) -> Result<String> {
        if Instant::now() + Duration::from_secs(60) >= self.expires {
            let refresh = RefreshToken::new(
                self.refresh
                    .clone()
                    .ok_or("Debe iniciar sesión nuevamente")?,
            );
            let token = oauth_client(&self.config)?
                .exchange_refresh_token(&refresh)
                .request_async(&self.http)
                .await
                .map_err(|_| "La sesión expiró; inicie sesión nuevamente")?;
            self.access = token.access_token().secret().clone();
            if let Some(r) = token.refresh_token() {
                self.refresh = Some(r.secret().clone());
            }
            self.expires = Instant::now() + token.expires_in().unwrap_or(Duration::from_secs(3600));
        }
        Ok(self.access.clone())
    }
    async fn list(&mut self, query: &str) -> Result<Vec<DriveFile>> {
        let mut files = Vec::new();
        let mut page = String::new();
        loop {
            let token = self.token().await?;
            let mut params = vec![
                ("q", query),
                ("fields", "nextPageToken,files(id,name)"),
                ("pageSize", "1000"),
                ("orderBy", "name"),
            ];
            if !page.is_empty() {
                params.push(("pageToken", &page));
            }
            let result: FileList = self
                .http
                .get(API)
                .bearer_auth(token)
                .query(&params)
                .send()
                .await?
                .error_for_status()?
                .json()
                .await?;
            files.extend(result.files);
            match result.next {
                Some(next) => page = next,
                None => break,
            }
        }
        Ok(files)
    }
    async fn folder(&mut self, name: &str, parent: &str) -> Result<String> {
        let query = format!(
            "trashed=false and mimeType='application/vnd.google-apps.folder' and name='{name}' and '{parent}' in parents"
        );
        let mut found = self.list(&query).await?;
        if found.len() > 1 {
            return Err(
                format!("Hay varias carpetas {name}; resuelva el duplicado en Drive").into(),
            );
        }
        if let Some(file) = found.pop() {
            return Ok(file.id);
        }
        let token = self.token().await?;
        let file: DriveFile = self.http.post(API).bearer_auth(token).json(&json!({"name":name,"mimeType":"application/vnd.google-apps.folder","parents":[parent]})).send().await?.error_for_status()?.json().await?;
        Ok(file.id)
    }
    async fn folders(&mut self) -> Result<[String; 2]> {
        let root = self.folder("Backup_ReadyShow", "root").await?;
        Ok([
            self.folder("cantos", &root).await?,
            self.folder("biblias", &root).await?,
        ])
    }
    async fn upload(&mut self, folder: &str, name: &str, bytes: Vec<u8>) -> Result<()> {
        let token = self.token().await?;
        // MIME multipart/related, not multipart/form-data.
        let boundary = CsrfToken::new_random().secret().clone();
        let metadata = serde_json::to_string(
            &json!({"name":name,"mimeType":"application/json","parents":[folder]}),
        )?;
        let mut body=format!("--{boundary}\r\nContent-Type: application/json; charset=UTF-8\r\n\r\n{metadata}\r\n--{boundary}\r\nContent-Type: application/json\r\n\r\n").into_bytes();
        body.extend(bytes);
        body.extend(format!("\r\n--{boundary}--\r\n").as_bytes());
        self.http
            .post("https://www.googleapis.com/upload/drive/v3/files")
            .query(&[("uploadType", "multipart")])
            .bearer_auth(token)
            .header(
                reqwest::header::CONTENT_TYPE,
                format!("multipart/related; boundary={boundary}"),
            )
            .body(body)
            .send()
            .await?
            .error_for_status()?;
        Ok(())
    }
    async fn download(&mut self, id: &str) -> Result<Delta> {
        let token = self.token().await?;
        Ok(self
            .http
            .get(format!("{API}/{id}"))
            .query(&[("alt", "media")])
            .bearer_auth(token)
            .send()
            .await?
            .error_for_status()?
            .json()
            .await?)
    }
}
fn authorization_error(error: &str) -> &'static str {
    match error {
        "access_denied" => {
            "Google no autorizó el acceso. Si indica que ReadyShow está en pruebas, el desarrollador debe habilitar tu cuenta o publicar la aplicación"
        }
        _ => "Google no pudo autorizar el acceso a Drive. Intenta iniciar sesión nuevamente",
    }
}
const GOOGLE_CONFIG_FILE: &str = "google_oauth.json";
#[derive(Clone, Serialize, Deserialize)]
struct GoogleOAuthConfig {
    client_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    client_secret: Option<String>,
}
#[derive(Serialize, Deserialize)]
struct GoogleCredentials {
    installed: GoogleOAuthConfig,
}
fn parse_google_config(bytes: &[u8]) -> Result<GoogleOAuthConfig> {
    let mut config = serde_json::from_slice::<GoogleCredentials>(bytes)
        .map_err(|_| "Selecciona el JSON de un cliente OAuth de tipo Aplicación de escritorio, no una API key ni una cuenta de servicio")?.installed;
    config.client_id = config.client_id.trim().to_string();
    if !config.client_id.ends_with(".apps.googleusercontent.com")
        || config.client_id.chars().any(char::is_whitespace)
    {
        return Err("El JSON no contiene un client_id válido de Google".into());
    }
    config.client_secret = config
        .client_secret
        .map(|v| v.trim().to_string())
        .filter(|v| !v.is_empty());
    Ok(config)
}
const BUNDLED_GOOGLE_CONFIG: &str = include_str!(concat!(env!("OUT_DIR"), "/google_oauth.json"));
fn load_google_config(dir: &Path) -> Result<GoogleOAuthConfig> {
    let environment = std::env::var("READYSHOW_GOOGLE_CLIENT_ID")
        .ok()
        .filter(|id| !id.trim().is_empty())
        .map(|id| GoogleOAuthConfig {
            client_id: id,
            client_secret: std::env::var("READYSHOW_GOOGLE_CLIENT_SECRET").ok(),
        });
    resolve_google_config(dir, BUNDLED_GOOGLE_CONFIG, environment)
}
fn resolve_google_config(
    dir: &Path,
    bundled: &str,
    environment: Option<GoogleOAuthConfig>,
) -> Result<GoogleOAuthConfig> {
    if !bundled.trim().is_empty() {
        return parse_google_config(bundled.as_bytes());
    }
    // Development/older-installation compatibility; never ask users for a JSON.
    if let Some(config) = environment {
        return parse_google_config(&serde_json::to_vec(&GoogleCredentials {
            installed: config,
        })?);
    }
    match std::fs::read(dir.join(GOOGLE_CONFIG_FILE)) {
        Ok(bytes) => parse_google_config(&bytes),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Err("Esta versión de ReadyShow no incluye un cliente de Google Drive. El desarrollador debe configurar el cliente OAuth al compilar la aplicación".into()),
        Err(_) => Err("No se pudo leer la configuración de Google Drive de esta versión de ReadyShow".into()),
    }
}

fn oauth_client(
    config: &GoogleOAuthConfig,
) -> Result<
    oauth2::basic::BasicClient<
        oauth2::EndpointSet,
        oauth2::EndpointNotSet,
        oauth2::EndpointNotSet,
        oauth2::EndpointNotSet,
        oauth2::EndpointSet,
    >,
> {
    let mut client = BasicClient::new(ClientId::new(config.client_id.clone()))
        .set_auth_uri(AuthUrl::new(
            "https://accounts.google.com/o/oauth2/v2/auth".into(),
        )?)
        .set_token_uri(TokenUrl::new("https://oauth2.googleapis.com/token".into())?);
    if let Some(secret) = &config.client_secret {
        client = client.set_client_secret(ClientSecret::new(secret.clone()));
    }
    Ok(client)
}

#[derive(Clone, Copy)]
pub enum Command {
    Login,
    Restore,
}
#[derive(Clone)]
pub struct Status {
    pub text: String,
    pub busy: bool,
    pub connected: bool,
    pub restored: bool,
}
fn status(
    report: &impl Fn(Status),
    text: impl Into<String>,
    busy: bool,
    connected: bool,
    restored: bool,
) {
    report(Status {
        text: text.into(),
        busy,
        connected,
        restored,
    });
}
async fn backup(drive: &mut Drive, dir: &Path, folders: &[String; 2]) -> Result<()> {
    for (index, dataset) in [Dataset::Cantos, Dataset::Biblias].into_iter().enumerate() {
        let path = dir.join(format!("{}.db", dataset.name()));
        let p = path.clone();
        let folder = folders[index].clone();
        let delta =
            tokio::task::spawn_blocking(move || snapshot_for(&p, dataset, Some(&folder))).await??;
        if delta.changes.is_empty() {
            continue;
        }
        let through = delta.through;
        let source = delta.source.clone();
        let name = format!(
            "{}_delta_{:016}_{}.json",
            dataset.name(),
            through,
            CsrfToken::new_random().secret()
        );
        let bytes = tokio::task::spawn_blocking(move || serde_json::to_vec(&delta)).await??;
        drive.upload(&folders[index], &name, bytes).await?;
        let folder = folders[index].clone();
        tokio::task::spawn_blocking(move || {
            acknowledge_for(&path, dataset, through, &folder, &source)
        })
        .await??;
    }
    Ok(())
}
async fn restore(drive: &mut Drive, dir: &Path, folders: &[String; 2]) -> Result<()> {
    for (index, dataset) in [Dataset::Cantos, Dataset::Biblias].into_iter().enumerate() {
        let query = format!(
            "trashed=false and mimeType='application/json' and '{}' in parents",
            folders[index]
        );
        let files = drive.list(&query).await?;
        let mut deltas = Vec::new();
        for file in files {
            if file.name.starts_with(&format!("{}_delta_", dataset.name())) {
                deltas.push(drive.download(&file.id).await?);
            }
        }
        deltas.sort_by_key(|d| d.through);
        let path = dir.join(format!("{}.db", dataset.name()));
        tokio::task::spawn_blocking(move || merge(&path, dataset, deltas)).await??;
    }
    Ok(())
}
/// One serialized worker avoids races between login, uploads and restore.
pub fn start(
    dir: PathBuf,
    report: impl Fn(Status) + Send + Sync + 'static,
) -> mpsc::Sender<Command> {
    let report = std::sync::Arc::new(report);
    let (tx, mut rx) = mpsc::channel(4);
    std::thread::spawn(move || {
        let runtime = match tokio::runtime::Builder::new_multi_thread()
            .worker_threads(2)
            .enable_all()
            .build()
        {
            Ok(r) => r,
            Err(e) => {
                status(
                    &*report,
                    format!("No se pudo iniciar el respaldo: {e}"),
                    false,
                    false,
                    false,
                );
                return;
            }
        };
        runtime.block_on(async move {
            let worker = tokio::spawn(async move {
                let mut drive: Option<Drive> = None;
                let mut folders: Option<[String; 2]> = None;
                let mut next_backup = Instant::now() + INTERVAL;
                loop {
                    let command = if drive.is_some() {
                        match tokio::time::timeout(
                            next_backup.saturating_duration_since(Instant::now()),
                            rx.recv(),
                        )
                        .await
                        {
                            Ok(Some(c)) => Some(c),
                            Ok(None) => break,
                            Err(_) => None,
                        }
                    } else {
                        match rx.recv().await {
                            Some(c) => Some(c),
                            None => break,
                        }
                    };
                    let is_restore = matches!(command, Some(Command::Restore));
                    status(
                        &*report,
                        if is_restore {
                            "Restaurando datos..."
                        } else {
                            "Sincronizando..."
                        },
                        true,
                        drive.is_some(),
                        false,
                    );
                    let result: Result<()> = async {
                        if drive.is_none() || matches!(command, Some(Command::Login)) {
                            status(
                                &*report,
                                "Esperando autorización de Google en tu navegador...",
                                true,
                                false,
                                false,
                            );
                            drive = Some(Drive::login(&dir, &*report).await?);
                            folders = None;
                        }
                        let d = drive.as_mut().ok_or("Desconectado")?;
                        if folders.is_none() {
                            status(
                                &*report,
                                "Preparando carpetas de respaldo en Google Drive...",
                                true,
                                true,
                                false,
                            );
                            folders = Some(d.folders().await?);
                        }
                        let f = folders.as_ref().ok_or("Carpetas no disponibles")?;
                        if is_restore {
                            status(
                                &*report,
                                "Descargando y restaurando datos...",
                                true,
                                true,
                                false,
                            );
                            restore(d, &dir, f).await
                        } else {
                            status(
                                &*report,
                                "Guardando datos en Google Drive...",
                                true,
                                true,
                                false,
                            );
                            backup(d, &dir, f).await
                        }
                    }
                    .await;
                    next_backup = Instant::now() + INTERVAL;
                    let report = report.clone();
                    let connected = drive.is_some();
                    tokio::task::spawn_blocking(move || {
                        match result {
                            Ok(()) => status(
                                &*report,
                                if is_restore {
                                    "Datos restaurados"
                                } else {
                                    "Sincronizado"
                                },
                                false,
                                true,
                                is_restore,
                            ),
                            // Each database commits independently; refresh any successfully restored data on error too.
                            Err(e) => status(
                                &*report,
                                format!("Error de respaldo: {e}"),
                                false,
                                connected,
                                is_restore,
                            ),
                        }
                    })
                    .await?;
                }
                Ok::<(), Error>(())
            });
            let _ = worker.await;
        });
    });
    tx
}

#[cfg(test)]
mod tests {
    use super::*;
    struct Database(PathBuf);
    impl Database {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "readyshow-sync-{}.db",
                CsrfToken::new_random().secret()
            ));
            let conn = Connection::open(&path).unwrap();
            conn.execute_batch("CREATE TABLE cantos(id INTEGER PRIMARY KEY AUTOINCREMENT,titulo TEXT NOT NULL,tono TEXT,categoria TEXT);
                CREATE TABLE diapositivas(id INTEGER PRIMARY KEY AUTOINCREMENT,canto_id INTEGER,orden INTEGER,texto TEXT);
                CREATE TABLE favoritos(id INTEGER PRIMARY KEY AUTOINCREMENT,tipo TEXT NOT NULL DEFAULT 'canto',ref_id INTEGER NOT NULL DEFAULT 0,referencia TEXT NOT NULL DEFAULT '',titulo TEXT NOT NULL DEFAULT '',version TEXT NOT NULL DEFAULT '');
                INSERT INTO cantos VALUES(1,'Original','',''); INSERT INTO diapositivas VALUES(1,1,1,'Letra original');").unwrap();
            Self(path)
        }
        fn conn(&self) -> Connection {
            open(&self.0, Dataset::Cantos).unwrap()
        }
    }
    impl Drop for Database {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    #[test]
    fn bundled_client_works_without_user_json_and_has_priority() {
        let dir = std::env::temp_dir().join(format!(
            "readyshow-oauth-{}",
            CsrfToken::new_random().secret()
        ));
        let bundled = r#"{"installed":{"client_id":"123-readyshow.apps.googleusercontent.com","client_secret":"test-secret"}}"#;
        let loaded = resolve_google_config(
            &dir,
            bundled,
            Some(GoogleOAuthConfig {
                client_id: "other.apps.googleusercontent.com".into(),
                client_secret: None,
            }),
        )
        .unwrap();
        assert_eq!(loaded.client_id, "123-readyshow.apps.googleusercontent.com");
        assert_eq!(loaded.client_secret.as_deref(), Some("test-secret"));
        assert!(!dir.exists());
    }
    #[test]
    fn version_without_client_explains_app_configuration_to_developer() {
        let dir = std::env::temp_dir().join(format!(
            "readyshow-oauth-{}",
            CsrfToken::new_random().secret()
        ));
        let message = resolve_google_config(&dir, "", None)
            .err()
            .unwrap()
            .to_string();
        assert!(message.contains("desarrollador"));
        assert!(!message.contains("JSON"));
        assert!(!dir.exists());
    }
    #[test]
    fn compiled_client_can_be_loaded_without_a_user_configuration_file() {
        if BUNDLED_GOOGLE_CONFIG.is_empty() {
            return;
        }
        let dir = std::env::temp_dir().join(format!(
            "readyshow-oauth-{}",
            CsrfToken::new_random().secret()
        ));
        assert!(load_google_config(&dir).is_ok());
        assert!(!dir.exists());
    }
    #[test]
    fn existing_local_configuration_still_works_in_development() {
        let dir = std::env::temp_dir().join(format!(
            "readyshow-oauth-{}",
            CsrfToken::new_random().secret()
        ));
        std::fs::create_dir(&dir).unwrap();
        std::fs::write(
            dir.join(GOOGLE_CONFIG_FILE),
            br#"{"installed":{"client_id":"123-readyshow.apps.googleusercontent.com"}}"#,
        )
        .unwrap();
        assert_eq!(
            resolve_google_config(&dir, "", None).unwrap().client_id,
            "123-readyshow.apps.googleusercontent.com"
        );
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn google_denial_explains_testing_restriction_without_asking_for_json() {
        assert!(authorization_error("access_denied").contains("en pruebas"));
        assert!(!authorization_error("access_denied").contains("JSON"));
    }
    #[test]
    fn oauth_configuration_rejects_api_keys_service_accounts_and_empty_ids() {
        for json in [
            br#"{"api_key":"test"}"#.as_slice(),
            br#"{"type":"service_account","client_id":"123"}"#,
            br#"{"installed":{"client_id":""}}"#,
            br#"{"installed":{"client_id":"AIza-test"}}"#,
        ] {
            assert!(parse_google_config(json).is_err());
        }
    }
    #[test]
    fn migration_preserves_rows_and_dates_existing_data_now() {
        let db = Database::new();
        let before = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as i64;
        let mut conn = db.conn();
        let (id, title, stamp, deleted): (i64, String, i64, i64) = conn
            .query_row(
                "SELECT id,titulo,updated_at,is_deleted FROM cantos",
                [],
                |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?)),
            )
            .unwrap();
        assert_eq!((id, title, deleted), (1, "Original".into(), 0));
        assert!(stamp >= before - 1);
        assert_eq!(
            conn.query_row("SELECT texto FROM diapositivas WHERE id=1", [], |r| r
                .get::<_, String>(0))
                .unwrap(),
            "Letra original"
        );
        conn.execute(
            "UPDATE sync_metadata SET last_sync_timestamp=42 WHERE id=1",
            [],
        )
        .unwrap();
        let pending: i64 = conn
            .query_row("SELECT COUNT(*) FROM sync_changes", [], |r| r.get(0))
            .unwrap();
        migrate(&mut conn, Dataset::Cantos).unwrap();
        assert_eq!(
            conn.query_row("SELECT updated_at FROM cantos WHERE id=1", [], |r| r
                .get::<_, i64>(0))
                .unwrap(),
            stamp
        );
        assert_eq!(
            conn.query_row("SELECT last_sync_timestamp FROM sync_metadata", [], |r| r
                .get::<_, i64>(
                0
            ))
            .unwrap(),
            42
        );
        assert_eq!(
            conn.query_row("SELECT COUNT(*) FROM sync_changes", [], |r| r
                .get::<_, i64>(0))
                .unwrap(),
            pending
        );
    }
    #[test]
    fn partial_schema_adds_only_missing_columns_and_preserves_sync_marker() {
        let db = Database::new();
        let mut conn = Connection::open(&db.0).unwrap();
        conn.execute_batch(
            "ALTER TABLE cantos ADD COLUMN updated_at TIMESTAMP NOT NULL DEFAULT 123;
            CREATE TABLE sync_metadata(id INTEGER PRIMARY KEY, last_sync_timestamp INTEGER);
            INSERT INTO sync_metadata VALUES(1,777);",
        )
        .unwrap();
        migrate(&mut conn, Dataset::Cantos).unwrap();
        assert_eq!(
            conn.query_row("SELECT updated_at FROM cantos WHERE id=1", [], |r| r
                .get::<_, i64>(0))
                .unwrap(),
            123
        );
        assert_eq!(
            conn.query_row("SELECT is_deleted FROM cantos WHERE id=1", [], |r| r
                .get::<_, i64>(0))
                .unwrap(),
            0
        );
        assert_eq!(
            conn.query_row("SELECT last_sync_timestamp FROM sync_metadata", [], |r| r
                .get::<_, i64>(
                0
            ))
            .unwrap(),
            777
        );
        assert_eq!(snapshot(&db.0, Dataset::Cantos).unwrap().changes.len(), 2);
    }
    #[test]
    fn failed_migration_rolls_back_schema_and_keeps_original_records() {
        let db = Database::new();
        let mut conn = Connection::open(&db.0).unwrap();
        conn.execute_batch("DROP TABLE diapositivas; CREATE TABLE diapositivas(unexpected TEXT);")
            .unwrap();
        assert!(migrate(&mut conn, Dataset::Cantos).is_err());
        assert!(
            !columns(&conn, "cantos")
                .unwrap()
                .iter()
                .any(|c| c == "updated_at" || c == "is_deleted")
        );
        assert_eq!(
            conn.query_row("SELECT titulo FROM cantos WHERE id=1", [], |r| r
                .get::<_, String>(0))
                .unwrap(),
            "Original"
        );
        let exists: bool = conn
            .query_row(
                "SELECT EXISTS(SELECT 1 FROM sqlite_master WHERE name='sync_metadata')",
                [],
                |r| r.get(0),
            )
            .unwrap();
        assert!(!exists);
    }
    #[test]
    fn preparing_local_files_never_overwrites_an_existing_database() {
        let db = Database::new();
        let before = std::fs::read(&db.0).unwrap();
        let absent_seed = db.0.with_extension("missing-seed");
        prepare_local_file(&db.0, &absent_seed).unwrap();
        assert_eq!(std::fs::read(&db.0).unwrap(), before);
        let new_path = db.0.with_extension("missing-target");
        assert!(prepare_local_file(&new_path, &absent_seed).is_err());
        assert!(!new_path.exists());
    }
    #[test]
    fn migration_is_idempotent_and_baseline_contains_children() {
        let db = Database::new();
        let mut conn = db.conn();
        migrate(&mut conn, Dataset::Cantos).unwrap();
        let delta = snapshot(&db.0, Dataset::Cantos).unwrap();
        assert_eq!(delta.changes.len(), 2);
        assert!(delta.changes.iter().any(|c| c.table == "diapositivas"));
    }
    #[test]
    fn acknowledging_snapshot_preserves_concurrent_edits() {
        let db = Database::new();
        let conn = db.conn();
        let first = snapshot(&db.0, Dataset::Cantos).unwrap();
        conn.execute("UPDATE cantos SET titulo='Cambio posterior' WHERE id=1", [])
            .unwrap();
        acknowledge(&db.0, Dataset::Cantos, first.through).unwrap();
        let delta = snapshot(&db.0, Dataset::Cantos).unwrap();
        assert_eq!(delta.changes.len(), 1);
        assert_eq!(delta.changes[0].row["titulo"], "Cambio posterior");
        assert!(delta.through > first.through);
    }
    #[test]
    fn replay_is_idempotent_and_tombstones_prevent_resurrection() {
        let source = Database::new();
        let target = Database::new();
        let conn = source.conn();
        conn.execute("UPDATE cantos SET titulo='Actualizado' WHERE id=1", [])
            .unwrap();
        let edit = snapshot(&source.0, Dataset::Cantos).unwrap();
        let saved = serde_json::to_vec(&edit).unwrap();
        assert!(merge(&target.0, Dataset::Cantos, vec![edit]).unwrap() > 0);
        assert_eq!(
            merge(
                &target.0,
                Dataset::Cantos,
                vec![serde_json::from_slice(&saved).unwrap()]
            )
            .unwrap(),
            0
        );
        acknowledge(
            &source.0,
            Dataset::Cantos,
            snapshot(&source.0, Dataset::Cantos).unwrap().through,
        )
        .unwrap();
        conn.execute("DELETE FROM diapositivas WHERE canto_id=1", [])
            .unwrap();
        conn.execute("DELETE FROM cantos WHERE id=1", []).unwrap();
        merge(
            &target.0,
            Dataset::Cantos,
            vec![snapshot(&source.0, Dataset::Cantos).unwrap()],
        )
        .unwrap();
        merge(
            &target.0,
            Dataset::Cantos,
            vec![serde_json::from_slice(&saved).unwrap()],
        )
        .unwrap();
        assert_eq!(
            target
                .conn()
                .query_row("SELECT COUNT(*) FROM cantos", [], |r| r.get::<_, i64>(0))
                .unwrap(),
            0
        );
        // Imported changes don't produce a feedback loop in the outbox.
        assert_eq!(
            snapshot(&target.0, Dataset::Cantos).unwrap().changes.len(),
            0
        );
    }
    #[test]
    fn new_remote_receives_full_snapshot_after_journal_was_pruned() {
        let db = Database::new();
        let conn = db.conn();
        conn.execute("UPDATE cantos SET titulo='Respaldado' WHERE id=1", [])
            .unwrap();
        let first = snapshot_for(&db.0, Dataset::Cantos, Some("folder-a")).unwrap();
        acknowledge_for(
            &db.0,
            Dataset::Cantos,
            first.through,
            "folder-a",
            &first.source,
        )
        .unwrap();
        assert!(
            snapshot_for(&db.0, Dataset::Cantos, Some("folder-a"))
                .unwrap()
                .changes
                .is_empty()
        );
        let next = snapshot_for(&db.0, Dataset::Cantos, Some("folder-b")).unwrap();
        assert_eq!(next.changes.len(), 2);
        assert_eq!(next.from, 0);
        assert!(
            next.changes
                .iter()
                .any(|c| c.row.get("titulo") == Some(&json!("Respaldado")))
        );
    }
    #[test]
    fn bible_versions_and_verses_restore_together() {
        let source = Database::new();
        let target = Database::new();
        for db in [&source, &target] {
            Connection::open(&db.0).unwrap().execute_batch("CREATE TABLE versiones(id INTEGER PRIMARY KEY AUTOINCREMENT,nombre TEXT UNIQUE);
                CREATE TABLE versiculos(id INTEGER PRIMARY KEY AUTOINCREMENT,version_id INTEGER,libro_nombre TEXT,libro_numero INTEGER,capitulo INTEGER,versiculo INTEGER,texto TEXT,FOREIGN KEY(version_id) REFERENCES versiones(id));").unwrap();
        }
        let conn = open(&source.0, Dataset::Biblias).unwrap();
        conn.execute(
            "INSERT INTO versiones(id,nombre) VALUES(7,'Nueva versión')",
            [],
        )
        .unwrap();
        conn.execute("INSERT INTO versiculos(id,version_id,libro_nombre,libro_numero,capitulo,versiculo,texto) VALUES(12,7,'Génesis',1,1,1,'Texto restaurado')", []).unwrap();
        let delta = snapshot_for(&source.0, Dataset::Biblias, None).unwrap();
        assert_eq!(merge(&target.0, Dataset::Biblias, vec![delta]).unwrap(), 2);
        let conn = open(&target.0, Dataset::Biblias).unwrap();
        assert_eq!(
            conn.query_row("SELECT texto FROM versiculos WHERE id=12", [], |r| r
                .get::<_, String>(0))
                .unwrap(),
            "Texto restaurado"
        );
        assert_eq!(
            conn.query_row("SELECT nombre FROM versiones WHERE id=7", [], |r| r
                .get::<_, String>(0))
                .unwrap(),
            "Nueva versión"
        );
    }
    #[test]
    fn acknowledgement_from_another_database_cannot_prune_pending_changes() {
        let source = Database::new();
        let other = Database::new();
        let source_delta = snapshot(&source.0, Dataset::Cantos).unwrap();
        assert!(
            acknowledge_for(
                &other.0,
                Dataset::Cantos,
                source_delta.through,
                "folder-a",
                &source_delta.source
            )
            .is_err()
        );
        assert_eq!(
            snapshot(&other.0, Dataset::Cantos).unwrap().changes.len(),
            2
        );
    }
    #[test]
    fn legacy_backup_restores_content_different_from_installation_seed() {
        let source = Database::new();
        let target = Database::new();
        Connection::open(&source.0)
            .unwrap()
            .execute(
                "UPDATE cantos SET titulo='Personalizado antes de migrar' WHERE id=1",
                [],
            )
            .unwrap();
        let delta = snapshot(&source.0, Dataset::Cantos).unwrap();
        let bytes = serde_json::to_vec(&delta).unwrap();
        assert_eq!(merge(&target.0, Dataset::Cantos, vec![delta]).unwrap(), 2);
        assert_eq!(
            merge(
                &target.0,
                Dataset::Cantos,
                vec![serde_json::from_slice(&bytes).unwrap()]
            )
            .unwrap(),
            0
        );
        assert_eq!(
            target
                .conn()
                .query_row("SELECT titulo FROM cantos WHERE id=1", [], |r| r
                    .get::<_, String>(0))
                .unwrap(),
            "Personalizado antes de migrar"
        );
    }
    #[test]
    fn boolean_tombstone_is_accepted() {
        let source = Database::new();
        let target = Database::new();
        let conn = source.conn();
        conn.execute("DELETE FROM diapositivas WHERE canto_id=1", [])
            .unwrap();
        let mut delta = snapshot(&source.0, Dataset::Cantos).unwrap();
        for change in &mut delta.changes {
            if change.row.get("is_deleted") == Some(&json!(1)) {
                change.row.insert("is_deleted".into(), json!(true));
            }
        }
        merge(&target.0, Dataset::Cantos, vec![delta]).unwrap();
        assert_eq!(
            target
                .conn()
                .query_row("SELECT COUNT(*) FROM diapositivas", [], |r| r
                    .get::<_, i64>(0))
                .unwrap(),
            0
        );
    }
    #[test]
    fn invalid_delta_rolls_back_changes_and_suppression() {
        let source = Database::new();
        let target = Database::new();
        source
            .conn()
            .execute("UPDATE cantos SET titulo='Nuevo' WHERE id=1", [])
            .unwrap();
        let mut delta = snapshot(&source.0, Dataset::Cantos).unwrap();
        delta.changes.push(Change {
            table: "sqlite_master".into(),
            row: BTreeMap::new(),
        });
        assert!(merge(&target.0, Dataset::Cantos, vec![delta]).is_err());
        let conn = target.conn();
        assert_eq!(
            conn.query_row("SELECT titulo FROM cantos WHERE id=1", [], |r| r
                .get::<_, String>(0))
                .unwrap(),
            "Original"
        );
        assert_eq!(
            conn.query_row("SELECT suppress FROM sync_metadata", [], |r| r
                .get::<_, i64>(0))
                .unwrap(),
            0
        );
    }
}
