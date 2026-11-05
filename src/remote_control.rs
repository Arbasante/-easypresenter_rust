//! LAN remote: HTTP workers never touch Slint objects outside its event loop.
use super::*;
use serde_json::{Value, json};
use std::io::{Cursor, Read};
use std::sync::atomic::AtomicUsize;
use std::sync::mpsc;
use std::time::{Duration, Instant};
use tiny_http::{Header, Method, Request, Response, Server};

const PORT: u16 = 8091;
const MAX_BODY: usize = 8192;
type Screen = Arc<Mutex<Option<(i32, i32, u32, u32)>>>;
type Handler = dyn Fn(ApiRequest) -> Result<Reply, String> + Send + Sync;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Selection {
    Song {
        id: i32,
    },
    Chapter {
        book: i32,
        chapter: i32,
        version: i32,
    },
    Image {
        id: String,
    },
    Video {
        id: String,
    },
}

#[derive(Debug, Deserialize)]
#[serde(tag = "action", rename_all = "snake_case", deny_unknown_fields)]
enum ApiRequest {
    Catalog,
    Books { version: i32 },
    Load { selection: Selection },
    Thumbnail { selection: Selection },
    Project { selection: Selection, number: i32 },
    Status,
    Playback { control: String },
}

enum Reply {
    Json(Value),
    Thumbnail(std::path::PathBuf),
}

struct RemoteServer {
    server: Arc<Server>,
    active: Arc<AtomicBool>,
    thread: Option<thread::JoinHandle<()>>,
    token: String,
}

fn response(request: Request, status: u16, mime: &str, bytes: Vec<u8>) {
    let _ = request.respond(
        Response::from_data(bytes)
            .with_status_code(status)
            .with_header(Header::from_bytes("Content-Type", mime).unwrap())
            .with_header(Header::from_bytes("Cache-Control", "no-store").unwrap())
            .with_header(Header::from_bytes("X-Content-Type-Options", "nosniff").unwrap())
            .with_header(Header::from_bytes("Referrer-Policy", "no-referrer").unwrap())
            .with_header(Header::from_bytes("Content-Security-Policy", "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' blob:; media-src 'self' blob:; object-src 'none'; connect-src 'self'; worker-src 'self'; manifest-src 'self'; frame-ancestors 'none'; base-uri 'none'").unwrap()),
    );
}

fn error(request: Request, status: u16, message: &str) {
    response(
        request,
        status,
        "application/json",
        serde_json::to_vec(&json!({"error":message})).unwrap(),
    );
}

fn authenticated(request: &Request, token: &str) -> bool {
    let expected = format!("Bearer {token}");
    request
        .headers()
        .iter()
        .find(|h| h.field.equiv("Authorization"))
        .is_some_and(|h| {
            let actual = h.value.as_str().as_bytes();
            actual.len() == expected.len()
                && actual
                    .iter()
                    .zip(expected.as_bytes())
                    .fold(0u8, |acc, (a, b)| acc | (a ^ b))
                    == 0
        })
}

fn same_origin(request: &Request) -> bool {
    let origin = request.headers().iter().find(|h| h.field.equiv("Origin"));
    let host = request.headers().iter().find(|h| h.field.equiv("Host"));
    match (origin, host) {
        (None, _) => true, // Native clients and tests; the bearer token is still required.
        (Some(origin), Some(host)) => ["http://", "https://"]
            .iter()
            .any(|scheme| origin.value.as_str() == format!("{scheme}{}", host.value)),
        _ => false,
    }
}

fn serve(mut request: Request, token: &str, handler: &dyn Fn(ApiRequest) -> Result<Reply, String>) {
    let path = request.url().split('?').next().unwrap_or("").to_string();
    if path != "/api" {
        if !matches!(request.method(), Method::Get | Method::Head) {
            return error(request, 405, "Método no permitido");
        }
        let asset: Option<(&str, &[u8])> = match path.as_str() {
            "/" | "/index.html" => Some((
                "text/html; charset=utf-8",
                include_bytes!("../remote-pwa/index.html"),
            )),
            "/app.js" => Some((
                "text/javascript; charset=utf-8",
                include_bytes!("../remote-pwa/app.js"),
            )),
            "/modules/ui.js" => Some((
                "text/javascript; charset=utf-8",
                include_bytes!("../remote-pwa/modules/ui.js"),
            )),
            "/modules/storage.js" => Some((
                "text/javascript; charset=utf-8",
                include_bytes!("../remote-pwa/modules/storage.js"),
            )),
            "/modules/migration.js" => Some((
                "text/javascript; charset=utf-8",
                include_bytes!("../remote-pwa/modules/migration.js"),
            )),
            "/modules/local.js" => Some((
                "text/javascript; charset=utf-8",
                include_bytes!("../remote-pwa/modules/local.js"),
            )),
            "/modules/remote.js" => Some((
                "text/javascript; charset=utf-8",
                include_bytes!("../remote-pwa/modules/remote.js"),
            )),
            "/modules/projection.js" => Some((
                "text/javascript; charset=utf-8",
                include_bytes!("../remote-pwa/modules/projection.js"),
            )),
            "/modules/pwa.js" => Some((
                "text/javascript; charset=utf-8",
                include_bytes!("../remote-pwa/modules/pwa.js"),
            )),
            "/styles.css" => Some((
                "text/css; charset=utf-8",
                include_bytes!("../remote-pwa/styles.css"),
            )),
            "/sw.js" => Some((
                "text/javascript; charset=utf-8",
                include_bytes!("../remote-pwa/sw.js"),
            )),
            "/manifest.webmanifest" => Some((
                "application/manifest+json",
                include_bytes!("../remote-pwa/manifest.webmanifest"),
            )),
            "/icon-192.png" => Some(("image/png", include_bytes!("../remote-pwa/icon-192.png"))),
            "/icon-maskable-512.png" => Some((
                "image/png",
                include_bytes!("../remote-pwa/icon-maskable-512.png"),
            )),
            "/icon-512.png" => Some(("image/png", include_bytes!("../remote-pwa/icon-512.png"))),
            _ => None,
        };
        return match asset {
            Some((mime, body)) => response(request, 200, mime, body.to_vec()),
            None => error(request, 404, "No encontrado"),
        };
    }
    if request.method() != &Method::Post {
        return error(request, 405, "Usa POST");
    }
    if !authenticated(&request, token) {
        return error(request, 401, "Código incorrecto o sesión finalizada");
    }
    if !same_origin(&request) {
        return error(request, 403, "Origen no permitido");
    }
    if !request.headers().iter().any(|h| {
        h.field.equiv("Content-Type")
            && h.value.as_str().split(';').next() == Some("application/json")
    }) {
        return error(request, 415, "Se requiere JSON");
    }
    if request.body_length().is_some_and(|len| len > MAX_BODY) {
        return error(request, 413, "Solicitud demasiado grande");
    }
    let mut body = Vec::new();
    if request
        .as_reader()
        .take((MAX_BODY + 1) as u64)
        .read_to_end(&mut body)
        .is_err()
        || body.len() > MAX_BODY
    {
        return error(request, 413, "Solicitud inválida o demasiado grande");
    }
    let action = match serde_json::from_slice(&body) {
        Ok(action) => action,
        Err(_) => return error(request, 400, "Acción inválida"),
    };
    match handler(action) {
        Ok(Reply::Json(value)) => response(
            request,
            200,
            "application/json",
            serde_json::to_vec(&value).unwrap(),
        ),
        Ok(Reply::Thumbnail(path)) => {
            // Only registered library paths can reach here. Resize on this worker, never on the UI.
            let thumbnail = image::ImageReader::open(path)
                .ok()
                .and_then(|r| r.decode().ok())
                .and_then(|img| {
                    let mut bytes = Cursor::new(Vec::new());
                    img.thumbnail(360, 240)
                        .write_to(&mut bytes, image::ImageFormat::Png)
                        .ok()?;
                    Some(bytes.into_inner())
                });
            match thumbnail {
                Some(bytes) => response(request, 200, "image/png", bytes),
                None => error(request, 404, "Miniatura no disponible"),
            }
        }
        Err(message) => error(request, 400, &message),
    }
}

impl RemoteServer {
    fn start(port: u16, handler: Arc<Handler>, active: Arc<AtomicBool>) -> Result<Self, String> {
        let mut random = [0u8; 16];
        getrandom::fill(&mut random).map_err(|e| e.to_string())?;
        let token: String = random.iter().map(|b| format!("{b:02x}")).collect();
        let server = Arc::new(Server::http(("0.0.0.0", port)).map_err(|e| e.to_string())?);
        let (srv, flag, secret) = (server.clone(), active.clone(), token.clone());
        let thread = thread::Builder::new()
            .name("remote-http".into())
            .spawn(move || {
                let workers = Arc::new(AtomicUsize::new(0));
                while flag.load(Ordering::Acquire) {
                    let request = match srv.recv_timeout(Duration::from_millis(100)) {
                        Ok(Some(r)) => r,
                        Ok(None) => continue,
                        Err(_) => break,
                    };
                    if workers.fetch_add(1, Ordering::AcqRel) >= 8 {
                        workers.fetch_sub(1, Ordering::AcqRel);
                        error(request, 503, "Servidor ocupado");
                        continue;
                    }
                    let (workers, handler, token, active) = (
                        workers.clone(),
                        handler.clone(),
                        secret.clone(),
                        flag.clone(),
                    );
                    thread::spawn(move || {
                        struct Permit(Arc<AtomicUsize>);
                        impl Drop for Permit {
                            fn drop(&mut self) {
                                self.0.fetch_sub(1, Ordering::AcqRel);
                            }
                        }
                        let _permit = Permit(workers);
                        let guarded = |action| {
                            if !active.load(Ordering::Acquire) {
                                return Err("Control remoto desactivado".into());
                            }
                            handler(action)
                        };
                        serve(request, &token, &guarded);
                    });
                }
            })
            .map_err(|e| e.to_string())?;
        Ok(Self {
            server,
            active,
            thread: Some(thread),
            token,
        })
    }
}
impl Drop for RemoteServer {
    fn drop(&mut self) {
        self.active.store(false, Ordering::Release);
        self.server.unblock();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn media_id(path: &str) -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    path.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

struct Context {
    state: Arc<Mutex<AppState>>,
    overlay: Arc<Mutex<EstadoOverlay>>,
    screen: Screen,
    book: Arc<Mutex<i32>>,
    chapter: Arc<Mutex<i32>>,
}

impl Context {
    fn books(&self, version: i32) -> Result<Value, String> {
        let state = self.state.lock().unwrap();
        if !state.versiones.iter().any(|v| v.id == version) {
            return Err("Versión no disponible".into());
        }
        let mut stmt = state.biblias_db.prepare_cached("SELECT libro_numero, libro_nombre, MAX(capitulo) FROM versiculos WHERE version_id=? GROUP BY libro_numero ORDER BY libro_numero").map_err(|e|e.to_string())?;
        let rows = stmt.query_map([version], |r| Ok(json!({"id":r.get::<_,i32>(0)?, "title":r.get::<_,String>(1)?, "chapters":r.get::<_,i32>(2)?}))).map_err(|e|e.to_string())?;
        Ok(Value::Array(
            rows.collect::<Result<Vec<_>, _>>()
                .map_err(|e| e.to_string())?,
        ))
    }

    fn load(&self, selection: &Selection) -> Result<Value, String> {
        let state = self.state.lock().unwrap();
        match selection {
            Selection::Song { id } => {
                let slides = state.get_canto_diapositivas(*id);
                if slides.is_empty() {
                    return Err("Canto vacío o eliminado; actualiza la biblioteca".into());
                }
                Ok(
                    json!({"title":state.get_canto_titulo(*id), "selection":selection, "cards":slides.iter().map(|s|json!({"number":s.orden,"text":s.texto})).collect::<Vec<_>>()}),
                )
            }
            Selection::Chapter {
                book,
                chapter,
                version,
            } => {
                if !(1..=66).contains(book)
                    || !(1..=176).contains(chapter)
                    || !state.versiones.iter().any(|v| v.id == *version)
                {
                    return Err("Capítulo o versión inválidos".into());
                }
                let mut stmt = state.biblias_db.prepare_cached("SELECT versiculo, texto, libro_nombre FROM versiculos WHERE version_id=? AND libro_numero=? AND capitulo=? ORDER BY versiculo").map_err(|e|e.to_string())?;
                let rows = stmt
                    .query_map([version, book, chapter], |r| {
                        Ok((
                            r.get::<_, i32>(0)?,
                            r.get::<_, String>(1)?,
                            r.get::<_, String>(2)?,
                        ))
                    })
                    .map_err(|e| e.to_string())?
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| e.to_string())?;
                let name = rows.first().ok_or("Capítulo no disponible")?.2.clone();
                Ok(
                    json!({"title":format!("{name} {chapter}"), "selection":selection,"book_name":name,"cards":rows.iter().map(|(n,t,_)|json!({"number":n,"text":t})).collect::<Vec<_>>()}),
                )
            }
            _ => Err("Selecciona un canto o capítulo".into()),
        }
    }

    fn media(ui: &AppWindow, selection: &Selection) -> Result<(usize, MediaItem), String> {
        let (items, id) = match selection {
            Selection::Image { id } => (ui.get_multimedia_items(), id),
            Selection::Video { id } => (ui.get_video_items(), id),
            _ => return Err("Selección multimedia inválida".into()),
        };
        items
            .iter()
            .enumerate()
            .find(|(_, item)| media_id(item.path.as_str()) == *id)
            .ok_or("El archivo ya no está en la biblioteca; actualiza la lista".into())
    }

    fn handle(
        &self,
        ui: &AppWindow,
        projector: &ProjectorWindow,
        action: ApiRequest,
    ) -> Result<Reply, String> {
        match action {
            ApiRequest::Catalog => {
                let state = self.state.lock().unwrap();
                let favorites: Vec<_> = state.get_all_favoritos().iter().filter_map(|fav| {
                    if fav.tipo == "canto" {
                        Some(json!({"title":fav.titulo.as_str(),"selection":Selection::Song{id:fav.id}}))
                    } else {
                        let caps = RE_FAV.captures(fav.referencia.as_str())?;
                        let (book, _) = buscar_libro_inteligente(&caps[1])?;
                        let version = state.versiones.iter().find(|v| v.id == fav.id)
                            .or_else(|| state.versiones.iter().find(|v| !fav.version.is_empty() && (v.sigla.eq_ignore_ascii_case(fav.version.as_str()) || v.nombre_completo.eq_ignore_ascii_case(fav.version.as_str()))))
                            .or_else(|| state.versiones.iter().find(|v| v.id == state.current_version_id))?.id;
                        Some(json!({"title":format!("{} · {}",fav.referencia,fav.version),"number":caps[3].parse::<i32>().ok()?,"selection":Selection::Chapter{book,chapter:caps[2].parse().ok()?,version}}))
                    }
                }).collect();
                let media = |items: ModelRc<MediaItem>, kind: &str| {
                    items.iter().map(|m|json!({"title":m.nombre.as_str(),"selection":{"kind":kind,"id":media_id(m.path.as_str())}})).collect::<Vec<_>>()
                };
                Ok(Reply::Json(
                    json!({"songs":state.get_all_cantos().iter().map(|s|json!({"title":s.titulo,"selection":Selection::Song{id:s.id}})).collect::<Vec<_>>(),"favorites":favorites,"versions":state.versiones.iter().map(|v|json!({"id":v.id,"title":v.nombre_completo})).collect::<Vec<_>>(),"images":media(ui.get_multimedia_items(),"image"),"videos":media(ui.get_video_items(),"video")}),
                ))
            }
            ApiRequest::Books { version } => Ok(Reply::Json(self.books(version)?)),
            ApiRequest::Load { selection } => Ok(Reply::Json(self.load(&selection)?)),
            ApiRequest::Thumbnail { selection } => {
                let (_, item) = Self::media(ui, &selection)?;
                let path = if matches!(selection, Selection::Video { .. }) {
                    ruta_thumb_video(
                        item.path.as_str(),
                        &self.state.lock().unwrap().user_data_dir,
                    )
                } else {
                    std::path::PathBuf::from(item.path.as_str())
                };
                Ok(Reply::Thumbnail(path))
            }
            ApiRequest::Status => Ok(Reply::Json(
                json!({"output": &*self.overlay.lock().unwrap(),"projector_visible":projector.window().is_visible(),"screen_ready":self.screen.lock().unwrap().is_some(),"playing":ui.get_is_proyector_playing(),"muted":ui.get_is_proyector_muted(),"video":ui.get_is_video_projecting()}),
            )),
            ApiRequest::Playback { control } => {
                match control.as_str() {
                    "show" => {
                        ui.invoke_abrir_proyector();
                    }
                    "hide" => {
                        projector.hide().map_err(|e| e.to_string())?;
                    }
                    "play_pause" if ui.get_is_video_projecting() => {
                        ui.invoke_toggle_proyector_play()
                    }
                    "mute" if ui.get_is_video_projecting() => ui.invoke_toggle_proyector_mute(),
                    _ => return Err("Control no disponible en la proyección actual".into()),
                }
                Ok(Reply::Json(json!({"ok":true})))
            }
            ApiRequest::Project { selection, number } => {
                match &selection {
                    Selection::Image { .. } | Selection::Video { .. } => {
                        let (index, item) = Self::media(ui, &selection)?;
                        if !std::path::Path::new(item.path.as_str()).is_file() {
                            return Err("El archivo ya no existe en el PC".into());
                        }
                        ui.set_active_tab(
                            if matches!(selection, Selection::Image { .. }) {
                                "imagenes"
                            } else {
                                "videos"
                            }
                            .into(),
                        );
                        if matches!(selection, Selection::Image { .. }) {
                            ui.set_selected_media_idx(index as i32);
                            ui.invoke_proyectar_multimedia(index as i32);
                        } else {
                            ui.set_selected_video_idx(index as i32);
                            ui.invoke_proyectar_video(index as i32);
                        }
                    }
                    _ => {
                        let loaded = self.load(&selection)?;
                        let cards = loaded["cards"].as_array().ok_or("Sin tarjetas")?;
                        let index = cards
                            .iter()
                            .position(|c| c["number"].as_i64() == Some(number as i64))
                            .ok_or("Tarjeta no disponible; actualiza la biblioteca")?;
                        let title = loaded["title"].as_str().unwrap_or("");
                        let text = cards[index]["text"].as_str().unwrap_or("");
                        let mut reference = String::new();
                        match selection {
                            Selection::Song { id } => {
                                ui.set_active_tab("cantos".into());
                                ui.invoke_seleccionar_canto(id);
                            }
                            Selection::Chapter {
                                book,
                                chapter,
                                version,
                            } => {
                                *self.book.lock().unwrap() = book;
                                *self.chapter.lock().unwrap() = chapter;
                                let mut state = self.state.lock().unwrap();
                                state.current_version_id = version;
                                let version_name = state
                                    .versiones
                                    .iter()
                                    .find(|v| v.id == version)
                                    .unwrap()
                                    .nombre_completo
                                    .clone();
                                ui.set_current_bible_version(version_name.into());
                                ui.set_active_tab("biblias".into());
                                let books: Vec<BookInfo> = state
                                    .get_libros_biblia()
                                    .into_iter()
                                    .map(|b| BookInfo {
                                        id: b.id,
                                        nombre: b.nombre.into(),
                                        capitulos: b.capitulos,
                                    })
                                    .collect();
                                let selected_book = books
                                    .iter()
                                    .find(|b| b.id == book)
                                    .cloned()
                                    .ok_or("Libro no disponible")?;
                                ui.set_bible_books(ModelRc::from(Rc::new(VecModel::from(books))));
                                ui.set_selected_bible_book(selected_book.clone());
                                ui.invoke_bible_book_selected(selected_book);
                                ui.set_elemento_seleccionado(title.into());
                                let verses = state.get_capitulo(book, chapter);
                                let favorites = state.get_favoritos_refs_versiculos_actual();
                                let slides = verses
                                    .iter()
                                    .map(|v| versiculo_a_ui_fav(v, &favorites, title))
                                    .collect::<Vec<_>>();
                                ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(
                                    slides,
                                ))));
                                ui.set_scroll_to_y(-((index as f32 * 115.0 - 150.0).max(0.0)));
                                reference = format!("{title}:{number}");
                            }
                            _ => unreachable!(),
                        }
                        ui.set_active_estrofa_index(index as i32);
                        ui.invoke_proyectar_estrofa(text.into(), reference.into());
                    }
                }
                // Uses the same screen placement and rendering path as the LIVE button.
                ui.invoke_abrir_proyector();
                Ok(Reply::Json(json!({"ok":true})))
            }
        }
    }
}

pub(super) fn install(
    ui: &AppWindow,
    projector: &ProjectorWindow,
    state: Arc<Mutex<AppState>>,
    overlay: Arc<Mutex<EstadoOverlay>>,
    screen: Screen,
    book: Arc<Mutex<i32>>,
    chapter: Arc<Mutex<i32>>,
) {
    let context = Arc::new(Context {
        state,
        overlay,
        screen,
        book,
        chapter,
    });
    let (ui_h, projector_h) = (ui.as_weak(), projector.as_weak());
    let mut running: Option<RemoteServer> = None;
    ui.on_toggle_remote_control(move || {
        let Some(ui) = ui_h.upgrade() else {
            return;
        };
        ui.set_remote_error("".into());
        if let Some(server) = running.take() {
            drop(server);
            ui.set_remote_active(false);
            ui.set_remote_code("".into());
            return;
        }
        let (weak, projection, context) = (ui_h.clone(), projector_h.clone(), context.clone());
        let session_active = Arc::new(AtomicBool::new(true));
        let session = session_active.clone();
        let handler: Arc<Handler> = Arc::new(move |action| {
            let (tx, rx) = mpsc::sync_channel(1);
            let (weak, projection, context, session) = (
                weak.clone(),
                projection.clone(),
                context.clone(),
                session.clone(),
            );
            let deadline = Instant::now() + Duration::from_secs(5);
            slint::invoke_from_event_loop(move || {
                let result = if Instant::now() > deadline || !session.load(Ordering::Acquire) {
                    Err("Solicitud cancelada; vuelve a conectar".into())
                } else if let (Some(ui), Some(projector)) = (weak.upgrade(), projection.upgrade()) {
                    context.handle(&ui, &projector, action)
                } else {
                    Err("La app de PC se cerró".into())
                };
                let _ = tx.send(result);
            })
            .map_err(|e| e.to_string())?;
            rx.recv_timeout(Duration::from_secs(6)).map_err(|_| {
                "La app no respondió. Comprueba el estado antes de repetir una acción".to_string()
            })?
        });
        match RemoteServer::start(PORT, handler, session_active) {
            Ok(server) => {
                // Share cancellation with queued UI commands when the server stops.
                let ip = local_ip_address::local_ip()
                    .unwrap_or(std::net::IpAddr::V4(std::net::Ipv4Addr::LOCALHOST));
                let address = std::net::SocketAddr::new(ip, PORT);
                ui.set_remote_url(format!("http://{address}").into());
                ui.set_remote_code(server.token.clone().into());
                ui.set_remote_active(true);
                running = Some(server);
            }
            Err(message) => {
                ui.set_remote_error(format!("No se pudo abrir el puerto {PORT}: {message}").into())
            }
        }
    });
    let copy_ui = ui.as_weak();
    let mut clipboard: Option<arboard::Clipboard> = None;
    ui.on_copy_remote_link(move || {
        if let Some(ui) = copy_ui.upgrade() {
            let link = format!("{}/#token={}", ui.get_remote_url(), ui.get_remote_code());
            let result = (|| {
                if clipboard.is_none() {
                    clipboard = Some(arboard::Clipboard::new()?);
                }
                clipboard.as_mut().unwrap().set_text(link)
            })();
            match result {
                Ok(()) => ui.set_remote_error("Enlace copiado. Compártelo con tu celular.".into()),
                Err(e) => ui.set_remote_error(format!("No se pudo copiar: {e}").into()),
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::net::TcpStream;

    fn start() -> RemoteServer {
        RemoteServer::start(
            0,
            Arc::new(|action| match action {
                ApiRequest::Catalog => Ok(Reply::Json(json!({"songs":[]}))),
                _ => Err("Acción no disponible".into()),
            }),
            Arc::new(AtomicBool::new(true)),
        )
        .unwrap()
    }

    fn request(
        server: &RemoteServer,
        method: &str,
        path: &str,
        headers: &str,
        body: &str,
    ) -> String {
        let port = server.server.server_addr().to_ip().unwrap().port();
        let mut stream = TcpStream::connect(("127.0.0.1", port)).unwrap();
        stream
            .set_read_timeout(Some(Duration::from_secs(5)))
            .unwrap();
        write!(stream,"{method} {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\nContent-Length: {}\r\n{headers}\r\n{body}",body.len()).unwrap();
        let mut response = String::new();
        stream.read_to_string(&mut response).unwrap();
        response
    }

    #[test]
    fn remote_requires_session_token_and_rejects_cross_origin_and_unknown_actions() {
        let server = start();
        let auth = format!(
            "Authorization: Bearer {}\r\nContent-Type: application/json\r\n",
            server.token
        );
        assert!(
            request(
                &server,
                "POST",
                "/api",
                "Content-Type: application/json\r\n",
                r#"{"action":"catalog"}"#
            )
            .starts_with("HTTP/1.1 401")
        );
        let ok = request(&server, "POST", "/api", &auth, r#"{"action":"catalog"}"#);
        assert!(ok.starts_with("HTTP/1.1 200"));
        assert!(ok.contains("\"songs\":[]"));
        assert!(
            request(
                &server,
                "POST",
                "/api",
                &format!("{auth}Origin: https://untrusted.example\r\n"),
                r#"{"action":"catalog"}"#
            )
            .starts_with("HTTP/1.1 403")
        );
        assert!(
            request(
                &server,
                "POST",
                "/api",
                &auth,
                r#"{"action":"delete_database"}"#
            )
            .starts_with("HTTP/1.1 400")
        );
        assert!(
            request(&server, "POST", "/api", &auth, &"x".repeat(MAX_BODY + 1))
                .starts_with("HTTP/1.1 413")
        );
        assert!(request(&server, "GET", "/api", &auth, "").starts_with("HTTP/1.1 405"));
        assert!(request(&server, "GET", "/../../Cargo.toml", "", "").starts_with("HTTP/1.1 404"));
    }

    #[test]
    fn remote_shell_is_public_and_stopping_revokes_the_session() {
        let server = start();
        let active = server.active.clone();
        let token = server.token.clone();
        let page = request(&server, "GET", "/", "", "");
        assert!(page.starts_with("HTTP/1.1 200"));
        assert!(page.contains("ReadyShow"));
        let manifest = request(&server, "GET", "/manifest.webmanifest", "", "");
        assert!(manifest.contains("fullscreen"));
        for path in [
            "/modules/migration.js",
            "/modules/storage.js",
            "/modules/local.js",
            "/modules/remote.js",
            "/modules/pwa.js",
            "/modules/projection.js",
            "/modules/ui.js",
            "/icon-maskable-512.png",
        ] {
            let method = if path.ends_with(".png") {
                "HEAD"
            } else {
                "GET"
            };
            assert!(request(&server, method, path, "", "").starts_with("HTTP/1.1 200"));
        }
        drop(server);
        assert!(!active.load(Ordering::Acquire));
        let replacement = start();
        assert_ne!(token, replacement.token);
        let headers =
            format!("Authorization: Bearer {token}\r\nContent-Type: application/json\r\n");
        assert!(
            request(
                &replacement,
                "POST",
                "/api",
                &headers,
                r#"{"action":"catalog"}"#
            )
            .starts_with("HTTP/1.1 401")
        );
    }

    fn context() -> Context {
        let songs = Connection::open_in_memory().unwrap();
        songs.execute_batch("CREATE TABLE cantos(id INTEGER, titulo TEXT); CREATE TABLE diapositivas(canto_id INTEGER, orden INTEGER, texto TEXT); INSERT INTO cantos VALUES(7,'Canto de prueba'); INSERT INTO diapositivas VALUES(7,1,'Primera estrofa'),(7,2,'Segunda estrofa');").unwrap();
        let bible = Connection::open_in_memory().unwrap();
        bible.execute_batch("CREATE TABLE versiculos(version_id INTEGER, libro_numero INTEGER, libro_nombre TEXT, capitulo INTEGER, versiculo INTEGER, texto TEXT); INSERT INTO versiculos VALUES(2,1,'Génesis',1,1,'Texto versión dos'),(1,1,'Génesis',1,1,'Texto versión uno');").unwrap();
        let state = AppState {
            cantos_db: songs,
            biblias_db: bible,
            versiones: vec![
                VersionInfo {
                    id: 1,
                    sigla: "UNO".into(),
                    nombre_completo: "Uno".into(),
                    prioridad: 1,
                },
                VersionInfo {
                    id: 2,
                    sigla: "DOS".into(),
                    nombre_completo: "Dos".into(),
                    prioridad: 2,
                },
            ],
            current_version_id: 1,
            chapter_cache: LruCache::new(std::num::NonZeroUsize::new(2).unwrap()),
            biblias_image_paths: vec![],
            cantos_image_paths: vec![],
            biblias_video_paths: vec![],
            cantos_video_paths: vec![],
            user_data_dir: std::env::temp_dir(),
        };
        Context {
            state: Arc::new(Mutex::new(state)),
            overlay: Arc::new(Mutex::new(EstadoOverlay::default())),
            screen: Arc::new(Mutex::new(None)),
            book: Arc::new(Mutex::new(-1)),
            chapter: Arc::new(Mutex::new(-1)),
        }
    }

    #[test]
    fn preview_reads_complete_cards_without_changing_desktop_bible_version() {
        let context = context();
        let song = context.load(&Selection::Song { id: 7 }).unwrap();
        assert_eq!(song["cards"].as_array().unwrap().len(), 2);
        assert_eq!(song["cards"][1]["text"], "Segunda estrofa");
        let chapter = context
            .load(&Selection::Chapter {
                book: 1,
                chapter: 1,
                version: 2,
            })
            .unwrap();
        assert_eq!(chapter["cards"][0]["text"], "Texto versión dos");
        assert_eq!(context.state.lock().unwrap().current_version_id, 1);
        assert!(
            context
                .load(&Selection::Chapter {
                    book: 1,
                    chapter: 9999,
                    version: 2
                })
                .is_err()
        );
        assert!(
            context
                .load(&Selection::Chapter {
                    book: 1,
                    chapter: 1,
                    version: 999
                })
                .is_err()
        );
        assert!(context.load(&Selection::Song { id: 999 }).is_err());
        assert!(context.books(999).is_err());
    }

    #[test]
    fn protocol_rejects_arbitrary_paths_and_text_injection() {
        assert!(serde_json::from_str::<ApiRequest>(r#"{"action":"project","selection":{"kind":"image","id":"x","path":"/etc/passwd"},"number":0}"#).is_err());
        assert!(serde_json::from_str::<ApiRequest>(r#"{"action":"project","selection":{"kind":"song","id":7},"number":1,"text":"contenido ajeno"}"#).is_err());
        assert_ne!(media_id("/library/one.png"), media_id("/library/two.png"));
    }
}
