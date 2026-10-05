-- Objetos auxiliares idempotentes; los ALTER y el respaldo inicial se aplican desde Rust.
-- Ejecutar dentro de la transacción de migrate(). Timestamps: milisegundos UTC.

CREATE TABLE IF NOT EXISTS sync_metadata (id INTEGER PRIMARY KEY CHECK(id=1), last_sync_timestamp INTEGER NOT NULL DEFAULT 0, clock INTEGER NOT NULL DEFAULT 1, suppress INTEGER NOT NULL DEFAULT 0, remote_folder TEXT NOT NULL DEFAULT '', local_instance TEXT NOT NULL DEFAULT (lower(hex(randomblob(16)))));



CREATE TABLE IF NOT EXISTS sync_changes (timestamp INTEGER NOT NULL, table_name TEXT NOT NULL, record_id INTEGER NOT NULL, payload TEXT NOT NULL);

CREATE INDEX IF NOT EXISTS sync_changes_timestamp ON sync_changes(timestamp);

CREATE TABLE IF NOT EXISTS sync_versions (table_name TEXT NOT NULL, record_id INTEGER NOT NULL, timestamp INTEGER NOT NULL, PRIMARY KEY(table_name,record_id));

CREATE TRIGGER IF NOT EXISTS sync_cantos_insert AFTER INSERT ON cantos
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE cantos SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'cantos', id, json_object('id', id, 'titulo', titulo, 'tono', tono, 'categoria', categoria, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM cantos WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'cantos', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_cantos_update AFTER UPDATE OF id, titulo, tono, categoria, is_deleted ON cantos
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE cantos SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'cantos', id, json_object('id', id, 'titulo', titulo, 'tono', tono, 'categoria', categoria, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM cantos WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'cantos', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_cantos_delete AFTER DELETE ON cantos
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
INSERT INTO sync_changes SELECT clock, 'cantos', OLD.id, json_object('id', OLD.id, 'updated_at', clock, 'is_deleted', 1) FROM sync_metadata WHERE id=1;
INSERT INTO sync_versions SELECT 'cantos', OLD.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_diapositivas_insert AFTER INSERT ON diapositivas
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE diapositivas SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'diapositivas', id, json_object('id', id, 'canto_id', canto_id, 'orden', orden, 'texto', texto, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM diapositivas WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'diapositivas', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_diapositivas_update AFTER UPDATE OF id, canto_id, orden, texto, is_deleted ON diapositivas
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE diapositivas SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'diapositivas', id, json_object('id', id, 'canto_id', canto_id, 'orden', orden, 'texto', texto, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM diapositivas WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'diapositivas', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_diapositivas_delete AFTER DELETE ON diapositivas
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
INSERT INTO sync_changes SELECT clock, 'diapositivas', OLD.id, json_object('id', OLD.id, 'updated_at', clock, 'is_deleted', 1) FROM sync_metadata WHERE id=1;
INSERT INTO sync_versions SELECT 'diapositivas', OLD.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_favoritos_insert AFTER INSERT ON favoritos
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE favoritos SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'favoritos', id, json_object('id', id, 'tipo', tipo, 'ref_id', ref_id, 'referencia', referencia, 'titulo', titulo, 'version', version, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM favoritos WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'favoritos', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_favoritos_update AFTER UPDATE OF id, tipo, ref_id, referencia, titulo, version, is_deleted ON favoritos
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE favoritos SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'favoritos', id, json_object('id', id, 'tipo', tipo, 'ref_id', ref_id, 'referencia', referencia, 'titulo', titulo, 'version', version, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM favoritos WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'favoritos', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_favoritos_delete AFTER DELETE ON favoritos
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
INSERT INTO sync_changes SELECT clock, 'favoritos', OLD.id, json_object('id', OLD.id, 'updated_at', clock, 'is_deleted', 1) FROM sync_metadata WHERE id=1;
INSERT INTO sync_versions SELECT 'favoritos', OLD.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;
