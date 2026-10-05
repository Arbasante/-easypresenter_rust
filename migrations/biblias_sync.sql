-- Objetos auxiliares idempotentes; los ALTER y el respaldo inicial se aplican desde Rust.
-- Ejecutar dentro de la transacción de migrate(). Timestamps: milisegundos UTC.

CREATE TABLE IF NOT EXISTS sync_metadata (id INTEGER PRIMARY KEY CHECK(id=1), last_sync_timestamp INTEGER NOT NULL DEFAULT 0, clock INTEGER NOT NULL DEFAULT 1, suppress INTEGER NOT NULL DEFAULT 0, remote_folder TEXT NOT NULL DEFAULT '', local_instance TEXT NOT NULL DEFAULT (lower(hex(randomblob(16)))));



CREATE TABLE IF NOT EXISTS sync_changes (timestamp INTEGER NOT NULL, table_name TEXT NOT NULL, record_id INTEGER NOT NULL, payload TEXT NOT NULL);

CREATE INDEX IF NOT EXISTS sync_changes_timestamp ON sync_changes(timestamp);

CREATE TABLE IF NOT EXISTS sync_versions (table_name TEXT NOT NULL, record_id INTEGER NOT NULL, timestamp INTEGER NOT NULL, PRIMARY KEY(table_name,record_id));

CREATE TRIGGER IF NOT EXISTS sync_versiones_insert AFTER INSERT ON versiones
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE versiones SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'versiones', id, json_object('id', id, 'nombre', nombre, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM versiones WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'versiones', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_versiones_update AFTER UPDATE OF id, nombre, is_deleted ON versiones
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE versiones SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'versiones', id, json_object('id', id, 'nombre', nombre, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM versiones WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'versiones', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_versiones_delete AFTER DELETE ON versiones
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
INSERT INTO sync_changes SELECT clock, 'versiones', OLD.id, json_object('id', OLD.id, 'updated_at', clock, 'is_deleted', 1) FROM sync_metadata WHERE id=1;
INSERT INTO sync_versions SELECT 'versiones', OLD.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_versiculos_insert AFTER INSERT ON versiculos
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE versiculos SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'versiculos', id, json_object('id', id, 'version_id', version_id, 'libro_nombre', libro_nombre, 'libro_numero', libro_numero, 'capitulo', capitulo, 'versiculo', versiculo, 'texto', texto, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM versiculos WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'versiculos', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_versiculos_update AFTER UPDATE OF id, version_id, libro_nombre, libro_numero, capitulo, versiculo, texto, is_deleted ON versiculos
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
UPDATE versiculos SET updated_at=(SELECT clock FROM sync_metadata WHERE id=1) WHERE id=NEW.id;
INSERT INTO sync_changes SELECT updated_at, 'versiculos', id, json_object('id', id, 'version_id', version_id, 'libro_nombre', libro_nombre, 'libro_numero', libro_numero, 'capitulo', capitulo, 'versiculo', versiculo, 'texto', texto, 'updated_at', updated_at, 'is_deleted', is_deleted) FROM versiculos WHERE id=NEW.id;
INSERT INTO sync_versions SELECT 'versiculos', NEW.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;

CREATE TRIGGER IF NOT EXISTS sync_versiculos_delete AFTER DELETE ON versiculos
WHEN (SELECT suppress FROM sync_metadata WHERE id=1)=0 BEGIN
UPDATE sync_metadata SET clock = MAX(clock + 1, CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)) WHERE id=1;
INSERT INTO sync_changes SELECT clock, 'versiculos', OLD.id, json_object('id', OLD.id, 'updated_at', clock, 'is_deleted', 1) FROM sync_metadata WHERE id=1;
INSERT INTO sync_versions SELECT 'versiculos', OLD.id, clock FROM sync_metadata WHERE id=1 ON CONFLICT(table_name,record_id) DO UPDATE SET timestamp=excluded.timestamp;
END;
