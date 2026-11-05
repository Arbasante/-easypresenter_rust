// The device database is the source of truth. Remote credentials never enter it.
export const STORES = ['events', 'plans', 'notes', 'tasks', 'library', 'settings'];
const DATABASE = 'readyshow-local';
let opening;

export function openDatabase() {
  if (!opening) opening = new Promise((resolve, reject) => {
    const request = indexedDB.open(DATABASE, 1);
    request.onupgradeneeded = () => {
      for (const name of STORES) {
        if (!request.result.objectStoreNames.contains(name)) request.result.createObjectStore(name, { keyPath: 'id' });
      }
    };
    request.onerror = () => { opening = null; reject(request.error); };
    request.onblocked = () => { opening = null; reject(new Error('Cierra otras ventanas de ReadyShow para actualizar la base local.')); };
    request.onsuccess = () => {
      const db = request.result;
      db.onversionchange = () => { db.close(); opening = null; };
      resolve(db);
    };
  });
  return opening;
}

async function transaction(stores, mode, operation) {
  const db = await openDatabase();
  return new Promise((resolve, reject) => {
    const tx = db.transaction(stores, mode);
    let result;
    tx.oncomplete = () => resolve(result?.result);
    tx.onerror = () => reject(tx.error || new Error('No se pudo guardar en el dispositivo.'));
    tx.onabort = () => reject(tx.error || new Error('La operación local fue cancelada.'));
    try { result = operation(tx); }
    catch (error) { tx.abort(); reject(error); }
  });
}

function storeName(name) {
  if (!STORES.includes(name)) throw new Error('Colección local inválida.');
  return name;
}
export const list = name => transaction([storeName(name)], 'readonly', tx => tx.objectStore(name).getAll());
export const get = (name, id) => transaction([storeName(name)], 'readonly', tx => tx.objectStore(name).get(id));
export async function put(name, record) {
  const saved = { ...record, id: record.id || crypto.randomUUID(), updatedAt: new Date().toISOString() };
  await transaction([storeName(name)], 'readwrite', tx => tx.objectStore(name).put(saved));
  return saved;
}
export const remove = (name, id) => transaction([storeName(name)], 'readwrite', tx => tx.objectStore(name).delete(id));

export async function exportBackup() {
  const data = {};
  // One transaction gives a consistent snapshot across all collections.
  await transaction(STORES, 'readonly', tx => {
    for (const name of STORES) {
      const request = tx.objectStore(name).getAll();
      request.onsuccess = () => { data[name] = request.result; };
    }
  });
  for (const record of data.library) {
    if (record.file instanceof Blob) {
      const bytes = new Uint8Array(await record.file.arrayBuffer());
      let binary = '';
      for (let i = 0; i < bytes.length; i += 8192) binary += String.fromCharCode(...bytes.subarray(i, i + 8192));
      record.attachment = { type: record.file.type, data: btoa(binary) };
      delete record.file;
    }
  }
  return { format: 'readyshow-local', version: 1, exportedAt: new Date().toISOString(), data };
}

export async function importBackup(backup) {
  if (backup?.format !== 'readyshow-local' || backup.version !== 1 || !backup.data) throw new Error('El archivo no es una copia compatible de ReadyShow.');
  const records = {};
  for (const name of STORES) {
    const rows = backup.data[name];
    if (!Array.isArray(rows) || rows.length > 50000) throw new Error('Colección inválida en la copia.');
    const ids = new Set();
    records[name] = rows.map(row => {
      if (!row || typeof row.id !== 'string' || !row.id || ids.has(row.id)
        || (name !== 'settings' && (typeof row.title !== 'string' || !row.title.trim()))) throw new Error('Registro inválido en la copia.');
      ids.add(row.id);
      const copy = { id: row.id, title: row.title };
      // Keep backup files from supplying credentials or connection configuration.
      if (name === 'settings' && row.id !== 'preferences') throw new Error('Ajuste no permitido en la copia.');
      if (name === 'settings') return { id: 'preferences', displayName: String(row.displayName || ''), updatedAt: String(row.updatedAt || '') };
      for (const field of ['body', 'date', 'end', 'location', 'eventId', 'kind', 'fileName', 'source', 'updatedAt']) {
        if (row[field] === undefined) continue;
        if (typeof row[field] !== 'string' || row[field].length > 200000) throw new Error('Campo inválido en la copia.');
        copy[field] = row[field];
      }
      if (row.completed !== undefined) {
        if (typeof row.completed !== 'boolean') throw new Error('Estado de tarea inválido.');
        copy.completed = row.completed;
      }
      if (row.resourceIds !== undefined) {
        if (!Array.isArray(row.resourceIds) || row.resourceIds.some(id => typeof id !== 'string')) throw new Error('Recursos inválidos.');
        copy.resourceIds = row.resourceIds;
      }
      if (row.cards !== undefined) {
        if (name !== 'library' || !Array.isArray(row.cards) || row.cards.some(card => !Number.isInteger(card?.number) || typeof card.text !== 'string')) throw new Error('Tarjetas inválidas.');
        copy.cards = row.cards.map(card => ({ number: card.number, text: card.text }));
      }
      if (row.attachment) {
        if (name !== 'library' || typeof row.attachment.data !== 'string' || row.attachment.data.length > 140000000) throw new Error('Adjunto inválido.');
        const binary = atob(row.attachment.data);
        copy.file = new Blob([Uint8Array.from(binary, ch => ch.charCodeAt(0))], { type: String(row.attachment.type || 'application/octet-stream') });
      }
      return copy;
    });
  }
  // Validate and decode everything before replacing anything. Roll back on failure.
  await transaction(STORES, 'readwrite', tx => {
    for (const name of STORES) {
      const store = tx.objectStore(name);
      store.clear();
      for (const record of records[name]) store.put(record);
    }
  });
}
