import { $, notice, download } from './ui.js';
import { STORES, list, exportBackup } from './storage.js';
export async function initMigration() {
  const collections = await Promise.all(STORES.map(list));
  if (!collections.some(rows => rows.length)) return;
  $('legacy-data').hidden = false;
  $('export-legacy').addEventListener('click', async () => {
    const button = $('export-legacy'); button.disabled = true;
    try {
      const blob = new Blob([JSON.stringify(await exportBackup())], { type: 'application/json' });
      if (blob.size > 150 * 1024 * 1024) throw new Error('La copia supera 150 MB. Usa la versión anterior para reducir los adjuntos.');
      download(blob, `readyshow-migracion-${new Date().toISOString().slice(0, 10)}.json`);
      notice('Copia exportada. En la app Android abre Ajustes → Importar copia. Los datos del navegador se conservan.');
    } catch (error) { notice(error.message, true); }
    finally { button.disabled = false; }
  });
}
