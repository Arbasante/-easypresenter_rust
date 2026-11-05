import { initRemote } from './modules/remote.js';
import { initPwa } from './modules/pwa.js';
import { initMigration } from './modules/migration.js';
import { notice } from './modules/ui.js';
initRemote();
initPwa();
// Preserve earlier IndexedDB data and offer an explicit export to the native app.
initMigration().catch(error => notice(`No se pudieron consultar los datos anteriores: ${error.message}`, true));
