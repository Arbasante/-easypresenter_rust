import { $, notice } from './ui.js';

export function initPwa() {
  let prompt;
  const connectivity = () => {
    $('offline-status').textContent = navigator.onLine
      ? 'Mando remoto · Requiere el PC encendido y la misma red.'
      : 'Sin red · El mando necesita conexión con el PC. No se guardan órdenes pendientes.';
  };
  connectivity();
  window.addEventListener('online', connectivity);
  window.addEventListener('offline', connectivity);
  window.addEventListener('beforeinstallprompt', event => {
    event.preventDefault(); prompt = event; $('install').hidden = false;
  });
  window.addEventListener('appinstalled', () => { prompt = null; $('install').hidden = true; notice('ReadyShow instalado.'); });
  $('install').addEventListener('click', async () => {
    if (!prompt) return;
    await prompt.prompt(); await prompt.userChoice; prompt = null; $('install').hidden = true;
  });
  $('install-note').textContent = window.isSecureContext
    ? 'En Android abre el menú del navegador → Instalar aplicación. Se abrirá desde su icono a pantalla completa cuando el navegador lo admita.'
    : 'Para instalar y habilitar el arranque offline, abre esta app con HTTPS confiable. HTTP por IP local solo permite usarla mientras esté abierta. Consulta README.md para configurar HTTPS local.';
  if (!('serviceWorker' in navigator) || !window.isSecureContext) {
    $('cache-status').textContent = 'Arranque offline no disponible: se requiere HTTPS confiable y Service Worker.';
    $('check-update').disabled = true;
    return;
  }
  navigator.serviceWorker.register('/sw.js').then(async registration => {
    const installing = registration.installing;
    if (installing && !['installed', 'activated'].includes(installing.state)) {
      await new Promise((resolve, reject) => {
        installing.addEventListener('statechange', () => {
          if (['installed', 'activated'].includes(installing.state)) resolve();
          if (installing.state === 'redundant') reject(new Error('No se descargaron todos los archivos.'));
        });
      });
    }
    const worker = registration.waiting || registration.active;
    const ready = await new Promise((resolve, reject) => {
      const channel = new MessageChannel();
      const timeout = setTimeout(() => { channel.port1.close(); reject(new Error('No se pudo verificar la copia offline.')); }, 8000);
      channel.port1.onmessage = event => { clearTimeout(timeout); channel.port1.close(); resolve(event.data.ready); };
      worker?.postMessage({ type: 'OFFLINE_READY' }, [channel.port2]);
    });
    if (!ready) throw new Error('La copia offline está incompleta.');
    $('cache-status').textContent = registration.waiting
      ? 'Nueva versión lista para uso offline. Cierra todas las ventanas y vuelve a abrir la app para aplicarla.'
      : 'Interfaz del mando guardada. Controlar la proyección requiere el PC conectado.';
    $('check-update').addEventListener('click', async () => {
      try {
        await registration.update();
        notice('Actualización consultada. Si hay una nueva versión, cierra y vuelve a abrir la app para aplicarla.');
      } catch { notice('No se pudo consultar. La versión guardada sigue funcionando offline.', true); }
    });
    registration.addEventListener('updatefound', () => {
      const worker = registration.installing;
      worker?.addEventListener('statechange', () => {
        if (worker.state === 'installed' && navigator.serviceWorker.controller) notice('Nueva versión descargada. Cierra todas las ventanas y vuelve a abrir ReadyShow para aplicarla.');
      });
    });
  }).catch(error => {
    $('cache-status').textContent = `No se completó la descarga offline: ${error.message}. Mantén la conexión y vuelve a abrir la app.`;
  });
}
