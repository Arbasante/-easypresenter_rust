const CACHE = 'readyshow-control-v5';
const SHELL = ['/', '/index.html', '/app.js', '/styles.css', '/manifest.webmanifest', '/icon-192.png', '/icon-512.png', '/icon-maskable-512.png', '/modules/ui.js', '/modules/storage.js', '/modules/migration.js', '/modules/remote.js', '/modules/projection.js', '/modules/pwa.js'];
self.addEventListener('install', event => {
  // A failed download does not replace the working offline version.
  // Updates activate after every existing app window closes, without discarding edits.
  event.waitUntil(caches.open(CACHE).then(cache => cache.addAll(SHELL)));
});
self.addEventListener('activate', event => {
  event.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(key => (key.startsWith('readyshow-control-') || key.startsWith('readyshow-offline-')) && key !== CACHE).map(key => caches.delete(key)))).then(() => self.clients.claim()));
});
self.addEventListener('message', event => {
  if (event.data?.type !== 'OFFLINE_READY' || !event.ports[0]) return;
  event.waitUntil(caches.open(CACHE).then(async cache => {
    const files = await Promise.all(SHELL.map(path => cache.match(path)));
    event.ports[0].postMessage({ ready: files.every(Boolean), version: CACHE });
  }));
});
self.addEventListener('fetch', event => {
  const url = new URL(event.request.url);
  // Commands and API responses are never cached, queued, replayed or synchronized.
  if (event.request.method !== 'GET' || url.origin !== self.location.origin || url.pathname === '/api') return;
  if (!SHELL.includes(url.pathname) && event.request.mode !== 'navigate') return;
  const key = event.request.mode === 'navigate' ? '/index.html' : url.pathname;
  event.respondWith(caches.open(CACHE).then(async cache => {
    const cached = await cache.match(key);
    if (cached) return cached;
    try {
      const response = await fetch(event.request);
      if (response.ok && SHELL.includes(url.pathname)) await cache.put(key, response.clone());
      return response;
    } catch { return Response.error(); }
  }));
});
