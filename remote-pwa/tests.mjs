import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import vm from 'node:vm';
const uiSource = fs.readFileSync(new URL('./modules/ui.js', import.meta.url), 'utf8').replaceAll('export ', '');
const projectionSource = fs.readFileSync(new URL('./modules/projection.js', import.meta.url), 'utf8').replaceAll('export ', '');
const source = uiSource + '\n' + projectionSource + '\n' + fs.readFileSync(new URL('./modules/remote.js', import.meta.url), 'utf8').replace(/^import .*;$/gm, '').replaceAll('export ', '');
function app(fetch, mockRender = false) {
  const nodes = new Map();
  const get = id => {
    if (!nodes.has(id)) nodes.set(id, { textContent: '', classList: { toggle() {}, remove() {} }, hidden: false, replaceChildren() {}, value: '' });
    return nodes.get(id);
  };
  const context = vm.createContext({
    document: { getElementById: get, querySelectorAll: () => [], hidden: false },
    fetch, AbortController, setTimeout, clearTimeout, URL, sessionStorage: { removeItem() {} },
  });
  const setup = source.slice(0, source.indexOf("function initRemote("));
  vm.runInContext(`${setup}
    const renders = { library: 0, versions: 0, detail: 0 };
    ${mockRender ? `renderLibrary = () => { renders.library++; state.generation++; };
      renderVersions = () => { renders.versions++; };
      renderDetail = detail => { renders.detail++; state.detail = detail; };` : ''}
    globalThis.testing={api,command,normalize,state,disconnect,syncLibrary,renders};`, context);
  return { ...context.testing, nodes, get };
}
test('browser scripts parse and manifest icons exist', () => {
  new vm.Script(source);
  new vm.Script(fs.readFileSync(new URL('./sw.js', import.meta.url), 'utf8'));
  const manifest = JSON.parse(fs.readFileSync(new URL('./manifest.webmanifest', import.meta.url)));
  assert.equal(manifest.display, 'fullscreen');
  for (const icon of manifest.icons) assert.ok(fs.existsSync(new URL(`.${icon.src}`, import.meta.url)));
});
test('search ignores Spanish accents and capitalization', () => {
  const { normalize } = app();
  assert.equal(normalize('CANCIÓN del Señor'), 'cancion del senor');
});
test('API uses session authorization and never caches commands', async () => {
  let sent;
  const t = app(async (url, options) => { sent = { url, options }; return { ok: true, json: async () => ({ ok: true }) }; });
  t.state.token = 'session-code';
  await t.api({ action: 'project', selection: { kind: 'song', id: 5 }, number: 2 });
  assert.equal(sent.url, '/api');
  assert.equal(sent.options.method, 'POST');
  assert.equal(sent.options.headers.Authorization, 'Bearer session-code');
  assert.equal(sent.options.cache, 'no-store');
  assert.deepEqual(JSON.parse(sent.options.body), { action: 'project', selection: { kind: 'song', id: 5 }, number: 2 });
});
test('an expired session clears access and returns the server error', async () => {
  const t = app(async () => ({ ok: false, status: 401, json: async () => ({ error: 'Sesión finalizada' }) }));
  t.state.token = 'expired'; t.state.connected = true;
  await assert.rejects(t.api({ action: 'status' }), /Sesión finalizada/);
  assert.equal(t.state.connected, false); assert.equal(t.state.token, '');
});
test('projection commands are not sent offline or while another command is pending', async () => {
  let count = 0;
  const t = app(async () => { count++; return { ok: true, json: async () => ({ ok: true }) }; });
  t.state.connected = true; t.state.online = false;
  await t.command({ action: 'project' });
  t.state.online = true; t.state.busy = true;
  await t.command({ action: 'project' });
  assert.equal(count, 0);
});
test('failed commands are reported and never automatically retried', async () => {
  let count = 0;
  const t = app(async () => { count++; return { ok: false, status: 400, json: async () => ({ error: 'Sin segunda pantalla' }) }; });
  t.state.connected = true; t.state.online = true;
  await t.command({ action: 'project' });
  assert.equal(count, 1);
  assert.equal(t.get('message').textContent, 'Sin segunda pantalla');
  assert.equal(t.state.busy, false);
});
test('service worker ignores API requests, including all POST commands', () => {
  const handlers = {};
  let intercepted = 0;
  const context = vm.createContext({ URL, self: { location: { origin: 'https://readyshow.test' }, addEventListener: (name, callback) => { handlers[name] = callback; } } });
  vm.runInContext(fs.readFileSync(new URL('./sw.js', import.meta.url), 'utf8'), context);
  for (const [method, path] of [['POST', '/api'], ['GET', '/api'], ['POST', '/']]) {
    handlers.fetch({ request: { method, url: `https://readyshow.test${path}` }, respondWith() { intercepted++; } });
  }
  assert.equal(intercepted, 0);
});

function syncing(respond) {
  const t = app(async (_url, options) => ({ ok: true, json: async () => respond(JSON.parse(options.body)) }), true);
  t.state.connected = true; t.state.token = 'session-code';
  t.state.catalog = { songs: [], favorites: [], versions: [], images: [], videos: [] };
  return t;
}
test('unchanged library polling keeps the existing view intact', async () => {
  const t = syncing(() => t.state.catalog);
  await t.syncLibrary();
  assert.equal(t.renders.library, 0);
  assert.equal(t.renders.versions, 0);
});
test('desktop catalog changes update the library without resetting Bible selectors', async () => {
  const t = syncing(() => ({ ...t.state.catalog, songs: [{ title: 'Nuevo canto' }] }));
  t.state.tab = 'songs'; t.get('search').value = 'nuevo';
  await t.syncLibrary();
  assert.equal(t.renders.library, 1);
  assert.equal(t.renders.versions, 0);
  assert.equal(t.state.tab, 'songs');
  assert.equal(t.get('search').value, 'nuevo');
});
test('desktop song edits refresh open cards even when the catalog is unchanged', async () => {
  const original = { title: 'Canto', selection: { kind: 'song', id: 7 }, cards: [{ number: 1, text: 'Antes' }] };
  const changed = { ...original, cards: [{ number: 1, text: 'Después' }] };
  const t = syncing(action => action.action === 'load' ? changed : t.state.catalog);
  t.state.detail = original;
  await t.syncLibrary();
  assert.equal(t.renders.detail, 1);
  assert.equal(t.state.detail.cards[0].text, 'Después');
});
test('a deleted open song returns to the library automatically', async () => {
  const t = syncing(action => {
    if (action.action === 'load') throw Object.assign(new Error('Canto eliminado'), { status: 400 });
    return t.state.catalog;
  });
  t.state.detail = { selection: { kind: 'song', id: 7 } };
  await t.syncLibrary();
  assert.equal(t.state.detail, null);
  assert.equal(t.renders.library, 1);
});
test('a delayed synchronization cannot overwrite a newer navigation', async () => {
  let resolve;
  const response = new Promise(done => { resolve = done; });
  const t = syncing(() => response);
  const pending = t.syncLibrary();
  t.state.generation++;
  resolve({ ...t.state.catalog, songs: [{ title: 'Nuevo' }] });
  await pending;
  assert.equal(t.renders.library, 0);
  assert.equal(t.state.catalog.songs.length, 0);
});

test('red live markers follow actual visible text and reference, including desktop changes', () => {
  const { isLiveSlide } = vm.runInNewContext(projectionSource + ';({ isLiveSlide });');
  const detail = { title: 'Génesis 1', selection: { kind: 'chapter' } };
  const slide = { number: 1, text: 'En el principio' };
  const status = { projector_visible: true, video: false, output: { texto: slide.text, referencia: 'Génesis 1:1' } };
  assert.equal(isLiveSlide(status, detail, slide), true);
  assert.equal(isLiveSlide({ ...status, projector_visible: false }, detail, slide), false);
  assert.equal(isLiveSlide({ ...status, video: true }, detail, slide), false);
  assert.equal(isLiveSlide(status, detail, { number: 2, text: 'Otro versículo' }), false);
  assert.equal(isLiveSlide(null, detail, slide), false);
});

test('Bible red markers accept the version suffix added by the desktop', () => {
  const { isLiveSlide } = vm.runInNewContext(projectionSource + ';({ isLiveSlide });');
  const detail = { title: 'Génesis 1', selection: { kind: 'chapter' } };
  const slide = { number: 1, text: 'En el principio' };
  const status = { projector_visible: true, video: false, output: { texto: slide.text, referencia: '' } };
  for (const reference of ['Génesis 1:1  |  RVR1960', 'Génesis 1:1 | NVI', 'Génesis 1:1']) {
    status.output.referencia = reference;
    assert.equal(isLiveSlide(status, detail, slide), true, reference);
  }
  status.output.referencia = 'Génesis 1:2 | RVR1960';
  assert.equal(isLiveSlide(status, detail, slide), false);
  status.output.referencia = 'Génesis 1:1 | RVR1960';
  status.output.texto = 'Otro texto';
  assert.equal(isLiveSlide(status, detail, slide), false);
  status.output.texto = slide.text; status.projector_visible = false;
  assert.equal(isLiveSlide(status, detail, slide), false);
});
