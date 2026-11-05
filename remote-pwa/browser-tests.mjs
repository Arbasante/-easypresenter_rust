import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import { createServer } from 'node:http';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
const { chromium } = await import(process.env.READYSHOW_TEST_DEPS
  ? pathToFileURL(`${process.env.READYSHOW_TEST_DEPS}/playwright/index.mjs`).href : 'playwright');
const root = path.dirname(fileURLToPath(import.meta.url));
const artifacts = await fs.mkdtemp(path.join(tmpdir(), 'readyshow-pwa-browser-'));
const profile = path.join(artifacts, 'profile');
const token = 'a'.repeat(32);
let title = 'Canto de prueba', text = 'Primera estrofa', visible = false, projected = '', reference = '', apiCalls = 0;
const commands = [];
const errors = [];
const server = createServer(async (request, response) => {
  const route = new URL(request.url, 'http://localhost').pathname;
  if (route === '/api') {
    apiCalls++;
    response.setHeader('Content-Type', 'application/json'); response.setHeader('Cache-Control', 'no-store');
    if (request.method !== 'POST') { response.writeHead(405); return response.end('{}'); }
    if (request.headers.authorization !== `Bearer ${token}`) { response.writeHead(401); return response.end('{"error":"Sesión finalizada"}'); }
    let body = ''; for await (const chunk of request) body += chunk;
    const action = JSON.parse(body);
    switch (action.action) {
      case 'catalog': return response.end(JSON.stringify({ songs: [{ title, selection: { kind: 'song', id: 7 } }], favorites: [], versions: [{ id: 1, title: 'Reina Valera 1960' }], images: [], videos: [] }));
      case 'status': return response.end(JSON.stringify({ projector_visible: visible, screen_ready: false, playing: false, muted: false, video: false, output: { texto: projected, referencia: reference } }));
      case 'books': return response.end(JSON.stringify([{ id: 1, title: 'Génesis', chapters: 1 }]));
      case 'load': return response.end(JSON.stringify(action.selection.kind === 'chapter'
        ? { title: 'Génesis 1', selection: action.selection, cards: [{ number: 1, text: 'En el principio' }, { number: 2, text: 'Segundo versículo' }] }
        : { title, selection: action.selection, cards: [{ number: 1, text }, { number: 2, text: 'Segunda estrofa' }] }));
      case 'project':
        commands.push(action); visible = true;
        if (action.selection.kind === 'chapter') {
          projected = action.number === 1 ? 'En el principio' : 'Segundo versículo';
          reference = `Génesis 1:${action.number}  |  RVR1960`;
        } else { projected = action.number === 1 ? text : 'Segunda estrofa'; reference = ''; }
        return response.end('{"ok":true}');
      case 'playback': commands.push(action); visible = action.control === 'show'; return response.end('{"ok":true}');
      default: response.writeHead(400); return response.end('{"error":"Acción inválida"}');
    }
  }
  try {
    const file = path.resolve(root, '.' + (route === '/' ? '/index.html' : route));
    if (!file.startsWith(root + path.sep)) throw new Error('Invalid path');
    const bytes = await fs.readFile(file);
    const types = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.png': 'image/png', '.webmanifest': 'application/manifest+json' };
    response.setHeader('Content-Type', types[path.extname(file)] || 'application/octet-stream');
    response.setHeader('Content-Security-Policy', "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' blob:; media-src 'self' blob:; object-src 'none'; connect-src 'self'; worker-src 'self'; manifest-src 'self'; frame-ancestors 'none'; base-uri 'none'");
    response.end(bytes);
  } catch { response.writeHead(404); response.end('Not found'); }
});
await new Promise((resolve, reject) => { server.once('error', reject); server.listen(0, '127.0.0.1', resolve); });
const origin = `http://127.0.0.1:${server.address().port}`;
let context;
const openBrowser = async () => {
  context = await chromium.launchPersistentContext(profile, { headless: true, viewport: { width: 390, height: 844 } });
  const page = context.pages()[0] || await context.newPage();
  page.on('pageerror', error => errors.push(error.message));
  page.setDefaultTimeout(12000);
  return page;
};
const tab = (page, name) => page.locator(`#app-nav [data-page="${name}"]`).click();
async function create(page, section, name, body, extra) {
  await tab(page, section); await page.locator('#new-local').click();
  await page.locator('#local-title').fill(name); await page.locator('#local-body').fill(body);
  if (extra) await extra();
  await page.locator('#save-local').click();
  await page.locator('#local-editor').waitFor({ state: 'hidden' });
  await page.locator('.local-card').filter({ hasText: name }).waitFor();
}
try {
  let page = await openBrowser();
  await page.goto(origin);
  await page.waitForFunction(() => document.querySelector('#cache-status').textContent.startsWith('Interfaz del mando guardada'));
  assert.equal(await page.locator('#app-nav').count(), 0);
  assert.equal(await page.locator('#local-workspace').count(), 0);
  assert.equal(await page.locator('#save-offline').count(), 0);
  assert.equal(apiCalls, 0);
  await page.waitForFunction(() => !!navigator.serviceWorker.controller);
  const cdp = await context.newCDPSession(page);
  const manifest = await cdp.send('Page.getAppManifest');
  assert.equal(manifest.errors.length, 0);
  assert.equal(JSON.parse(manifest.data).name, 'ReadyShow Control');
  assert.deepEqual((await cdp.send('Page.getInstallabilityErrors')).installabilityErrors, []);
  console.log('PASS remote-only PWA, no local CRUD interface, no automatic PC API calls, installability');

  await page.evaluate(async () => {
    const db = await import('/modules/storage.js');
    await db.put('notes', { title: 'Nota anterior a Android', body: 'Conservar para migración' });
    await db.put('library', { title: 'Archivo anterior', fileName: 'prueba.txt', file: new Blob(['Texto áéí'], { type: 'text/plain' }) });
  });
  await page.reload(); await page.locator('#legacy-data').waitFor();
  await page.locator('#legacy-data summary').click();
  const exported = page.waitForEvent('download'); await page.locator('#export-legacy').click();
  const backup = await exported; const backupPath = path.join(artifacts, 'pwa-migration.json'); await backup.saveAs(backupPath);
  const data = JSON.parse(await fs.readFile(backupPath, 'utf8'));
  assert.equal(data.data.notes[0].title, 'Nota anterior a Android');
  assert.ok(data.data.library[0].attachment.data);
  assert.equal(await page.evaluate(async () => (await (await import('/modules/storage.js')).list('notes')).length), 1);
  console.log('PASS previous IndexedDB data preserved and exportable with files for native Android migration');

  await page.locator('#code').fill(token); await page.locator('#connect-form button').click();
  await page.locator('#controller').waitFor();
  await page.waitForFunction(() => document.querySelector('#connection').textContent === 'CONECTADO AL PC');
  await page.locator('[data-tab="songs"]').click(); await page.getByRole('button', { name: 'Ver tarjetas', exact: true }).click();
  await page.locator('#cards .slide-card').first().getByRole('button', { name: 'Proyectar', exact: true }).click();
  await page.locator('#cards .on-air').waitFor();
  assert.deepEqual(commands[0], { action: 'project', selection: { kind: 'song', id: 7 }, number: 1 });
  assert.equal(await page.locator('.live-panel').count(), 0);
  for (const width of [320, 390, 768, 1366]) {
    await page.setViewportSize({ width, height: 900 });
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
    await page.evaluate(() => scrollTo({ top: 0, behavior: 'instant' }));
    await page.screenshot({ path: path.join(artifacts, `remote-${width}.png`), fullPage: true });
  }
  projected = 'Segunda estrofa';
  await page.waitForFunction(() => document.querySelector('#cards .on-air p')?.textContent === 'Segunda estrofa');
  text = 'Editado desde el PC'; title = 'Canto actualizado';
  await page.waitForFunction(() => document.querySelector('#detail-title').textContent === 'Canto actualizado' && document.querySelector('#cards').textContent.includes('Editado desde el PC'));
  await page.locator('[data-control="hide"]').click();
  await page.waitForFunction(() => document.querySelectorAll('#cards .on-air').length === 0);
  console.log('PASS existing remote protocol, projection, red markers, desktop synchronization and responsive layout');
  await page.locator('[data-tab="bible"]').click();
  await page.waitForFunction(() => !document.querySelector('#open-chapter').disabled);
  await page.locator('#open-chapter').click();
  await page.locator('#cards .slide-card').first().getByRole('button', { name: 'Proyectar', exact: true }).click();
  await page.waitForFunction(() => document.querySelector('#cards .on-air p')?.textContent === 'En el principio');
  assert.equal(await page.locator('#cards .on-air').count(), 1);
  projected = 'Segundo versículo'; reference = 'Génesis 1:2  |  RVR1960';
  await page.waitForFunction(() => document.querySelector('#cards .on-air p')?.textContent === 'Segundo versículo');
  assert.equal(await page.locator('#cards .on-air').count(), 1);
  await page.screenshot({ path: path.join(artifacts, 'bible-live.png'), fullPage: true });
  await page.locator('[data-control="hide"]').click();
  await page.waitForFunction(() => document.querySelectorAll('#cards .on-air').length === 0);
  console.log('PASS Bible red live marker with desktop version suffix, verse change and hide');


  await context.setOffline(true);
  assert.equal(await page.locator('[data-control="show"]').isDisabled(), true);
  const beforeOffline = commands.length;
  await context.close();
  await new Promise(resolve => { server.close(resolve); server.closeAllConnections(); });
  page = await openBrowser(); await page.goto(origin);
  await page.locator('#pairing').waitFor();
  assert.equal(commands.length, beforeOffline);
  await page.locator('#legacy-data').waitFor();
  assert.equal(await page.evaluate(async () => (await (await import('/modules/storage.js')).list('notes'))[0].title), 'Nota anterior a Android');
  assert.deepEqual(errors, []);
  console.log('PASS shell cold-start without PC, no queued commands, legacy data retained');
  console.log(`Artifacts: ${artifacts}`);
} finally {
  await context?.close();
  if (server.listening) await new Promise(resolve => { server.close(resolve); server.closeAllConnections(); });
}
