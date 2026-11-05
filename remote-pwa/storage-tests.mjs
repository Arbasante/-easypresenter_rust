import test from 'node:test';
import assert from 'node:assert/strict';
import { pathToFileURL } from 'node:url';
const fake = await import(process.env.READYSHOW_TEST_DEPS
  ? pathToFileURL(`${process.env.READYSHOW_TEST_DEPS}/fake-indexeddb/build/esm/index.js`).href : 'fake-indexeddb');
globalThis.indexedDB = fake.indexedDB;
const db = await import('./modules/storage.js');

async function empty() {
  const data = Object.fromEntries(db.STORES.map(store => [store, []]));
  await db.importBackup({ format: 'readyshow-local', version: 1, data });
}
test('every local collection persists creates, edits and deletes without fetch', async () => {
  await empty();
  globalThis.fetch = () => { throw new Error('Local storage must not contact a server'); };
  for (const name of db.STORES) {
    const saved = await db.put(name, { id: name === 'settings' ? 'preferences' : undefined, title: `Prueba ${name}`, body: 'Sin PC' });
    assert.equal((await db.get(name, saved.id)).body, 'Sin PC');
    await db.put(name, { ...saved, body: 'Editado offline' });
    assert.equal((await db.list(name))[0].body, 'Editado offline');
    await db.remove(name, saved.id);
    assert.equal((await db.list(name)).length, 0);
  }
});
test('backups restore local relationships, completed tasks, settings and binary files', async () => {
  await empty();
  const event = await db.put('events', { title: 'Reunión', date: '2026-11-06T18:00' });
  const resource = await db.put('library', { title: 'Archivo', fileName: 'prueba.txt', file: new Blob(['Texto áéí'], { type: 'text/plain' }) });
  await db.put('plans', { title: 'Programa', eventId: event.id, resourceIds: [resource.id], body: '1. Inicio\n2. Lectura' });
  await db.put('tasks', { title: 'Preparar', completed: true });
  await db.put('settings', { id: 'preferences', displayName: 'Mi espacio' });
  const backup = JSON.parse(JSON.stringify(await db.exportBackup()));
  assert.equal(backup.data.library[0].file, undefined);
  assert.ok(backup.data.library[0].attachment.data);
  await empty(); await db.importBackup(backup);
  const plan = (await db.list('plans'))[0];
  assert.equal(plan.eventId, event.id);
  assert.deepEqual(plan.resourceIds, [resource.id]);
  assert.equal((await db.list('tasks'))[0].completed, true);
  assert.equal((await db.get('library', resource.id)).file.type, 'text/plain');
  assert.equal(await (await db.get('library', resource.id)).file.text(), 'Texto áéí');
  assert.equal((await db.get('settings', 'preferences')).displayName, 'Mi espacio');
});
test('invalid restores leave every collection intact and exclude credentials', async () => {
  const before = await db.exportBackup();
  const bad = structuredClone(before);
  bad.data.notes = [{ id: 'invalid' }];
  await assert.rejects(db.importBackup(bad), /Registro inválido/);
  assert.deepEqual((await db.exportBackup()).data, before.data);
  const secret = structuredClone(before);
  secret.data.settings = [{ id: 'remote-token', title: 'Credentials' }];
  await assert.rejects(db.importBackup(secret), /Ajuste no permitido/);
  assert.deepEqual((await db.exportBackup()).data, before.data);
});
