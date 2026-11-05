import * as db from './storage.js';
import { $, notice, element, download } from './ui.js';

const names = { events: 'Eventos', plans: 'Planificaciones', notes: 'Notas', tasks: 'Tareas', library: 'Biblioteca local' };
let section = 'events';
let editing = null;
let generation = 0;
let previewUrl;

function revokePreview() {
  if (previewUrl) URL.revokeObjectURL(previewUrl);
  previewUrl = null;
}
function closeEditor() {
  editing = null;
  $('local-editor').hidden = true;
  $('local-form').reset();
}
async function editor(record = null) {
  const ticket = generation;
  editing = record;
  $('local-form').reset();
  $('editor-title').textContent = record ? 'Editar' : 'Crear';
  $('local-title').value = record?.title || '';
  $('local-body').value = record?.cards ? record.cards.map(card => `${card.number}. ${card.text}`).join('\n\n') : record?.body || '';
  $('local-date').value = record?.date || '';
  $('local-end').value = record?.end || '';
  $('local-location').value = record?.location || '';
  $('local-kind').value = record?.kind || 'text';
  $('local-completed').checked = !!record?.completed;
  $('date-field').hidden = !['events', 'plans', 'tasks'].includes(section);
  $('event-fields').hidden = section !== 'events';
  $('plan-fields').hidden = section !== 'plans';
  $('library-fields').hidden = section !== 'library';
  $('task-fields').hidden = section !== 'tasks';
  if (section === 'plans') {
    const [events, library] = await Promise.all([db.list('events'), db.list('library')]);
    if (ticket !== generation) return;
    $('local-event').replaceChildren(new Option('Sin evento asociado', ''), ...events.map(event => new Option(event.title, event.id)));
    $('local-event').value = record?.eventId || '';
    $('local-resources').replaceChildren(...library.map(item => new Option(item.title, item.id)));
    for (const option of $('local-resources').options) option.selected = (record?.resourceIds || []).includes(option.value);
  }
  $('local-editor').hidden = false;
  $('local-title').focus();
}

async function preview(record) {
  revokePreview();
  $('local-preview').hidden = false;
  $('preview-title').textContent = record.title;
  $('preview-content').replaceChildren(element('p', record.body || '', 'preserve-lines'));
  if (record.cards) {
    for (const card of record.cards) $('preview-content').append(element('p', `${card.number}. ${card.text}`, 'preserve-lines'));
  }
  if (record.file instanceof Blob) {
    previewUrl = URL.createObjectURL(record.file);
    if (record.file.type.startsWith('image/')) {
      const image = element('img', undefined, 'local-media'); image.src = previewUrl; image.alt = record.title;
      $('preview-content').append(image);
    } else if (/^(video|audio)\//.test(record.file.type)) {
      const media = element(record.file.type.startsWith('video/') ? 'video' : 'audio', undefined, 'local-media');
      media.src = previewUrl; media.controls = true; $('preview-content').append(media);
    }
    const file = element('a', `Abrir / descargar ${record.fileName || 'archivo'}`, 'file-link');
    file.href = previewUrl; file.download = record.fileName || record.title; $('preview-content').append(file);
  }
  if (section === 'plans') {
    const [event, resources] = await Promise.all([
      record.eventId ? db.get('events', record.eventId) : null,
      Promise.all((record.resourceIds || []).map(id => db.get('library', id))),
    ]);
    if (event) $('preview-content').append(element('p', `Evento: ${event.title}`));
    for (const item of resources.filter(Boolean)) {
      const button = element('button', `Abrir: ${item.title}`);
      button.addEventListener('click', () => preview(item)); $('preview-content').append(button);
    }
  }
  $('local-preview').scrollIntoView({ block: 'nearest' });
}

async function render() {
  const ticket = ++generation;
  const selected = section;
  const rows = await db.list(selected);
  if (ticket !== generation) return;
  const query = $('local-search').value.normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
  const filtered = rows.filter(row => `${row.title} ${row.body || ''} ${(row.cards || []).map(card => card.text).join(' ')}`.normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().includes(query));
  filtered.sort((a, b) => selected === 'tasks' && !!a.completed !== !!b.completed ? Number(!!a.completed) - Number(!!b.completed)
    : ['events', 'plans', 'tasks'].includes(selected) ? (a.date || '9999').localeCompare(b.date || '9999') : (b.updatedAt || '').localeCompare(a.updatedAt || ''));
  $('local-items').replaceChildren();
  if (!filtered.length) $('local-items').append(element('p', query ? 'No hay resultados.' : 'Aún no hay contenido. Crea el primero; quedará guardado en este dispositivo.', 'hint'));
  const events = selected === 'plans' ? await db.list('events') : [];
  if (ticket !== generation) return;
  for (const row of filtered) {
    const card = element('article', undefined, 'local-card'); card.dataset.id = row.id;
    card.append(element('h3', row.title));
    if (row.date) card.append(element('p', new Date(row.date).toLocaleString('es'), 'hint'));
    if (row.end) card.append(element('p', `Finaliza: ${new Date(row.end).toLocaleString('es')}`, 'hint'));
    if (row.location) card.append(element('p', row.location, 'hint'));
    if (row.eventId) card.append(element('p', `Evento: ${events.find(event => event.id === row.eventId)?.title || 'eliminado'}`, 'hint'));
    if (row.body) card.append(element('p', row.body.slice(0, 220), 'preserve-lines'));
    if (row.fileName) card.append(element('p', row.fileName, 'hint'));
    if (selected === 'tasks') {
      const label = element('label', undefined, 'check-label');
      const checkbox = element('input'); checkbox.type = 'checkbox'; checkbox.checked = !!row.completed;
      checkbox.addEventListener('change', () => guarded(async () => { await db.put(selected, { ...row, completed: checkbox.checked }); await render(); }));
      label.append(checkbox, document.createTextNode('Completada')); card.append(label);
      card.classList.toggle('completed', !!row.completed);
    }
    const actions = element('div', undefined, 'card-actions');
    const open = element('button', 'Abrir'); open.addEventListener('click', () => guarded(() => preview(row)));
    const edit = element('button', 'Editar'); edit.addEventListener('click', () => guarded(() => editor(row)));
    const remove = element('button', 'Eliminar', 'danger-button');
    remove.addEventListener('click', () => guarded(async () => {
      if (!confirm(`¿Eliminar «${row.title}» de este dispositivo?`)) return;
      await db.remove(selected, row.id); closeEditor(); $('local-preview').hidden = true; revokePreview(); await render();
    }));
    actions.append(open, edit, remove); card.append(actions); $('local-items').append(card);
  }
}

async function guarded(action) {
  try { await action(); }
  catch (error) { notice(`No se pudo completar la operación local: ${error.message}`, true); }
}
export async function selectLocal(name) {
  section = name; generation++; closeEditor(); revokePreview(); $('local-preview').hidden = true;
  $('local-heading').textContent = names[name]; $('local-search').value = '';
  await guarded(render);
}
export async function saveRemoteDetail(detail) {
  // Explicit copies stay independent of later desktop edits/deletions.
  await db.put('library', {
    title: detail.title, kind: detail.selection.kind === 'song' ? 'song' : 'bible',
    body: '', cards: detail.cards.map(card => ({ number: card.number, text: card.text })),
    source: 'ReadyShow PC',
  });
  notice('Copia guardada en Biblioteca local. Ya puedes leerla sin el PC.');
}
export async function initLocal() {
  $('new-local').addEventListener('click', () => guarded(() => editor()));
  $('cancel-local').addEventListener('click', closeEditor);
  $('local-search').addEventListener('input', () => guarded(render));
  $('close-preview').addEventListener('click', () => { $('local-preview').hidden = true; revokePreview(); });
  $('local-form').addEventListener('submit', event => {
    event.preventDefault();
    const selected = section;
    guarded(async () => {
      const submit = $('save-local'); submit.disabled = true;
      try {
        const row = { ...editing, title: $('local-title').value.trim(), body: $('local-body').value.trim() };
        if (!row.title) throw new Error('Escribe un título.');
        if (['events', 'plans', 'tasks'].includes(selected)) row.date = $('local-date').value;
        if (selected === 'events') {
          row.end = $('local-end').value; row.location = $('local-location').value.trim();
          if (row.date && row.end && row.end < row.date) throw new Error('La fecha final debe ser posterior al inicio.');
        }
        if (selected === 'plans') { row.eventId = $('local-event').value; row.resourceIds = [...$('local-resources').selectedOptions].map(option => option.value); }
        if (selected === 'tasks') row.completed = $('local-completed').checked;
        if (selected === 'library') {
          row.kind = $('local-kind').value;
          const file = $('local-file').files[0];
          if (file) {
            if (file.size > 100 * 1024 * 1024) throw new Error('El archivo supera 100 MB.');
            row.file = file; row.fileName = file.name;
          }
          if ($('remove-file').checked) { delete row.file; delete row.fileName; }
          if (row.cards) delete row.cards; // The editor preserves copied cards as editable plain text.
        }
        await db.put(selected, row); closeEditor(); await render(); notice('Guardado en este dispositivo.');
      } finally { submit.disabled = false; }
    });
  });
  $('preferences-form').addEventListener('submit', event => {
    event.preventDefault(); guarded(async () => {
      await db.put('settings', { id: 'preferences', displayName: $('display-name').value.trim() }); await loadPreferences(); notice('Ajustes guardados.');
    });
  });
  $('export-backup').addEventListener('click', () => guarded(async () => {
    const backup = await db.exportBackup();
    const file = new Blob([JSON.stringify(backup)], { type: 'application/json' });
    if (file.size > 150 * 1024 * 1024) throw new Error('La copia supera 150 MB. Reduce los adjuntos de la biblioteca para poder exportarla y restaurarla.');
    download(file, `readyshow-${new Date().toISOString().slice(0, 10)}.json`);
    notice('Copia exportada con los archivos locales.');
  }));
  $('import-backup').addEventListener('change', event => guarded(async () => {
    const file = event.target.files[0];
    if (!file) return;
    try {
      if (file.size > 150 * 1024 * 1024) throw new Error('La copia supera 150 MB.');
      const backup = JSON.parse(await file.text());
      if (!confirm('La copia reemplazará todos los datos locales de este dispositivo. ¿Restaurar?')) return;
      await db.importBackup(backup); closeEditor(); revokePreview(); $('local-preview').hidden = true;
      await loadPreferences(); await render(); notice('Copia restaurada.');
    } finally { event.target.value = ''; }
  }));
  $('persist-storage').addEventListener('click', () => guarded(async () => {
    const granted = await navigator.storage?.persist?.();
    notice(granted ? 'El navegador concedió almacenamiento persistente.' : 'El navegador no concedió persistencia. Conserva una copia exportada.');
  }));
  await db.openDatabase(); await loadPreferences(); await render();
}
async function loadPreferences() {
  $('display-name').value = (await db.get('settings', 'preferences'))?.displayName || '';
  $('workspace-label').textContent = $('display-name').value || 'TU ESPACIO DE TRABAJO';
}
