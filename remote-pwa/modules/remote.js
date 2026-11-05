import { $, notice, element } from './ui.js';
import { isLiveSlide } from './projection.js';

const names = { favorites: 'Favoritos', songs: 'Cantos', bible: 'Biblias', images: 'Imágenes', videos: 'Videos' };
const state = { token: '', catalog: null, tab: 'favorites', connected: false, busy: false, detail: null, generation: 0, booksGeneration: 0, urls: [], polling: false, online: false };
let remoteVisible = () => true;
function normalize(text) { return text.normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase(); }
async function api(action, binary = false) {
  const token = state.token;
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 10000);
  try {
    const response = await fetch('/api', { method: 'POST', cache: 'no-store', credentials: 'omit', headers: { 'Content-Type': 'application/json', Authorization: `Bearer ${token}` }, body: JSON.stringify(action), signal: controller.signal });
    if (!response.ok) {
      const data = await response.json().catch(() => ({}));
      if (response.status === 401 && token === state.token) disconnect();
      throw Object.assign(new Error(data.error || `Error ${response.status}`), { status: response.status });
    }
    return binary ? await response.blob() : await response.json();
  } catch (error) {
    if (error.name === 'AbortError' || error instanceof TypeError) throw new Error('No hay respuesta del PC. Verifica la conexión y el estado de la pantalla antes de repetir una acción.');
    throw error;
  } finally { clearTimeout(timeout); }
}
function updateButtons() {
  document.querySelectorAll('[data-project], [data-control]').forEach(button => {
    button.disabled = state.busy || !state.online || (['play_pause', 'mute'].includes(button.dataset.control) && !state.video);
  });
}
async function command(action) {
  if (state.busy || !state.connected || !state.online) return;
  state.busy = true; updateButtons();
  try {
    await api(action);
    notice(action.action === 'project' ? 'Contenido enviado a la ventana de proyección' : 'Control enviado');
    await poll();
  } catch (error) { notice(error.message, true); }
  finally { state.busy = false; updateButtons(); }
}
function disconnect() {
  state.connected = false; state.online = false; state.token = ''; state.catalog = null; state.detail = null;
  state.generation++; state.booksGeneration++;
  sessionStorage.removeItem('readyshow-token');
  state.urls.forEach(url => URL.revokeObjectURL(url)); state.urls = [];
  $('controller').hidden = true; $('pairing').hidden = false; $('disconnect').hidden = true;
  $('code').value = ''; state.live = null; $('connection').textContent = 'SIN CONEXIÓN AL PC'; $('connection').classList.remove('on-air'); $('items').replaceChildren(); $('cards').replaceChildren();
}
async function connect(token) {
  if (!/^[a-f0-9]{32}$/i.test(token)) return notice('Pega el código completo que aparece en el PC.', true);
  const attempt = ++state.generation;
  state.token = token.toLowerCase();
  const connectingToken = state.token;
  try {
    const catalog = await api({ action: 'catalog' });
    if (attempt !== state.generation || connectingToken !== state.token) return;
    state.catalog = catalog; state.connected = true;
    sessionStorage.setItem('readyshow-token', state.token);
    $('pairing').hidden = true; $('controller').hidden = false; $('disconnect').hidden = false;
    $('code').value = '';
    renderVersions(); renderLibrary(); await poll();
    if (state.online) notice('Conectado con ReadyShow');
  } catch (error) { notice(error.message, true); }
}
async function refresh() {
  const generation = ++state.generation;
  try {
    const catalog = await api({ action: 'catalog' });
    if (generation !== state.generation || !state.connected) return;
    state.catalog = catalog; state.detail = null;
    renderVersions(); renderLibrary(); notice('Biblioteca actualizada');
  } catch (error) { notice(error.message, true); }
}
function renderVersions() {
  const selected = $('version').value;
  $('version').replaceChildren(...state.catalog.versions.map(version => new Option(version.title, String(version.id))));
  if ([...$('version').options].some(option => option.value === selected)) $('version').value = selected;
  loadBooks();
}
async function loadBooks() {
  const generation = ++state.booksGeneration;
  $('book').replaceChildren(); $('chapter').replaceChildren(); $('open-chapter').disabled = true;
  const version = Number($('version').value);
  if (!version) return;
  try {
    const books = await api({ action: 'books', version });
    if (generation !== state.booksGeneration || !state.connected) return;
    for (const book of books) {
      const option = new Option(book.title, String(book.id));
      option.dataset.chapters = String(book.chapters); $('book').add(option);
    }
    renderChapters();
  } catch (error) { notice(error.message, true); }
}
function renderChapters() {
  const count = Number($('book').selectedOptions[0]?.dataset.chapters || 0);
  $('chapter').replaceChildren(...Array.from({ length: count }, (_, i) => new Option(String(i + 1), String(i + 1))));
  $('open-chapter').disabled = !count;
}
function clearThumbnails() {
  state.urls.forEach(url => URL.revokeObjectURL(url)); state.urls = [];
}
function renderLibrary() {
  state.generation++;
  clearThumbnails();
  $('section-title').textContent = names[state.tab];
  $('search').placeholder = `Buscar en ${names[state.tab].toLowerCase()}…`;
  $('search').hidden = state.tab === 'bible' || !!state.detail;
  $('bible-picker').hidden = state.tab !== 'bible' || !!state.detail;
  $('detail').hidden = !state.detail;
  $('items').hidden = !!state.detail || state.tab === 'bible';
  if (state.detail) return;
  $('items').replaceChildren(); $('cards').replaceChildren();
  if (state.tab === 'bible') return;
  const query = normalize($('search').value);
  const items = (state.catalog[state.tab] || []).filter(item => normalize(item.title).includes(query));
  if (!items.length) {
    $('items').append(element('p', query ? 'No hay resultados para esta búsqueda.' : 'Esta sección está vacía. El contenido que agregues desde el PC aparecerá automáticamente.', 'hint'));
    return;
  }
  const thumbnails = [];
  for (const item of items) {
    const card = element('article', undefined, 'library-item');
    const media = ['image', 'video'].includes(item.selection.kind);
    if (media) {
      const img = element('img', undefined, 'thumbnail'); img.alt = item.title; img.hidden = true;
      card.append(img); thumbnails.push({ img, selection: item.selection });
    }
    card.append(element('h3', item.title));
    const button = element('button', media ? 'Proyectar' : 'Ver tarjetas');
    if (media) {
      button.dataset.project = ''; button.classList.add('primary');
      button.addEventListener('click', () => command({ action: 'project', selection: item.selection, number: 0 }));
    } else button.addEventListener('click', () => loadDetail(item.selection, item.number));
    card.append(button); $('items').append(card);
  }
  updateButtons(); loadThumbnails(thumbnails, state.generation);
}
async function loadThumbnails(items, generation) {
  // Two concurrent thumbnails keep the LAN server responsive to projection commands.
  let index = 0;
  async function worker() {
    while (index < items.length && generation === state.generation && state.connected) {
      const { img, selection } = items[index++];
      try {
        const blob = await api({ action: 'thumbnail', selection }, true);
        if (generation !== state.generation || !state.connected) return;
        const url = URL.createObjectURL(blob); state.urls.push(url); img.src = url; img.hidden = false;
      } catch { /* Missing thumbnails leave the title and projection button usable. */ }
    }
  }
  await Promise.all([worker(), worker()]);
}
async function loadDetail(selection, target) {
  const generation = ++state.generation;
  try {
    const detail = await api({ action: 'load', selection });
    if (generation !== state.generation || !state.connected) return;
    renderDetail(detail, target, true);
  } catch (error) { notice(error.message, true); }
}
function renderDetail(detail, target, scroll = false) {
    state.detail = detail; renderLibrary();
    $('detail-title').textContent = detail.title; $('cards').replaceChildren();
    let selectedCard;
    for (const slide of detail.cards) {
      const card = element('article', undefined, 'slide-card');
      if (slide.number === target) { card.classList.add('target'); selectedCard = card; }
      card.dataset.number = String(slide.number);
      card.append(element('header', `${detail.selection.kind === 'song' ? 'ESTROFA' : 'VERSÍCULO'} ${slide.number}`), element('p', slide.text));
      const project = element('button', 'Proyectar', 'primary'); project.dataset.project = '';
      project.addEventListener('click', () => command({ action: 'project', selection: detail.selection, number: slide.number }));
      card.append(project); $('cards').append(card);
    }
    updateButtons(); updateLiveMarkers();
    if (scroll) (selectedCard || $('detail')).scrollIntoView({ block: 'start', behavior: 'smooth' });
}
async function syncLibrary() {
  const generation = state.generation;
  const token = state.token;
  const currentDetail = state.detail;
  const catalog = await api({ action: 'catalog' });
  let detail = currentDetail;
  if (currentDetail) {
    try { detail = await api({ action: 'load', selection: currentDetail.selection }); }
    catch (error) {
      if (error.status !== 400) throw error;
      detail = null; // The desktop may have deleted the open song or chapter.
    }
  }
  if (!state.connected || token !== state.token || generation !== state.generation) return;
  const catalogChanged = JSON.stringify(catalog) !== JSON.stringify(state.catalog);
  const detailChanged = JSON.stringify(detail) !== JSON.stringify(currentDetail);
  if (catalogChanged) {
    const versionsChanged = JSON.stringify(catalog.versions) !== JSON.stringify(state.catalog?.versions);
    state.catalog = catalog;
    if (versionsChanged) renderVersions();
  }
  if (detailChanged) {
    if (detail) renderDetail(detail);
    else {
      state.detail = null; renderLibrary();
      notice('El contenido abierto ya no está disponible en el PC.');
    }
  } else if (catalogChanged && !state.detail) renderLibrary();
}

async function poll() {
  if (!state.connected || state.polling || document.hidden || !remoteVisible()) return;
  const token = state.token;
  state.polling = true;
  try {
    const data = await api({ action: 'status' });
    if (!state.connected || token !== state.token) return;
    state.online = true; state.video = data.video; state.live = data;
    $('connection').textContent = data.projector_visible ? 'EN VIVO' : 'CONECTADO AL PC';
    $('connection').classList.toggle('on-air', data.projector_visible);
    $('play').textContent = data.playing ? 'Pausar video' : 'Reanudar video';
    $('mute').textContent = data.muted ? 'Activar audio' : 'Silenciar';
    await syncLibrary();
    updateLiveMarkers();
  } catch (error) {
    if (token !== state.token) return;
    const wasOnline = state.online;
    state.online = false; state.live = null; updateLiveMarkers();
    $('connection').textContent = 'SIN CONEXIÓN AL PC'; $('connection').classList.remove('on-air');
    if (state.connected && wasOnline) notice(error.message, true);
  } finally { state.polling = false; updateButtons(); }
}
function updateLiveMarkers() {
  if (!state.detail) return;
  document.querySelectorAll('#cards .slide-card').forEach(card => {
    const slide = state.detail.cards.find(item => item.number === Number(card.dataset.number));
    const live = state.online && isLiveSlide(state.live, state.detail, slide);
    card.classList.toggle('on-air', !!live);
    const button = card.querySelector('[data-project]');
    if (button) { button.textContent = live ? 'EN VIVO' : 'Proyectar'; button.setAttribute('aria-label', live ? 'En vivo: volver a proyectar' : 'Proyectar'); }
  });
}
export function initRemote(isVisible = () => true) {
  remoteVisible = isVisible;
  $('connect-form').addEventListener('submit', event => { event.preventDefault(); connect($('code').value.trim()); });
  $('disconnect').addEventListener('click', disconnect);
  $('refresh').addEventListener('click', refresh);
  $('search').addEventListener('input', renderLibrary);
  $('version').addEventListener('change', loadBooks);
  $('book').addEventListener('change', renderChapters);
  $('open-chapter').addEventListener('click', () => loadDetail({ kind: 'chapter', book: Number($('book').value), chapter: Number($('chapter').value), version: Number($('version').value) }));
  $('back').addEventListener('click', () => { state.detail = null; renderLibrary(); });
  $('tabs').addEventListener('click', event => {
    const button = event.target.closest('[data-tab]'); if (!button) return;
    state.tab = button.dataset.tab; state.detail = null; $('search').value = '';
    $('tabs').querySelectorAll('button').forEach(tab => tab.setAttribute('aria-pressed', String(tab === button)));
    renderLibrary();
  });
  document.querySelectorAll('[data-control]').forEach(button => button.addEventListener('click', () => command({ action: 'playback', control: button.dataset.control })));
  document.addEventListener('visibilitychange', () => { if (!document.hidden) poll(); });
  window.addEventListener('online', poll);
  window.addEventListener('offline', () => { state.online = false; state.live = null; $('connection').textContent = 'SIN CONEXIÓN AL PC'; $('connection').classList.remove('on-air'); updateButtons(); updateLiveMarkers(); });
  document.addEventListener('readyshow-page', poll);
  setInterval(poll, 2000);
  const linkToken = new URLSearchParams(location.hash.slice(1)).get('token');
  if (location.hash) history.replaceState(null, '', location.pathname);
  const savedToken = linkToken || sessionStorage.getItem('readyshow-token');
  if (savedToken) {
    // Reuse the session code without persisting it into the device database.
    $('code').value = savedToken;
  }

}
