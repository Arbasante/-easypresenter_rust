use rusqlite::{Connection, Result};
use slint::{ModelRc, SharedString, VecModel, ComponentHandle, Image}; 
use rfd::FileDialog; 
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::rc::Rc;
use std::thread;
use regex::Regex;

slint::include_modules!(); 

struct CantoDB { pub id: i32, pub titulo: String }
struct DiapositivaDB { pub orden: i32, pub texto: String }
struct LibroBibliaDB { pub id: i32, pub nombre: String, pub capitulos: i32 }
#[derive(Clone)] struct VersiculoDB { pub versiculo: i32, pub texto: String }
#[derive(Clone)] struct VersionInfo { pub id: i32, pub sigla: String, pub nombre_completo: String, pub prioridad: i32 }

#[derive(Hash, Eq, PartialEq, Clone, Debug)] struct CacheKey { version_id: i32, libro_numero: i32, capitulo: i32 }

const NOMBRES_LIBROS: [&str; 66] = [
    "Génesis", "Éxodo", "Levítico", "Números", "Deuteronomio", "Josué", "Jueces", "Rut", "1 Samuel", "2 Samuel",
    "1 Reyes", "2 Reyes", "1 Crónicas", "2 Crónicas", "Esdras", "Nehemías", "Ester", "Job", "Salmos", "Proverbios",
    "Eclesiastés", "Cantares", "Isaías", "Jeremías", "Lamentaciones", "Ezequiel", "Daniel", "Oseas", "Joel", "Amós",
    "Abdías", "Jonás", "Miqueas", "Nahúm", "Habacuc", "Sofonías", "Hageo", "Zacarías", "Malaquías", "Mateo",
    "Marcos", "Lucas", "Juan", "Hechos", "Romanos", "1 Corintios", "2 Corintios", "Gálatas", "Efesios", "Filipenses",
    "Colosenses", "1 Tesalonicenses", "2 Tesalonicenses", "1 Timoteo", "2 Timoteo", "Tito", "Filemón", "Hebreos", "Santiago",
    "1 Pedro", "2 Pedro", "1 Juan", "2 Juan", "3 Juan", "Judas", "Apocalipsis"
];

fn trim(s: &str) -> String { s.trim().to_string() }

fn normalizar(texto: &str) -> String {
    let mut resultado = texto.to_string();
    let reemplazos = [ ("á", "a"), ("é", "e"), ("í", "i"), ("ó", "o"), ("ú", "u"), ("Á", "a"), ("É", "e"), ("Í", "i"), ("Ó", "o"), ("Ú", "u") ];
    for (viejo, nuevo) in reemplazos { resultado = resultado.replace(viejo, nuevo); }
    resultado.to_lowercase()
}

fn buscar_libro_inteligente(query: &str) -> Option<(i32, String)> {
    let q = normalizar(&trim(query));
    if q.is_empty() { return None; }
    for (i, &nombre) in NOMBRES_LIBROS.iter().enumerate() { if normalizar(nombre).starts_with(&q) { return Some(((i + 1) as i32, nombre.to_string())); } }
    None
}

struct AppState { cantos_db: Connection, biblias_db: Connection, versiones: Vec<VersionInfo>, current_version_id: i32, chapter_cache: HashMap<CacheKey, Vec<VersiculoDB>> }

impl AppState {
    fn new() -> Result<Self> {
        let cantos_db = Connection::open("data/cantos.db")?;
        let biblias_db = Connection::open("data/biblias.db")?;
        cantos_db.execute_batch("PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;")?;
        biblias_db.execute_batch("PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;")?;
        let mut state = Self { cantos_db, biblias_db, versiones: Vec::new(), current_version_id: 1, chapter_cache: HashMap::new() };
        state.procesar_versiones();
        Ok(state)
    }

    fn procesar_versiones(&mut self) {
        let mut stmt = self.biblias_db.prepare("SELECT id, nombre FROM versiones").unwrap();
        let iter = stmt.query_map([], |row| { Ok((row.get::<_, i32>(0)?, row.get::<_, String>(1)?)) }).unwrap();
        for item in iter.filter_map(Result::ok) {
            let (id, nombre_bd) = item;
            let (sigla, nombre_comp, prioridad) = match nombre_bd.as_str() {
                "ReinaValera1960" => ("RVR", "Reina Valera 1960", 0), "NuevaVersiónInternacional" => ("NVI", "Nueva Versión Internacional", 1), "NuevaTraduccionViviente" => ("NTV", "Nueva Traducción Viviente", 2), "BibliaDeLasAméricas" => ("LBLA", "La Biblia de las Américas", 3), "NuevaBibliadelasAméricas" => ("NBLA", "Nueva Biblia de las Américas", 4), "TraduccionLenguajeActual" => ("TLA", "Traducción en Lenguaje Actual", 5), "DiosHablaHoy" => ("DHH", "Dios Habla Hoy", 6), "LaPalabra" => ("BLP", "La Palabra", 7), "TraduccionInterconfesionalVersionHispanoamericana" => ("TIVH", "Trad. Interconfesional Hispanoamericana", 8), "BibliaTextual" => ("BTX", "Biblia Textual", 9), "BibliaJubileo" => ("JUB", "Biblia del Jubileo", 10), "BibliadelOso1573" => ("OSO", "Biblia del Oso 1573", 11), _ => { let s = if nombre_bd.len() >= 4 { &nombre_bd[0..4] } else { &nombre_bd }; ("", s, 999) }
            };
            let sigla_final = if sigla.is_empty() { nombre_comp.to_uppercase() } else { sigla.to_string() };
            self.versiones.push(VersionInfo { id, sigla: sigla_final, nombre_completo: nombre_comp.to_string(), prioridad });
        }
        self.versiones.sort_by_key(|v| v.prioridad);
        if !self.versiones.is_empty() { self.current_version_id = self.versiones[0].id; }
    }

    fn set_version_by_name(&mut self, name: &str) -> String {
        if let Some(v) = self.versiones.iter().find(|v| v.nombre_completo == name) { self.current_version_id = v.id; return v.nombre_completo.clone(); }
        String::new()
    }
    fn get_sigla_actual(&self) -> String { self.versiones.iter().find(|v| v.id == self.current_version_id).map(|v| v.sigla.clone()).unwrap_or_default() }
    fn get_libros_biblia(&self) -> Vec<LibroBibliaDB> {
        let mut stmt = self.biblias_db.prepare("SELECT libro_numero, libro_nombre, MAX(capitulo) FROM versiculos WHERE version_id = ? GROUP BY libro_numero ORDER BY libro_numero").unwrap();
        let iter = stmt.query_map([self.current_version_id], |row| Ok(LibroBibliaDB { id: row.get(0)?, nombre: row.get(1)?, capitulos: row.get(2)? })).unwrap();
        iter.filter_map(Result::ok).collect()
    }
    fn get_capitulo(&mut self, libro_numero: i32, capitulo: i32) -> Vec<VersiculoDB> {
        let key = CacheKey { version_id: self.current_version_id, libro_numero, capitulo };
        if let Some(cached) = self.chapter_cache.get(&key) { return cached.clone(); }
        let mut stmt = self.biblias_db.prepare("SELECT versiculo, texto FROM versiculos WHERE version_id = ? AND libro_numero = ? AND capitulo = ? ORDER BY versiculo").unwrap();
        let iter = stmt.query_map([self.current_version_id, libro_numero, capitulo], |row| Ok(VersiculoDB { versiculo: row.get(0)?, texto: row.get(1)? })).unwrap();
        let lista: Vec<VersiculoDB> = iter.filter_map(Result::ok).collect();
        self.chapter_cache.insert(key, lista.clone());
        lista
    }

    fn get_all_cantos(&self) -> Vec<CantoDB> {
        let mut stmt = self.cantos_db.prepare("SELECT id, titulo FROM cantos ORDER BY titulo").unwrap();
        let iter = stmt.query_map([], |row| Ok(CantoDB { id: row.get(0)?, titulo: row.get(1)? })).unwrap();
        iter.filter_map(Result::ok).collect()
    }
    fn get_cantos_filtrados(&self, busqueda: &str) -> Vec<CantoDB> {
        let mut stmt = self.cantos_db.prepare("SELECT id, titulo FROM cantos WHERE titulo LIKE ? ORDER BY titulo").unwrap();
        let iter = stmt.query_map([format!("%{}%", busqueda)], |row| Ok(CantoDB { id: row.get(0)?, titulo: row.get(1)? })).unwrap();
        iter.filter_map(Result::ok).collect()
    }
    fn get_canto_titulo(&self, id: i32) -> String { self.cantos_db.query_row("SELECT titulo FROM cantos WHERE id = ?", [id], |row| row.get(0)).unwrap_or_default() }
    fn get_canto_diapositivas(&self, id: i32) -> Vec<DiapositivaDB> {
        let mut stmt = self.cantos_db.prepare("SELECT orden, texto FROM diapositivas WHERE canto_id = ? ORDER BY orden").unwrap();
        let iter = stmt.query_map([id], |row| Ok(DiapositivaDB { orden: row.get(0)?, texto: row.get(1)? })).unwrap();
        iter.filter_map(Result::ok).collect()
    }
    fn insert_diapositivas_intern(&self, canto_id: i32, letra: &str) {
        let mut orden = 1;
        for estrofa in letra.split("\n\n") {
            let texto = trim(estrofa);
            if !texto.is_empty() { self.cantos_db.execute("INSERT INTO diapositivas (canto_id, orden, texto) VALUES (?, ?, ?)", rusqlite::params![canto_id, orden, texto]).unwrap(); orden += 1; }
        }
    }
    fn add_canto(&self, titulo: &str, letra: &str) {
        self.cantos_db.execute("INSERT INTO cantos (titulo, tono, categoria) VALUES (?, '', 'Personalizado')", [titulo]).unwrap();
        self.insert_diapositivas_intern(self.cantos_db.last_insert_rowid() as i32, letra);
    }
    fn update_canto(&self, id: i32, titulo: &str, letra: &str) {
        self.cantos_db.execute("UPDATE cantos SET titulo = ? WHERE id = ?", rusqlite::params![titulo, id]).unwrap();
        self.cantos_db.execute("DELETE FROM diapositivas WHERE canto_id = ?", [id]).unwrap();
        self.insert_diapositivas_intern(id, letra);
    }
    fn delete_canto(&self, id: i32) {
        self.cantos_db.execute("DELETE FROM diapositivas WHERE canto_id = ?", [id]).unwrap();
        self.cantos_db.execute("DELETE FROM cantos WHERE id = ?", [id]).unwrap();
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let state = Arc::new(Mutex::new(AppState::new()?));
    let ui = AppWindow::new()?;
    let proyector = ProjectorWindow::new()?;

    let current_biblia_libro = Arc::new(Mutex::new(-1));
    let current_biblia_capitulo = Arc::new(Mutex::new(-1));

    {
        // ADVERTENCIA AMARILLA ARREGLADA AQUI (quite el "mut")
        let st = state.lock().unwrap();
        let versiones_slint: Vec<SharedString> = st.versiones.iter().map(|v| SharedString::from(&v.nombre_completo)).collect();
        ui.set_bible_versions(ModelRc::from(Rc::new(VecModel::from(versiones_slint))));
        if let Some(primera) = st.versiones.first() { ui.set_current_bible_version(SharedString::from(&primera.nombre_completo)); }
        let libros = st.get_libros_biblia();
        let libros_slint: Vec<BookInfo> = libros.into_iter().map(|l| BookInfo { id: l.id, nombre: SharedString::from(l.nombre), capitulos: l.capitulos }).collect();
        ui.set_bible_books(ModelRc::from(Rc::new(VecModel::from(libros_slint))));
    }

    let ui_handle = ui.as_weak(); let state_clone = Arc::clone(&state);
    let cargar_cantos = move |busqueda: String| {
        let ui = ui_handle.unwrap(); let estado = state_clone.lock().unwrap();
        let cantos_db = if busqueda.is_empty() { estado.get_all_cantos() } else { estado.get_cantos_filtrados(&busqueda) };
        let mut cantos_slint: Vec<Canto> = cantos_db.into_iter().map(|c| Canto { id: c.id, titulo: SharedString::from(c.titulo), letra: SharedString::from("") }).collect();
        if cantos_slint.is_empty() { cantos_slint.push(Canto { id: 0, titulo: SharedString::from("Click derecho para agregar canto"), letra: SharedString::from("") }); }
        ui.set_cantos(ModelRc::from(Rc::new(VecModel::from(cantos_slint))));
    };
    cargar_cantos(String::new());

    let c_clone = cargar_cantos.clone(); ui.on_buscar_cantos(move |t| c_clone(t.to_string()));
    
    let ui_handle = ui.as_weak(); let state_clone = Arc::clone(&state); let cb_lib = Arc::clone(&current_biblia_libro); let cb_cap = Arc::clone(&current_biblia_capitulo);
    ui.on_seleccionar_canto(move |id| {
        if id == 0 { return; }
        *cb_lib.lock().unwrap() = -1; *cb_cap.lock().unwrap() = -1;
        let ui = ui_handle.unwrap(); let estado = state_clone.lock().unwrap();
        ui.set_elemento_seleccionado(SharedString::from(estado.get_canto_titulo(id)));
        let diapos_slint: Vec<DiapositivaUI> = estado.get_canto_diapositivas(id).into_iter().map(|d| DiapositivaUI { orden: SharedString::from(d.orden.to_string()), texto: SharedString::from(d.texto) }).collect();
        ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos_slint))));
        ui.set_active_estrofa_index(-1); ui.invoke_focus_panel();
    });

    let state_clone = Arc::clone(&state); let c_clone = cargar_cantos.clone();
    ui.on_guardar_canto(move |id, titulo, letra| {
        let estado = state_clone.lock().unwrap();
        if id == -1 { estado.add_canto(&titulo, &letra); } else { estado.update_canto(id, &titulo, &letra); }
        c_clone(String::new());
    });

    let state_clone = Arc::clone(&state); let c_clone = cargar_cantos.clone();
    ui.on_eliminar_canto(move |id| { state_clone.lock().unwrap().delete_canto(id); c_clone(String::new()); });

    let proyector_handle = proyector.as_weak();
    ui.on_abrir_proyector(move || { proyector_handle.unwrap().show().unwrap(); });

    let proyector_handle = proyector.as_weak(); let state_clone = Arc::clone(&state);
    ui.on_proyectar_estrofa(move |texto, referencia| {
        let p = proyector_handle.unwrap();
        p.set_texto_proyeccion(texto.clone());
        let mut ref_str = referencia.to_string();
        if !ref_str.is_empty() {
            let sigla = state_clone.lock().unwrap().get_sigla_actual();
            if !sigla.is_empty() { ref_str = format!("{}  |  {}", ref_str, sigla); }
        }
        p.set_referencia(SharedString::from(ref_str));
        let len = texto.len();
        let font_size = if len >= 450 { 32.0 } else if len >= 320 { 38.0 } else if len >= 220 { 46.0 } else if len >= 120 { 56.0 } else if len >= 60 { 68.0 } else { 85.0 };
        p.set_tamano_letra(font_size);
    });

    let ui_h = ui.as_weak();
    ui.on_bible_search_changed(move |query| {
        let ui = ui_h.unwrap();
        if let Some((_, sug)) = buscar_libro_inteligente(&query) {
            if sug.to_lowercase() != query.to_lowercase() { ui.set_bible_search_suggestion(SharedString::from(sug)); return; }
        }
        ui.set_bible_search_suggestion(SharedString::from(""));
    });

    let ui_h = ui.as_weak();
    ui.on_bible_book_selected(move |book| {
        let ui = ui_h.unwrap(); let mut filas = Vec::new(); let mut fila_actual = Vec::new();
        for i in 1..=book.capitulos {
            fila_actual.push(i);
            if fila_actual.len() == 5 || i == book.capitulos {
                filas.push(ChapterRow { caps: ModelRc::from(Rc::new(VecModel::from(fila_actual.clone()))) });
                fila_actual.clear();
            }
        }
        ui.set_chapter_rows(ModelRc::from(Rc::new(VecModel::from(filas))));
    });

    let ui_h = ui.as_weak(); let state_clone = Arc::clone(&state); let cb_lib = Arc::clone(&current_biblia_libro); let cb_cap = Arc::clone(&current_biblia_capitulo);
    ui.on_bible_chapter_selected(move |cap| {
        let ui = ui_h.unwrap(); let book = ui.get_selected_bible_book();
        *cb_lib.lock().unwrap() = book.id; *cb_cap.lock().unwrap() = cap;
        let titulo = format!("{} {}", book.nombre, cap);
        ui.set_elemento_seleccionado(SharedString::from(&titulo));

        let state_thread = Arc::clone(&state_clone); let ui_thread = ui.as_weak();
        thread::spawn(move || {
            let versiculos = state_thread.lock().unwrap().get_capitulo(book.id, cap);
            let _ = slint::invoke_from_event_loop(move || {
                let ui = ui_thread.unwrap();
                let diapos: Vec<DiapositivaUI> = versiculos.into_iter().map(|v| DiapositivaUI { orden: SharedString::from(v.versiculo.to_string()), texto: SharedString::from(v.texto) }).collect();
                ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
                ui.set_active_estrofa_index(0);
                if !diapos.is_empty() { ui.invoke_proyectar_estrofa(diapos[0].texto.clone(), SharedString::from(format!("{}:{}", titulo, diapos[0].orden))); }
                ui.invoke_focus_panel();
            });
        });
    });

    let ui_h = ui.as_weak(); let state_clone = Arc::clone(&state); let cb_lib = Arc::clone(&current_biblia_libro); let cb_cap = Arc::clone(&current_biblia_capitulo);
    ui.on_bible_search_accepted(move |query| {
        let ui = ui_h.unwrap(); let q = query.to_string();
        let re = Regex::new(r"^\s*(.*?)\s+(\d+)(?:\s+(\d+))?\s*$").unwrap();
        if let Some(caps) = re.captures(&q) {
            let book_query = &caps[1]; let capitulo: i32 = caps[2].parse().unwrap_or(1); let versiculo_obj: i32 = caps.get(3).map_or(1, |m| m.as_str().parse().unwrap_or(1));
            if let Some((libro_id, nombre_real)) = buscar_libro_inteligente(book_query) {
                *cb_lib.lock().unwrap() = libro_id; *cb_cap.lock().unwrap() = capitulo;
                let titulo = format!("{} {}", nombre_real, capitulo);
                ui.set_elemento_seleccionado(SharedString::from(&titulo));

                let state_thread = Arc::clone(&state_clone); let ui_thread = ui.as_weak();
                thread::spawn(move || {
                    let versiculos = state_thread.lock().unwrap().get_capitulo(libro_id, capitulo);
                    let _ = slint::invoke_from_event_loop(move || {
                        let ui = ui_thread.unwrap(); let mut target_index = 0;
                        let diapos: Vec<DiapositivaUI> = versiculos.into_iter().enumerate().map(|(i, v)| {
                            if v.versiculo == versiculo_obj { target_index = i as i32; }
                            DiapositivaUI { orden: SharedString::from(v.versiculo.to_string()), texto: SharedString::from(v.texto) }
                        }).collect();
                        ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
                        ui.set_active_estrofa_index(target_index); ui.set_scroll_to_y(target_index as f32 * 115.0);
                        if (target_index as usize) < diapos.len() {
                            let text = diapos[target_index as usize].texto.clone(); let ord = diapos[target_index as usize].orden.clone();
                            ui.invoke_proyectar_estrofa(text, SharedString::from(format!("{}:{}", titulo, ord)));
                        }
                        ui.invoke_focus_panel();
                    });
                });
                ui.set_bible_search_suggestion(SharedString::from(""));
            }
        }
    });

    let ui_h = ui.as_weak(); let state_clone = Arc::clone(&state); let cb_lib = Arc::clone(&current_biblia_libro); let cb_cap = Arc::clone(&current_biblia_capitulo);
    ui.on_bible_version_changed(move |version_name| {
        let ui = ui_h.unwrap(); let lib = *cb_lib.lock().unwrap(); let cap = *cb_cap.lock().unwrap();
        let mut versiculos_nuevos = Vec::new();
        {
            let mut estado = state_clone.lock().unwrap(); estado.set_version_by_name(version_name.as_str());
            if lib != -1 && cap != -1 { versiculos_nuevos = estado.get_capitulo(lib, cap); }
        }
        if lib != -1 && cap != -1 && !versiculos_nuevos.is_empty() {
            let active_idx = ui.get_active_estrofa_index();
            let diapos: Vec<DiapositivaUI> = versiculos_nuevos.into_iter().map(|v| DiapositivaUI { orden: SharedString::from(v.versiculo.to_string()), texto: SharedString::from(v.texto) }).collect();
            ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
            if active_idx >= 0 && (active_idx as usize) < diapos.len() {
                let texto_nuevo = diapos[active_idx as usize].texto.clone(); let orden = diapos[active_idx as usize].orden.clone();
                let book_name = ui.get_selected_bible_book().nombre; let titulo = format!("{} {}", book_name, cap);
                ui.invoke_proyectar_estrofa(texto_nuevo, SharedString::from(format!("{}:{}", titulo, orden)));
            }
        }
    });

    // --- MAGIA FINAL: SINCRONIZADOR DE ESTILOS ---
    let ui_h_sync = ui.as_weak();
    let p_h_sync = proyector.as_weak();

    ui.on_sync_estilos(move || {
        let ui = ui_h_sync.unwrap();
        let p = p_h_sync.unwrap();
        let is_biblia = ui.get_active_tab() == "biblias";

        let bg_type = if is_biblia { ui.get_biblias_bg_type() } else { ui.get_cantos_bg_type() };
        let font_color = if is_biblia { ui.get_biblias_font_color() } else { ui.get_cantos_font_color() };

        p.set_text_color(font_color);

        if bg_type == "negro" {
            p.set_bg_color(slint::Color::from_rgb_u8(0, 0, 0));
            p.set_mostrar_imagen(false);
        } else if bg_type == "blanco" {
            p.set_bg_color(slint::Color::from_rgb_u8(255, 255, 255));
            p.set_mostrar_imagen(false);
        } else if bg_type == "imagen" || bg_type == "video" {
            p.set_bg_color(slint::Color::from_rgb_u8(0, 0, 0));
            if is_biblia && ui.get_biblias_has_image() {
                p.set_fondo_imagen(ui.get_biblias_bg_image());
                p.set_mostrar_imagen(true);
            } else if !is_biblia && ui.get_cantos_has_image() {
                p.set_fondo_imagen(ui.get_cantos_bg_image());
                p.set_mostrar_imagen(true);
            } else {
                p.set_mostrar_imagen(false);
            }
        }
    });

    // --- CARGAR ARCHIVOS MULTIMEDIA ---
    let ui_h_media = ui.as_weak();
    ui.on_cargar_fondo_media(move |tipo| {
        let ui = ui_h_media.unwrap();
        if let Some(path) = rfd::FileDialog::new().add_filter("Imágenes", &["png", "jpg", "jpeg", "webp"]).pick_file() {
            if let Ok(img) = slint::Image::load_from_path(&path) {
                if tipo == "biblias" {
                    ui.set_biblias_bg_image(img);
                    ui.set_biblias_has_image(true);
                    ui.set_biblias_bg_type(SharedString::from("imagen"));
                } else {
                    ui.set_cantos_bg_image(img);
                    ui.set_cantos_has_image(true);
                    ui.set_cantos_bg_type(SharedString::from("imagen"));
                }
                ui.invoke_sync_estilos(); 
            }
        }
    });

    let ui_h_rm = ui.as_weak();
    ui.on_quitar_fondo_media(move |tipo| {
        let ui = ui_h_rm.unwrap();
        if tipo == "biblias" {
            ui.set_biblias_has_image(false);
            ui.set_biblias_bg_type(SharedString::from("negro"));
        } else {
            ui.set_cantos_has_image(false);
            ui.set_cantos_bg_type(SharedString::from("negro"));
        }
        ui.invoke_sync_estilos();
    });

    ui.run()?;
    Ok(())
}