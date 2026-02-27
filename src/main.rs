use rusqlite::{Connection, Result};
use slint::{ModelRc, SharedString, VecModel, ComponentHandle, Image};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::rc::Rc;
use std::thread;
use regex::Regex;
use display_info::DisplayInfo;

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
    let reemplazos = [("á","a"),("é","e"),("í","i"),("ó","o"),("ú","u"),("Á","a"),("É","e"),("Í","i"),("Ó","o"),("Ú","u")];
    for (viejo, nuevo) in reemplazos { resultado = resultado.replace(viejo, nuevo); }
    resultado.to_lowercase()
}

fn buscar_libro_inteligente(query: &str) -> Option<(i32, String)> {
    let q = normalizar(&trim(query));
    if q.is_empty() { return None; }
    for (i, &nombre) in NOMBRES_LIBROS.iter().enumerate() {
        if normalizar(nombre).starts_with(&q) { return Some(((i + 1) as i32, nombre.to_string())); }
    }
    None
}

struct AppState {
    cantos_db: Connection, biblias_db: Connection,
    versiones: Vec<VersionInfo>, current_version_id: i32,
    chapter_cache: HashMap<CacheKey, Vec<VersiculoDB>>
}

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
        let iter = stmt.query_map([], |row| Ok((row.get::<_, i32>(0)?, row.get::<_, String>(1)?))).unwrap();
        for item in iter.filter_map(Result::ok) {
            let (id, nombre_bd) = item;
            let (sigla, nombre_comp, prioridad) = match nombre_bd.as_str() {
                "ReinaValera1960" => ("RVR", "Reina Valera 1960", 0),
                "NuevaVersiónInternacional" => ("NVI", "Nueva Versión Internacional", 1),
                "NuevaTraduccionViviente" => ("NTV", "Nueva Traducción Viviente", 2),
                "BibliaDeLasAméricas" => ("LBLA", "La Biblia de las Américas", 3),
                "NuevaBibliadelasAméricas" => ("NBLA", "Nueva Biblia de las Américas", 4),
                "TraduccionLenguajeActual" => ("TLA", "Traducción en Lenguaje Actual", 5),
                "DiosHablaHoy" => ("DHH", "Dios Habla Hoy", 6),
                "LaPalabra" => ("BLP", "La Palabra", 7),
                "TraduccionInterconfesionalVersionHispanoamericana" => ("TIVH", "Trad. Interconfesional Hispanoamericana", 8),
                "BibliaTextual" => ("BTX", "Biblia Textual", 9),
                "BibliaJubileo" => ("JUB", "Biblia del Jubileo", 10),
                "BibliadelOso1573" => ("OSO", "Biblia del Oso 1573", 11),
                _ => { let s = if nombre_bd.len() >= 4 { &nombre_bd[0..4] } else { &nombre_bd }; ("", s, 999) }
            };
            let sigla_final = if sigla.is_empty() { nombre_comp.to_uppercase() } else { sigla.to_string() };
            self.versiones.push(VersionInfo { id, sigla: sigla_final, nombre_completo: nombre_comp.to_string(), prioridad });
        }
        self.versiones.sort_by_key(|v| v.prioridad);
        if !self.versiones.is_empty() { self.current_version_id = self.versiones[0].id; }
    }

    fn set_version_by_name(&mut self, name: &str) -> String {
        if let Some(v) = self.versiones.iter().find(|v| v.nombre_completo == name) {
            self.current_version_id = v.id; return v.nombre_completo.clone();
        }
        String::new()
    }
    fn get_sigla_actual(&self) -> String {
        self.versiones.iter().find(|v| v.id == self.current_version_id).map(|v| v.sigla.clone()).unwrap_or_default()
    }
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
    fn get_canto_titulo(&self, id: i32) -> String {
        self.cantos_db.query_row("SELECT titulo FROM cantos WHERE id = ?", [id], |row| row.get(0)).unwrap_or_default()
    }
    fn get_canto_diapositivas(&self, id: i32) -> Vec<DiapositivaDB> {
        let mut stmt = self.cantos_db.prepare("SELECT orden, texto FROM diapositivas WHERE canto_id = ? ORDER BY orden").unwrap();
        let iter = stmt.query_map([id], |row| Ok(DiapositivaDB { orden: row.get(0)?, texto: row.get(1)? })).unwrap();
        iter.filter_map(Result::ok).collect()
    }
    fn insert_diapositivas_intern(&self, canto_id: i32, letra: &str) {
        let mut orden = 1;
        for estrofa in letra.split("\n\n") {
            let texto = trim(estrofa);
            if !texto.is_empty() {
                self.cantos_db.execute("INSERT INTO diapositivas (canto_id, orden, texto) VALUES (?, ?, ?)", rusqlite::params![canto_id, orden, texto]).unwrap();
                orden += 1;
            }
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

fn mover_proyector_a_pantalla(p_weak: slint::Weak<ProjectorWindow>, x: i32, y: i32, width: u32, height: u32) {
    // Delays diferentes por OS:
    // Windows: el DWM procesa rápido, ~80ms es suficiente
    // Linux X11: el WM necesita más tiempo, usamos intentos múltiples
    // IMPORTANTE: En Linux, forzar X11 con: WAYLAND_DISPLAY="" cargo run
    //             o agregar al inicio de main: std::env::set_var("WAYLAND_DISPLAY", "");

    let intentos: &[(u64, bool)] = if cfg!(target_os = "windows") {
        // Windows: 3 intentos con delays cortos
        &[(80, false), (200, false), (400, true)]
    } else {
        // Linux X11: más intentos con delays más largos
        &[(150, false), (350, false), (600, false), (900, true)]
    };

    for &(delay_ms, es_ultimo) in intentos {
        let p_clone = p_weak.clone();
        thread::spawn(move || {
            thread::sleep(std::time::Duration::from_millis(delay_ms));
            let _ = slint::invoke_from_event_loop(move || {
                if let Some(p) = p_clone.upgrade() {
                    p.window().set_position(slint::PhysicalPosition::new(x, y));
                    p.window().set_size(slint::PhysicalSize::new(width, height));
                    if es_ultimo {
                        // Solo maximizar en el último intento, cuando ya está en posición
                        p.window().set_maximized(true);
                    }
                }
            });
        });
    }
}

fn calcular_font_size(texto: &str, tiene_referencia: bool) -> f32 {
    let ancho_util: f32 = 1280.0 - 120.0; // 1160px (60px padding cada lado)
    
    // Reservar espacio según si hay referencia o no
    let alto_util: f32 = if tiene_referencia {
        720.0 - 180.0  // 540px: deja 180px para referencia + padding
    } else {
        720.0 - 120.0  // 600px: solo padding superior e inferior
    };

    // Factor de ancho por carácter para Inter Bold en español
    // Más alto que el promedio inglés por las letras acentuadas (á, é, etc.)
    let char_width_factor: f32 = 0.58;
    let line_height_factor: f32 = 1.40; // interlineado real de Slint

    let estimar_lineas = |font_size: f32| -> f32 {
        let chars_por_linea = (ancho_util / (font_size * char_width_factor))
            .floor()
            .max(1.0);
        
        let mut total_lineas = 0.0f32;
        for linea in texto.lines() {
            let chars = linea.chars().count() as f32;
            if chars == 0.0 {
                total_lineas += 0.5; // línea vacía = medio espacio
            } else {
                total_lineas += (chars / chars_por_linea).ceil();
            }
        }
        total_lineas.max(1.0)
    };

    // Búsqueda binaria del tamaño máximo que cabe
    let mut min_size: f32 = 20.0;
    let mut max_size: f32 = 160.0;

    for _ in 0..25 {
        let mid = (min_size + max_size) / 2.0;
        let lineas = estimar_lineas(mid);
        let alto_necesario = lineas * mid * line_height_factor;

        if alto_necesario <= alto_util {
            min_size = mid;
        } else {
            max_size = mid;
        }
    }

    // Factor de seguridad: 90% del máximo teórico para evitar desbordamientos
    // por diferencias entre la estimación y el render real de Slint
    let resultado = min_size * 0.90;

    resultado.clamp(26.0, 150.0)
}


fn main() -> Result<(), Box<dyn std::error::Error>> {
    // ═══════════════════════════════════════════════════════
    // FORZAR X11 EN LINUX (Wayland no permite set_position)
    // Esto no afecta Windows en absoluto
    // ═══════════════════════════════════════════════════════
    #[cfg(target_os = "linux")]
    {
        // Si está corriendo bajo Wayland, forzar compatibilidad XWayland
        // para poder posicionar ventanas en monitores específicos
        if std::env::var("WAYLAND_DISPLAY").is_ok() {
            println!("Detectado Wayland, forzando modo X11/XWayland para posicionamiento de ventanas...");
            std::env::set_var("WAYLAND_DISPLAY", "");
            std::env::set_var("GDK_BACKEND", "x11");
        }
    }

    let state = Arc::new(Mutex::new(AppState::new()?));
    let ui = AppWindow::new()?;
    let proyector = ProjectorWindow::new()?;

    let current_biblia_libro = Arc::new(Mutex::new(-1i32));
    let current_biblia_capitulo = Arc::new(Mutex::new(-1i32));

    // ═══════════════════════════════════════════════════════
    // DETECCIÓN DE SEGUNDA PANTALLA
    // display-info funciona en Windows y Linux
    // ═══════════════════════════════════════════════════════
    let segunda_pantalla: Arc<Mutex<Option<(i32, i32, u32, u32)>>> = Arc::new(Mutex::new(None));
    {
        match DisplayInfo::all() {
            Ok(pantallas) => {
                let pantallas: Vec<DisplayInfo> = pantallas;
                println!("=== Pantallas detectadas: {} ===", pantallas.len());
                for (i, p) in pantallas.iter().enumerate() {
                    println!("  [{}] {}x{} en ({},{}) scale={} primary={}", 
                        i, p.width, p.height, p.x, p.y, p.scale_factor, p.is_primary);
                }

                // ── DETECCIÓN ROBUSTA ──────────────────────────────────────
                // Bug conocido de display-info en Linux: a veces todas las
                // pantallas tienen is_primary=false. 
                // Solución: si ninguna está marcada como primaria,
                // asumir que la pantalla en (0,0) es la principal
                // y tomar cualquier otra como secundaria.
                // ──────────────────────────────────────────────────────────
                let hay_primaria_marcada = pantallas.iter().any(|d| d.is_primary);

                let segunda = if hay_primaria_marcada {
                    // Caso normal: hay una marcada como primaria
                    pantallas.iter().find(|d| !d.is_primary)
                } else {
                    // Ninguna marcada (bug de display-info en Linux/Wayland)
                    // La pantalla principal siempre está en coordenadas (0,0)
                    println!("  ⚠ Ninguna pantalla marcada como primaria");
                    println!("    → Usando heurística: la pantalla principal es la de (0,0)");
                    pantallas.iter().find(|d| !(d.x == 0 && d.y == 0))
                };

                if let Some(segunda) = segunda {
                    println!("  → Pantalla secundaria: {}x{} en ({},{})", 
                        segunda.width, segunda.height, segunda.x, segunda.y);
                    let w = (segunda.width as f32 * segunda.scale_factor) as u32;
                    let h = (segunda.height as f32 * segunda.scale_factor) as u32;
                    *segunda_pantalla.lock().unwrap() = Some((segunda.x, segunda.y, w, h));
                } else {
                    println!("  → Solo hay una pantalla disponible");
                }
            }
            Err(e) => println!("No se pudieron detectar pantallas: {}", e),
        }
    }

    {
        let st = state.lock().unwrap();
        let versiones_slint: Vec<SharedString> = st.versiones.iter().map(|v| SharedString::from(&v.nombre_completo)).collect();
        ui.set_bible_versions(ModelRc::from(Rc::new(VecModel::from(versiones_slint))));
        if let Some(primera) = st.versiones.first() { ui.set_current_bible_version(SharedString::from(&primera.nombre_completo)); }
        let libros = st.get_libros_biblia();
        let libros_slint: Vec<BookInfo> = libros.into_iter().map(|l| BookInfo { id: l.id, nombre: SharedString::from(l.nombre), capitulos: l.capitulos }).collect();
        ui.set_bible_books(ModelRc::from(Rc::new(VecModel::from(libros_slint))));
    }

    let ui_handle = ui.as_weak();
    let state_clone = Arc::clone(&state);
    let cargar_cantos = move |busqueda: String| {
        let ui = ui_handle.unwrap();
        let estado = state_clone.lock().unwrap();
        let cantos_db = if busqueda.is_empty() { estado.get_all_cantos() } else { estado.get_cantos_filtrados(&busqueda) };
        let mut cantos_slint: Vec<Canto> = cantos_db.into_iter().map(|c| Canto { id: c.id, titulo: SharedString::from(c.titulo), letra: SharedString::from("") }).collect();
        if cantos_slint.is_empty() {
            cantos_slint.push(Canto { id: 0, titulo: SharedString::from("Click derecho para agregar canto"), letra: SharedString::from("") });
        }
        ui.set_cantos(ModelRc::from(Rc::new(VecModel::from(cantos_slint))));
    };
    cargar_cantos(String::new());

    let c_clone = cargar_cantos.clone();
    ui.on_buscar_cantos(move |t| c_clone(t.to_string()));

    let ui_handle = ui.as_weak();
    let state_clone = Arc::clone(&state);
    let cb_lib = Arc::clone(&current_biblia_libro);
    let cb_cap = Arc::clone(&current_biblia_capitulo);
    ui.on_seleccionar_canto(move |id| {
        if id == 0 { return; }
        *cb_lib.lock().unwrap() = -1;
        *cb_cap.lock().unwrap() = -1;
        let ui = ui_handle.unwrap();
        let estado = state_clone.lock().unwrap();
        ui.set_elemento_seleccionado(SharedString::from(estado.get_canto_titulo(id)));
        let diapos_slint: Vec<DiapositivaUI> = estado.get_canto_diapositivas(id).into_iter()
            .map(|d| DiapositivaUI { orden: SharedString::from(d.orden.to_string()), texto: SharedString::from(d.texto) }).collect();
        ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos_slint))));
        ui.set_active_estrofa_index(-1);
        ui.invoke_focus_panel();
    });


    //-------------------------------------------------

    let state_clone = Arc::clone(&state);
    let state_clone2 = Arc::clone(&state);  // segundo clone para el refresh
    let c_clone = cargar_cantos.clone();
    let ui_handle_guardar = ui.as_weak();
    let proyector_handle_guardar = proyector.as_weak();


    ui.on_guardar_canto(move |id, titulo, letra| {
        // 1. Guardar en BD
        {
            let estado = state_clone.lock().unwrap();
            if id == -1 {
                estado.add_canto(&titulo, &letra);
            } else {
                estado.update_canto(id, &titulo, &letra);
            }
        }

        // 2. Recargar lista sidebar
        c_clone(String::new());

        // 3. Si era una edición (id != -1), refrescar panel central y proyector
        if id != -1 {
            let ui = ui_handle_guardar.unwrap();
            let p = proyector_handle_guardar.unwrap();
            let estado = state_clone2.lock().unwrap();

            let titulo_guardado = estado.get_canto_titulo(id);
            let titulo_en_panel = ui.get_elemento_seleccionado().to_string();

            // Solo refrescar si este canto es el que está activo en el panel
            // Comparamos con el título viejo (titulo param) y el nuevo (titulo_guardado)
            let es_canto_activo = titulo_en_panel == titulo.to_string() 
                || titulo_en_panel == titulo_guardado;

            if es_canto_activo {
                // Recargar diapositivas frescas de la BD
                let nuevas_diapos = estado.get_canto_diapositivas(id);
                let diapos_slint: Vec<DiapositivaUI> = nuevas_diapos.iter()
                    .map(|d| DiapositivaUI {
                        orden: SharedString::from(d.orden.to_string()),
                        texto: SharedString::from(d.texto.clone()),
                    })
                    .collect();

                // Guardar índice activo antes de actualizar
                let active_idx = ui.get_active_estrofa_index();

                // Actualizar título y estrofas en el panel central
                ui.set_elemento_seleccionado(SharedString::from(&titulo_guardado));
                ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos_slint.clone()))));

                // Actualizar proyector con la estrofa activa (o la primera si no hay)
                let idx_a_proyectar = if active_idx >= 0 && (active_idx as usize) < diapos_slint.len() {
                    active_idx as usize
                } else if !diapos_slint.is_empty() {
                    ui.set_active_estrofa_index(0);
                    0
                } else {
                    return;
                };

                let texto_nuevo = diapos_slint[idx_a_proyectar].texto.clone();
                let len = texto_nuevo.len();
                let font_size = if len >= 450 { 32.0 } 
                    else if len >= 320 { 38.0 } 
                    else if len >= 220 { 46.0 } 
                    else if len >= 120 { 56.0 } 
                    else if len >= 60  { 68.0 } 
                    else { 85.0 };

                p.set_texto_proyeccion(texto_nuevo);
                p.set_tamano_letra(font_size);
                p.set_referencia(SharedString::from(""));
            }
        }
    });


    let state_clone = Arc::clone(&state);
    let c_clone = cargar_cantos.clone();
    ui.on_eliminar_canto(move |id| {
        state_clone.lock().unwrap().delete_canto(id);
        c_clone(String::new());
    });

    let ui_handle = ui.as_weak();
    ui.on_abrir_formulario_nuevo(move || {
        let ui = ui_handle.unwrap();
        ui.set_form_id(-1);
        ui.set_form_titulo(SharedString::from(""));
        ui.set_form_letra(SharedString::from(""));
        ui.set_mostrar_formulario(true);
    });

    let ui_handle = ui.as_weak();
    let state_clone = Arc::clone(&state);
    ui.on_abrir_formulario_editar(move |id, _titulo| {
        let ui = ui_handle.unwrap();
        let estado = state_clone.lock().unwrap();
        let diapos = estado.get_canto_diapositivas(id);
        let letra_completa = diapos.iter().map(|d| d.texto.clone()).collect::<Vec<_>>().join("\n\n");
        ui.set_form_id(id);
        ui.set_form_titulo(SharedString::from(estado.get_canto_titulo(id)));
        ui.set_form_letra(SharedString::from(letra_completa));
        ui.set_mostrar_formulario(true);
    });

    let ui_handle = ui.as_weak();
    ui.on_confirmar_eliminar_canto(move |id, titulo| {
        let ui = ui_handle.unwrap();
        ui.set_menu_canto_id(id);
        ui.set_menu_canto_titulo(titulo);
        ui.set_mostrar_confirmar_eliminar(true);
    });

    // ═══════════════════════════════════════════════════════
    // ABRIR PROYECTOR → SEGUNDA PANTALLA (multi-OS)
    // ═══════════════════════════════════════════════════════
    let proyector_handle = proyector.as_weak();
    let segunda_pantalla_clone = Arc::clone(&segunda_pantalla);
    ui.on_abrir_proyector(move || {
        let p = proyector_handle.unwrap();
        let info = *segunda_pantalla_clone.lock().unwrap();

        if let Some((x, y, width, height)) = info {
            p.show().unwrap();
            // Llamar función que maneja delays por OS
            mover_proyector_a_pantalla(p.as_weak(), x, y, width, height);
            println!("Proyector → segunda pantalla {}x{} @ ({},{})", width, height, x, y);
        } else {
            p.show().unwrap();
            let p_weak = p.as_weak();
            thread::spawn(move || {
                thread::sleep(std::time::Duration::from_millis(100));
                let _ = slint::invoke_from_event_loop(move || {
                    if let Some(p) = p_weak.upgrade() { p.window().set_maximized(true); }
                });
            });
            println!("Proyector → pantalla principal (única pantalla)");
        }
    });

    let proyector_handle = proyector.as_weak();
    let state_clone = Arc::clone(&state);
    ui.on_proyectar_estrofa(move |texto, referencia| {
        let p = proyector_handle.unwrap();
        p.set_texto_proyeccion(texto.clone());

        let mut ref_str = referencia.to_string();
        if !ref_str.is_empty() {
            let sigla = state_clone.lock().unwrap().get_sigla_actual();
            if !sigla.is_empty() {
                ref_str = format!("{}  |  {}", ref_str, sigla);
            }
        }
        p.set_referencia(SharedString::from(ref_str.clone()));

        // Pasar si hay referencia para reservar espacio en el cálculo
        let tiene_referencia = !ref_str.is_empty();
        let font_size = calcular_font_size(&texto, tiene_referencia);
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
        let ui = ui_h.unwrap();
        let mut filas = Vec::new();
        let mut fila_actual = Vec::new();
        for i in 1..=book.capitulos {
            fila_actual.push(i);
            if fila_actual.len() == 5 || i == book.capitulos {
                filas.push(ChapterRow { caps: ModelRc::from(Rc::new(VecModel::from(fila_actual.clone()))) });
                fila_actual.clear();
            }
        }
        ui.set_chapter_rows(ModelRc::from(Rc::new(VecModel::from(filas))));
    });

    let ui_h = ui.as_weak();
    let state_clone = Arc::clone(&state);
    let cb_lib = Arc::clone(&current_biblia_libro);
    let cb_cap = Arc::clone(&current_biblia_capitulo);
    ui.on_bible_chapter_selected(move |cap| {
        let ui = ui_h.unwrap();
        let book = ui.get_selected_bible_book();
        *cb_lib.lock().unwrap() = book.id;
        *cb_cap.lock().unwrap() = cap;
        let titulo = format!("{} {}", book.nombre, cap);
        ui.set_elemento_seleccionado(SharedString::from(&titulo));
        let state_thread = Arc::clone(&state_clone);
        let ui_thread = ui.as_weak();
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

    let ui_h = ui.as_weak();
    let state_clone = Arc::clone(&state);
    let cb_lib = Arc::clone(&current_biblia_libro);
    let cb_cap = Arc::clone(&current_biblia_capitulo);
    ui.on_bible_search_accepted(move |query| {
        let ui = ui_h.unwrap();
        let q = query.to_string();
        let re = Regex::new(r"^\s*(.*?)\s+(\d+)(?:\s+(\d+))?\s*$").unwrap();
        if let Some(caps) = re.captures(&q) {
            let book_query = &caps[1];
            let capitulo: i32 = caps[2].parse().unwrap_or(1);
            let versiculo_obj: i32 = caps.get(3).map_or(1, |m| m.as_str().parse().unwrap_or(1));
            if let Some((libro_id, nombre_real)) = buscar_libro_inteligente(book_query) {
                *cb_lib.lock().unwrap() = libro_id;
                *cb_cap.lock().unwrap() = capitulo;
                let titulo = format!("{} {}", nombre_real, capitulo);
                ui.set_elemento_seleccionado(SharedString::from(&titulo));
                let state_thread = Arc::clone(&state_clone);
                let ui_thread = ui.as_weak();
                thread::spawn(move || {
                    let versiculos = state_thread.lock().unwrap().get_capitulo(libro_id, capitulo);
                    let _ = slint::invoke_from_event_loop(move || {
                        let ui = ui_thread.unwrap();
                        let mut target_index = 0;
                        let diapos: Vec<DiapositivaUI> = versiculos.into_iter().enumerate().map(|(i, v)| {
                            if v.versiculo == versiculo_obj { target_index = i as i32; }
                            DiapositivaUI { orden: SharedString::from(v.versiculo.to_string()), texto: SharedString::from(v.texto) }
                        }).collect();
                        ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
                        ui.set_active_estrofa_index(target_index);
                        ui.set_scroll_to_y(target_index as f32 * 115.0);
                        if (target_index as usize) < diapos.len() {
                            let text = diapos[target_index as usize].texto.clone();
                            let ord = diapos[target_index as usize].orden.clone();
                            ui.invoke_proyectar_estrofa(text, SharedString::from(format!("{}:{}", titulo, ord)));
                        }
                        ui.invoke_focus_panel();
                    });
                });
                ui.set_bible_search_suggestion(SharedString::from(""));
            }
        }
    });

    let ui_h = ui.as_weak();
    let state_clone = Arc::clone(&state);
    let cb_lib = Arc::clone(&current_biblia_libro);
    let cb_cap = Arc::clone(&current_biblia_capitulo);
    ui.on_bible_version_changed(move |version_name| {
        let ui = ui_h.unwrap();
        let lib = *cb_lib.lock().unwrap();
        let cap = *cb_cap.lock().unwrap();
        let mut versiculos_nuevos = Vec::new();
        {
            let mut estado = state_clone.lock().unwrap();
            estado.set_version_by_name(version_name.as_str());
            if lib != -1 && cap != -1 { versiculos_nuevos = estado.get_capitulo(lib, cap); }
        }
        if lib != -1 && cap != -1 && !versiculos_nuevos.is_empty() {
            let active_idx = ui.get_active_estrofa_index();
            let diapos: Vec<DiapositivaUI> = versiculos_nuevos.into_iter().map(|v| DiapositivaUI { orden: SharedString::from(v.versiculo.to_string()), texto: SharedString::from(v.texto) }).collect();
            ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
            if active_idx >= 0 && (active_idx as usize) < diapos.len() {
                let texto_nuevo = diapos[active_idx as usize].texto.clone();
                let orden = diapos[active_idx as usize].orden.clone();
                let book_name = ui.get_selected_bible_book().nombre;
                let titulo = format!("{} {}", book_name, cap);
                ui.invoke_proyectar_estrofa(texto_nuevo, SharedString::from(format!("{}:{}", titulo, orden)));
            }
        }
    });

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