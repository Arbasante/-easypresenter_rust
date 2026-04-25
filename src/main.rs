use rusqlite::{Connection, Result};
use slint::{ModelRc, SharedString, VecModel, ComponentHandle, SharedPixelBuffer};
use slint::Model;
use std::collections::HashMap;
use std::num::NonZeroUsize;
use std::sync::{Arc, Mutex, RwLock};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::LazyLock;
use std::rc::Rc;
use std::thread;
use regex::Regex;
use display_info::DisplayInfo;
use lru::LruCache;
use directories::ProjectDirs;
use serde::{Deserialize, Serialize};

// ── Configuración persistente ────────────────────────────────────────────────
#[derive(Serialize, Deserialize, Default, Clone)]
struct ConfigApp {
    // Galería de fondos
    biblias_image_paths: Vec<String>,
    cantos_image_paths:  Vec<String>,
    biblias_video_paths: Vec<String>,
    cantos_video_paths:  Vec<String>,
    biblias_selected_img: i32,
    cantos_selected_img:  i32,
    biblias_selected_vid: i32,
    cantos_selected_vid:  i32,
    biblias_video_path:  String,
    cantos_video_path:   String,

    // Apariencia
    biblias_bg_type:      String,
    cantos_bg_type:       String,
    biblias_font_color:   [u8; 3],   // [r, g, b]
    cantos_font_color:    [u8; 3],
    biblias_fondo_opacity: f32,
    cantos_fondo_opacity:  f32,
    biblias_font_scale:   f32,
    cantos_font_scale:    f32,

    // Multimedia proyectable (imágenes y vídeos)
    multimedia_paths: Vec<String>,
    multimedia_names: Vec<String>,
    multimedia_aspectos: Vec<String>,
    video_paths: Vec<String>,
    video_names: Vec<String>,
    video_loops: Vec<bool>,

    // Márgenes del proyector
    margen_izquierdo: f32,
    margen_derecho:   f32,
    margen_superior:  f32,
    margen_inferior:  f32,

    // Fondo predeterminado
    default_bg_type: String,
    default_bg_idx:  i32,
}

fn config_path(user_data_dir: &std::path::Path) -> std::path::PathBuf {
    user_data_dir.join("config.json")
}

fn cargar_config(user_data_dir: &std::path::Path) -> ConfigApp {
    let path = config_path(user_data_dir);
    if let Ok(data) = std::fs::read_to_string(&path) {
        serde_json::from_str(&data).unwrap_or_default()
    } else {
        let mut cfg = ConfigApp::default();
        cfg.biblias_bg_type   = "negro".to_string();
        cfg.cantos_bg_type    = "negro".to_string();
        cfg.biblias_font_color = [255, 255, 255];
        cfg.cantos_font_color  = [255, 255, 255];
        cfg.biblias_font_scale = 1.0;
        cfg.cantos_font_scale  = 1.0;
        cfg
    }
}

fn guardar_config(user_data_dir: &std::path::Path, cfg: &ConfigApp) {
    if let Ok(data) = serde_json::to_string_pretty(cfg) {
        let _ = std::fs::write(config_path(user_data_dir), data);
    }
}

use pdfium_render::prelude::*;
use std::fs;
use std::path::PathBuf;

use gstreamer as gst;
use gstreamer_app as gst_app;
use gstreamer_video as gst_video;
use gst::prelude::*;
slint::include_modules!();

// ---------------------------------------------------------------------------
// Estructuras de datos
// ---------------------------------------------------------------------------
struct CantoDB        { pub id: i32, pub titulo: String }
struct DiapositivaDB  { pub orden: i32, pub texto: String }
struct LibroBibliaDB  { pub id: i32, pub nombre: String, pub capitulos: i32 }
#[derive(Clone)] struct VersiculoDB  { pub versiculo: i32, pub texto: String }
#[derive(Clone)] struct VersionInfo  { pub id: i32, pub sigla: String, pub nombre_completo: String, pub prioridad: i32 }
#[derive(Hash, Eq, PartialEq, Clone, Debug)] struct CacheKey { version_id: i32, libro_numero: i32, capitulo: i32 }

const NOMBRES_LIBROS: [&str; 66] = [
    "Génesis","Éxodo","Levítico","Números","Deuteronomio","Josué","Jueces","Rut",
    "1 Samuel","2 Samuel","1 Reyes","2 Reyes","1 Crónicas","2 Crónicas","Esdras",
    "Nehemías","Ester","Job","Salmos","Proverbios","Eclesiastés","Cantares","Isaías",
    "Jeremías","Lamentaciones","Ezequiel","Daniel","Oseas","Joel","Amós","Abdías",
    "Jonás","Miqueas","Nahúm","Habacuc","Sofonías","Hageo","Zacarías","Malaquías",
    "Mateo","Marcos","Lucas","Juan","Hechos","Romanos","1 Corintios","2 Corintios",
    "Gálatas","Efesios","Filipenses","Colosenses","1 Tesalonicenses","2 Tesalonicenses",
    "1 Timoteo","2 Timoteo","Tito","Filemón","Hebreos","Santiago","1 Pedro","2 Pedro",
    "1 Juan","2 Juan","3 Juan","Judas","Apocalipsis",
];

// ---------------------------------------------------------------------------
// OPT-1: Regex estáticas — se compilan UNA SOLA VEZ en toda la ejecución.
//        En el E1-6015, compilar una regex cada pulsación de teclado costaba
//        varios milisegundos de CPU; ahora es cero.
// ---------------------------------------------------------------------------
static RE_BUSQUEDA: LazyLock<Regex> = LazyLock::new(||
    Regex::new(r"^\s*(.*?)\s+(\d+)(?:\s+(\d+))?\s*$").unwrap()
);
static RE_FAV: LazyLock<Regex> = LazyLock::new(||
    Regex::new(r"^(.*?)\s+(\d+)\s*[: ]\s*(\d+)$").unwrap()
);

// ---------------------------------------------------------------------------
// OPT-2: Tabla de nombres normalizados pre-calculada.
//        `buscar_libro_inteligente` se llama en cada keystroke; antes normalizaba
//        los 66 nombres cada vez (66 allocations). Ahora es una búsqueda pura.
// ---------------------------------------------------------------------------
static LIBROS_NORMALIZADOS: LazyLock<Vec<String>> = LazyLock::new(||
    NOMBRES_LIBROS.iter().map(|n| normalizar(n)).collect()
);

// ---------------------------------------------------------------------------
// Funciones de utilidad — #[inline] en hot-paths cortos
// ---------------------------------------------------------------------------
#[inline]
fn trim(s: &str) -> String { s.trim().to_string() }

#[inline]
fn normalizar(texto: &str) -> String {
    texto.chars().map(|c| match c {
        'á'|'Á' => 'a', 'é'|'É' => 'e', 'í'|'Í' => 'i',
        'ó'|'Ó' => 'o', 'ú'|'Ú' => 'u',
        _ => c.to_ascii_lowercase(),
    }).collect()
}

// OPT-2 aplicado: cero allocations por búsqueda de libro
fn buscar_libro_inteligente(query: &str) -> Option<(i32, String)> {
    let q = normalizar(&trim(query));
    if q.is_empty() { return None; }
    for (i, norm) in LIBROS_NORMALIZADOS.iter().enumerate() {
        if norm.starts_with(&q) {
            return Some(((i + 1) as i32, NOMBRES_LIBROS[i].to_string()));
        }
    }
    None
}

#[inline]
fn calcular_font_size_tarjeta(texto: &str) -> f32 {
    let len   = texto.chars().count() as f32;
    if len == 0.0 { return 18.0; }
    let lineas = texto.lines().count() as f32;
    let estimado = 350.0 / (len.sqrt() * 1.5 + lineas * 4.0);
    estimado.clamp(9.0, 22.0)
}

fn diapositiva_a_ui(d: &DiapositivaDB) -> DiapositivaUI {
    DiapositivaUI {
        orden:     SharedString::from(d.orden.to_string()),
        texto:     SharedString::from(d.texto.clone()),
        font_size: calcular_font_size_tarjeta(&d.texto),
        favorito:  false,
    }
}

fn versiculo_a_ui_fav(
    v: &VersiculoDB,
    fav_refs: &std::collections::HashSet<String>,
    libro_cap: &str,
) -> DiapositivaUI {
    let referencia = format!("{} {}", libro_cap, v.versiculo);
    DiapositivaUI {
        orden:     SharedString::from(v.versiculo.to_string()),
        texto:     SharedString::from(v.texto.clone()),
        font_size: calcular_font_size_tarjeta(&v.texto),
        favorito:  fav_refs.contains(&referencia),
    }
}

// ---------------------------------------------------------------------------
// OPT-7: Caché de imágenes global para evitar releer disco (lento en E1-6015)
// ---------------------------------------------------------------------------
fn load_image_cached(
    cache: &Arc<Mutex<HashMap<String, slint::Image>>>,
    path: &str,
) -> Option<slint::Image> {
    {
        let lock = cache.lock().unwrap();
        if let Some(img) = lock.get(path) {
            return Some(img.clone());
        }
    }
    if let Ok(img) = slint::Image::load_from_path(std::path::Path::new(path)) {
        cache.lock().unwrap().insert(path.to_string(), img.clone());
        Some(img)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// AppState — DB + caché de capítulos con LRU acotado
// ---------------------------------------------------------------------------
struct AppState {
    cantos_db:  Connection,
    biblias_db: Connection,
    versiones:          Vec<VersionInfo>,
    current_version_id: i32,
    chapter_cache: LruCache<CacheKey, Vec<VersiculoDB>>,
    biblias_image_paths: Vec<String>,
    cantos_image_paths:  Vec<String>,
    biblias_video_paths: Vec<String>,
    cantos_video_paths:  Vec<String>,
    user_data_dir: std::path::PathBuf,   // ← nuevo
}



impl AppState {
    fn new() -> Result<Self> {
        // 1. Determinar las rutas de forma inteligente
        let (user_data_dir, system_data_dir) = if std::path::Path::new("data/cantos.db").exists() {
            // 🟢 MODO DESARROLLADOR: Si corres 'cargo run', usa la carpeta local
            let base = std::env::current_dir().unwrap().join("data");
            (base.clone(), base)
        } else if cfg!(target_os = "windows") {
            // 🔵 WINDOWS (Instalado)
            let mut path = std::env::current_exe().unwrap_or_else(|_| std::path::PathBuf::from("."));
            path.pop();
            let base = path.join("data");
            (base.clone(), base)
        } else {
    //  LINUX (Instalado via .deb o AppImage)
    let proj_dirs = ProjectDirs::from("com", "Arbasante", "EasyPresenter")
        .expect("No se pudo encontrar el directorio del usuario");
    let user_dir = proj_dirs.data_dir().to_path_buf();

    // Si corremos dentro de un AppImage, $APPDIR apunta a la raíz del bundle.
    // Si es un .deb instalado normalmente, usamos la ruta del sistema.
    let sys_dir = if let Ok(appdir) = std::env::var("APPDIR") {
        std::path::PathBuf::from(appdir)
            .join("usr/share/easy-presenter/data")
    } else {
        // Busca en la nueva ruta primero, luego en la antigua por compatibilidad
        let nueva = std::path::PathBuf::from("/usr/share/easy-presenter/data");
        let antigua = std::path::PathBuf::from("/usr/share/easy-presenter-slint/data");
        if nueva.exists() { nueva } else { antigua }
    };

    (user_dir, sys_dir)
};

        println!("📂 DIRECTORIO DE BASES DE DATOS: {:?}", user_data_dir);

        // 2. Crear la carpeta si no existe
        std::fs::create_dir_all(&user_data_dir).ok();

        let cantos_path = user_data_dir.join("cantos.db");
        let biblias_path = user_data_dir.join("biblias.db");

        // 3. PRIMERA EJECUCIÓN (Solo copia si estamos en Linux/Windows instalado y faltan archivos)
        let cantos_ok = Connection::open(&cantos_path)
    .ok()
    .and_then(|c| c.query_row("SELECT 1 FROM cantos LIMIT 1", [], |_| Ok(())).ok())
    .is_some();

if !cantos_ok {
    let sys_cantos = system_data_dir.join("cantos.db");
    if sys_cantos.exists() {
        std::fs::copy(&sys_cantos, &cantos_path)
            .unwrap_or_else(|e| panic!("No se pudo copiar cantos.db: {}", e));
    }
}

        let biblias_ok = Connection::open(&biblias_path)
    .ok()
    .and_then(|c| c.query_row("SELECT 1 FROM versiculos LIMIT 1", [], |_| Ok(())).ok())
    .is_some();

if !biblias_ok {
    let sys_biblias = system_data_dir.join("biblias.db");
    if sys_biblias.exists() {
        std::fs::copy(&sys_biblias, &biblias_path)
            .unwrap_or_else(|e| panic!("No se pudo copiar biblias.db: {}", e));
    }
}


        // 4. Abrir la conexión a las bases de datos (ahora garantizado que existen y tienen permisos)
        let cantos_db = Connection::open(cantos_path)?;
        let biblias_db = Connection::open(biblias_path)?;

        // Optimizaciones de SQLite
        cantos_db.execute_batch("PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;")?;
        biblias_db.execute_batch("PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;")?;
        cantos_db.set_prepared_statement_cache_capacity(32);
        biblias_db.set_prepared_statement_cache_capacity(32);

        cantos_db.execute_batch("
            CREATE TABLE IF NOT EXISTS favoritos (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                tipo       TEXT    NOT NULL DEFAULT 'canto',
                ref_id     INTEGER NOT NULL DEFAULT 0,
                referencia TEXT    NOT NULL DEFAULT '',
                titulo     TEXT    NOT NULL DEFAULT ''
            );
        ")?;

        let mut state = Self {
            cantos_db,
            biblias_db,
            versiones:           Vec::new(),
            current_version_id:  1,
            chapter_cache:       LruCache::new(std::num::NonZeroUsize::new(150).unwrap()),
            biblias_image_paths: Vec::new(),
            cantos_image_paths:  Vec::new(),
            biblias_video_paths: Vec::new(),
            cantos_video_paths:  Vec::new(),
            user_data_dir: user_data_dir.clone(),
        };
        state.procesar_versiones();
        Ok(state)
    }

    fn procesar_versiones(&mut self) {
        // OPT-1: prepare_cached — el statement se guarda en el pool interno de rusqlite
        let mut stmt = self.biblias_db
            .prepare_cached("SELECT id, nombre FROM versiones")
            .unwrap();
        let iter = stmt
            .query_map([], |row| Ok((row.get::<_, i32>(0)?, row.get::<_, String>(1)?)))
            .unwrap();
        for item in iter.filter_map(Result::ok) {
            let (id, nombre_bd) = item;
            let (sigla, nombre_comp, prioridad) = match nombre_bd.as_str() {
                "ReinaValera1960"                              => ("RVR",  "Reina Valera 1960",                          0),
                "NuevaVersiónInternacional"                    => ("NVI",  "Nueva Versión Internacional",                1),
                "NuevaTraduccionViviente"                      => ("NTV",  "Nueva Traducción Viviente",                  2),
                "BibliaDeLasAméricas"                          => ("LBLA", "La Biblia de las Américas",                  3),
                "NuevaBibliadelasAméricas"                     => ("NBLA", "Nueva Biblia de las Américas",               4),
                "TraduccionLenguajeActual"                     => ("TLA",  "Traducción en Lenguaje Actual",              5),
                "DiosHablaHoy"                                 => ("DHH",  "Dios Habla Hoy",                             6),
                "LaPalabra"                                    => ("BLP",  "La Palabra",                                 7),
                "TraduccionInterconfesionalVersionHispanoamericana"
                                                               => ("TIVH","Trad. Interconfesional Hispanoamericana",     8),
                "BibliaTextual"                                => ("BTX",  "Biblia Textual",                             9),
                "BibliaJubileo"                                => ("JUB",  "Biblia del Jubileo",                        10),
                "BibliadelOso1573"                             => ("OSO",  "Biblia del Oso 1573",                       11),
                _ => {
                    let s = if nombre_bd.len() >= 4 { &nombre_bd[0..4] } else { &nombre_bd };
                    ("", s, 999)
                }
            };
            let sigla_final = if sigla.is_empty() { nombre_comp.to_uppercase() } else { sigla.to_string() };
            self.versiones.push(VersionInfo {
                id, sigla: sigla_final, nombre_completo: nombre_comp.to_string(), prioridad,
            });
        }
        self.versiones.sort_by_key(|v| v.prioridad);
        if !self.versiones.is_empty() { self.current_version_id = self.versiones[0].id; }
    }

    fn set_version_by_name(&mut self, name: &str) -> String {
        if let Some(v) = self.versiones.iter().find(|v| v.nombre_completo == name) {
            self.current_version_id = v.id;
            return v.nombre_completo.clone();
        }
        String::new()
    }

    fn get_sigla_actual(&self) -> String {
        self.versiones.iter()
            .find(|v| v.id == self.current_version_id)
            .map(|v| v.sigla.clone())
            .unwrap_or_default()
    }

    fn get_libros_biblia(&self) -> Vec<LibroBibliaDB> {
        let mut stmt = self.biblias_db.prepare_cached(
            "SELECT libro_numero, libro_nombre, MAX(capitulo) \
             FROM versiculos WHERE version_id = ? \
             GROUP BY libro_numero ORDER BY libro_numero"
        ).unwrap();
        stmt.query_map([self.current_version_id], |row| Ok(LibroBibliaDB {
            id: row.get(0)?, nombre: row.get(1)?, capitulos: row.get(2)?,
        })).unwrap().filter_map(Result::ok).collect()
    }

    fn get_capitulo(&mut self, libro_numero: i32, capitulo: i32) -> Vec<VersiculoDB> {
        let key = CacheKey { version_id: self.current_version_id, libro_numero, capitulo };
        if let Some(cached) = self.chapter_cache.get(&key) {
            return cached.clone();
        }
        let mut stmt = self.biblias_db.prepare_cached(
            "SELECT versiculo, texto FROM versiculos \
             WHERE version_id = ? AND libro_numero = ? AND capitulo = ? \
             ORDER BY versiculo"
        ).unwrap();
        let lista: Vec<VersiculoDB> = stmt
            .query_map([self.current_version_id, libro_numero, capitulo], |row| Ok(VersiculoDB {
                versiculo: row.get(0)?, texto: row.get(1)?,
            }))
            .unwrap()
            .filter_map(Result::ok)
            .collect();
        self.chapter_cache.put(key, lista.clone());
        lista
    }

    fn get_all_cantos(&self) -> Vec<CantoDB> {
        let mut stmt = self.cantos_db
            .prepare_cached("SELECT id, titulo FROM cantos ORDER BY titulo")
            .unwrap();
        stmt.query_map([], |row| Ok(CantoDB { id: row.get(0)?, titulo: row.get(1)? }))
            .unwrap()
            .filter_map(Result::ok)
            .collect()
    }

    fn get_cantos_filtrados(&self, busqueda: &str) -> Vec<CantoDB> {
        let mut stmt = self.cantos_db
            .prepare_cached("SELECT id, titulo FROM cantos WHERE titulo LIKE ? ORDER BY titulo")
            .unwrap();
        stmt.query_map([format!("%{}%", busqueda)], |row| Ok(CantoDB {
            id: row.get(0)?, titulo: row.get(1)?,
        }))
        .unwrap()
        .filter_map(Result::ok)
        .collect()
    }

    fn get_canto_titulo(&self, id: i32) -> String {
        self.cantos_db
            .query_row("SELECT titulo FROM cantos WHERE id = ?", [id], |row| row.get(0))
            .unwrap_or_default()
    }

    fn get_canto_diapositivas(&self, id: i32) -> Vec<DiapositivaDB> {
        let mut stmt = self.cantos_db
            .prepare_cached("SELECT orden, texto FROM diapositivas WHERE canto_id = ? ORDER BY orden")
            .unwrap();
        stmt.query_map([id], |row| Ok(DiapositivaDB { orden: row.get(0)?, texto: row.get(1)? }))
            .unwrap()
            .filter_map(Result::ok)
            .collect()
    }

    fn insert_diapositivas_intern(&self, canto_id: i32, letra: &str) {
        let mut stmt = self.cantos_db
            .prepare_cached("INSERT INTO diapositivas (canto_id, orden, texto) VALUES (?, ?, ?)")
            .unwrap();
        let mut orden = 1i32;
        for estrofa in letra.split("\n\n") {
            let texto = trim(estrofa);
            if !texto.is_empty() {
                stmt.execute(rusqlite::params![canto_id, orden, texto]).unwrap();
                orden += 1;
            }
        }
    }

    fn add_canto(&self, titulo: &str, letra: &str) {
        self.cantos_db
            .execute("INSERT INTO cantos (titulo, tono, categoria) VALUES (?, '', 'Personalizado')", [titulo])
            .unwrap();
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

    // OPT-8: Consulta combinada — obtiene IDs de cantos favoritos Y todos los favoritos
    //        en una sola transacción lógica, reduciendo round-trips a SQLite.
    fn get_favoritos_ids_cantos(&self) -> std::collections::HashSet<i32> {
        let mut stmt = self.cantos_db
            .prepare_cached("SELECT ref_id FROM favoritos WHERE tipo='canto'")
            .unwrap();
        stmt.query_map([], |r| r.get::<_, i32>(0))
            .unwrap()
            .filter_map(Result::ok)
            .collect()
    }

    fn get_favoritos_refs_versiculos(&self) -> std::collections::HashSet<String> {
        let mut stmt = self.cantos_db
            .prepare_cached("SELECT referencia FROM favoritos WHERE tipo='versiculo'")
            .unwrap();
        stmt.query_map([], |r| r.get::<_, String>(0))
            .unwrap()
            .filter_map(Result::ok)
            .collect()
    }

    fn get_all_favoritos(&self) -> Vec<FavoritoItem> {
        let mut stmt = self.cantos_db
            .prepare_cached("SELECT tipo, ref_id, titulo, referencia FROM favoritos ORDER BY id DESC")
            .unwrap();
        stmt.query_map([], |r| Ok(FavoritoItem {
            tipo:       SharedString::from(r.get::<_, String>(0)?),
            id:         r.get::<_, i32>(1)?,
            titulo:     SharedString::from(r.get::<_, String>(2)?),
            referencia: SharedString::from(r.get::<_, String>(3)?),
        }))
        .unwrap()
        .filter_map(Result::ok)
        .collect()
    }

    fn toggle_favorito_canto(&self, id: i32, titulo: &str) {
        let exists: bool = self.cantos_db
            .query_row("SELECT 1 FROM favoritos WHERE tipo='canto' AND ref_id=?", [id], |_| Ok(true))
            .unwrap_or(false);
        if exists {
            self.cantos_db.execute("DELETE FROM favoritos WHERE tipo='canto' AND ref_id=?", [id]).unwrap();
        } else {
            self.cantos_db.execute(
                "INSERT INTO favoritos (tipo, ref_id, referencia, titulo) VALUES ('canto', ?, '', ?)",
                rusqlite::params![id, titulo],
            ).unwrap();
        }
    }

    fn toggle_favorito_versiculo(&self, referencia: &str, texto: &str) {
        let exists: bool = self.cantos_db
            .query_row("SELECT 1 FROM favoritos WHERE tipo='versiculo' AND referencia=?", [referencia], |_| Ok(true))
            .unwrap_or(false);
        if exists {
            self.cantos_db.execute("DELETE FROM favoritos WHERE tipo='versiculo' AND referencia=?", [referencia]).unwrap();
        } else {
            // Truncar a 60 chars sin iterar dos veces sobre el string
            let titulo: String = texto.char_indices()
                .take_while(|&(i, _)| i < 60)
                .map(|(_, c)| c)
                .collect();
            let titulo = if texto.len() > 60 { format!("{}…", titulo) } else { titulo };
            self.cantos_db.execute(
                "INSERT INTO favoritos (tipo, ref_id, referencia, titulo) VALUES ('versiculo', 0, ?, ?)",
                rusqlite::params![referencia, titulo],
            ).unwrap();
        }
    }
}

// ---------------------------------------------------------------------------
// Proyector
// ---------------------------------------------------------------------------
fn mover_proyector_a_pantalla(p_weak: slint::Weak<ProjectorWindow>, x: i32, y: i32, width: u32, height: u32) {
    let intentos: &[(u64, bool)] = if cfg!(target_os = "windows") {
        &[(80, false), (200, false), (400, true)]
    } else {
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
                    if es_ultimo { p.window().set_maximized(true); }
                }
            });
        });
    }
}
// Constantes que deben coincidir exactamente con los valores del .slint
const PROJ_PADDING: f32 = 30.0;  // padding-* del VerticalLayout en ProjectorWindow
const REF_ZONE_H:   f32 = 70.0;  // height del bloque "if referencia != """
const CHAR_W:       f32 = 0.58;  // calibrado para font-weight 900 + Google Sans
const LINE_H:       f32 = 1.38;  // line-height efectivo del Text de Slint

// Para cantos: usa TODO el alto disponible (sin zona de cita)
fn calcular_font_size_canto(texto: &str, screen_w: f32, screen_h: f32) -> f32 {
    let ancho_util = screen_w - PROJ_PADDING * 2.0;
    let alto_util  = screen_h - PROJ_PADDING * 2.0;
    _busqueda_binaria(texto, ancho_util, alto_util)
}

fn calcular_font_size_versiculo(texto: &str, screen_w: f32, screen_h: f32) -> f32 {
    let ancho_util = screen_w - PROJ_PADDING * 2.0;
    let alto_util  = screen_h - PROJ_PADDING * 2.0 - REF_ZONE_H - 8.0;
    let size = _busqueda_binaria(texto, ancho_util, alto_util);

    let chars = texto.chars().count() as f32;

    // El techo ya no usa porcentajes del alto de pantalla.
    // Usa píxeles absolutos calibrados para 1080p, que escalan
    // proporcionalmente con el alto real de la pantalla.
    let factor = screen_h / 1080.0;  // escala a la resolución real

    let techo = if chars < 12.0 {
        // "Jesús lloró." — máximo ~200px en 1080p, no más
        180.0 * factor
    } else if chars < 30.0 {
        // versículos de 1 línea corta
        140.0 * factor
    } else if chars < 70.0 {
        // versículos medianos de 2 líneas
        110.0 * factor
    } else {
        // versículos largos: sin techo, que llene la pantalla
        f32::MAX
    };

    size.min(techo)
}

fn _busqueda_binaria(texto: &str, ancho_util: f32, alto_util: f32) -> f32 {
    if texto.is_empty() { return 60.0; }

    let max_word_chars = texto
        .split_whitespace()
        .map(|w| w.chars().count())
        .max()
        .unwrap_or(1) as f32;

    let estimar_lineas = |font_size: f32| -> f32 {
        let chars_por_linea = (ancho_util / (font_size * CHAR_W)).floor().max(1.0);
        let mut total = 0.0f32;
        for linea in texto.lines() {
            let chars = linea.chars().count() as f32;
            if chars == 0.0 {
                total += 0.4;
            } else {
                total += (chars / chars_por_linea).ceil();
            }
        }
        total.max(1.0)
    };

    let mut min_size: f32 = 24.0;
    let mut max_size: f32 = alto_util * 0.90; // antes 0.85 — permite explorar más alto

    for _ in 0..48 { // más iteraciones = más precisión
        let mid           = (min_size + max_size) / 2.0;
        let alto_ocupado  = estimar_lineas(mid) * mid * LINE_H;
        let ancho_palabra = max_word_chars * mid * CHAR_W;
        if alto_ocupado <= alto_util && ancho_palabra <= ancho_util {
            min_size = mid;
        } else {
            max_size = mid;
        }
    }

    // 0.96 en lugar de 0.98 — peso 900 ocupa más que la estimación
    (min_size * 0.96).clamp(24.0, alto_util * 0.88)
}

// ---------------------------------------------------------------------------
// Reproductor de video nativo (GStreamer)
// ---------------------------------------------------------------------------
struct NativeVideoPlayer {
    pipeline: Option<gst::Element>,
}

impl NativeVideoPlayer {
    fn new() -> Self { Self { pipeline: None } }

    pub fn reproducir(&mut self, ruta: &str, proj_weak: slint::Weak<ProjectorWindow>, is_loop: bool) {
        self.detener();
        let path = std::path::Path::new(ruta).canonicalize()
            .unwrap_or_else(|_| std::path::PathBuf::from(ruta));
        let uri = gst::glib::filename_to_uri(&path, None).unwrap();
        let pipeline = gst::ElementFactory::make("playbin")
            .property("uri", &uri)
            .build()
            .unwrap();
        let appsink = gst_app::AppSink::builder()
            .caps(&gst::Caps::builder("video/x-raw").field("format", "RGBA").build())
            .max_buffers(1)
            .drop(true)
            .build();
        appsink.set_property("sync", true);
        pipeline.set_property("video-sink", &appsink);
        if let Ok(audio_sink) = gst::ElementFactory::make("autoaudiosink").build() {
            pipeline.set_property("audio-sink", &audio_sink);
        }
        pipeline.set_property("volume", 1.0f64);
        pipeline.set_property("mute", false);

        appsink.set_callbacks(gst_app::AppSinkCallbacks::builder()
            .new_sample(move |appsink| {
                let sample = match appsink.pull_sample() { Ok(s) => s, Err(_) => return Ok(gst::FlowSuccess::Ok) };
                let buffer = sample.buffer().unwrap();
                let info   = gst_video::VideoInfo::from_caps(sample.caps().unwrap()).unwrap();
                let map    = buffer.map_readable().unwrap();
                let mut pixel_buffer = SharedPixelBuffer::<slint::Rgba8Pixel>::new(info.width(), info.height());
                unsafe {
                    let dest   = pixel_buffer.make_mut_slice();
                    let dest_u8 = std::slice::from_raw_parts_mut(dest.as_mut_ptr() as *mut u8, dest.len() * 4);
                    dest_u8.copy_from_slice(map.as_slice());
                }
                let proj_clone = proj_weak.clone();
                let _ = slint::invoke_from_event_loop(move || {
                    if let Some(p) = proj_clone.upgrade() {
                        p.set_fondo_video_frame(slint::Image::from_rgba8(pixel_buffer));
                    }
                });
                Ok(gst::FlowSuccess::Ok)
            })
            .build()
        );
        pipeline.set_state(gst::State::Playing).unwrap();
        self.pipeline = Some(pipeline.clone());
        let bus            = pipeline.bus().unwrap();
        let pipeline_clone = pipeline.clone();
        std::thread::spawn(move || {
            for msg in bus.iter_timed(gst::ClockTime::NONE) {
                match msg.view() {
                    gst::MessageView::Eos(..) => {
                        if is_loop {
                            let _ = pipeline_clone.seek_simple(
                                gst::SeekFlags::FLUSH | gst::SeekFlags::KEY_UNIT,
                                gst::ClockTime::ZERO,
                            );
                            let _ = pipeline_clone.set_state(gst::State::Playing);
                        } else {
                            let _ = pipeline_clone.set_state(gst::State::Paused);
                        }
                    }
                    gst::MessageView::Error(err) => {
                        println!("Error de reproducción: {}", err.error());
                        break;
                    }
                    _ => {}
                }
            }
        });
    }

    fn detener(&mut self) {
        if let Some(pipeline) = self.pipeline.take() {
            let _ = pipeline.set_state(gst::State::Null);
        }
    }

    pub fn reproducir_preview(&mut self, ruta: &str, ui_weak: slint::Weak<AppWindow>) {
        self.detener();
        let path = std::path::Path::new(ruta).canonicalize()
            .unwrap_or_else(|_| std::path::PathBuf::from(ruta));
        let uri = gst::glib::filename_to_uri(&path, None).unwrap();
        let pipeline = gst::ElementFactory::make("playbin")
            .property("uri", &uri)
            .build()
            .unwrap();
        pipeline.set_property("volume", 0.0f64);

        let videoscale  = gst::ElementFactory::make("videoscale").build().unwrap();
        let capsfilter  = gst::ElementFactory::make("capsfilter")
            .property("caps", &gst::Caps::builder("video/x-raw")
                .field("width", 320i32).field("height", 180i32).field("format", "RGBA")
                .build())
            .build()
            .unwrap();
        let appsink = gst_app::AppSink::builder().max_buffers(1).drop(true).sync(true).build();
        let sink_bin = gst::Bin::new();
        sink_bin.add_many([&videoscale, &capsfilter, appsink.upcast_ref()]).unwrap();
        gst::Element::link_many([&videoscale, &capsfilter, appsink.upcast_ref()]).unwrap();
        let pad       = videoscale.static_pad("sink").unwrap();
        let ghost_pad = gst::GhostPad::with_target(&pad).unwrap();
        sink_bin.add_pad(&ghost_pad).unwrap();
        pipeline.set_property("video-sink", &sink_bin);

        appsink.set_callbacks(gst_app::AppSinkCallbacks::builder()
            .new_sample(move |appsink| {
                let sample = match appsink.pull_sample() { Ok(s) => s, Err(_) => return Ok(gst::FlowSuccess::Ok) };
                let buffer = sample.buffer().unwrap();
                let info   = gst_video::VideoInfo::from_caps(sample.caps().unwrap()).unwrap();
                let map    = buffer.map_readable().unwrap();
                let mut pixel_buffer = SharedPixelBuffer::<slint::Rgba8Pixel>::new(info.width(), info.height());
                unsafe {
                    let dest    = pixel_buffer.make_mut_slice();
                    let dest_u8 = std::slice::from_raw_parts_mut(dest.as_mut_ptr() as *mut u8, dest.len() * 4);
                    dest_u8.copy_from_slice(map.as_slice());
                }
                let ui_clone = ui_weak.clone();
                let _ = slint::invoke_from_event_loop(move || {
                    if let Some(ui) = ui_clone.upgrade() {
                        ui.set_preview_video_frame(slint::Image::from_rgba8(pixel_buffer));
                    }
                });
                Ok(gst::FlowSuccess::Ok)
            })
            .build()
        );
        pipeline.set_state(gst::State::Playing).unwrap();
        self.pipeline = Some(pipeline);
    }

    pub fn toggle_play_pause(&mut self) -> bool {
        if let Some(pipeline) = &self.pipeline {
            let (_, state, _) = pipeline.state(gst::ClockTime::NONE);
            if state == gst::State::Playing {
                pipeline.set_state(gst::State::Paused).unwrap();
                return false;
            } else {
                pipeline.set_state(gst::State::Playing).unwrap();
                return true;
            }
        }
        false
    }

    pub fn get_position_and_duration(&self) -> (u64, u64) {
        if let Some(pipeline) = &self.pipeline {
            let pos = pipeline.query_position::<gst::ClockTime>().map_or(0, |t| t.mseconds());
            let dur = pipeline.query_duration::<gst::ClockTime>().map_or(0, |t| t.mseconds());
            return (pos, dur);
        }
        (0, 0)
    }

    pub fn seek_percentage(&self, percent: f32) {
        if let Some(pipeline) = &self.pipeline {
            let dur = pipeline.query_duration::<gst::ClockTime>().map_or(0, |t| t.nseconds());
            if dur > 0 {
                let target_ns = (dur as f64 * percent as f64) as u64;
                let _ = pipeline.seek_simple(
                    gst::SeekFlags::FLUSH | gst::SeekFlags::ACCURATE,
                    gst::ClockTime::from_nseconds(target_ns),
                );
            }
        }
    }

    pub fn set_mute(&self, mute: bool) {
        if let Some(pipeline) = &self.pipeline { pipeline.set_property("mute", mute); }
    }
}

impl Drop for NativeVideoPlayer {
    fn drop(&mut self) { self.detener(); }
}

// ---------------------------------------------------------------------------
// Estilos del proyector
// ---------------------------------------------------------------------------
fn aplicar_estilos(
    ui: &AppWindow,
    p:  &ProjectorWindow,
    vp: &Arc<Mutex<NativeVideoPlayer>>,
    modo: &str,
    forzar_reinicio_video: bool,
) {
    let is_biblia  = modo == "biblias";
    let bg_type    = if is_biblia { ui.get_biblias_bg_type()      } else { ui.get_cantos_bg_type()      };
    let font_color = if is_biblia { ui.get_biblias_font_color()   } else { ui.get_cantos_font_color()   };
    let opacity    = if is_biblia { ui.get_biblias_fondo_opacity() } else { ui.get_cantos_fondo_opacity() };
    p.set_text_color(font_color);
    p.set_fondo_opacity(opacity);

    if bg_type == "negro" {
        vp.lock().unwrap().detener();
        p.set_es_video(false);
        p.set_bg_color(slint::Color::from_rgb_u8(0, 0, 0));
        p.set_mostrar_imagen(false);
    } else if bg_type == "blanco" {
        vp.lock().unwrap().detener();
        p.set_es_video(false);
        p.set_bg_color(slint::Color::from_rgb_u8(255, 255, 255));
        p.set_mostrar_imagen(false);
    } else if bg_type == "imagen" {
        vp.lock().unwrap().detener();
        p.set_es_video(false);
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
    } else if bg_type == "video" {
        p.set_bg_color(slint::Color::from_rgb_u8(0, 0, 0));
        p.set_mostrar_imagen(false);
        p.set_es_video(true);
        if forzar_reinicio_video {
            let ruta = if is_biblia { ui.get_biblias_video_path() } else { ui.get_cantos_video_path() };
            if !ruta.is_empty() {
                vp.lock().unwrap().reproducir(ruta.as_str(), p.as_weak(), true);
            } else {
                vp.lock().unwrap().detener();
            }
        }
    }
}

fn configurar_ventana_proyector_linux(wid_store: Arc<Mutex<Option<String>>>) {
    #[cfg(target_os = "linux")]
    {
        let pid = std::process::id().to_string();
        thread::spawn(move || {
            for delay_ms in [600u64, 1200u64, 2500u64, 4000u64] {
                thread::sleep(std::time::Duration::from_millis(delay_ms));

                let Ok(out) = std::process::Command::new("xdotool")
                    .args(["search", "--pid", &pid])
                    .output()
                else { continue };

                let wids_raw = String::from_utf8_lossy(&out.stdout);
                let wids: Vec<&str> = wids_raw.split_whitespace().collect();
                if wids.is_empty() { continue; }

                // ── CLAVE: buscar la ventana SIN título (el proyector tiene title: "")
                let mut proyector_wid: Option<String> = None;
                for wid in &wids {
                    let nombre_out = std::process::Command::new("xdotool")
                        .args(["getwindowname", wid])
                        .output();
                    let nombre = match nombre_out {
                        Ok(o) => String::from_utf8_lossy(&o.stdout).trim().to_string(),
                        Err(_) => continue,
                    };
                    // El proyector tiene title vacío en el .slint
                    if nombre.is_empty() || nombre == "Slint Window" && wids.len() == 1 {
                        proyector_wid = Some(wid.to_string());
                        break;
                    }
                }

                let wid = match proyector_wid {
                    Some(w) => w,
                    None => continue,
                };

                println!("✅ Proyector encontrado: wid={}", wid);
                *wid_store.lock().unwrap() = Some(wid.clone());

                // Quitar acción minimizar
                let _ = std::process::Command::new("xprop")
                    .args([
                        "-id", &wid,
                        "-f", "_NET_WM_ALLOWED_ACTIONS", "32a",
                        "-set", "_NET_WM_ALLOWED_ACTIONS",
                        "_NET_WM_ACTION_MOVE,_NET_WM_ACTION_RESIZE,\
                         _NET_WM_ACTION_MAXIMIZE_HORZ,_NET_WM_ACTION_MAXIMIZE_VERT,\
                         _NET_WM_ACTION_FULLSCREEN,_NET_WM_ACTION_CHANGE_DESKTOP,\
                         _NET_WM_ACTION_CLOSE",
                    ])
                    .output();

                // Ocultar del taskbar
                let _ = std::process::Command::new("xprop")
                    .args([
                        "-id", &wid,
                        "-f", "_NET_WM_STATE", "32a",
                        "-set", "_NET_WM_STATE",
                        "_NET_WM_STATE_SKIP_TASKBAR,_NET_WM_STATE_SKIP_PAGER",
                    ])
                    .output();

                break;
            }
        });
    }
}

// ---------------------------------------------------------------------------
// Estructuras auxiliares para multimedia/PDF
// ---------------------------------------------------------------------------
struct MediaData { path: String, name: String, aspecto: String, is_loop: bool }
struct PdfData   { name: String, thumb_path: String, pages: Vec<String>       }

// ---------------------------------------------------------------------------
// main()
// ---------------------------------------------------------------------------
fn main() -> Result<(), Box<dyn std::error::Error>> {
    gst::init().expect("Error al inicializar GStreamer.");

    #[cfg(target_os = "linux")]
    {
        if std::env::var("WAYLAND_DISPLAY").is_ok() {
            println!("Detectado Wayland, forzando modo X11/XWayland...");
            std::env::set_var("WAYLAND_DISPLAY", "");
            std::env::set_var("GDK_BACKEND", "x11");
        }
    }

    // Forzar inicialización de las tablas estáticas al arranque, no bajo demanda.
    // En el E1-6015 esto hace que el primer keystroke sea igual de rápido que los siguientes.
    let _ = &*LIBROS_NORMALIZADOS;
    let _ = &*RE_BUSQUEDA;
    let _ = &*RE_FAV;

    let current_biblia_libro   = Arc::new(Mutex::new(-1i32));
    let current_biblia_capitulo = Arc::new(Mutex::new(-1i32));
    let segunda_pantalla: Arc<Mutex<Option<(i32, i32, u32, u32)>>> = Arc::new(Mutex::new(None));

    let state       = Arc::new(Mutex::new(AppState::new()?));
    let ui          = AppWindow::new()?;
    let proyector   = ProjectorWindow::new()?;
    let video_player = Arc::new(Mutex::new(NativeVideoPlayer::new()));

    let multimedia_state = Arc::new(RwLock::new(Vec::<MediaData>::new()));
    let video_state      = Arc::new(RwLock::new(Vec::<MediaData>::new()));
    let pdf_state        = Arc::new(RwLock::new(Vec::<PdfData>::new()));
    let preview_player   = Arc::new(Mutex::new(NativeVideoPlayer::new()));

    // OPT-7: Caché de imágenes compartido entre closures que acceden a disco
    let image_cache: Arc<Mutex<HashMap<String, slint::Image>>> =
        Arc::new(Mutex::new(HashMap::new()));

    // OPT-3: AtomicBool — lecturas/escrituras sin lock del SO
    let bloqueo_estilos = Arc::new(AtomicBool::new(false));

    let proyector_abierto = Arc::new(AtomicBool::new(false));

    let proyector_wid: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));

    // ── Márgenes del proyector ───────────────────────────────────────────────
    // {
    //     let p_weak = proyector.as_weak();
        
    //     ui.on_actualizar_margenes(move |izq, der, sup, inf| {
    //         if let Some(p) = p_weak.upgrade() {
    //             p.set_margen_izquierdo(izq);
    //             p.set_margen_derecho(der);
    //             p.set_margen_superior(sup);
    //             p.set_margen_inferior(inf);
    //         }
    //         bsc_margenes();
    //     });
    // }

    // ── Detección de segunda pantalla ────────────────────────────────────────
    {
        match DisplayInfo::all() {
            Ok(pantallas) => {
                let hay_primaria = pantallas.iter().any(|d| d.is_primary);
                let segunda = if hay_primaria {
                    pantallas.iter().find(|d| !d.is_primary)
                } else {
                    pantallas.iter().find(|d| !(d.x == 0 && d.y == 0))
                };
                if let Some(s) = segunda {
                    let w = (s.width  as f32 * s.scale_factor) as u32;
                    let h = (s.height as f32 * s.scale_factor) as u32;
                    *segunda_pantalla.lock().unwrap() = Some((s.x, s.y, w, h));
                }
            }
            Err(e) => println!("No se pudieron detectar pantallas: {}", e),
        }
    }

    // ── Cargar configuración persistente ────────────────────────────────────
    let user_data_dir_cfg = state.lock().unwrap().user_data_dir.clone();
    let cfg = cargar_config(&user_data_dir_cfg);

    // Restaurar rutas de galería en AppState
    {
        let mut st = state.lock().unwrap();
        st.biblias_image_paths = cfg.biblias_image_paths.clone();
        st.cantos_image_paths  = cfg.cantos_image_paths.clone();
        st.biblias_video_paths = cfg.biblias_video_paths.clone();
        st.cantos_video_paths  = cfg.cantos_video_paths.clone();
    }

    // Restaurar multimedia proyectable
    {
        let mut mm = multimedia_state.write().unwrap();
        for i in 0..cfg.multimedia_paths.len() {
            mm.push(MediaData {
                path:    cfg.multimedia_paths.get(i).cloned().unwrap_or_default(),
                name:    cfg.multimedia_names.get(i).cloned().unwrap_or_default(),
                aspecto: cfg.multimedia_aspectos.get(i).cloned().unwrap_or_else(|| "centro".to_string()),
                is_loop: false,
            });
        }
    }
    {
        let mut vs = video_state.write().unwrap();
        for i in 0..cfg.video_paths.len() {
            vs.push(MediaData {
                path:    cfg.video_paths.get(i).cloned().unwrap_or_default(),
                name:    cfg.video_names.get(i).cloned().unwrap_or_default(),
                aspecto: "rellenar".to_string(),
                is_loop: *cfg.video_loops.get(i).unwrap_or(&false),
            });
        }
    }

    // Restaurar UI: apariencia
    ui.set_biblias_bg_type(SharedString::from(&cfg.biblias_bg_type));
    ui.set_cantos_bg_type(SharedString::from(&cfg.cantos_bg_type));
    ui.set_biblias_font_color(slint::Color::from_rgb_u8(cfg.biblias_font_color[0], cfg.biblias_font_color[1], cfg.biblias_font_color[2]));
    ui.set_cantos_font_color(slint::Color::from_rgb_u8(cfg.cantos_font_color[0], cfg.cantos_font_color[1], cfg.cantos_font_color[2]));
    ui.set_biblias_fondo_opacity(cfg.biblias_fondo_opacity);
    ui.set_cantos_fondo_opacity(cfg.cantos_fondo_opacity);
    ui.set_biblias_font_scale(if cfg.biblias_font_scale == 0.0 { 1.0 } else { cfg.biblias_font_scale });
    ui.set_cantos_font_scale(if cfg.cantos_font_scale == 0.0 { 1.0 } else { cfg.cantos_font_scale });
    ui.set_margen_izquierdo(cfg.margen_izquierdo);
    ui.set_margen_derecho(cfg.margen_derecho);
    ui.set_margen_superior(cfg.margen_superior);
    ui.set_margen_inferior(cfg.margen_inferior);
    ui.set_default_bg_type(SharedString::from(&cfg.default_bg_type));
    ui.set_default_bg_idx(cfg.default_bg_idx);

    // Restaurar galería de imágenes en la UI
    {
        let st = state.lock().unwrap();
        let images_b: Vec<slint::Image> = st.biblias_image_paths.iter()
            .filter_map(|p| load_image_cached(&image_cache, p))
            .collect();
        let images_c: Vec<slint::Image> = st.cantos_image_paths.iter()
            .filter_map(|p| load_image_cached(&image_cache, p))
            .collect();
        let names_bv: Vec<SharedString> = st.biblias_video_paths.iter()
            .map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap_or_default().to_string_lossy().to_string()))
            .collect();
        let names_cv: Vec<SharedString> = st.cantos_video_paths.iter()
            .map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap_or_default().to_string_lossy().to_string()))
            .collect();

        if !images_b.is_empty() {
            ui.set_biblias_image_data(ModelRc::from(Rc::new(VecModel::from(images_b))));
            ui.set_biblias_selected_img(cfg.biblias_selected_img);
            if let Some(img) = load_image_cached(&image_cache, st.biblias_image_paths.get(cfg.biblias_selected_img as usize).map(|s| s.as_str()).unwrap_or("")) {
                ui.set_biblias_bg_image(img);
                ui.set_biblias_has_image(true);
            }
        }
        if !images_c.is_empty() {
            ui.set_cantos_image_data(ModelRc::from(Rc::new(VecModel::from(images_c))));
            ui.set_cantos_selected_img(cfg.cantos_selected_img);
            if let Some(img) = load_image_cached(&image_cache, st.cantos_image_paths.get(cfg.cantos_selected_img as usize).map(|s| s.as_str()).unwrap_or("")) {
                ui.set_cantos_bg_image(img);
                ui.set_cantos_has_image(true);
            }
        }
        if !names_bv.is_empty() {
            ui.set_biblias_video_names(ModelRc::from(Rc::new(VecModel::from(names_bv))));
            ui.set_biblias_video_path(SharedString::from(cfg.biblias_video_path.as_str()));
            ui.set_biblias_selected_vid(cfg.biblias_selected_vid);
        }
        if !names_cv.is_empty() {
            ui.set_cantos_video_names(ModelRc::from(Rc::new(VecModel::from(names_cv))));
            ui.set_cantos_video_path(SharedString::from(cfg.cantos_video_path.as_str()));
            ui.set_cantos_selected_vid(cfg.cantos_selected_vid);
        }
    }
    // refresh_multimedia();
    //  refresh_videos();

    // Función auxiliar para construir y guardar ConfigApp desde el estado actual
    let build_and_save_config = {
        let state_cfg   = Arc::clone(&state);
        let mm_cfg      = Arc::clone(&multimedia_state);
        let vs_cfg      = Arc::clone(&video_state);
        let ui_cfg      = ui.as_weak();
        let udd         = user_data_dir_cfg.clone();
        move || {
            let ui = match ui_cfg.upgrade() { Some(u) => u, None => return };
            let st = state_cfg.lock().unwrap();
            let mm = mm_cfg.read().unwrap();
            let vs = vs_cfg.read().unwrap();
            let fc_b = ui.get_biblias_font_color();
            let fc_c = ui.get_cantos_font_color();
            let cfg = ConfigApp {
                biblias_image_paths:  st.biblias_image_paths.clone(),
                cantos_image_paths:   st.cantos_image_paths.clone(),
                biblias_video_paths:  st.biblias_video_paths.clone(),
                cantos_video_paths:   st.cantos_video_paths.clone(),
                biblias_selected_img: ui.get_biblias_selected_img(),
                cantos_selected_img:  ui.get_cantos_selected_img(),
                biblias_selected_vid: ui.get_biblias_selected_vid(),
                cantos_selected_vid:  ui.get_cantos_selected_vid(),
                biblias_video_path:   ui.get_biblias_video_path().to_string(),
                cantos_video_path:    ui.get_cantos_video_path().to_string(),
                biblias_bg_type:      ui.get_biblias_bg_type().to_string(),
                cantos_bg_type:       ui.get_cantos_bg_type().to_string(),
                biblias_font_color:   [fc_b.red(), fc_b.green(), fc_b.blue()],
                cantos_font_color:    [fc_c.red(), fc_c.green(), fc_c.blue()],
                biblias_fondo_opacity: ui.get_biblias_fondo_opacity(),
                cantos_fondo_opacity:  ui.get_cantos_fondo_opacity(),
                biblias_font_scale:   ui.get_biblias_font_scale(),
                cantos_font_scale:    ui.get_cantos_font_scale(),
                multimedia_paths:   mm.iter().map(|m| m.path.clone()).collect(),
                multimedia_names:   mm.iter().map(|m| m.name.clone()).collect(),
                multimedia_aspectos: mm.iter().map(|m| m.aspecto.clone()).collect(),
                video_paths: vs.iter().map(|v| v.path.clone()).collect(),
                video_names: vs.iter().map(|v| v.name.clone()).collect(),
                video_loops: vs.iter().map(|v| v.is_loop).collect(),
                margen_izquierdo: ui.get_margen_izquierdo(),
                margen_derecho:   ui.get_margen_derecho(),
                margen_superior:  ui.get_margen_superior(),
                margen_inferior:  ui.get_margen_inferior(),
                default_bg_type:  ui.get_default_bg_type().to_string(),
                default_bg_idx:   ui.get_default_bg_idx(),
            };
            guardar_config(&udd, &cfg);
        }
    };

    // Ahora sí se puede usar build_and_save_config en márgenes
    {
        let p_weak2 = proyector.as_weak();
        let bsc_margenes = build_and_save_config.clone();
        ui.on_actualizar_margenes(move |izq, der, sup, inf| {
            if let Some(p) = p_weak2.upgrade() {
                p.set_margen_izquierdo(izq);
                p.set_margen_derecho(der);
                p.set_margen_superior(sup);
                p.set_margen_inferior(inf);
            }
            bsc_margenes();
        });
    }

    // refresh_multimedia();
    // refresh_videos();
    // ── Inicialización de versiones y libros ─────────────────────────────────
    {
        let st = state.lock().unwrap();
        let versiones_slint: Vec<SharedString> = st.versiones.iter()
            .map(|v| SharedString::from(&v.nombre_completo))
            .collect();
        ui.set_bible_versions(ModelRc::from(Rc::new(VecModel::from(versiones_slint))));
        if let Some(primera) = st.versiones.first() {
            ui.set_current_bible_version(SharedString::from(&primera.nombre_completo));
        }
        let libros = st.get_libros_biblia();
        let libros_slint: Vec<BookInfo> = libros.into_iter()
            .map(|l| BookInfo { id: l.id, nombre: SharedString::from(l.nombre), capitulos: l.capitulos })
            .collect();
        ui.set_bible_books(ModelRc::from(Rc::new(VecModel::from(libros_slint))));
    }

    // ── Cargar cantos ────────────────────────────────────────────────────────
    let cargar_cantos = {
        let ui_handle   = ui.as_weak();
        let state_clone = Arc::clone(&state);
        move |busqueda: String| {
            let ui     = ui_handle.unwrap();
            let estado = state_clone.lock().unwrap();
            let fav_ids   = estado.get_favoritos_ids_cantos();
            let cantos_db = if busqueda.is_empty() {
                estado.get_all_cantos()
            } else {
                estado.get_cantos_filtrados(&busqueda)
            };
            let mut cantos_slint: Vec<Canto> = cantos_db.into_iter().map(|c| {
                let is_fav = fav_ids.contains(&c.id);
                Canto { id: c.id, titulo: SharedString::from(c.titulo), letra: SharedString::from(""), favorito: is_fav }
            }).collect();
            if cantos_slint.is_empty() {
                cantos_slint.push(Canto {
                    id:      0,
                    titulo:  SharedString::from("Click derecho para agregar canto"),
                    letra:   SharedString::from(""),
                    favorito: false,
                });
            }
            ui.set_cantos(ModelRc::from(Rc::new(VecModel::from(cantos_slint))));
            let favs = estado.get_all_favoritos();
            ui.set_favoritos(ModelRc::from(Rc::new(VecModel::from(favs))));
        }
    };
    cargar_cantos(String::new());

    {
        let c_clone = cargar_cantos.clone();
        ui.on_buscar_cantos(move |t| c_clone(t.to_string()));
    }

    // ── Seleccionar canto ────────────────────────────────────────────────────
    {
        let ui_handle   = ui.as_weak();
        let state_clone = Arc::clone(&state);
        let cb_lib      = Arc::clone(&current_biblia_libro);
        let cb_cap      = Arc::clone(&current_biblia_capitulo);
        ui.on_seleccionar_canto(move |id| {
            if id == 0 { return; }
            *cb_lib.lock().unwrap() = -1;
            *cb_cap.lock().unwrap() = -1;
            let ui     = ui_handle.unwrap();
            let estado = state_clone.lock().unwrap();
            ui.set_elemento_seleccionado(SharedString::from(estado.get_canto_titulo(id)));
            let diapos: Vec<DiapositivaUI> = estado.get_canto_diapositivas(id)
                .iter()
                .map(diapositiva_a_ui)
                .collect();
            ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos))));
            ui.set_active_estrofa_index(-1);
            ui.invoke_focus_panel();
        });
    }

    // ── Guardar canto ────────────────────────────────────────────────────────
    {
        let state_clone  = Arc::clone(&state);
        let state_clone2 = Arc::clone(&state);
        let c_clone      = cargar_cantos.clone();
        let ui_handle    = ui.as_weak();
        let p_handle     = proyector.as_weak();
        let sp_guardar   = Arc::clone(&segunda_pantalla);
        ui.on_guardar_canto(move |id, titulo, letra| {
            {
                let estado = state_clone.lock().unwrap();
                if id == -1 { estado.add_canto(&titulo, &letra); } else { estado.update_canto(id, &titulo, &letra); }
            }
            c_clone(String::new());
            if id != -1 {
                let ui     = ui_handle.unwrap();
                let p      = p_handle.unwrap();
                let estado = state_clone2.lock().unwrap();
                let titulo_guardado   = estado.get_canto_titulo(id);
                let titulo_en_panel   = ui.get_elemento_seleccionado().to_string();
                let es_canto_activo   = titulo_en_panel == titulo.to_string() || titulo_en_panel == titulo_guardado;
                if es_canto_activo {
                    let nuevas_diapos  = estado.get_canto_diapositivas(id);
                    let diapos_slint: Vec<DiapositivaUI> = nuevas_diapos.iter().map(diapositiva_a_ui).collect();
                    let active_idx     = ui.get_active_estrofa_index();
                    ui.set_elemento_seleccionado(SharedString::from(&titulo_guardado));
                    ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos_slint.clone()))));
                    let idx = if active_idx >= 0 && (active_idx as usize) < diapos_slint.len() {
                        active_idx as usize
                    } else if !diapos_slint.is_empty() {
                        ui.set_active_estrofa_index(0); 0
                    } else { return; };
                    let info_screen = *sp_guardar.lock().unwrap();
                    let (screen_w, screen_h) = if let Some((_, _, w, h)) = info_screen { (w as f32, h as f32) } else { (1920.0, 1080.0) };
                    let texto_nuevo = diapos_slint[idx].texto.clone();
                    let font_size   = calcular_font_size_canto(&texto_nuevo, screen_w, screen_h);
                    p.set_texto_proyeccion(texto_nuevo);
                    p.set_tamano_letra(font_size);
                    p.set_referencia(SharedString::from(""));
                }
            }
        });
    }

    {
        let state_clone = Arc::clone(&state);
        let c_clone     = cargar_cantos.clone();
        ui.on_eliminar_canto(move |id| { state_clone.lock().unwrap().delete_canto(id); c_clone(String::new()); });
    }

    {
        let ui_handle = ui.as_weak();
        ui.on_abrir_formulario_nuevo(move || {
            let ui = ui_handle.unwrap();
            ui.set_form_id(-1);
            ui.set_form_titulo(SharedString::from(""));
            ui.set_form_letra(SharedString::from(""));
            ui.set_mostrar_formulario(true);
        });
    }

    {
        let ui_handle   = ui.as_weak();
        let state_clone = Arc::clone(&state);
        ui.on_abrir_formulario_editar(move |id, _titulo| {
            let ui     = ui_handle.unwrap();
            let estado = state_clone.lock().unwrap();
            let diapos = estado.get_canto_diapositivas(id);
            let letra_completa = diapos.iter().map(|d| d.texto.clone()).collect::<Vec<_>>().join("\n\n");
            ui.set_form_id(id);
            ui.set_form_titulo(SharedString::from(estado.get_canto_titulo(id)));
            ui.set_form_letra(SharedString::from(letra_completa));
            ui.set_mostrar_formulario(true);
        });
    }

    {
        let ui_handle = ui.as_weak();
        ui.on_confirmar_eliminar_canto(move |id, titulo| {
            let ui = ui_handle.unwrap();
            ui.set_menu_canto_id(id);
            ui.set_menu_canto_titulo(titulo);
            ui.set_mostrar_confirmar_eliminar(true);
        });
    }

    // ── Abrir proyector ──────────────────────────────────────────────────────
    {
    let p_handle    = proyector.as_weak();
    let sp_clone    = Arc::clone(&segunda_pantalla);
    let pa          = Arc::clone(&proyector_abierto); // ← agregar
    let wid_clone   = Arc::clone(&proyector_wid);
    ui.on_abrir_proyector(move || {
        let p    = p_handle.unwrap();
        let info = *sp_clone.lock().unwrap();
        pa.store(true, Ordering::Release); // ← agregar
        if let Some((x, y, width, height)) = info {
            p.show().unwrap();
            configurar_ventana_proyector_linux(Arc::clone(&wid_clone));
            mover_proyector_a_pantalla(p.as_weak(), x, y, width, height);
        } else {
            p.show().unwrap();
            configurar_ventana_proyector_linux(Arc::clone(&wid_clone));
            let p_weak = p.as_weak();
            thread::spawn(move || {
                thread::sleep(std::time::Duration::from_millis(100));
                let _ = slint::invoke_from_event_loop(move || {
                    if let Some(p) = p_weak.upgrade() { p.window().set_maximized(true); }
                });
            });
        }
    });
}

    // ── Proyectar estrofa ────────────────────────────────────────────────────
    {
        let p_handle    = proyector.as_weak();
        let state_clone = Arc::clone(&state);
        let ui_h        = ui.as_weak();
        let vp          = Arc::clone(&video_player);
        let last_modo   = Arc::new(Mutex::new(String::new()));
        let sp          = Arc::clone(&segunda_pantalla);
        let bloqueo     = Arc::clone(&bloqueo_estilos);

        ui.on_proyectar_estrofa(move |texto, referencia| {
            let p        = p_handle.unwrap();
            let ui_local = ui_h.unwrap();

            ui_local.set_is_video_projecting(false);
            // OPT-3: store con Release para visibilidad cruzada de hilos
            bloqueo.store(false, Ordering::Release);

            p.set_texto_proyeccion(texto.clone());
            let mut ref_str = referencia.to_string();
            if !ref_str.is_empty() {
                let sigla = state_clone.lock().unwrap().get_sigla_actual();
                if !sigla.is_empty() { ref_str = format!("{}  |  {}", ref_str, sigla); }
            }
            p.set_referencia(SharedString::from(ref_str.clone()));
            let tiene_referencia = !ref_str.is_empty();
            let info = *sp.lock().unwrap();
            let (screen_w, screen_h) = if let Some((_, _, w, h)) = info { (w as f32, h as f32) } else { (1280.0, 720.0) };
            let base_font_size = if tiene_referencia {
                calcular_font_size_versiculo(&texto, screen_w, screen_h)
            } else {
                calcular_font_size_canto(&texto, screen_w, screen_h)
            };
            let scale = if tiene_referencia { ui_local.get_biblias_font_scale() } else { ui_local.get_cantos_font_scale() };
            p.set_tamano_letra(base_font_size * scale);
            let modo_actual = if tiene_referencia { "biblias" } else { "cantos" };
            let mut l_modo    = last_modo.lock().unwrap();
            let forzar_video  = *l_modo != modo_actual;
            *l_modo = modo_actual.to_string();
            aplicar_estilos(&ui_local, &p, &vp, modo_actual, forzar_video);
        });
    }

    // ── Búsqueda bíblica (sugerencias) ──────────────────────────────────────
    {
        let ui_h = ui.as_weak();
        ui.on_bible_search_changed(move |query| {
            let ui = ui_h.unwrap();
            if let Some((_, sug)) = buscar_libro_inteligente(&query) {
                if sug.to_lowercase() != query.to_lowercase() {
                    ui.set_bible_search_suggestion(SharedString::from(sug));
                    return;
                }
            }
            ui.set_bible_search_suggestion(SharedString::from(""));
        });
    }

    {
        let ui_h = ui.as_weak();
        ui.on_bible_book_selected(move |book| {
            let ui = ui_h.unwrap();
            let mut filas      = Vec::new();
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
    }

    // ── Seleccionar capítulo ─────────────────────────────────────────────────
    {
        let ui_h        = ui.as_weak();
        let state_clone = Arc::clone(&state);
        let cb_lib      = Arc::clone(&current_biblia_libro);
        let cb_cap      = Arc::clone(&current_biblia_capitulo);
        ui.on_bible_chapter_selected(move |cap| {
            let ui   = ui_h.unwrap();
            let book = ui.get_selected_bible_book();
            *cb_lib.lock().unwrap() = book.id;
            *cb_cap.lock().unwrap() = cap;
            let titulo = format!("{} {}", book.nombre, cap);
            ui.set_elemento_seleccionado(SharedString::from(&titulo));
            let state_t = Arc::clone(&state_clone);
            let ui_t    = ui.as_weak();
            let titulo2 = titulo.clone();
            thread::spawn(move || {
                let (versiculos, fav_refs) = {
                    let mut estado = state_t.lock().unwrap();
                    (estado.get_capitulo(book.id, cap), estado.get_favoritos_refs_versiculos())
                };
                let _ = slint::invoke_from_event_loop(move || {
                    let ui    = ui_t.unwrap();
                    let diapos: Vec<DiapositivaUI> = versiculos.iter()
                        .map(|v| versiculo_a_ui_fav(v, &fav_refs, &titulo2))
                        .collect();
                    ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
                    ui.set_active_estrofa_index(0);
                    if !diapos.is_empty() {
                        ui.invoke_proyectar_estrofa(
                            diapos[0].texto.clone(),
                            SharedString::from(format!("{}:{}", titulo2, diapos[0].orden)),
                        );
                    }
                    ui.invoke_focus_panel();
                });
            });
        });
    }

    // ── Búsqueda bíblica aceptada ────────────────────────────────────────────
    {
        let ui_h        = ui.as_weak();
        let state_clone = Arc::clone(&state);
        let cb_lib      = Arc::clone(&current_biblia_libro);
        let cb_cap      = Arc::clone(&current_biblia_capitulo);
        ui.on_bible_search_accepted(move |query| {
            let ui = ui_h.unwrap();
            let q  = query.to_string();
            // OPT-1: RE_BUSQUEDA ya está compilado; cero overhead aquí
            if let Some(caps) = RE_BUSQUEDA.captures(&q) {
                let book_query  = &caps[1];
                let capitulo: i32      = caps[2].parse().unwrap_or(1);
                let versiculo_obj: i32 = caps.get(3).map_or(1, |m| m.as_str().parse().unwrap_or(1));
                if let Some((libro_id, nombre_real)) = buscar_libro_inteligente(book_query) {
                    *cb_lib.lock().unwrap() = libro_id;
                    *cb_cap.lock().unwrap() = capitulo;
                    let titulo = format!("{} {}", nombre_real, capitulo);
                    ui.set_elemento_seleccionado(SharedString::from(&titulo));
                    let state_t = Arc::clone(&state_clone);
                    let ui_t    = ui.as_weak();
                    thread::spawn(move || {
                        let (versiculos, fav_refs) = {
                            let mut estado = state_t.lock().unwrap();
                            (estado.get_capitulo(libro_id, capitulo), estado.get_favoritos_refs_versiculos())
                        };
                        let _ = slint::invoke_from_event_loop(move || {
                            let ui = ui_t.unwrap();
                            let mut target_index = 0i32;
                            let diapos: Vec<DiapositivaUI> = versiculos.iter().enumerate().map(|(i, v)| {
                                if v.versiculo == versiculo_obj { target_index = i as i32; }
                                versiculo_a_ui_fav(v, &fav_refs, &titulo)
                            }).collect();
                            ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
                            ui.set_active_estrofa_index(target_index);
                            let offset = target_index as f32 * 115.0;
                            ui.set_scroll_to_y(if offset > 150.0 { -(offset - 150.0) } else { 0.0 });
                            if (target_index as usize) < diapos.len() {
                                let text = diapos[target_index as usize].texto.clone();
                                let ord  = diapos[target_index as usize].orden.clone();
                                ui.invoke_proyectar_estrofa(
                                    text,
                                    SharedString::from(format!("{}:{}", titulo, ord)),
                                );
                            }
                            ui.invoke_focus_panel();
                        });
                    });
                    ui.set_bible_search_suggestion(SharedString::from(""));
                }
            }
        });
    }

    // ── Cambio de versión bíblica ────────────────────────────────────────────
    {
        let ui_h        = ui.as_weak();
        let state_clone = Arc::clone(&state);
        let cb_lib      = Arc::clone(&current_biblia_libro);
        let cb_cap      = Arc::clone(&current_biblia_capitulo);
        ui.on_bible_version_changed(move |version_name| {
            let ui  = ui_h.unwrap();
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
                let book_name  = ui.get_selected_bible_book().nombre;
                let titulo     = format!("{} {}", book_name, cap);
                let fav_refs   = state_clone.lock().unwrap().get_favoritos_refs_versiculos();
                let diapos: Vec<DiapositivaUI> = versiculos_nuevos.iter()
                    .map(|v| versiculo_a_ui_fav(v, &fav_refs, &titulo))
                    .collect();
                ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
                if active_idx >= 0 && (active_idx as usize) < diapos.len() {
                    let texto_nuevo = diapos[active_idx as usize].texto.clone();
                    let orden       = diapos[active_idx as usize].orden.clone();
                    ui.invoke_proyectar_estrofa(
                        texto_nuevo,
                        SharedString::from(format!("{}:{}", titulo, orden)),
                    );
                }
            }
        });
    }

    // ── Sync estilos ─────────────────────────────────────────────────────────
    {
        let ui_h    = ui.as_weak();
        let p_h     = proyector.as_weak();
        let vp      = Arc::clone(&video_player);
        let sp      = Arc::clone(&segunda_pantalla);
        let bloqueo = Arc::clone(&bloqueo_estilos);
        let bsc_estilos = build_and_save_config.clone();
        ui.on_sync_estilos(move || {
            let ui = ui_h.unwrap();
            let p  = p_h.unwrap();
            if bloqueo.load(Ordering::Acquire) { return; }
            let modo = ui.get_modal_tab();
            aplicar_estilos(&ui, &p, &vp, modo.as_str(), true);
            let active_idx = ui.get_active_estrofa_index();
            if active_idx >= 0 {
                let estrofas = ui.get_estrofas_actuales();
                let idx = active_idx as usize;
                if idx < estrofas.row_count() {
                    if let Some(d) = estrofas.row_data(idx) {
                        let texto      = d.texto.to_string();
                        let referencia = p.get_referencia().to_string();
                        let tiene_ref  = !referencia.is_empty();
                        let info       = *sp.lock().unwrap();
                        let (sw, sh)   = if let Some((_, _, w, h)) = info { (w as f32, h as f32) } else { (1280.0, 720.0) };
                        let scale      = if modo == "biblias" { ui.get_biblias_font_scale() } else { ui.get_cantos_font_scale() };
                        let base_size  = if tiene_ref {
                            calcular_font_size_versiculo(&texto, sw, sh)
                        } else {
                            calcular_font_size_canto(&texto, sw, sh)
                        };
                        p.set_tamano_letra(base_size * scale);
                    }
                }
            }
            bsc_estilos();
        });
    }

    // ── Sync font scale ──────────────────────────────────────────────────────
    {
        let ui_h = ui.as_weak();
        let p_h  = proyector.as_weak();
        let sp   = Arc::clone(&segunda_pantalla);
        let bsc_font = build_and_save_config.clone();
        ui.on_sync_font_scale(move || {
            let ui         = ui_h.unwrap();
            let p          = p_h.unwrap();
            let active_idx = ui.get_active_estrofa_index();
            if active_idx < 0 { return; }
            let estrofas = ui.get_estrofas_actuales();
            let idx      = active_idx as usize;
            if idx >= estrofas.row_count() { return; }
            if let Some(d) = estrofas.row_data(idx) {
                let texto     = d.texto.to_string();
                let referencia = p.get_referencia().to_string();
                let tiene_ref  = !referencia.is_empty();
                let info       = *sp.lock().unwrap();
                let (sw, sh)   = if let Some((_, _, w, h)) = info { (w as f32, h as f32) } else { (1280.0, 720.0) };
                let modo       = ui.get_modal_tab();
                let scale      = if modo == "biblias" { ui.get_biblias_font_scale() } else { ui.get_cantos_font_scale() };
                let base_size  = if tiene_ref {
                    calcular_font_size_versiculo(&texto, sw, sh)
                } else {
                    calcular_font_size_canto(&texto, sw, sh)
                };
                p.set_tamano_letra(base_size * scale);
            }
            bsc_font();
        });
    }

    // ── Galería (imágenes y vídeos de fondo) ─────────────────────────────────
    {
        let ui_h        = ui.as_weak();
        let state_gal   = Arc::clone(&state);
        let img_cache   = Arc::clone(&image_cache);
        let bsc_galeria = build_and_save_config.clone();
        ui.on_agregar_a_galeria(move |tipo| {
            let ui       = ui_h.unwrap();
            let tipo_str = tipo.to_string();
            let es_video = tipo_str.ends_with("-vid");
            let dialog   = if es_video {
                rfd::FileDialog::new().add_filter("Videos", &["mp4","mov","mkv","webm"]).pick_file()
            } else {
                rfd::FileDialog::new().add_filter("Imágenes", &["png","jpg","jpeg","webp"]).pick_file()
            };
            if let Some(path) = dialog {
                let path_str = path.to_string_lossy().to_string();
                let mut estado = state_gal.lock().unwrap();
                if tipo_str == "biblias-img" {
                    if let Some(img) = load_image_cached(&img_cache, &path_str) {
                        estado.biblias_image_paths.push(path_str.clone());
                        let idx          = estado.biblias_image_paths.len() as i32 - 1;
                        let paths_copia: Vec<String> = estado.biblias_image_paths.clone();
                        drop(estado);
                        let images: Vec<slint::Image> = paths_copia.iter()
                            .filter_map(|p| load_image_cached(&img_cache, p))
                            .collect();
                        ui.set_biblias_image_data(ModelRc::from(Rc::new(VecModel::from(images))));
                        ui.set_biblias_selected_img(idx);
                        ui.set_biblias_bg_image(img);
                        ui.set_biblias_has_image(true);
                        ui.set_biblias_bg_type(SharedString::from("imagen"));
                        ui.invoke_sync_estilos();
                        bsc_galeria();
                    }
                } else if tipo_str == "cantos-img" {
                    if let Some(img) = load_image_cached(&img_cache, &path_str) {
                        estado.cantos_image_paths.push(path_str.clone());
                        let idx          = estado.cantos_image_paths.len() as i32 - 1;
                        let paths_copia: Vec<String> = estado.cantos_image_paths.clone();
                        drop(estado);
                        let images: Vec<slint::Image> = paths_copia.iter()
                            .filter_map(|p| load_image_cached(&img_cache, p))
                            .collect();
                        ui.set_cantos_image_data(ModelRc::from(Rc::new(VecModel::from(images))));
                        ui.set_cantos_selected_img(idx);
                        ui.set_cantos_bg_image(img);
                        ui.set_cantos_has_image(true);
                        ui.set_cantos_bg_type(SharedString::from("imagen"));
                        ui.invoke_sync_estilos();
                        bsc_galeria();
                    }
                } else if tipo_str == "biblias-vid" {
                    estado.biblias_video_paths.push(path_str.clone());
                    let names: Vec<SharedString> = estado.biblias_video_paths.iter()
                        .map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap().to_string_lossy().to_string()))
                        .collect();
                    let idx = estado.biblias_video_paths.len() as i32 - 1;
                    drop(estado);
                    ui.set_biblias_video_names(ModelRc::from(Rc::new(VecModel::from(names))));
                    ui.set_biblias_selected_vid(idx);
                    ui.set_biblias_video_path(SharedString::from(&path_str));
                    ui.set_biblias_bg_type(SharedString::from("video"));
                    ui.invoke_sync_estilos();
                    bsc_galeria();
                } else if tipo_str == "cantos-vid" {
                    estado.cantos_video_paths.push(path_str.clone());
                    let names: Vec<SharedString> = estado.cantos_video_paths.iter()
                        .map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap().to_string_lossy().to_string()))
                        .collect();
                    let idx = estado.cantos_video_paths.len() as i32 - 1;
                    drop(estado);
                    ui.set_cantos_video_names(ModelRc::from(Rc::new(VecModel::from(names))));
                    ui.set_cantos_selected_vid(idx);
                    ui.set_cantos_video_path(SharedString::from(&path_str));
                    ui.set_cantos_bg_type(SharedString::from("video"));
                    ui.invoke_sync_estilos();
                    bsc_galeria();
                }
            }
        });
    }

    {
        let ui_h      = ui.as_weak();
        let state_sel = Arc::clone(&state);
        let img_cache = Arc::clone(&image_cache);
        ui.on_seleccionar_galeria_item(move |tipo, idx| {
            let ui       = ui_h.unwrap();
            let estado   = state_sel.lock().unwrap();
            let tipo_str = tipo.to_string();
            let idx_u    = idx as usize;
            if tipo_str == "biblias-img" {
                if let Some(p) = estado.biblias_image_paths.get(idx_u) {
                    if let Some(img) = load_image_cached(&img_cache, p) {
                        ui.set_biblias_selected_img(idx); ui.set_biblias_bg_image(img);
                        ui.set_biblias_has_image(true); ui.set_biblias_bg_type(SharedString::from("imagen"));
                        ui.invoke_sync_estilos();
                    }
                }
            } else if tipo_str == "cantos-img" {
                if let Some(p) = estado.cantos_image_paths.get(idx_u) {
                    if let Some(img) = load_image_cached(&img_cache, p) {
                        ui.set_cantos_selected_img(idx); ui.set_cantos_bg_image(img);
                        ui.set_cantos_has_image(true); ui.set_cantos_bg_type(SharedString::from("imagen"));
                        ui.invoke_sync_estilos();
                    }
                }
            } else if tipo_str == "biblias-vid" {
                if let Some(p) = estado.biblias_video_paths.get(idx_u) {
                    ui.set_biblias_selected_vid(idx); ui.set_biblias_video_path(SharedString::from(p.as_str()));
                    ui.set_biblias_bg_type(SharedString::from("video")); ui.invoke_sync_estilos();
                }
            } else if tipo_str == "cantos-vid" {
                if let Some(p) = estado.cantos_video_paths.get(idx_u) {
                    ui.set_cantos_selected_vid(idx); ui.set_cantos_video_path(SharedString::from(p.as_str()));
                    ui.set_cantos_bg_type(SharedString::from("video")); ui.invoke_sync_estilos();
                }
            }
        });
    }

    {
        let ui_h        = ui.as_weak();
        let state_del   = Arc::clone(&state);
        let img_cache   = Arc::clone(&image_cache);
        let bsc_del_gal = build_and_save_config.clone();
        ui.on_eliminar_galeria_item(move |tipo, idx| {
            let ui       = ui_h.unwrap();
            let mut estado = state_del.lock().unwrap();
            let tipo_str = tipo.to_string();
            let idx_u    = idx as usize;
            if tipo_str == "biblias-img" && idx_u < estado.biblias_image_paths.len() {
                // Invalida del caché la imagen eliminada
                let removed = estado.biblias_image_paths.remove(idx_u);
                img_cache.lock().unwrap().remove(&removed);
                if estado.biblias_image_paths.is_empty() {
                    drop(estado);
                    ui.set_biblias_image_data(ModelRc::from(Rc::new(VecModel::<slint::Image>::from(vec![]))));
                    ui.set_biblias_has_image(false); ui.set_biblias_bg_type(SharedString::from("negro"));
                    ui.invoke_sync_estilos();
                    bsc_del_gal();
                } else {
                    let paths: Vec<slint::Image> = estado.biblias_image_paths.iter()
                        .filter_map(|p| load_image_cached(&img_cache, p))
                        .collect();
                    drop(estado);
                    ui.set_biblias_image_data(ModelRc::from(Rc::new(VecModel::from(paths))));
                    ui.set_biblias_selected_img(0);
                    ui.invoke_seleccionar_galeria_item(SharedString::from("biblias-img"), 0);
                    bsc_del_gal();
                }
            } else if tipo_str == "cantos-img" && idx_u < estado.cantos_image_paths.len() {
                let removed = estado.cantos_image_paths.remove(idx_u);
                img_cache.lock().unwrap().remove(&removed);
                if estado.cantos_image_paths.is_empty() {
                    drop(estado);
                    ui.set_cantos_image_data(ModelRc::from(Rc::new(VecModel::<slint::Image>::from(vec![]))));
                    ui.set_cantos_has_image(false); ui.set_cantos_bg_type(SharedString::from("negro"));
                    ui.invoke_sync_estilos();
                    bsc_del_gal();
                } else {
                    let paths: Vec<slint::Image> = estado.cantos_image_paths.iter()
                        .filter_map(|p| load_image_cached(&img_cache, p))
                        .collect();
                    drop(estado);
                    ui.set_cantos_image_data(ModelRc::from(Rc::new(VecModel::from(paths))));
                    ui.set_cantos_selected_img(0);
                    ui.invoke_seleccionar_galeria_item(SharedString::from("cantos-img"), 0);
                    bsc_del_gal();
                }
            } else if tipo_str == "biblias-vid" && idx_u < estado.biblias_video_paths.len() {
                estado.biblias_video_paths.remove(idx_u);
                let names: Vec<SharedString> = estado.biblias_video_paths.iter()
                    .map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap().to_string_lossy().to_string()))
                    .collect();
                let is_empty = estado.biblias_video_paths.is_empty();
                drop(estado);
                ui.set_biblias_video_names(ModelRc::from(Rc::new(VecModel::from(names))));
                if is_empty { ui.set_biblias_bg_type(SharedString::from("negro")); ui.invoke_sync_estilos(); }
                bsc_del_gal();
            } else if tipo_str == "cantos-vid" && idx_u < estado.cantos_video_paths.len() {
                estado.cantos_video_paths.remove(idx_u);
                let names: Vec<SharedString> = estado.cantos_video_paths.iter()
                    .map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap().to_string_lossy().to_string()))
                    .collect();
                let is_empty = estado.cantos_video_paths.is_empty();
                drop(estado);
                ui.set_cantos_video_names(ModelRc::from(Rc::new(VecModel::from(names))));
                if is_empty { ui.set_cantos_bg_type(SharedString::from("negro")); ui.invoke_sync_estilos(); }
                bsc_del_gal();
            }
        });
    }

    // ── Multimedia (imágenes proyectables) ───────────────────────────────────
    let refresh_multimedia = {
        let ui_handle = ui.as_weak();
        let state_arc = Arc::clone(&multimedia_state);
        let img_cache = Arc::clone(&image_cache);
        move || {
            let ui    = ui_handle.unwrap();
            let items = state_arc.read().unwrap();
            let slint_items: Vec<MediaItem> = items.iter().enumerate()
                .filter_map(|(i, item)| {
                    load_image_cached(&img_cache, &item.path).map(|img| MediaItem {
                        id:      i as i32,
                        nombre:  SharedString::from(&item.name),
                        path:    SharedString::from(&item.path),
                        img,
                        aspecto: SharedString::from(&item.aspecto),
                        is_loop: false,
                    })
                })
                .collect();
            ui.set_multimedia_items(ModelRc::from(Rc::new(VecModel::from(slint_items))));
        }
    };

    {
        let multi_state   = Arc::clone(&multimedia_state);
        let refresh_clone = refresh_multimedia.clone();
        let bsc_add_multi = build_and_save_config.clone();
        ui.on_agregar_multimedia(move || {
            if let Some(path) = rfd::FileDialog::new()
                .add_filter("Imágenes", &["png","jpg","jpeg","webp"]).pick_file()
            {
                let file_name = path.file_name().unwrap_or_default().to_string_lossy().to_string();
                let path_str  = path.to_string_lossy().to_string();
                multi_state.write().unwrap().push(MediaData { path: path_str, name: file_name, aspecto: "centro".to_string(), is_loop: false });
                refresh_clone();
                bsc_add_multi();
            }
        });
    }

    
    // ── PDF ──────────────────────────────────────────────────────────────────
{
    let ui_pdf    = ui.as_weak();
    let state_pdf = Arc::clone(&pdf_state);
    let udd_pdf   = user_data_dir_cfg.clone();

    ui.on_agregar_pdf(move || {
        let ui = ui_pdf.unwrap();
        if let Some(path) = rfd::FileDialog::new().add_filter("PDF", &["pdf"]).pick_file() {
            let file_name  = path.file_name().unwrap_or_default().to_string_lossy().to_string();
            ui.set_is_importing_pdf(true);
            ui.set_pdf_import_progress(0.0);
            ui.set_pdf_import_filename(SharedString::from(&file_name));

            let ui_t       = ui_pdf.clone();
            let state_t    = Arc::clone(&state_pdf);
            let path_clone = path.clone();
            let udd_clone  = udd_pdf.clone();

            thread::spawn(move || {
                // Buscar libpdfium en múltiples rutas sin panic
                let exe_dir = std::env::current_exe()
                    .unwrap_or_default()
                    .parent()
                    .unwrap_or(std::path::Path::new("."))
                    .to_path_buf();

                let pdfium_paths = [
                    exe_dir,
                    std::path::PathBuf::from("/usr/share/easy-presenter"),
                    std::path::PathBuf::from("/usr/share/easy-presenter-slint"),
                    std::path::PathBuf::from("/usr/lib"),
                    std::path::PathBuf::from("."),
                ];

                let bind = pdfium_paths.iter().find_map(|p| {
                    Pdfium::bind_to_library(
                        Pdfium::pdfium_platform_library_name_at_path(p)
                    ).ok()
                });

                let bind = match bind {
                    Some(b) => b,
                    None => {
                        eprintln!("ERROR: No se encontró libpdfium en ninguna ruta");
                        let ui_err = ui_t.clone();
                        let _ = slint::invoke_from_event_loop(move || {
                            if let Some(ui) = ui_err.upgrade() {
                                ui.set_is_importing_pdf(false);
                            }
                        });
                        return;
                    }
                };

                let pdfium = Pdfium::new(bind);

                let document = match pdfium.load_pdf_from_file(&path_clone, None) {
                    Ok(d) => d,
                    Err(e) => {
                        eprintln!("ERROR al abrir PDF: {}", e);
                        let ui_err = ui_t.clone();
                        let _ = slint::invoke_from_event_loop(move || {
                            if let Some(ui) = ui_err.upgrade() {
                                ui.set_is_importing_pdf(false);
                            }
                        });
                        return;
                    }
                };

                let total_pages = document.pages().len();
                let safe_name   = file_name.replace(' ', "_").replace(".pdf", "");

                // Guardar en user_data_dir/pdfs/ — funciona tanto en dev como en .deb
                let out_dir = udd_clone.join("pdfs").join(&safe_name);
                if let Err(e) = fs::create_dir_all(&out_dir) {
                    eprintln!("ERROR creando directorio {:?}: {}", out_dir, e);
                    let ui_err = ui_t.clone();
                    let _ = slint::invoke_from_event_loop(move || {
                        if let Some(ui) = ui_err.upgrade() {
                            ui.set_is_importing_pdf(false);
                        }
                    });
                    return;
                }

                let mut saved_pages_paths = Vec::new();
                let mut thumb_path_str    = String::new();

                for (i, page) in document.pages().iter().enumerate() {
                    // 1280px es suficiente para proyección y ~2x más rápido que 1920px
                    let config = PdfRenderConfig::new().set_target_width(1280);

                    match page.render_with_config(&config) {
                        Ok(bitmap) => {
                            let img       = bitmap.as_image();
                            let page_path = out_dir.join(format!("page_{}.jpg", i));

                            if let Err(e) = img.save(&page_path) {
                                eprintln!("ERROR guardando página {}: {}", i, e);
                                continue;
                            }

                            saved_pages_paths.push(page_path.to_string_lossy().to_string());

                            if i == 0 {
                                let t_path = out_dir.join("thumb.jpg");
                                if let Ok(thumb_bmp) = page.render_with_config(
                                    &PdfRenderConfig::new().set_target_width(200)
                                ) {
                                    let _ = thumb_bmp.as_image().save(&t_path);
                                    thumb_path_str = t_path.to_string_lossy().to_string();
                                }
                            }
                        }
                        Err(e) => {
                            eprintln!("ERROR renderizando página {}: {}", i, e);
                            continue;
                        }
                    }

                    // Actualizar barra de progreso
                    let progress = (i as f32 + 1.0) / total_pages as f32;
                    let ui_prog  = ui_t.clone();
                    let _ = slint::invoke_from_event_loop(move || {
                        if let Some(ui) = ui_prog.upgrade() {
                            ui.set_pdf_import_progress(progress);
                        }
                    });
                }

                state_t.write().unwrap().push(PdfData {
                    name:       file_name,
                    thumb_path: thumb_path_str,
                    pages:      saved_pages_paths,
                });

                let ui_fin    = ui_t.clone();
                let state_fin = Arc::clone(&state_t);
                let _ = slint::invoke_from_event_loop(move || {
                    if let Some(ui) = ui_fin.upgrade() {
                        ui.set_is_importing_pdf(false);
                        let items = state_fin.read().unwrap();
                        let slint_items: Vec<PdfItem> = items.iter().enumerate().map(|(i, item)| {
                            let img = slint::Image::load_from_path(
                                std::path::Path::new(&item.thumb_path)
                            ).unwrap_or_default();
                            PdfItem {
                                id:            i as i32,
                                nombre:        SharedString::from(&item.name),
                                miniatura:     img,
                                total_paginas: item.pages.len() as i32,
                            }
                        }).collect();
                        ui.set_pdf_items(ModelRc::from(Rc::new(VecModel::from(slint_items))));
                    }
                });
            });
        }
    });
}
    {
        let ui_pdf_sel  = ui.as_weak();
        let state_pdf_s = Arc::clone(&pdf_state);
        ui.on_seleccionar_pdf(move |idx| {
            let ui    = ui_pdf_sel.unwrap();
            let state = state_pdf_s.read().unwrap();
            if let Some(pdf) = state.get(idx as usize) {
                ui.set_selected_pdf_idx(idx);
                let pages_img: Vec<slint::Image> = pdf.pages.iter()
                    .filter_map(|p| slint::Image::load_from_path(std::path::Path::new(p)).ok())
                    .collect();
                ui.set_pdf_pages(ModelRc::from(Rc::new(VecModel::from(pages_img))));
            }
        });
    }

    {
        let ui_pdf_proj = ui.as_weak();
        let p_pdf       = proyector.as_weak();
        let vp_pdf      = Arc::clone(&video_player);
        let bloqueo     = Arc::clone(&bloqueo_estilos);
        ui.on_proyectar_pdf_pagina(move |page_idx| {
            let ui = ui_pdf_proj.unwrap();
            let p  = p_pdf.unwrap();
            bloqueo.store(true, Ordering::Release);
            ui.set_is_video_projecting(false);
            ui.set_active_pdf_page(page_idx);
            let current_pages = ui.get_pdf_pages();
            if let Some(img) = current_pages.row_data(page_idx as usize) {
                vp_pdf.lock().unwrap().detener();
                p.set_es_video(false);
                p.set_fondo_imagen_aspecto(slint::SharedString::from("contain"));
                p.set_fondo_imagen(img);
                p.set_mostrar_imagen(true);
            }
        });
    }

    ui.on_eliminar_pdf(move |_idx| { /* Lógica de borrado local */ });

    {
        let multi_state   = Arc::clone(&multimedia_state);
        let refresh_clone = refresh_multimedia.clone();
        let bsc_aspecto   = build_and_save_config.clone();
        ui.on_cambiar_aspecto_multimedia(move |idx, aspecto| {
            let mut state = multi_state.write().unwrap();
            if let Some(item) = state.get_mut(idx as usize) { item.aspecto = aspecto.to_string(); }
            drop(state);
            refresh_clone();
            bsc_aspecto();
        });
    }

    {
        let multi_state   = Arc::clone(&multimedia_state);
        let refresh_clone = refresh_multimedia.clone();
        let ui_handle     = ui.as_weak();
        let bsc_del_multi = build_and_save_config.clone();
        ui.on_eliminar_multimedia(move |idx| {
            let mut state = multi_state.write().unwrap();
            if (idx as usize) < state.len() { state.remove(idx as usize); }
            drop(state);
            let ui = ui_handle.unwrap();
            ui.set_selected_media_idx(-1);
            refresh_clone();
            bsc_del_multi();
        });
    }

    {
        let p_handle  = proyector.as_weak();
        let multi_state = Arc::clone(&multimedia_state);
        let vp        = Arc::clone(&video_player);
        let ui_h      = ui.as_weak();
        let bloqueo   = Arc::clone(&bloqueo_estilos);
        ui.on_proyectar_multimedia(move |idx| {
            let p        = p_handle.unwrap();
            let ui_local = ui_h.unwrap();
            bloqueo.store(true, Ordering::Release);
            ui_local.set_is_video_projecting(false);
            let state = multi_state.read().unwrap();
            if let Some(item) = state.get(idx as usize) {
                if let Ok(img) = slint::Image::load_from_path(std::path::Path::new(&item.path)) {
                    vp.lock().unwrap().detener();
                    p.set_es_video(false);
                    p.set_bg_color(slint::Color::from_rgb_u8(0, 0, 0));
                    p.set_texto_proyeccion(slint::SharedString::from(""));
                    p.set_referencia(slint::SharedString::from(""));
                    p.set_fondo_opacity(0.0);
                    p.set_fondo_imagen_aspecto(slint::SharedString::from(&item.aspecto));
                    p.set_fondo_imagen(img);
                    p.set_mostrar_imagen(true);
                }
            }
        });
    }

    // ── Vídeos proyectables ──────────────────────────────────────────────────
    let refresh_videos = {
        let ui_handle = ui.as_weak();
        let state_arc = Arc::clone(&video_state);
        move || {
            let ui    = ui_handle.unwrap();
            let items = state_arc.read().unwrap();
            let slint_items: Vec<MediaItem> = items.iter().enumerate().map(|(i, item)| {
                let pixel_buffer = SharedPixelBuffer::<slint::Rgba8Pixel>::new(80, 45);
                MediaItem {
                    id:      i as i32,
                    nombre:  SharedString::from(&item.name),
                    path:    SharedString::from(&item.path),
                    img:     slint::Image::from_rgba8(pixel_buffer),
                    aspecto: SharedString::from("rellenar"),
                    is_loop: item.is_loop,
                }
            }).collect();
            ui.set_video_items(ModelRc::from(Rc::new(VecModel::from(slint_items))));
        }
    };
    refresh_multimedia();
    refresh_videos();
    {
        
        let vid_state       = Arc::clone(&video_state);
        let refresh_clone   = refresh_videos.clone();
        let bsc_add_vid     = build_and_save_config.clone();
        ui.on_agregar_video(move || {
            if let Some(path) = rfd::FileDialog::new()
                .add_filter("Videos", &["mp4","mkv","avi","mov"]).pick_file()
            {
                let file_name = path.file_name().unwrap_or_default().to_string_lossy().to_string();
                vid_state.write().unwrap().push(MediaData {
                    path:    path.to_string_lossy().to_string(),
                    name:    file_name,
                    aspecto: "rellenar".to_string(),
                    is_loop: false,
                });
                refresh_clone();
                bsc_add_vid();
            }
        });
    }

    {
        let vid_state       = Arc::clone(&video_state);
        let refresh_clone   = refresh_videos.clone();
        let ui_handle       = ui.as_weak();
        let prev_del        = Arc::clone(&preview_player);
        let bsc_del_vid     = build_and_save_config.clone();
        ui.on_eliminar_video(move |idx| {
            let mut state = vid_state.write().unwrap();
            if (idx as usize) < state.len() { state.remove(idx as usize); }
            drop(state);
            let ui = ui_handle.unwrap();
            ui.set_selected_video_idx(-1);
            prev_del.lock().unwrap().detener();
            refresh_clone();
            bsc_del_vid();
        });
    }

    {
        let ui_handle   = ui.as_weak();
        let prev_sel    = Arc::clone(&preview_player);
        ui.on_seleccionar_video_lista(move |idx| {
            let ui = ui_handle.unwrap();
            ui.set_selected_video_idx(idx);
            prev_sel.lock().unwrap().detener();
            ui.set_is_preview_playing(false);
            ui.set_preview_video_frame(slint::Image::default());
            ui.set_is_video_projecting(false);
        });
    }

    {
        let vid_state   = Arc::clone(&video_state);
        let ui_handle   = ui.as_weak();
        let prev_clone  = Arc::clone(&preview_player);
        ui.on_toggle_preview_video(move |idx| {
            let ui    = ui_handle.unwrap();
            let state = vid_state.read().unwrap();
            if let Some(item) = state.get(idx as usize) {
                let mut player     = prev_clone.lock().unwrap();
                let is_playing     = ui.get_is_preview_playing();
                if !is_playing {
                    player.reproducir_preview(&item.path, ui.as_weak());
                    ui.set_is_preview_playing(true);
                } else {
                    player.detener();
                    ui.set_is_preview_playing(false);
                }
            }
        });
    }

    {
        let p_handle    = proyector.as_weak();
        let vid_state   = Arc::clone(&video_state);
        let vp          = Arc::clone(&video_player);
        let ui_h        = ui.as_weak();
        let bloqueo     = Arc::clone(&bloqueo_estilos);
        ui.on_proyectar_video(move |idx| {
            let p  = p_handle.unwrap();
            let ui = ui_h.unwrap();
            bloqueo.store(true, Ordering::Release);
            let state = vid_state.read().unwrap();
            if let Some(item) = state.get(idx as usize) {
                p.set_es_video(true);
                p.set_bg_color(slint::Color::from_rgb_u8(0, 0, 0));
                p.set_mostrar_imagen(false);
                p.set_texto_proyeccion(slint::SharedString::from(""));
                p.set_referencia(slint::SharedString::from(""));
                vp.lock().unwrap().reproducir(&item.path, p.as_weak(), item.is_loop);
                ui.set_is_video_projecting(true);
                ui.set_is_proyector_playing(true);
            }
        });
    }

    {
        let vp_controls = Arc::clone(&video_player);
        let ui_h        = ui.as_weak();
        ui.on_toggle_proyector_play(move || {
            let ui        = ui_h.unwrap();
            let is_playing = vp_controls.lock().unwrap().toggle_play_pause();
            ui.set_is_proyector_playing(is_playing);
        });
    }

    {
        let vp_mute = Arc::clone(&video_player);
        let ui_h    = ui.as_weak();
        ui.on_toggle_proyector_mute(move || {
            let ui            = ui_h.unwrap();
            let new_mute      = !ui.get_is_proyector_muted();
            vp_mute.lock().unwrap().set_mute(new_mute);
            ui.set_is_proyector_muted(new_mute);
        });
    }

    {
        let vp_seek = Arc::clone(&video_player);
        ui.on_seek_proyector_video(move |percent| { vp_seek.lock().unwrap().seek_percentage(percent); });
    }

    // Evitar que el proyector sea minimizado (Win+D, Super+H, etc.)
// Impedir que el proyector sea minimizado por atajos de teclado (Super+H, Win+D, etc.)
// Anti-minimize: 100ms es lo suficientemente rápido para ser imperceptible
let p_restore = proyector.as_weak();
let pa_timer  = Arc::clone(&proyector_abierto);
let _restore_timer = slint::Timer::default();
_restore_timer.start(
    slint::TimerMode::Repeated,
    std::time::Duration::from_millis(100),
    move || {
        if pa_timer.load(Ordering::Acquire) {
            if let Some(p) = p_restore.upgrade() {
                p.window().set_minimized(false);
            }
        }
    },
);

    // OPT-8: Timer declarado como variable local — vive hasta el final de main().
    //        El Box::leak original era un memory leak innecesario.
    let vp_timer       = Arc::clone(&video_player);
    let ui_timer_handle = ui.as_weak();
    let _video_timer   = slint::Timer::default(); // '_' evita unused-variable warning
    _video_timer.start(slint::TimerMode::Repeated, std::time::Duration::from_millis(500), move || {
        if let Some(ui) = ui_timer_handle.upgrade() {
            if ui.get_is_video_projecting() {
                let (pos_ms, dur_ms) = vp_timer.lock().unwrap().get_position_and_duration();
                if dur_ms > 0 {
                    let progress  = pos_ms as f32 / dur_ms as f32;
                    ui.set_proyector_progress(progress);
                    let pos_sec   = pos_ms / 1000;
                    let dur_sec   = dur_ms / 1000;
                    let time_str  = format!("{:02}:{:02} / {:02}:{:02}",
                        pos_sec / 60, pos_sec % 60,
                        dur_sec / 60, dur_sec % 60);
                    ui.set_proyector_time(slint::SharedString::from(time_str));
                }
            }
        }
    });

    {
        let vid_state_mode = Arc::clone(&video_state);
        let refresh_clone  = refresh_videos.clone();
        let bsc_modo       = build_and_save_config.clone();
        ui.on_cambiar_modo_reproduccion(move |idx, modo| {
            let mut state = vid_state_mode.write().unwrap();
            if let Some(item) = state.get_mut(idx as usize) { item.is_loop = modo == "bucle"; }
            drop(state);
            refresh_clone();
            bsc_modo();
        });
    }

    // ── Favoritos — cantos ───────────────────────────────────────────────────
    {
        let ui_h   = ui.as_weak();
        let state  = Arc::clone(&state);
        let c_clone = cargar_cantos.clone();
        ui.on_toggle_favorito_canto(move |id| {
            let ui    = ui_h.unwrap();
            let favs  = {
                let estado = state.lock().unwrap();
                estado.toggle_favorito_canto(id, &estado.get_canto_titulo(id));
                estado.get_all_favoritos()
            };
            ui.set_favoritos(ModelRc::from(Rc::new(VecModel::from(favs))));
            c_clone(ui.get_buscador_texto().to_string());
        });
    }

    // ── Favoritos — versículos ───────────────────────────────────────────────
    {
        let ui_h    = ui.as_weak();
        let state   = Arc::clone(&state);
        let cb_lib  = Arc::clone(&current_biblia_libro);
        let cb_cap  = Arc::clone(&current_biblia_capitulo);
        ui.on_toggle_favorito_estrofa(move |referencia, texto| {
            let ui  = ui_h.unwrap();
            { state.lock().unwrap().toggle_favorito_versiculo(&referencia, &texto); }
            let lib = *cb_lib.lock().unwrap();
            let cap = *cb_cap.lock().unwrap();
            let (versiculos, fav_refs, favs, titulo_cap) = {
                let mut estado    = state.lock().unwrap();
                let book_name     = ui.get_selected_bible_book().nombre.to_string();
                let t             = format!("{} {}", book_name, cap);
                let vs = if lib != -1 && cap != -1 { estado.get_capitulo(lib, cap) } else { Vec::new() };
                let fr = estado.get_favoritos_refs_versiculos();
                let fa = estado.get_all_favoritos();
                (vs, fr, fa, t)
            };
            if !versiculos.is_empty() {
                let diapos: Vec<DiapositivaUI> = versiculos.iter()
                    .map(|v| versiculo_a_ui_fav(v, &fav_refs, &titulo_cap))
                    .collect();
                ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos))));
            }
            ui.set_favoritos(ModelRc::from(Rc::new(VecModel::from(favs))));
        });
    }

    // ── Abrir favorito ───────────────────────────────────────────────────────
    {
        let ui_h    = ui.as_weak();
        let state   = Arc::clone(&state);
        let cb_lib  = Arc::clone(&current_biblia_libro);
        let cb_cap  = Arc::clone(&current_biblia_capitulo);
        ui.on_abrir_favorito(move |fav| {
            let ui = ui_h.unwrap();
            if fav.tipo == "canto" {
                ui.set_active_tab(SharedString::from("cantos"));
                let id    = fav.id;
                let titulo = state.lock().unwrap().get_canto_titulo(id);
                ui.set_elemento_seleccionado(SharedString::from(&titulo));
                let diapos: Vec<DiapositivaUI> = state.lock().unwrap()
                    .get_canto_diapositivas(id)
                    .iter()
                    .map(diapositiva_a_ui)
                    .collect();
                ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos))));
                ui.set_active_estrofa_index(-1);
            } else {
                ui.set_active_tab(SharedString::from("biblias"));
                let ref_str = fav.referencia.to_string();
                // OPT-1: RE_FAV compilada una sola vez
                if let Some(caps) = RE_FAV.captures(&ref_str) {
                    let libro_nombre  = caps[1].to_string();
                    let capitulo: i32 = caps[2].parse().unwrap_or(1);
                    let versiculo_num: i32 = caps[3].parse().unwrap_or(1);
                    if let Some((libro_id, nombre_real)) = buscar_libro_inteligente(&libro_nombre) {
                        *cb_lib.lock().unwrap() = libro_id;
                        *cb_cap.lock().unwrap() = capitulo;
                        let titulo = format!("{} {}", nombre_real, capitulo);
                        ui.set_elemento_seleccionado(SharedString::from(&titulo));
                        let state_t = Arc::clone(&state);
                        let ui_t    = ui.as_weak();
                        thread::spawn(move || {
                            let (versiculos, fav_refs) = {
                                let mut estado = state_t.lock().unwrap();
                                (estado.get_capitulo(libro_id, capitulo), estado.get_favoritos_refs_versiculos())
                            };
                            let _ = slint::invoke_from_event_loop(move || {
                                let ui = ui_t.unwrap();
                                let mut target_idx = 0i32;
                                let diapos: Vec<DiapositivaUI> = versiculos.iter().enumerate().map(|(i, v)| {
                                    if v.versiculo == versiculo_num { target_idx = i as i32; }
                                    versiculo_a_ui_fav(v, &fav_refs, &titulo)
                                }).collect();
                                ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
                                ui.set_active_estrofa_index(target_idx);
                                if (target_idx as usize) < diapos.len() {
                                    let text = diapos[target_idx as usize].texto.clone();
                                    let ord  = diapos[target_idx as usize].orden.clone();
                                    ui.invoke_proyectar_estrofa(
                                        text,
                                        SharedString::from(format!("{}:{}", titulo, ord)),
                                    );
                                }
                                ui.invoke_focus_panel();
                            });
                        });
                    }
                }
            }
        });
    }

      {
        let p_close = proyector.as_weak();
        ui.window().on_close_requested(move || {
            if let Some(p) = p_close.upgrade() {
                p.hide().unwrap();
            }
            slint::CloseRequestResponse::HideWindow
        });
    }

    ui.run()?;
    Ok(())
}