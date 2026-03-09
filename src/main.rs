#![windows_subsystem = "windows"]

use rusqlite::{Connection, Result};
use slint::{ModelRc, SharedString, VecModel, ComponentHandle, SharedPixelBuffer};
use slint::Model;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::rc::Rc;
use std::thread;
use regex::Regex;
use display_info::DisplayInfo;

use pdfium_render::prelude::*;
use std::fs;
use std::path::PathBuf;

use gstreamer as gst;
use gstreamer_app as gst_app;
use gstreamer_video as gst_video;
use gst::prelude::*;
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

// ══════════════════════════════════════════════════════════════
// CALCULA EL TAMAÑO DE FUENTE ÓPTIMO PARA UNA TARJETA DE CUADRÍCULA
//
// Dimensiones del área de texto útil dentro de la tarjeta (px lógicos):
//   ancho_util ≈ 296 px  (tarjeta ~316 − 20px de padding interno horizontal)
//   alto_util  ≈ 119 px  (tarjeta 180 − cabecera 28 − separador 1 − padding 12 − spacing 20)
//
// El algoritmo hace búsqueda binaria entre 7px y 28px para encontrar
// el tamaño máximo que hace caber el texto en esa área.
// ══════════════════════════════════════════════════════════════
fn calcular_font_size_tarjeta(texto: &str) -> f32 {
    const ANCHO_UTIL: f32 = 296.0;
    const ALTO_UTIL: f32 = 119.0;
    const CHAR_W: f32 = 0.55;   // factor ancho promedio carácter sans-serif
    const LINE_H: f32 = 1.30;   // interlineado

    let estimar_alto = |font_size: f32| -> f32 {
        let chars_por_linea = (ANCHO_UTIL / (font_size * CHAR_W)).floor().max(1.0);
        let mut lineas = 0.0f32;
        for linea in texto.lines() {
            let n = linea.chars().count() as f32;
            lineas += if n == 0.0 { 0.3 } else { (n / chars_por_linea).ceil() };
        }
        lineas.max(1.0) * font_size * LINE_H
    };

    let mut lo: f32 = 7.0;
    let mut hi: f32 = 28.0;   // techo razonable para tarjeta pequeña

    for _ in 0..20 {
        let mid = (lo + hi) / 2.0;
        if estimar_alto(mid) <= ALTO_UTIL { lo = mid; } else { hi = mid; }
    }

    // 90% del tamaño máximo como margen de seguridad, clampado entre 9 y 22 px
    (lo * 0.90).clamp(9.0, 22.0)
}

// ── Helper: DiapositivaDB → DiapositivaUI con font_size calculado ──
fn diapositiva_a_ui(d: &DiapositivaDB) -> DiapositivaUI {
    DiapositivaUI {
        orden: SharedString::from(d.orden.to_string()),
        texto: SharedString::from(d.texto.clone()),
        font_size: calcular_font_size_tarjeta(&d.texto),
    }
}

// ── Helper: VersiculoDB → DiapositivaUI con font_size calculado ──
fn versiculo_a_ui(v: &VersiculoDB) -> DiapositivaUI {
    DiapositivaUI {
        orden: SharedString::from(v.versiculo.to_string()),
        texto: SharedString::from(v.texto.clone()),
        font_size: calcular_font_size_tarjeta(&v.texto),
    }
}

struct AppState {
    cantos_db: Connection, biblias_db: Connection,
    versiones: Vec<VersionInfo>, current_version_id: i32,
    chapter_cache: HashMap<CacheKey, Vec<VersiculoDB>>,
    biblias_image_paths: Vec<String>,
    cantos_image_paths: Vec<String>,
    biblias_video_paths: Vec<String>,
    cantos_video_paths: Vec<String>,
}

impl AppState {
    fn new() -> Result<Self> {
        let cantos_db = Connection::open("data/cantos.db")?;
        let biblias_db = Connection::open("data/biblias.db")?;
        cantos_db.execute_batch("PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;")?;
        biblias_db.execute_batch("PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;")?;
        let mut state = Self {
            cantos_db, biblias_db, versiones: Vec::new(), current_version_id: 1,
            chapter_cache: HashMap::new(),
            biblias_image_paths: Vec::new(), cantos_image_paths: Vec::new(),
            biblias_video_paths: Vec::new(), cantos_video_paths: Vec::new(),
        };
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
                    if es_ultimo { p.window().set_fullscreen(true); }
                }
            });
        });
    }
}

fn calcular_font_size(texto: &str, tiene_referencia: bool, screen_w: f32, screen_h: f32) -> f32 {
    let padding_w: f32 = 140.0;
    let padding_h: f32 = if tiene_referencia { 200.0 } else { 120.0 };
    let ancho_util = (screen_w - padding_w).max(800.0);
    let alto_util = (screen_h - padding_h).max(600.0);
    let char_width_factor: f32 = 0.55;
    let line_height_factor: f32 = 1.25;

    let estimar_lineas = |font_size: f32| -> f32 {
        let chars_por_linea = (ancho_util / (font_size * char_width_factor)).floor().max(1.0);
        let mut total_lineas = 0.0f32;
        for linea in texto.lines() {
            let chars = linea.chars().count() as f32;
            if chars == 0.0 { total_lineas += 0.3; } else { total_lineas += (chars / chars_por_linea).ceil(); }
        }
        total_lineas.max(1.0)
    };

    let mut min_size: f32 = 20.0;
    let mut max_size: f32 = 300.0;
    for _ in 0..30 {
        let mid = (min_size + max_size) / 2.0;
        let lineas = estimar_lineas(mid);
        let alto_necesario = lineas * mid * line_height_factor;
        let max_word_len = texto.split_whitespace().map(|w| w.chars().count()).max().unwrap_or(1) as f32;
        let ancho_max_palabra = max_word_len * mid * char_width_factor;
        if alto_necesario <= alto_util && ancho_max_palabra <= ancho_util { min_size = mid; } else { max_size = mid; }
    }
    let size_final = min_size * 0.92;
    size_final.clamp(30.0, screen_h * 0.18)
}

struct NativeVideoPlayer {
    pipeline: Option<gst::Element>,
}

impl NativeVideoPlayer {
    fn new() -> Self { Self { pipeline: None } }

    pub fn reproducir(&mut self, ruta: &str, proj_weak: slint::Weak<ProjectorWindow>, is_loop: bool) {
        self.detener();
        let path = std::path::Path::new(ruta).canonicalize().unwrap_or_else(|_| std::path::PathBuf::from(ruta));
        let uri = gst::glib::filename_to_uri(&path, None).unwrap();
        let pipeline = gst::ElementFactory::make("playbin").property("uri", &uri).build().unwrap();
        let appsink = gst_app::AppSink::builder()
            .caps(&gst::Caps::builder("video/x-raw").field("format", "RGBA").build())
            .max_buffers(1).drop(true).build();
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
                let info = gst_video::VideoInfo::from_caps(sample.caps().unwrap()).unwrap();
                let map = buffer.map_readable().unwrap();
                let mut pixel_buffer = SharedPixelBuffer::<slint::Rgba8Pixel>::new(info.width(), info.height());
                unsafe {
                    let dest = pixel_buffer.make_mut_slice();
                    let dest_u8 = std::slice::from_raw_parts_mut(dest.as_mut_ptr() as *mut u8, dest.len() * 4);
                    dest_u8.copy_from_slice(map.as_slice());
                }
                let proj_clone = proj_weak.clone();
                let _ = slint::invoke_from_event_loop(move || {
                    if let Some(p) = proj_clone.upgrade() { p.set_fondo_video_frame(slint::Image::from_rgba8(pixel_buffer)); }
                });
                Ok(gst::FlowSuccess::Ok)
            }).build()
        );
        pipeline.set_state(gst::State::Playing).unwrap();
        self.pipeline = Some(pipeline.clone());
        let bus = pipeline.bus().unwrap();
        let pipeline_clone = pipeline.clone();
        std::thread::spawn(move || {
            for msg in bus.iter_timed(gst::ClockTime::NONE) {
                match msg.view() {
                    gst::MessageView::Eos(..) => {
                        if is_loop {
                            let _ = pipeline_clone.seek_simple(gst::SeekFlags::FLUSH | gst::SeekFlags::KEY_UNIT, gst::ClockTime::ZERO);
                            let _ = pipeline_clone.set_state(gst::State::Playing);
                        } else {
                            let _ = pipeline_clone.set_state(gst::State::Paused);
                        }
                    }
                    gst::MessageView::Error(err) => { println!("Error de reproducción: {}", err.error()); break; }
                    _ => {}
                }
            }
        });
    }

    fn detener(&mut self) {
        if let Some(pipeline) = self.pipeline.take() { let _ = pipeline.set_state(gst::State::Null); }
    }

    pub fn reproducir_preview(&mut self, ruta: &str, ui_weak: slint::Weak<AppWindow>) {
        self.detener();
        let path = std::path::Path::new(ruta).canonicalize().unwrap_or_else(|_| std::path::PathBuf::from(ruta));
        let uri = gst::glib::filename_to_uri(&path, None).unwrap();
        let pipeline = gst::ElementFactory::make("playbin").property("uri", &uri).build().unwrap();
        pipeline.set_property("volume", 0.0f64);
        let appsink = gst_app::AppSink::builder()
            .caps(&gst::Caps::builder("video/x-raw").field("format", "RGBA").build())
            .max_buffers(1).drop(true).build();
        appsink.set_property("sync", true);
        pipeline.set_property("video-sink", &appsink);
        appsink.set_callbacks(gst_app::AppSinkCallbacks::builder()
            .new_sample(move |appsink| {
                let sample = match appsink.pull_sample() { Ok(s) => s, Err(_) => return Ok(gst::FlowSuccess::Ok) };
                let buffer = sample.buffer().unwrap();
                let info = gst_video::VideoInfo::from_caps(sample.caps().unwrap()).unwrap();
                let map = buffer.map_readable().unwrap();
                let mut pixel_buffer = SharedPixelBuffer::<slint::Rgba8Pixel>::new(info.width(), info.height());
                unsafe {
                    let dest = pixel_buffer.make_mut_slice();
                    let dest_u8 = std::slice::from_raw_parts_mut(dest.as_mut_ptr() as *mut u8, dest.len() * 4);
                    dest_u8.copy_from_slice(map.as_slice());
                }
                let ui_clone = ui_weak.clone();
                let _ = slint::invoke_from_event_loop(move || {
                    if let Some(ui) = ui_clone.upgrade() { ui.set_preview_video_frame(slint::Image::from_rgba8(pixel_buffer)); }
                });
                Ok(gst::FlowSuccess::Ok)
            }).build()
        );
        pipeline.set_state(gst::State::Playing).unwrap();
        self.pipeline = Some(pipeline);
    }

    pub fn toggle_play_pause(&mut self) -> bool {
        if let Some(pipeline) = &self.pipeline {
            let (_, state, _) = pipeline.state(gst::ClockTime::NONE);
            if state == gst::State::Playing { pipeline.set_state(gst::State::Paused).unwrap(); return false; }
            else { pipeline.set_state(gst::State::Playing).unwrap(); return true; }
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
                    gst::ClockTime::from_nseconds(target_ns)
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

fn aplicar_estilos(ui: &AppWindow, p: &ProjectorWindow, vp: &Arc<Mutex<NativeVideoPlayer>>, modo: &str, forzar_reinicio_video: bool) {
    let is_biblia = modo == "biblias";
    let bg_type = if is_biblia { ui.get_biblias_bg_type() } else { ui.get_cantos_bg_type() };
    let font_color = if is_biblia { ui.get_biblias_font_color() } else { ui.get_cantos_font_color() };
    let opacity = if is_biblia { ui.get_biblias_fondo_opacity() } else { ui.get_cantos_fondo_opacity() };
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

struct MediaData {
    path: String, name: String, aspecto: String, is_loop: bool,
}

struct PdfData {
    name: String,
    thumb_path: String, // Ahora solo guardamos la ruta del archivo
    pages: Vec<String>,
}

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

    let current_biblia_libro = Arc::new(Mutex::new(-1i32));
    let current_biblia_capitulo = Arc::new(Mutex::new(-1i32));
    let segunda_pantalla: Arc<Mutex<Option<(i32, i32, u32, u32)>>> = Arc::new(Mutex::new(None));

    let state = Arc::new(Mutex::new(AppState::new()?));
    let ui = AppWindow::new()?;
    let proyector = ProjectorWindow::new()?;
    let video_player = Arc::new(Mutex::new(NativeVideoPlayer::new()));
    let multimedia_state = Arc::new(Mutex::new(Vec::<MediaData>::new()));
    let video_state = Arc::new(Mutex::new(Vec::<MediaData>::new()));
    let preview_player = Arc::new(Mutex::new(NativeVideoPlayer::new()));
    let pdf_state = Arc::new(Mutex::new(Vec::<PdfData>::new()));

    {
        match DisplayInfo::all() {
            Ok(pantallas) => {
                let pantallas: Vec<DisplayInfo> = pantallas;
                let hay_primaria_marcada = pantallas.iter().any(|d| d.is_primary);
                let segunda = if hay_primaria_marcada {
                    pantallas.iter().find(|d| !d.is_primary)
                } else {
                    pantallas.iter().find(|d| !(d.x == 0 && d.y == 0))
                };
                if let Some(segunda) = segunda {
                    let w = (segunda.width as f32 * segunda.scale_factor) as u32;
                    let h = (segunda.height as f32 * segunda.scale_factor) as u32;
                    *segunda_pantalla.lock().unwrap() = Some((segunda.x, segunda.y, w, h));
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
        // ── font_size calculado por estrofa con diapositiva_a_ui ──
        let diapos_slint: Vec<DiapositivaUI> = estado.get_canto_diapositivas(id)
            .iter().map(diapositiva_a_ui).collect();
        ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos_slint))));
        ui.set_active_estrofa_index(-1);
        ui.invoke_focus_panel();
    });

    let state_clone = Arc::clone(&state);
    let state_clone2 = Arc::clone(&state);
    let c_clone = cargar_cantos.clone();
    let ui_handle_guardar = ui.as_weak();
    let proyector_handle_guardar = proyector.as_weak();

    ui.on_guardar_canto(move |id, titulo, letra| {
        {
            let estado = state_clone.lock().unwrap();
            if id == -1 { estado.add_canto(&titulo, &letra); } else { estado.update_canto(id, &titulo, &letra); }
        }
        c_clone(String::new());
        if id != -1 {
            let ui = ui_handle_guardar.unwrap();
            let p = proyector_handle_guardar.unwrap();
            let estado = state_clone2.lock().unwrap();
            let titulo_guardado = estado.get_canto_titulo(id);
            let titulo_en_panel = ui.get_elemento_seleccionado().to_string();
            let es_canto_activo = titulo_en_panel == titulo.to_string() || titulo_en_panel == titulo_guardado;
            if es_canto_activo {
                let nuevas_diapos = estado.get_canto_diapositivas(id);
                // ── font_size calculado ──
                let diapos_slint: Vec<DiapositivaUI> = nuevas_diapos.iter().map(diapositiva_a_ui).collect();
                let active_idx = ui.get_active_estrofa_index();
                ui.set_elemento_seleccionado(SharedString::from(&titulo_guardado));
                ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos_slint.clone()))));
                let idx_a_proyectar = if active_idx >= 0 && (active_idx as usize) < diapos_slint.len() {
                    active_idx as usize
                } else if !diapos_slint.is_empty() {
                    ui.set_active_estrofa_index(0); 0
                } else { return; };
                let texto_nuevo = diapos_slint[idx_a_proyectar].texto.clone();
                let font_size = calcular_font_size(&texto_nuevo, false, 1920.0, 1080.0);
                p.set_texto_proyeccion(texto_nuevo);
                p.set_tamano_letra(font_size);
                p.set_referencia(SharedString::from(""));
            }
        }
    });

    let state_clone = Arc::clone(&state);
    let c_clone = cargar_cantos.clone();
    ui.on_eliminar_canto(move |id| { state_clone.lock().unwrap().delete_canto(id); c_clone(String::new()); });

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

    let proyector_handle = proyector.as_weak();
    let segunda_pantalla_clone = Arc::clone(&segunda_pantalla);
    ui.on_abrir_proyector(move || {
        let p = proyector_handle.unwrap();
        let info = *segunda_pantalla_clone.lock().unwrap();
        if let Some((x, y, width, height)) = info {
            p.show().unwrap();
            mover_proyector_a_pantalla(p.as_weak(), x, y, width, height);
        } else {
            p.show().unwrap();
            let p_weak = p.as_weak();
            thread::spawn(move || {
                thread::sleep(std::time::Duration::from_millis(100));
                let _ = slint::invoke_from_event_loop(move || {
                    if let Some(p) = p_weak.upgrade() { p.window().set_fullscreen(true); }
                });
            });
        }
    });

    let proyector_handle = proyector.as_weak();
    let state_clone = Arc::clone(&state);
    let ui_h_proy = ui.as_weak();
    let vp_proy = Arc::clone(&video_player);
    let last_modo = Arc::new(Mutex::new(String::new()));
    let segunda_pantalla_proy = Arc::clone(&segunda_pantalla);

    ui.on_proyectar_estrofa(move |texto, referencia| {
        let p = proyector_handle.unwrap();
        let ui = ui_h_proy.unwrap();
        p.set_texto_proyeccion(texto.clone());
        let mut ref_str = referencia.to_string();
        if !ref_str.is_empty() {
            let sigla = state_clone.lock().unwrap().get_sigla_actual();
            if !sigla.is_empty() { ref_str = format!("{}  |  {}", ref_str, sigla); }
        }
        p.set_referencia(SharedString::from(ref_str.clone()));
        let tiene_referencia = !ref_str.is_empty();
        let info = *segunda_pantalla_proy.lock().unwrap();
        let (screen_w, screen_h) = if let Some((_, _, w, h)) = info { (w as f32, h as f32) } else { (1280.0, 720.0) };
        let base_font_size = calcular_font_size(&texto, tiene_referencia, screen_w, screen_h);
        // Aplicar escala del usuario (cantos o biblias según modo)
        let scale = if tiene_referencia { ui.get_biblias_font_scale() } else { ui.get_cantos_font_scale() };
        let font_size = base_font_size * scale;
        p.set_tamano_letra(font_size);
        let modo_actual = if tiene_referencia { "biblias" } else { "cantos" };
        let mut l_modo = last_modo.lock().unwrap();
        let forzar_video = *l_modo != modo_actual;
        *l_modo = modo_actual.to_string();
        aplicar_estilos(&ui, &p, &vp_proy, modo_actual, forzar_video);
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
                // ── font_size calculado por versículo ──
                let diapos: Vec<DiapositivaUI> = versiculos.iter().map(versiculo_a_ui).collect();
                ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
                ui.set_active_estrofa_index(0);
                if !diapos.is_empty() {
                    ui.invoke_proyectar_estrofa(diapos[0].texto.clone(), SharedString::from(format!("{}:{}", titulo, diapos[0].orden)));
                }
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
                        // ── font_size calculado por versículo ──
                        let diapos: Vec<DiapositivaUI> = versiculos.iter().enumerate().map(|(i, v)| {
                            if v.versiculo == versiculo_obj { target_index = i as i32; }
                            versiculo_a_ui(v)
                        }).collect();
                        ui.set_estrofas_actuales(ModelRc::from(Rc::new(VecModel::from(diapos.clone()))));
                        ui.set_active_estrofa_index(target_index);
                        ui.set_scroll_to_y(-((target_index as f32) * 115.0));
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
            // ── font_size calculado ──
            let diapos: Vec<DiapositivaUI> = versiculos_nuevos.iter().map(versiculo_a_ui).collect();
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
    let vp_sync = Arc::clone(&video_player);
    let segunda_pantalla_sync = Arc::clone(&segunda_pantalla);
    ui.on_sync_estilos(move || {
        let ui = ui_h_sync.unwrap();
        let p = p_h_sync.unwrap();
        let modo = ui.get_modal_tab();
        aplicar_estilos(&ui, &p, &vp_sync, modo.as_str(), true);

        // Re-aplicar font size con el nuevo scale al slide activo
        let active_idx = ui.get_active_estrofa_index();
        if active_idx >= 0 {
            let estrofas = ui.get_estrofas_actuales();
            let idx = active_idx as usize;
            if idx < estrofas.row_count() {
                if let Some(d) = estrofas.row_data(idx) {
                    let texto = d.texto.to_string();
                    let referencia = p.get_referencia().to_string();
                    let tiene_ref = !referencia.is_empty();
                    let info = *segunda_pantalla_sync.lock().unwrap();
                    let (sw, sh) = if let Some((_, _, w, h)) = info { (w as f32, h as f32) } else { (1280.0, 720.0) };
                    let scale = if modo == "biblias" { ui.get_biblias_font_scale() } else { ui.get_cantos_font_scale() };
                    let font_size = calcular_font_size(&texto, tiene_ref, sw, sh) * scale;
                    p.set_tamano_letra(font_size);
                }
            }
        }
    });

    // ── Cambia SOLO el tamaño de letra sin tocar fondos ni imágenes ──
    let ui_h_fs = ui.as_weak();
    let p_h_fs = proyector.as_weak();
    let segunda_pantalla_fs = Arc::clone(&segunda_pantalla);
    ui.on_sync_font_scale(move || {
        let ui = ui_h_fs.unwrap();
        let p = p_h_fs.unwrap();
        let active_idx = ui.get_active_estrofa_index();
        if active_idx < 0 { return; }
        let estrofas = ui.get_estrofas_actuales();
        let idx = active_idx as usize;
        if idx >= estrofas.row_count() { return; }
        if let Some(d) = estrofas.row_data(idx) {
            let texto = d.texto.to_string();
            let referencia = p.get_referencia().to_string();
            let tiene_ref = !referencia.is_empty();
            let info = *segunda_pantalla_fs.lock().unwrap();
            let (sw, sh) = if let Some((_, _, w, h)) = info { (w as f32, h as f32) } else { (1280.0, 720.0) };
            let modo = ui.get_modal_tab();
            let scale = if modo == "biblias" { ui.get_biblias_font_scale() } else { ui.get_cantos_font_scale() };
            let font_size = calcular_font_size(&texto, tiene_ref, sw, sh) * scale;
            p.set_tamano_letra(font_size);
        }
    });

    let ui_h_gal = ui.as_weak();
    let state_gal = Arc::clone(&state);
    ui.on_agregar_a_galeria(move |tipo| {
        let ui = ui_h_gal.unwrap();
        let tipo_str = tipo.to_string();
        let es_video = tipo_str.ends_with("-vid");
        let dialog = if es_video {
            rfd::FileDialog::new().add_filter("Videos", &["mp4", "mov", "mkv", "webm"]).pick_file()
        } else {
            rfd::FileDialog::new().add_filter("Imágenes", &["png", "jpg", "jpeg", "webp"]).pick_file()
        };
        if let Some(path) = dialog {
            let path_str = path.to_string_lossy().to_string();
            let mut estado = state_gal.lock().unwrap();
            if tipo_str == "biblias-img" {
                if let Ok(img) = slint::Image::load_from_path(&path) {
                    estado.biblias_image_paths.push(path_str.clone());
                    let idx = estado.biblias_image_paths.len() as i32 - 1;
                    let paths_copia: Vec<String> = estado.biblias_image_paths.clone();
                    drop(estado);
                    let images: Vec<slint::Image> = paths_copia.iter().filter_map(|p| slint::Image::load_from_path(std::path::Path::new(p)).ok()).collect();
                    ui.set_biblias_image_data(ModelRc::from(Rc::new(VecModel::from(images))));
                    ui.set_biblias_selected_img(idx);
                    ui.set_biblias_bg_image(img);
                    ui.set_biblias_has_image(true);
                    ui.set_biblias_bg_type(SharedString::from("imagen"));
                    ui.invoke_sync_estilos();
                }
            } else if tipo_str == "cantos-img" {
                if let Ok(img) = slint::Image::load_from_path(&path) {
                    estado.cantos_image_paths.push(path_str.clone());
                    let idx = estado.cantos_image_paths.len() as i32 - 1;
                    let paths_copia: Vec<String> = estado.cantos_image_paths.clone();
                    drop(estado);
                    let images: Vec<slint::Image> = paths_copia.iter().filter_map(|p| slint::Image::load_from_path(std::path::Path::new(p)).ok()).collect();
                    ui.set_cantos_image_data(ModelRc::from(Rc::new(VecModel::from(images))));
                    ui.set_cantos_selected_img(idx);
                    ui.set_cantos_bg_image(img);
                    ui.set_cantos_has_image(true);
                    ui.set_cantos_bg_type(SharedString::from("imagen"));
                    ui.invoke_sync_estilos();
                }
            } else if tipo_str == "biblias-vid" {
                estado.biblias_video_paths.push(path_str.clone());
                let names: Vec<SharedString> = estado.biblias_video_paths.iter().map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap().to_string_lossy().to_string())).collect();
                let idx = estado.biblias_video_paths.len() as i32 - 1;
                drop(estado);
                ui.set_biblias_video_names(ModelRc::from(Rc::new(VecModel::from(names))));
                ui.set_biblias_selected_vid(idx);
                ui.set_biblias_video_path(SharedString::from(&path_str));
                ui.set_biblias_bg_type(SharedString::from("video"));
                ui.invoke_sync_estilos();
            } else if tipo_str == "cantos-vid" {
                estado.cantos_video_paths.push(path_str.clone());
                let names: Vec<SharedString> = estado.cantos_video_paths.iter().map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap().to_string_lossy().to_string())).collect();
                let idx = estado.cantos_video_paths.len() as i32 - 1;
                drop(estado);
                ui.set_cantos_video_names(ModelRc::from(Rc::new(VecModel::from(names))));
                ui.set_cantos_selected_vid(idx);
                ui.set_cantos_video_path(SharedString::from(&path_str));
                ui.set_cantos_bg_type(SharedString::from("video"));
                ui.invoke_sync_estilos();
            }
        }
    });

    let ui_h_sel = ui.as_weak();
    let state_sel = Arc::clone(&state);
    ui.on_seleccionar_galeria_item(move |tipo, idx| {
        let ui = ui_h_sel.unwrap();
        let estado = state_sel.lock().unwrap();
        let tipo_str = tipo.to_string();
        let idx_usize = idx as usize;
        if tipo_str == "biblias-img" {
            if let Some(p) = estado.biblias_image_paths.get(idx_usize) {
                if let Ok(img) = slint::Image::load_from_path(std::path::Path::new(p)) {
                    ui.set_biblias_selected_img(idx); ui.set_biblias_bg_image(img);
                    ui.set_biblias_has_image(true); ui.set_biblias_bg_type(SharedString::from("imagen"));
                    ui.invoke_sync_estilos();
                }
            }
        } else if tipo_str == "cantos-img" {
            if let Some(p) = estado.cantos_image_paths.get(idx_usize) {
                if let Ok(img) = slint::Image::load_from_path(std::path::Path::new(p)) {
                    ui.set_cantos_selected_img(idx); ui.set_cantos_bg_image(img);
                    ui.set_cantos_has_image(true); ui.set_cantos_bg_type(SharedString::from("imagen"));
                    ui.invoke_sync_estilos();
                }
            }
        } else if tipo_str == "biblias-vid" {
            if let Some(p) = estado.biblias_video_paths.get(idx_usize) {
                ui.set_biblias_selected_vid(idx); ui.set_biblias_video_path(SharedString::from(p.as_str()));
                ui.set_biblias_bg_type(SharedString::from("video")); ui.invoke_sync_estilos();
            }
        } else if tipo_str == "cantos-vid" {
            if let Some(p) = estado.cantos_video_paths.get(idx_usize) {
                ui.set_cantos_selected_vid(idx); ui.set_cantos_video_path(SharedString::from(p.as_str()));
                ui.set_cantos_bg_type(SharedString::from("video")); ui.invoke_sync_estilos();
            }
        }
    });

    let ui_h_del = ui.as_weak();
    let state_del = Arc::clone(&state);
    ui.on_eliminar_galeria_item(move |tipo, idx| {
        let ui = ui_h_del.unwrap();
        let mut estado = state_del.lock().unwrap();
        let tipo_str = tipo.to_string();
        let idx_usize = idx as usize;
        if tipo_str == "biblias-img" && idx_usize < estado.biblias_image_paths.len() {
            estado.biblias_image_paths.remove(idx_usize);
            if estado.biblias_image_paths.is_empty() {
                drop(estado);
                ui.set_biblias_image_data(ModelRc::from(Rc::new(VecModel::<slint::Image>::from(vec![]))));
                ui.set_biblias_has_image(false); ui.set_biblias_bg_type(SharedString::from("negro"));
                ui.invoke_sync_estilos();
            } else {
                let paths: Vec<slint::Image> = estado.biblias_image_paths.iter().filter_map(|p| slint::Image::load_from_path(std::path::Path::new(p)).ok()).collect();
                drop(estado);
                ui.set_biblias_image_data(ModelRc::from(Rc::new(VecModel::from(paths))));
                ui.set_biblias_selected_img(0); ui.invoke_seleccionar_galeria_item(SharedString::from("biblias-img"), 0);
            }
        } else if tipo_str == "cantos-img" && idx_usize < estado.cantos_image_paths.len() {
            estado.cantos_image_paths.remove(idx_usize);
            if estado.cantos_image_paths.is_empty() {
                drop(estado);
                ui.set_cantos_image_data(ModelRc::from(Rc::new(VecModel::<slint::Image>::from(vec![]))));
                ui.set_cantos_has_image(false); ui.set_cantos_bg_type(SharedString::from("negro"));
                ui.invoke_sync_estilos();
            } else {
                let paths: Vec<slint::Image> = estado.cantos_image_paths.iter().filter_map(|p| slint::Image::load_from_path(std::path::Path::new(p)).ok()).collect();
                drop(estado);
                ui.set_cantos_image_data(ModelRc::from(Rc::new(VecModel::from(paths))));
                ui.set_cantos_selected_img(0); ui.invoke_seleccionar_galeria_item(SharedString::from("cantos-img"), 0);
            }
        } else if tipo_str == "biblias-vid" && idx_usize < estado.biblias_video_paths.len() {
            estado.biblias_video_paths.remove(idx_usize);
            let names: Vec<SharedString> = estado.biblias_video_paths.iter().map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap().to_string_lossy().to_string())).collect();
            let is_empty = estado.biblias_video_paths.is_empty(); drop(estado);
            ui.set_biblias_video_names(ModelRc::from(Rc::new(VecModel::from(names))));
            if is_empty { ui.set_biblias_bg_type(SharedString::from("negro")); ui.invoke_sync_estilos(); }
        } else if tipo_str == "cantos-vid" && idx_usize < estado.cantos_video_paths.len() {
            estado.cantos_video_paths.remove(idx_usize);
            let names: Vec<SharedString> = estado.cantos_video_paths.iter().map(|p| SharedString::from(std::path::Path::new(p).file_name().unwrap().to_string_lossy().to_string())).collect();
            let is_empty = estado.cantos_video_paths.is_empty(); drop(estado);
            ui.set_cantos_video_names(ModelRc::from(Rc::new(VecModel::from(names))));
            if is_empty { ui.set_cantos_bg_type(SharedString::from("negro")); ui.invoke_sync_estilos(); }
        }
    });

    let refresh_multimedia = {
        let ui_handle = ui.as_weak();
        let state_arc = Arc::clone(&multimedia_state);
        move || {
            let ui = ui_handle.unwrap();
            let items = state_arc.lock().unwrap();
            let mut slint_items = Vec::new();
            for (i, item) in items.iter().enumerate() {
                if let Ok(img) = slint::Image::load_from_path(std::path::Path::new(&item.path)) {
                    slint_items.push(MediaItem { id: i as i32, nombre: SharedString::from(&item.name), path: SharedString::from(&item.path), img, aspecto: SharedString::from(&item.aspecto), is_loop: false });
                }
            }
            ui.set_multimedia_items(ModelRc::from(Rc::new(VecModel::from(slint_items))));
        }
    };

    let multi_state = Arc::clone(&multimedia_state);
    let refresh_clone = refresh_multimedia.clone();
    ui.on_agregar_multimedia(move || {
        if let Some(path) = rfd::FileDialog::new().add_filter("Imágenes", &["png", "jpg", "jpeg", "webp"]).pick_file() {
            let file_name = path.file_name().unwrap_or_default().to_string_lossy().to_string();
            let path_str = path.to_string_lossy().to_string();
            multi_state.lock().unwrap().push(MediaData { path: path_str, name: file_name, aspecto: "centro".to_string(), is_loop: false });
            refresh_clone();
        }
    });

    let multi_state = Arc::clone(&multimedia_state);
    let refresh_clone = refresh_multimedia.clone();
    ui.on_cambiar_aspecto_multimedia(move |idx, aspecto| {
        let mut state = multi_state.lock().unwrap();
        if let Some(item) = state.get_mut(idx as usize) { item.aspecto = aspecto.to_string(); }
        drop(state); refresh_clone();
    });

    let multi_state = Arc::clone(&multimedia_state);
    let refresh_clone = refresh_multimedia.clone();
    let ui_handle = ui.as_weak();
    ui.on_eliminar_multimedia(move |idx| {
        let mut state = multi_state.lock().unwrap();
        if (idx as usize) < state.len() { state.remove(idx as usize); }
        drop(state);
        let ui = ui_handle.unwrap();
        ui.set_selected_media_idx(-1); refresh_clone();
    });

    let p_handle = proyector.as_weak();
    let multi_state = Arc::clone(&multimedia_state);
    let vp_sync = Arc::clone(&video_player);
    ui.on_proyectar_multimedia(move |idx| {
        let p = p_handle.unwrap();
        let state = multi_state.lock().unwrap();
        if let Some(item) = state.get(idx as usize) {
            if let Ok(img) = slint::Image::load_from_path(std::path::Path::new(&item.path)) {
                vp_sync.lock().unwrap().detener();
                p.set_es_video(false); p.set_bg_color(slint::Color::from_rgb_u8(0, 0, 0));
                p.set_texto_proyeccion(slint::SharedString::from(""));
                p.set_referencia(slint::SharedString::from(""));
                p.set_fondo_opacity(0.0);
                p.set_fondo_imagen_aspecto(slint::SharedString::from(&item.aspecto));
                p.set_fondo_imagen(img); p.set_mostrar_imagen(true);
            }
        }
    });

    let refresh_videos = {
        let ui_handle = ui.as_weak();
        let state_arc = Arc::clone(&video_state);
        move || {
            let ui = ui_handle.unwrap();
            let items = state_arc.lock().unwrap();
            let mut slint_items = Vec::new();
            for (i, item) in items.iter().enumerate() {
                let pixel_buffer = SharedPixelBuffer::<slint::Rgba8Pixel>::new(80, 45);
                let img = slint::Image::from_rgba8(pixel_buffer);
                slint_items.push(MediaItem { id: i as i32, nombre: SharedString::from(&item.name), path: SharedString::from(&item.path), img, aspecto: SharedString::from("rellenar"), is_loop: item.is_loop });
            }
            ui.set_video_items(ModelRc::from(Rc::new(VecModel::from(slint_items))));
        }
    };

    let vid_state = Arc::clone(&video_state);
    let refresh_vid_clone = refresh_videos.clone();
    ui.on_agregar_video(move || {
        if let Some(path) = rfd::FileDialog::new().add_filter("Videos", &["mp4", "mkv", "avi", "mov"]).pick_file() {
            let file_name = path.file_name().unwrap_or_default().to_string_lossy().to_string();
            vid_state.lock().unwrap().push(MediaData { path: path.to_string_lossy().to_string(), name: file_name, aspecto: "rellenar".to_string(), is_loop: false });
            refresh_vid_clone();
        }
    });

    let vid_state = Arc::clone(&video_state);
    let refresh_vid_clone = refresh_videos.clone();
    let ui_handle = ui.as_weak();
    let preview_player_del = Arc::clone(&preview_player);
    ui.on_eliminar_video(move |idx| {
        let mut state = vid_state.lock().unwrap();
        if (idx as usize) < state.len() { state.remove(idx as usize); }
        drop(state);
        let ui = ui_handle.unwrap();
        ui.set_selected_video_idx(-1);
        preview_player_del.lock().unwrap().detener();
        refresh_vid_clone();
    });

    let ui_handle_sel = ui.as_weak();
    let preview_player_sel = Arc::clone(&preview_player);
    ui.on_seleccionar_video_lista(move |idx| {
        let ui = ui_handle_sel.unwrap();
        ui.set_selected_video_idx(idx);
        preview_player_sel.lock().unwrap().detener();
        ui.set_is_preview_playing(false);
        ui.set_preview_video_frame(slint::Image::default());
        ui.set_is_video_projecting(false);
    });

    let vid_state = Arc::clone(&video_state);
    let ui_handle = ui.as_weak();
    let preview_player_clone = Arc::clone(&preview_player);
    ui.on_toggle_preview_video(move |idx| {
        let ui = ui_handle.unwrap();
        let state = vid_state.lock().unwrap();
        if let Some(item) = state.get(idx as usize) {
            let mut player = preview_player_clone.lock().unwrap();
            let is_playing = ui.get_is_preview_playing();
            if !is_playing { player.reproducir_preview(&item.path, ui.as_weak()); ui.set_is_preview_playing(true); }
            else { player.detener(); ui.set_is_preview_playing(false); }
        }
    });

    let p_handle = proyector.as_weak();
    let vid_state = Arc::clone(&video_state);
    let vp_sync = Arc::clone(&video_player);
    let ui_handle_proj = ui.as_weak();
    ui.on_proyectar_video(move |idx| {
        let p = p_handle.unwrap();
        let ui = ui_handle_proj.unwrap();
        let state = vid_state.lock().unwrap();
        if let Some(item) = state.get(idx as usize) {
            p.set_es_video(true); 
            p.set_bg_color(slint::Color::from_rgb_u8(0, 0, 0));
            p.set_mostrar_imagen(false); 
            
            
            p.set_texto_proyeccion(slint::SharedString::from(""));
            p.set_referencia(slint::SharedString::from(""));
            
            vp_sync.lock().unwrap().reproducir(&item.path, p.as_weak(), item.is_loop);
            ui.set_is_video_projecting(true); 
            ui.set_is_proyector_playing(true);
        }
    });

    let vp_controls = Arc::clone(&video_player);
    let ui_handle_ctrl = ui.as_weak();
    ui.on_toggle_proyector_play(move || {
        let ui = ui_handle_ctrl.unwrap();
        let mut player = vp_controls.lock().unwrap();
        let is_playing = player.toggle_play_pause();
        ui.set_is_proyector_playing(is_playing);
    });

    let vp_mute = Arc::clone(&video_player);
    let ui_handle_mute = ui.as_weak();
    ui.on_toggle_proyector_mute(move || {
        let ui = ui_handle_mute.unwrap();
        let is_currently_muted = ui.get_is_proyector_muted();
        let new_mute_state = !is_currently_muted;
        vp_mute.lock().unwrap().set_mute(new_mute_state);
        ui.set_is_proyector_muted(new_mute_state);
    });

    let vp_seek = Arc::clone(&video_player);
    ui.on_seek_proyector_video(move |percent| { vp_seek.lock().unwrap().seek_percentage(percent); });

    let vp_timer = Arc::clone(&video_player);
    let ui_timer_handle = ui.as_weak();
    let video_timer = Box::leak(Box::new(slint::Timer::default()));
    video_timer.start(slint::TimerMode::Repeated, std::time::Duration::from_millis(500), move || {
        if let Some(ui) = ui_timer_handle.upgrade() {
            if ui.get_is_video_projecting() {
                let (pos_ms, dur_ms) = vp_timer.lock().unwrap().get_position_and_duration();
                if dur_ms > 0 {
                    let progress = (pos_ms as f32) / (dur_ms as f32);
                    ui.set_proyector_progress(progress);
                    let pos_sec = pos_ms / 1000; let dur_sec = dur_ms / 1000;
                    let time_str = format!("{:02}:{:02} / {:02}:{:02}", pos_sec / 60, pos_sec % 60, dur_sec / 60, dur_sec % 60);
                    ui.set_proyector_time(slint::SharedString::from(time_str));
                }
            }
        }
    });

    let vid_state_mode = Arc::clone(&video_state);
    let refresh_vid_mode = refresh_videos.clone();
    ui.on_cambiar_modo_reproduccion(move |idx, modo| {
        let mut state = vid_state_mode.lock().unwrap();
        if let Some(item) = state.get_mut(idx as usize) { item.is_loop = modo == "bucle"; }
        drop(state); refresh_vid_mode();
    });

    // ── LÓGICA DE IMPORTACIÓN PDF ──
    let ui_pdf_add = ui.as_weak();
    let state_pdf_add = Arc::clone(&pdf_state);
    ui.on_agregar_pdf(move || {
        if let Some(path) = rfd::FileDialog::new().add_filter("PDF", &["pdf"]).pick_file() {
            let ui = ui_pdf_add.unwrap();
            let file_name = path.file_name().unwrap_or_default().to_string_lossy().to_string();
            
            ui.set_is_importing_pdf(true);
            ui.set_pdf_import_progress(0.0);
            ui.set_pdf_import_filename(SharedString::from(&file_name));

            let ui_thread = ui.as_weak();
            let state_thread = Arc::clone(&state_pdf_add);
            let path_clone = path.clone();

            thread::spawn(move || {
                // Configurar Pdfium buscando la DLL en la raíz (donde está el .exe)
                let bind = Pdfium::bind_to_library(Pdfium::pdfium_platform_library_name_at_path("./")).unwrap();
                let pdfium = Pdfium::new(bind);
                
                if let Ok(document) = pdfium.load_pdf_from_file(&path_clone, None) {
                    let total_pages = document.pages().len();
                    
                    // Crear carpeta en data/pdfs/ para guardar las imágenes extraídas
                    let safe_name = file_name.replace(" ", "_").replace(".pdf", "");
                    let out_dir = PathBuf::from(format!("data/pdfs/{}", safe_name));
                    let _ = fs::create_dir_all(&out_dir);

                    let mut saved_pages_paths = Vec::new();
                    let mut thumb_path_str = String::new(); // Guardaremos la ruta aquí

                    for (i, page) in document.pages().iter().enumerate() {
                        let config = PdfRenderConfig::new().set_target_width(1920);
                        if let Ok(bitmap) = page.render_with_config(&config) {
                            let img = bitmap.as_image();
                            let page_path = out_dir.join(format!("page_{}.jpg", i));
                            
                            // Guardar la página en disco
                            let _ = img.save(&page_path);
                            saved_pages_paths.push(page_path.to_string_lossy().to_string());

                            // Guardar la miniatura como archivo 'thumb.jpg' en lugar de memoria
                            if i == 0 {
                                let thumb_config = PdfRenderConfig::new().thumbnail(200);
                                if let Ok(thumb_bitmap) = page.render_with_config(&thumb_config) {
                                    let t_path = out_dir.join("thumb.jpg");
                                    let _ = thumb_bitmap.as_image().save(&t_path);
                                    thumb_path_str = t_path.to_string_lossy().to_string();
                                }
                            }
                        }

                        // Actualizar barra de progreso
                        let progress = (i as f32 + 1.0) / total_pages as f32;
                        let ui_prog = ui_thread.clone();
                        let _ = slint::invoke_from_event_loop(move || {
                            if let Some(ui) = ui_prog.upgrade() { ui.set_pdf_import_progress(progress); }
                        });
                    }

                    // Guardar en la memoria global (Solo Strings, 100% seguro entre hilos)
                    let mut st = state_thread.lock().unwrap();
                    st.push(PdfData {
                        name: file_name.clone(),
                        thumb_path: thumb_path_str,
                        pages: saved_pages_paths,
                    });
                }

                // Finalizar actualización en la Interfaz
                let ui_fin = ui_thread.clone();
                let state_fin = Arc::clone(&state_thread);
                let _ = slint::invoke_from_event_loop(move || {
                    if let Some(ui) = ui_fin.upgrade() {
                        ui.set_is_importing_pdf(false);
                        
                        // Refrescar lista lateral cargando la imagen directamente en el hilo principal
                        let items = state_fin.lock().unwrap();
                        let mut slint_items = Vec::new();
                        for (i, item) in items.iter().enumerate() {
                            let img = slint::Image::load_from_path(std::path::Path::new(&item.thumb_path)).unwrap_or_default();
                            slint_items.push(PdfItem {
                                id: i as i32,
                                nombre: SharedString::from(&item.name),
                                miniatura: img,
                                total_paginas: item.pages.len() as i32
                            });
                        }
                        ui.set_pdf_items(ModelRc::from(Rc::new(VecModel::from(slint_items))));
                    }
                });
            });

    // ── MOSTRAR PÁGINAS DEL PDF SELECCIONADO ──
    let ui_pdf_sel = ui.as_weak();
    let state_pdf_sel = Arc::clone(&pdf_state);
    ui.on_seleccionar_pdf(move |idx| {
        let ui = ui_pdf_sel.unwrap();
        ui.set_selected_pdf_idx(idx);
        ui.set_active_pdf_page(-1); // Reset
        
        let state = state_pdf_sel.lock().unwrap();
        if let Some(pdf) = state.get(idx as usize) {
            ui.set_elemento_seleccionado(SharedString::from(&pdf.name));
            
            // Cargar imágenes de la carpeta
            let mut pages_img = Vec::new();
            for path in &pdf.pages {
                if let Ok(img) = slint::Image::load_from_path(std::path::Path::new(path)) {
                    pages_img.push(img);
                }
            }
            ui.set_pdf_pages(ModelRc::from(Rc::new(VecModel::from(pages_img))));
        }
    });

    // ── PROYECTAR PÁGINA DEL PDF ──
    let ui_pdf_proj = ui.as_weak();
    let p_handle_pdf = proyector.as_weak();
    let vp_pdf = Arc::clone(&video_player);
    ui.on_proyectar_pdf_pagina(move |page_idx| {
        let ui = ui_pdf_proj.unwrap();
        let p = p_handle_pdf.unwrap();
        ui.set_active_pdf_page(page_idx);

        let current_pages = ui.get_pdf_pages();
        if let Some(img) = current_pages.row_data(page_idx as usize) {
            // Reutilizamos la lógica del proyector para imágenes
            vp_pdf.lock().unwrap().detener();
            p.set_es_video(false);
            p.set_bg_color(slint::Color::from_rgb_u8(0, 0, 0));
            p.set_texto_proyeccion(slint::SharedString::from(""));
            p.set_referencia(slint::SharedString::from(""));
            p.set_fondo_opacity(0.0);
            p.set_fondo_imagen_aspecto(slint::SharedString::from("contain")); // Importante para PDF
            p.set_fondo_imagen(img);
            p.set_mostrar_imagen(true);
        }
    });

    // ── ELIMINAR PDF DE LA LISTA ──
    let ui_pdf_del = ui.as_weak();
    let state_pdf_del = Arc::clone(&pdf_state);
    ui.on_eliminar_pdf(move |idx| {
        let ui = ui_pdf_del.unwrap();
        let mut state = state_pdf_del.lock().unwrap();
        if (idx as usize) < state.len() {
            state.remove(idx as usize);
        }
        
        ui.set_selected_pdf_idx(-1);
        ui.set_pdf_pages(ModelRc::from(Rc::new(VecModel::<slint::Image>::from(vec![]))));
        ui.set_elemento_seleccionado(SharedString::from(""));
        
        // Refrescar lista
        let mut slint_items = Vec::new();
        for (i, item) in state.iter().enumerate() {
            let img = slint::Image::load_from_path(std::path::Path::new(&item.thumb_path)).unwrap_or_default();
            slint_items.push(PdfItem { 
                id: i as i32, 
                nombre: SharedString::from(&item.name), 
                miniatura: img, 
                total_paginas: item.pages.len() as i32 
            });
        }
        ui.set_pdf_items(ModelRc::from(Rc::new(VecModel::from(slint_items))));
    });

    } // <-- ESTA LLAVE CIERRA EL 'if let Some(path)...'
    });
    ui.run()?;
    Ok(())
}