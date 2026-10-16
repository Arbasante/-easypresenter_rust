use std::io::{self, Read, Seek, SeekFrom};
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc, Mutex,
};
use std::thread::{self, JoinHandle};
use std::time::Duration;
use tiny_http::{Header, Method, Request, Response, Server, StatusCode};

#[derive(Clone, Default, serde::Serialize)]
pub struct EstadoOverlay {
    pub session_id: String,
    pub texto: String,
    pub referencia: String,
    pub color_texto: String,  // hex "#rrggbb"
    pub fondo_tipo: String,   // "color" | "imagen" | "video" | "transparente"
    pub fondo_color: String,  // hex, usado si fondo_tipo == "color"
    pub fondo_opacity: f32,   // scrim oscuro sobre la imagen (0.0-1.0)
    pub fondo_ajuste: String, // "cover" | "contain" | "fill"
    #[serde(skip)]
    pub fondo_imagen_bytes: Arc<[u8]>, // bytes crudos del archivo (jpg/png/webp)
    #[serde(skip)]
    pub fondo_imagen_content_type: String, // "image/jpeg", "image/png", etc.
    pub fondo_version: u64,   // se incrementa cada vez que cambia la imagen

    // ── Video con audio para OBS ──────────────────────────────────────
    // No transcodificamos nada: el navegador de OBS (Chromium) descarga
    // y decodifica el archivo original vía <video>, igual que en una
    // pestaña normal. Cero costo extra de CPU en esta app.
    pub video_activo: bool,
    #[serde(skip)]
    pub video_ruta: String, // ruta local del archivo en disco (solo servidor)
    #[serde(skip)]
    pub fondo_video_ruta: String,
    pub fondo_video_token: u64,
    pub video_pausado: bool,
    pub video_silenciado: bool,
    pub video_posicion: f64,
    pub video_loop: bool,
    pub video_token: u64, // se incrementa cada vez que cambia el video, para forzar reload
}

pub struct ServerHandle {
    server: Arc<Server>,
    active: Arc<AtomicBool>,
    dispatcher: Option<JoinHandle<()>>,
}

impl ServerHandle {
    pub fn start(port: u16, state: Arc<Mutex<EstadoOverlay>>) -> Result<Self, String> {
        // Bind before reporting success to the UI. Each run owns its own stop flag.
        // tiny_http closes its accept socket asynchronously on Drop. Allow that
        // brief close to finish when the user immediately restarts the server.
        let deadline = std::time::Instant::now() + Duration::from_millis(250);
        let server = loop {
            match Server::http(("0.0.0.0", port)) {
                Ok(server) => break Arc::new(server),
                Err(error) => {
                    let closing = error
                        .downcast_ref::<io::Error>()
                        .is_some_and(|error| error.kind() == io::ErrorKind::AddrInUse);
                    if !closing || std::time::Instant::now() >= deadline {
                        return Err(error.to_string());
                    }
                    thread::sleep(Duration::from_millis(5));
                }
            }
        };
        state.lock().unwrap().session_id = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos()
            .to_string();
        let active = Arc::new(AtomicBool::new(true));
        let dispatcher_server = Arc::clone(&server);
        let dispatcher_active = Arc::clone(&active);
        let dispatcher = thread::Builder::new()
            .name("obs-http".into())
            .spawn(move || {
                let media_requests = Arc::new(AtomicUsize::new(0));
                while dispatcher_active.load(Ordering::Acquire) {
                    let request = match dispatcher_server.recv_timeout(Duration::from_millis(100)) {
                        Ok(Some(request)) => request,
                        Ok(None) => continue,
                        Err(error) => {
                            eprintln!("Servidor OBS: {error}");
                            break;
                        }
                    };
                    let path = request.url().split('?').next().unwrap_or("");
                    if matches!(path, "/video" | "/fondo-video" | "/fondo") {
                        // A slow media download must never block /status or another OBS source.
                        if media_requests.fetch_add(1, Ordering::AcqRel) >= 16 {
                            media_requests.fetch_sub(1, Ordering::AcqRel);
                            reply(request, 503, "text/plain", b"Demasiadas descargas".to_vec());
                            continue;
                        }
                        let permit = MediaPermit(Arc::clone(&media_requests));
                        let state = Arc::clone(&state);
                        let active = Arc::clone(&dispatcher_active);
                        let _ = thread::Builder::new()
                            .name("obs-media".into())
                            .spawn(move || {
                                let _permit = permit;
                                serve(request, &state, &active);
                            });
                    } else {
                        serve(request, &state, &dispatcher_active);
                    }
                }
            })
            .map_err(|error| error.to_string())?;
        Ok(Self {
            server,
            active,
            dispatcher: Some(dispatcher),
        })
    }

    #[cfg(test)]
    fn port(&self) -> u16 {
        self.server.server_addr().to_ip().unwrap().port()
    }
}

impl Drop for ServerHandle {
    fn drop(&mut self) {
        self.active.store(false, Ordering::Release);
        self.server.unblock();
        if let Some(dispatcher) = self.dispatcher.take() {
            let _ = dispatcher.join();
        }
    }
}

struct MediaPermit(Arc<AtomicUsize>);
impl Drop for MediaPermit {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::AcqRel);
    }
}

fn header(name: &str, value: &str) -> Header {
    Header::from_bytes(name.as_bytes(), value.as_bytes()).unwrap()
}

fn reply(request: Request, status: u16, mime: &str, body: Vec<u8>) {
    let _ = request.respond(
        Response::from_data(body)
            .with_status_code(status)
            .with_header(header("Content-Type", mime))
            .with_header(header("Cache-Control", "no-store")),
    );
}

fn serve(request: Request, state: &Mutex<EstadoOverlay>, active: &Arc<AtomicBool>) {
    if !matches!(request.method(), Method::Get | Method::Head) {
        let _ = request.respond(Response::empty(405).with_header(header("Allow", "GET, HEAD")));
        return;
    }
    let path = request.url().split('?').next().unwrap_or("").to_owned();
    match path.as_str() {
        "/" | "/index.html" => reply(
            request,
            200,
            "text/html; charset=utf-8",
            include_bytes!("../assets/obs_overlay.html").to_vec(),
        ),
        "/status" => {
            let body = serde_json::to_vec(&*state.lock().unwrap()).unwrap();
            reply(request, 200, "application/json; charset=utf-8", body);
        }
        "/fondo" => {
            let (bytes, mime) = {
                let state = state.lock().unwrap();
                if state.fondo_tipo != "imagen" || state.fondo_imagen_bytes.is_empty() {
                    drop(state);
                    reply(request, 404, "text/plain", Vec::new());
                    return;
                }
                (
                    state.fondo_imagen_bytes.clone(),
                    state.fondo_imagen_content_type.clone(),
                )
            };
            let length = bytes.len();
            let _ = request.respond(Response::new(
                StatusCode(200),
                vec![
                    header("Content-Type", &mime),
                    header("Cache-Control", "no-store"),
                ],
                io::Cursor::new(bytes),
                Some(length),
                None,
            ));
        }
        "/video" | "/fondo-video" => {
            let file_path = {
                let state = state.lock().unwrap();
                if path == "/video" && state.video_activo {
                    state.video_ruta.clone()
                } else if path == "/fondo-video" && state.fondo_tipo == "video" {
                    state.fondo_video_ruta.clone()
                } else {
                    String::new()
                }
            };
            serve_video(request, &file_path, active);
        }
        _ => reply(request, 404, "text/plain", Vec::new()),
    }
}

/// Inclusive byte range, including open-ended and suffix requests from Chromium.
fn byte_range(value: &str, length: u64) -> Result<(u64, u64), ()> {
    let (start, end) = value
        .strip_prefix("bytes=")
        .ok_or(())?
        .split_once('-')
        .ok_or(())?;
    if length == 0 {
        return Err(());
    }
    if start.is_empty() {
        let suffix: u64 = end.parse().map_err(|_| ())?;
        if suffix == 0 {
            return Err(());
        }
        Ok((length.saturating_sub(suffix), length - 1))
    } else {
        let start: u64 = start.parse().map_err(|_| ())?;
        let end = if end.is_empty() {
            length - 1
        } else {
            end.parse::<u64>().map_err(|_| ())?.min(length - 1)
        };
        if start >= length || start > end {
            return Err(());
        }
        Ok((start, end))
    }
}

struct VideoReader {
    file: io::Take<std::fs::File>,
    active: Arc<AtomicBool>,
}
impl Read for VideoReader {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        if !self.active.load(Ordering::Acquire) {
            return Ok(0);
        }
        self.file.read(bytes)
    }
}

fn serve_video(request: Request, path: &str, active: &Arc<AtomicBool>) {
    let mut file = match std::fs::File::open(path) {
        Ok(file) => file,
        Err(_) => {
            reply(request, 404, "text/plain", Vec::new());
            return;
        }
    };
    let length = match file.metadata() {
        Ok(metadata) => metadata.len(),
        Err(_) => {
            reply(request, 500, "text/plain", Vec::new());
            return;
        }
    };
    let range = request.headers().iter().find(|h| h.field.equiv("Range"));
    let mut headers = vec![
        header("Content-Type", video_content_type_desde_extension(path)),
        header("Accept-Ranges", "bytes"),
        header("Cache-Control", "no-store"),
    ];
    let (status, start, count) = if let Some(range) = range {
        let (start, end) = match byte_range(range.value.as_str(), length) {
            Ok(range) => range,
            Err(()) => {
                let _ = request.respond(
                    Response::empty(416)
                        .with_header(header("Content-Range", &format!("bytes */{length}"))),
                );
                return;
            }
        };
        headers.push(header(
            "Content-Range",
            &format!("bytes {start}-{end}/{length}"),
        ));
        (206, start, end - start + 1)
    } else {
        (200, 0, length)
    };
    if file.seek(SeekFrom::Start(start)).is_err() {
        reply(request, 500, "text/plain", Vec::new());
        return;
    }
    let reader = VideoReader {
        file: file.take(count),
        active: Arc::clone(active),
    };
    let _ = request.respond(Response::new(
        StatusCode(status),
        headers,
        reader,
        usize::try_from(count).ok(),
        None,
    ));
}

fn video_content_type_desde_extension(path: &str) -> &'static str {
    let ext = std::path::Path::new(path)
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("")
        .to_lowercase();
    match ext.as_str() {
        "webm" => "video/webm",
        "mov" => "video/quicktime",
        "mkv" => "video/x-matroska",
        _ => "video/mp4",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use reqwest::blocking::Client;
    use std::io::Write;
    use std::net::TcpStream;

    fn client() -> Client {
        Client::builder()
            .no_proxy()
            .timeout(Duration::from_secs(2))
            .build()
            .unwrap()
    }

    #[test]
    fn serves_text_images_video_ranges_and_background_video() {
        let directory = tempfile::tempdir().unwrap();
        let video_path = directory.path().join("video.mp4");
        std::fs::write(&video_path, b"0123456789").unwrap();
        let state = Arc::new(Mutex::new(EstadoOverlay {
            texto: "Canción\n\"Amén\" <texto>".into(),
            referencia: "Juan 3:16".into(),
            fondo_tipo: "imagen".into(),
            fondo_imagen_bytes: b"image fixture".to_vec().into(),
            fondo_imagen_content_type: "image/png".into(),
            video_activo: true,
            video_ruta: video_path.to_str().unwrap().into(),
            ..Default::default()
        }));
        let server = ServerHandle::start(0, Arc::clone(&state)).unwrap();
        let url = format!("http://127.0.0.1:{}", server.port());
        let client = client();
        let page = client.get(&url).send().unwrap();
        assert_eq!(page.status(), 200);
        assert!(page.text().unwrap().contains("/fondo-video?v="));
        let response = client.get(format!("{url}/status")).send().unwrap();
        assert_eq!(response.headers()["cache-control"], "no-store");
        let status: serde_json::Value = response.json().unwrap();
        assert_eq!(status["texto"], state.lock().unwrap().texto);
        assert!(status.get("video_ruta").is_none());
        assert!(status.get("fondo_imagen_bytes").is_none());
        let image = client.get(format!("{url}/fondo?v=1")).send().unwrap();
        assert_eq!(image.headers()["content-type"], "image/png");
        assert_eq!(image.bytes().unwrap().as_ref(), b"image fixture");
        for (range, expected, content_range) in [
            ("bytes=2-5", "2345", "bytes 2-5/10"),
            ("bytes=7-", "789", "bytes 7-9/10"),
            ("bytes=-3", "789", "bytes 7-9/10"),
            ("bytes=7-99", "789", "bytes 7-9/10"),
        ] {
            let response = client
                .get(format!("{url}/video?v=1"))
                .header("Range", range)
                .send()
                .unwrap();
            assert_eq!(response.status(), 206);
            assert_eq!(response.headers()["content-range"], content_range);
            assert_eq!(response.text().unwrap(), expected);
        }
        let head = client.head(format!("{url}/video")).send().unwrap();
        assert_eq!(head.status(), 200);
        assert_eq!(head.headers()["content-length"], "10");
        assert!(head.bytes().unwrap().is_empty());
        let full = client.get(format!("{url}/video")).send().unwrap();
        assert_eq!(full.status(), 200);
        assert_eq!(full.text().unwrap(), "0123456789");
        for range in [
            "bytes=99-",
            "bytes=4-2",
            "bytes=-0",
            "bytes=oops",
            "bytes=0-1,3-4",
        ] {
            let response = client
                .get(format!("{url}/video"))
                .header("Range", range)
                .send()
                .unwrap();
            assert_eq!(response.status(), 416);
            assert_eq!(response.headers()["content-range"], "bytes */10");
        }
        {
            let mut state = state.lock().unwrap();
            state.video_activo = false;
            state.fondo_tipo = "video".into();
            state.fondo_video_ruta = video_path.to_str().unwrap().into();
            state.texto = "Nuevo texto".into();
        }
        assert_eq!(
            client.get(format!("{url}/video")).send().unwrap().status(),
            404
        );
        assert_eq!(
            client
                .get(format!("{url}/fondo-video"))
                .send()
                .unwrap()
                .text()
                .unwrap(),
            "0123456789"
        );
        let status: serde_json::Value = client
            .get(format!("{url}/status"))
            .send()
            .unwrap()
            .json()
            .unwrap();
        assert_eq!(status["texto"], "Nuevo texto");
        assert_eq!(
            client
                .get(format!("{url}/missing"))
                .send()
                .unwrap()
                .status(),
            404
        );
    }

    #[test]
    fn stop_releases_port_without_needing_a_request_and_occupied_port_is_reported() {
        let state = Arc::new(Mutex::new(EstadoOverlay::default()));
        let server = ServerHandle::start(0, Arc::clone(&state)).unwrap();
        let port = server.port();
        assert!(ServerHandle::start(port, Arc::clone(&state)).is_err());
        drop(server);
        let restarted = ServerHandle::start(port, state).expect("port released immediately");
        assert_eq!(
            client()
                .get(format!("http://127.0.0.1:{port}/status"))
                .send()
                .unwrap()
                .status(),
            200
        );
        drop(restarted);
    }

    #[test]
    fn slow_video_client_does_not_block_status_updates() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("large.mp4");
        let file = std::fs::File::create(&path).unwrap();
        file.set_len(128 * 1024 * 1024).unwrap();
        let state = Arc::new(Mutex::new(EstadoOverlay {
            video_activo: true,
            video_ruta: path.to_str().unwrap().into(),
            ..Default::default()
        }));
        let server = ServerHandle::start(0, Arc::clone(&state)).unwrap();
        let mut slow = TcpStream::connect(("127.0.0.1", server.port())).unwrap();
        slow.set_read_timeout(Some(Duration::from_secs(2))).unwrap();
        write!(
            slow,
            "GET /video HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n"
        )
        .unwrap();
        let mut first = [0; 128];
        assert!(slow.read(&mut first).unwrap() > 0);
        state.lock().unwrap().texto = "Texto mientras descarga el video".into();
        let status: serde_json::Value = client()
            .get(format!("http://127.0.0.1:{}/status", server.port()))
            .send()
            .unwrap()
            .json()
            .unwrap();
        assert_eq!(status["texto"], "Texto mientras descarga el video");
        drop(slow);
    }
}
