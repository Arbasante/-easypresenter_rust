fn main() {
    bundle_google_client().expect("No se pudo preparar el cliente OAuth de ReadyShow");
    println!("cargo:rerun-if-changed=assets/icon.ico");
    slint_build::compile("ui/main_ui.slint").unwrap();

    // Solo aplica en compilaciones para Windows
    #[cfg(target_os = "windows")]
    {
        use embed_manifest::manifest::{DpiAwareness, ExecutionLevel};
        use embed_manifest::{embed_manifest, new_manifest};

        let manifest = new_manifest("EasyPresenter.App")
            .dpi_awareness(DpiAwareness::PerMonitorV2)
            .requested_execution_level(ExecutionLevel::AsInvoker);

        embed_manifest(manifest).expect("No se pudo incrustar el manifiesto de Windows");

        // Incrusta el icono de la app en el .exe (ventana, taskbar, inicio, accesos directos)
        let mut res = winres::WindowsResource::new();
        res.set_icon("assets/icon.ico");
        res.compile()
            .expect("No se pudo compilar el recurso de icono de Windows");
    }
}

// Configure the application's desktop OAuth client once at build time, not per user.
fn bundle_google_client() -> Result<(), Box<dyn std::error::Error>> {
    use std::{env, fs, path::PathBuf};
    for variable in [
        "READYSHOW_GOOGLE_OAUTH_FILE",
        "READYSHOW_GOOGLE_CLIENT_ID",
        "READYSHOW_GOOGLE_CLIENT_SECRET",
    ] {
        println!("cargo:rerun-if-env-changed={variable}");
    }
    let explicit_file = env::var_os("READYSHOW_GOOGLE_OAUTH_FILE");
    let file = explicit_file
        .clone()
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("data/google_oauth.json"));
    println!("cargo:rerun-if-changed={}", file.display());
    let config = if let Ok(id) = env::var("READYSHOW_GOOGLE_CLIENT_ID") {
        if id.trim().is_empty() {
            return Err("READYSHOW_GOOGLE_CLIENT_ID está vacío. En GitHub Actions, configura el secreto del repositorio en Settings > Secrets and variables > Actions con el campo client_id del JSON OAuth de escritorio de Google".into());
        }
        let id = id.trim();
        if !id.ends_with(".apps.googleusercontent.com") || id.chars().any(char::is_whitespace) {
            return Err("READYSHOW_GOOGLE_CLIENT_ID no es válido: debe contener solo el campo client_id del JSON OAuth de escritorio de Google, terminado en .apps.googleusercontent.com; no el JSON completo, el client_secret ni el nombre del campo".into());
        }
        Some(
            serde_json::json!({"installed": {"client_id": id, "client_secret": env::var("READYSHOW_GOOGLE_CLIENT_SECRET").ok()}}),
        )
    } else {
        match fs::read(&file) {
            Ok(bytes) => Some(
                serde_json::from_slice::<serde_json::Value>(&bytes)
                    .map_err(|_| "El archivo OAuth no contiene JSON válido")?,
            ),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound && explicit_file.is_none() => None,
            Err(e) => return Err(e.into()),
        }
    };
    let bundled = match config {
        Some(value) => {
            let installed = value
                .get("installed")
                .ok_or("El cliente OAuth debe ser de tipo Aplicación de escritorio")?;
            let id = installed
                .get("client_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
                .trim();
            if !id.ends_with(".apps.googleusercontent.com") || id.chars().any(char::is_whitespace) {
                return Err(
                    "El cliente OAuth de escritorio no contiene un client_id válido".into(),
                );
            }
            let secret = installed
                .get("client_secret")
                .and_then(serde_json::Value::as_str)
                .map(str::trim)
                .filter(|s| !s.is_empty());
            // Do not include tokens, arbitrary URLs or other fields from the input file.
            serde_json::to_vec(
                &serde_json::json!({"installed":{"client_id":id,"client_secret":secret}}),
            )?
        }
        None => Vec::new(),
    };
    let out = PathBuf::from(env::var_os("OUT_DIR").ok_or("OUT_DIR no está disponible")?)
        .join("google_oauth.json");
    // Never print the contents of the credentials to build logs.
    fs::write(out, bundled)?;
    Ok(())
}
