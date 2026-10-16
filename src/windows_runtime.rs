//! Keep the installed Windows runtime independent of administrator environment settings.

#[cfg(any(windows, test))]
use std::{ffi::OsString, path::Path};

#[cfg(any(windows, test))]
fn bundled_environment(
    installation: &Path,
    cache: &Path,
    inherited_path: Option<OsString>,
) -> Result<Vec<(&'static str, OsString)>, std::env::JoinPathsError> {
    let plugins = installation.join("lib/gstreamer-1.0");
    if !plugins.is_dir() {
        // Development builds can continue using a separately installed GStreamer.
        return Ok(Vec::new());
    }
    let mut paths = vec![installation.to_path_buf()];
    if let Some(path) = inherited_path {
        paths.extend(std::env::split_paths(&path));
    }
    let mut environment = vec![
        ("PATH", std::env::join_paths(paths)?),
        ("GST_PLUGIN_PATH_1_0", plugins.clone().into_os_string()),
        ("GST_PLUGIN_SYSTEM_PATH_1_0", plugins.into_os_string()),
        (
            "GST_REGISTRY_1_0",
            cache.join("gstreamer/registry.bin").into_os_string(),
        ),
    ];
    let scanner = installation.join("libexec/gstreamer-1.0/gst-plugin-scanner.exe");
    if scanner.is_file() {
        environment.push(("GST_PLUGIN_SCANNER_1_0", scanner.into_os_string()));
    }
    Ok(environment)
}

#[cfg(windows)]
pub fn initialize() -> Result<(), Box<dyn std::error::Error>> {
    let executable = std::env::current_exe()?;
    let installation = executable
        .parent()
        .ok_or("El ejecutable no tiene directorio")?;
    let directories = directories::ProjectDirs::from("com", "Arbasante", "EasyPresenter")
        .ok_or("No se encontró la carpeta del usuario")?;
    let environment = bundled_environment(
        installation,
        directories.cache_dir(),
        std::env::var_os("PATH"),
    )?;
    if !environment.is_empty() {
        std::fs::create_dir_all(directories.cache_dir().join("gstreamer"))?;
        for (name, value) in environment {
            // SAFETY: environment mutation is thread-safe on Windows. This also
            // runs before Slint, GStreamer or application workers are started.
            unsafe { std::env::set_var(name, value) };
        }
    }
    Ok(())
}

#[cfg(windows)]
pub fn report_error(error: &str) {
    use std::io::Write;
    let log = directories::ProjectDirs::from("com", "Arbasante", "EasyPresenter")
        .map(|directories| directories.data_local_dir().join("logs/startup.log"));
    let saved_log = log.filter(|path| {
        (|| -> std::io::Result<()> {
            std::fs::create_dir_all(path.parent().unwrap())?;
            let mut file = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)?;
            writeln!(file, "ReadyShow {}: {error}", env!("CARGO_PKG_VERSION"))
        })()
        .is_ok()
    });
    let mut message = format!("ReadyShow encontró un error:\n\n{error}");
    if let Some(log) = saved_log {
        message.push_str(&format!("\n\nRegistro: {}", log.display()));
    }
    rfd::MessageDialog::new()
        .set_title("ReadyShow")
        .set_level(rfd::MessageLevel::Error)
        .set_description(&message)
        .show();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bundled_runtime_uses_installation_resources_and_user_cache() {
        let directory = tempfile::tempdir().unwrap();
        let installation = directory.path().join("Program Files/ReadyShow");
        let cache = directory.path().join("usuario/Cache");
        std::fs::create_dir_all(installation.join("lib/gstreamer-1.0")).unwrap();
        std::fs::create_dir_all(installation.join("libexec/gstreamer-1.0")).unwrap();
        let scanner = installation.join("libexec/gstreamer-1.0/gst-plugin-scanner.exe");
        std::fs::write(&scanner, b"fixture").unwrap();
        let previous = directory.path().join("system-bin");
        let environment = bundled_environment(
            &installation,
            &cache,
            Some(std::env::join_paths([&previous]).unwrap()),
        )
        .unwrap();
        let value = |name| &environment.iter().find(|(key, _)| *key == name).unwrap().1;
        assert_eq!(value("GST_PLUGIN_SCANNER_1_0"), scanner.as_os_str());
        assert_eq!(
            value("GST_REGISTRY_1_0"),
            cache.join("gstreamer/registry.bin").as_os_str()
        );
        for name in ["GST_PLUGIN_PATH_1_0", "GST_PLUGIN_SYSTEM_PATH_1_0"] {
            assert_eq!(
                value(name),
                installation.join("lib/gstreamer-1.0").as_os_str()
            );
        }
        assert_eq!(
            std::env::split_paths(value("PATH")).collect::<Vec<_>>(),
            vec![installation, previous]
        );
        // Planning reads installed files without creating or writing the cache there.
        assert!(!cache.exists());
    }

    #[test]
    fn development_without_bundle_keeps_system_runtime() {
        let directory = tempfile::tempdir().unwrap();
        assert!(
            bundled_environment(directory.path(), directory.path(), None)
                .unwrap()
                .is_empty()
        );
    }
}
