use std::path::{Path, PathBuf};

/// Prefer installed seeds, falling back to a source checkout for `cargo run --release`.
/// This only selects read-only seeds; user databases stay in the user data directory.
pub fn seed_data_dir(installed: PathBuf, executable: &Path) -> PathBuf {
    if installed.join("cantos.db").is_file() {
        return installed;
    }
    executable
        .ancestors()
        .find_map(|directory| development_data_dir(directory, true))
        .unwrap_or(installed)
}

/// Installed data files alone must never select a writable development directory.
pub fn development_data_dir(directory: &Path, debug_build: bool) -> Option<PathBuf> {
    if debug_build
        && directory.join("Cargo.toml").is_file()
        && directory.join("src/main.rs").is_file()
        && directory.join("data/cantos.db").is_file()
    {
        Some(directory.join("data"))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn installed_seed_does_not_select_local_data() {
        let directory = tempfile::tempdir().unwrap();
        std::fs::create_dir(directory.path().join("data")).unwrap();
        std::fs::write(directory.path().join("data/cantos.db"), b"seed").unwrap();
        for debug_build in [false, true] {
            assert_eq!(development_data_dir(directory.path(), debug_build), None);
        }
    }

    #[test]
    fn repository_data_is_only_used_by_development_builds() {
        let directory = tempfile::tempdir().unwrap();
        std::fs::create_dir(directory.path().join("data")).unwrap();
        std::fs::create_dir(directory.path().join("src")).unwrap();
        for file in ["Cargo.toml", "src/main.rs", "data/cantos.db"] {
            std::fs::write(directory.path().join(file), b"fixture").unwrap();
        }
        assert_eq!(
            development_data_dir(directory.path(), true),
            Some(directory.path().join("data"))
        );
        assert_eq!(development_data_dir(directory.path(), false), None);
    }

    #[test]
    fn release_seeds_are_found_relative_to_executable() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        std::fs::create_dir(root.join("data")).unwrap();
        std::fs::create_dir(root.join("src")).unwrap();
        for file in ["Cargo.toml", "src/main.rs", "data/cantos.db"] {
            std::fs::write(root.join(file), b"fixture").unwrap();
        }
        let installed = root.join("installed");
        let executable = root.join("target/release/ReadyShow");
        assert_eq!(
            seed_data_dir(installed.clone(), &executable),
            root.join("data")
        );
        std::fs::create_dir(&installed).unwrap();
        std::fs::write(installed.join("cantos.db"), b"installed seed").unwrap();
        assert_eq!(seed_data_dir(installed.clone(), &executable), installed);
    }

    #[test]
    fn missing_seeds_keep_installation_path() {
        let directory = tempfile::tempdir().unwrap();
        let installed = directory.path().join("installed");
        assert_eq!(
            seed_data_dir(installed.clone(), &directory.path().join("bin/ReadyShow")),
            installed
        );
    }
}
