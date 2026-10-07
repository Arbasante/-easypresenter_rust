use std::path::{Path, PathBuf};

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
}
