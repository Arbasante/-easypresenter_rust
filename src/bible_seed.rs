use std::fs::File;
use std::io;
use std::path::Path;

/// Publish the complete seed only after gzip validation succeeds, preserving existing data.
pub fn decompress_if_missing(archive: &Path, destination: &Path) -> io::Result<()> {
    if destination.try_exists()? {
        return Ok(());
    }
    let source = File::open(archive)?;
    let mut decoder = flate2::read::MultiGzDecoder::new(source);
    let parent = destination.parent().unwrap_or_else(|| Path::new("."));
    let mut temporary = tempfile::NamedTempFile::new_in(parent)?;
    io::copy(&mut decoder, &mut temporary)?;
    temporary.as_file().sync_all()?;
    match temporary.persist_noclobber(destination) {
        Ok(_) => Ok(()),
        Err(error) if error.error.kind() == io::ErrorKind::AlreadyExists => Ok(()),
        Err(error) => Err(error.error),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn extracts_seed_and_preserves_existing_database() {
        let directory = tempfile::tempdir().unwrap();
        let archive = directory.path().join("biblias.db.gz");
        let destination = directory.path().join("biblias.db");
        let mut encoder = flate2::write::GzEncoder::new(
            File::create(&archive).unwrap(),
            flate2::Compression::default(),
        );
        encoder.write_all(b"seed database").unwrap();
        encoder.finish().unwrap();
        decompress_if_missing(&archive, &destination).unwrap();
        assert_eq!(std::fs::read(&destination).unwrap(), b"seed database");
        std::fs::write(&destination, b"user database").unwrap();
        std::fs::remove_file(&archive).unwrap();
        decompress_if_missing(&archive, &destination).unwrap();
        assert_eq!(std::fs::read(&destination).unwrap(), b"user database");
    }

    #[test]
    fn invalid_archive_leaves_no_database_or_temporary_file() {
        let directory = tempfile::tempdir().unwrap();
        let archive = directory.path().join("biblias.db.gz");
        let destination = directory.path().join("biblias.db");
        std::fs::write(&archive, b"invalid gzip").unwrap();
        assert!(decompress_if_missing(&archive, &destination).is_err());
        assert!(!destination.exists());
        assert_eq!(std::fs::read_dir(directory.path()).unwrap().count(), 1);
    }
}
