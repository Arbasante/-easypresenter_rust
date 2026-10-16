use lru::LruCache;
use rusqlite::Connection;
use slint::Image;
use std::num::NonZeroUsize;
use std::sync::Mutex;

pub const THUMBNAIL_SIZE: u32 = 192;
pub const THUMBNAIL_CACHE_BYTES: usize = 8 * 1024 * 1024;
pub const BACKGROUND_CACHE_BYTES: usize = 24 * 1024 * 1024;

/// Connection-local limits, also applied after database imports.
pub fn configure_sqlite(connection: &Connection) -> rusqlite::Result<()> {
    connection.execute_batch(
        "PRAGMA cache_size = -4096;
         PRAGMA mmap_size = 0;
         PRAGMA temp_store = FILE;",
    )
}

/// Return freed startup scratch buffers to the OS instead of keeping them in
/// glibc's allocator arenas. Other platforms retain their allocator's defaults.
pub fn release_unused_heap() {
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    {
        unsafe extern "C" {
            fn malloc_trim(pad: usize) -> std::ffi::c_int;
        }
        // SAFETY: glibc's thread-safe allocator hint takes no pointers and only
        // releases free pages; live Rust, Slint and GStreamer allocations remain valid.
        let _ = unsafe { malloc_trim(0) };
    }
}

/// Bound decoded RGBA storage as well as entry count. Active UI images keep
/// their own shared references, including originals too large to cache.
pub struct ImageCache {
    entries: LruCache<String, Image>,
    bytes: usize,
    budget: usize,
}

impl ImageCache {
    pub fn new(max_entries: usize, budget: usize) -> Self {
        Self {
            entries: LruCache::new(NonZeroUsize::new(max_entries.max(1)).unwrap()),
            bytes: 0,
            budget,
        }
    }

    fn cost(image: &Image) -> usize {
        let size = image.size();
        (size.width as usize)
            .saturating_mul(size.height as usize)
            .saturating_mul(4)
    }

    pub fn get(&mut self, path: &str) -> Option<&Image> {
        self.entries.get(path)
    }

    pub fn remove(&mut self, path: &str) {
        if let Some(image) = self.entries.pop(path) {
            self.bytes -= Self::cost(&image);
        }
    }

    pub fn insert(&mut self, path: String, image: Image) {
        self.remove(&path);
        let cost = Self::cost(&image);
        if cost > self.budget {
            return;
        }
        while self.bytes.saturating_add(cost) > self.budget
            || self.entries.len() == self.entries.cap().get()
        {
            if let Some((_, image)) = self.entries.pop_lru() {
                self.bytes -= Self::cost(&image);
            } else {
                break;
            }
        }
        self.bytes += cost;
        self.entries.put(path, image);
    }
}

/// Only one decoded frame and one event-loop notification may be pending.
/// Newer frames replace the old one when rendering cannot keep up.
pub struct LatestFrame<T>(Mutex<(Option<T>, bool)>);

impl<T> Default for LatestFrame<T> {
    fn default() -> Self {
        Self(Mutex::new((None, false)))
    }
}

impl<T> LatestFrame<T> {
    pub fn submit(&self, frame: T) -> bool {
        let mut state = self.0.lock().unwrap();
        state.0 = Some(frame);
        let notify = !state.1;
        state.1 = true;
        notify
    }

    pub fn take(&self) -> Option<T> {
        let mut state = self.0.lock().unwrap();
        state.1 = false;
        state.0.take()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use slint::{Rgba8Pixel, SharedPixelBuffer};
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };

    fn image() -> Image {
        Image::from_rgba8(SharedPixelBuffer::<Rgba8Pixel>::new(10, 10))
    }

    #[test]
    fn image_cache_evicts_least_recently_used_within_byte_budget() {
        let mut cache = ImageCache::new(10, 800);
        cache.insert("a".into(), image());
        cache.insert("b".into(), image());
        assert!(cache.get("a").is_some());
        cache.insert("c".into(), image());
        assert!(cache.get("b").is_none());
        assert!(cache.get("a").is_some());
        assert!(cache.get("c").is_some());
        assert_eq!(cache.bytes, 800);
    }

    #[test]
    fn oversized_original_is_not_retained_and_replacement_updates_accounting() {
        let mut cache = ImageCache::new(1, 800);
        cache.insert("a".into(), image());
        cache.insert("a".into(), image());
        assert_eq!(cache.bytes, 400);
        cache.insert("b".into(), image());
        assert!(cache.get("a").is_none());
        let original = Image::from_rgba8(SharedPixelBuffer::new(100, 100));
        cache.insert("original".into(), original.clone());
        assert!(cache.get("original").is_none());
        assert_eq!(original.size().height, 100);
        cache.remove("b");
        assert_eq!(cache.bytes, 0);
    }

    #[test]
    fn queued_frames_are_replaced_and_released_before_rendering() {
        struct Frame(Arc<AtomicUsize>);
        impl Drop for Frame {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::Relaxed);
            }
        }
        let dropped = Arc::new(AtomicUsize::new(0));
        let queue = LatestFrame::default();
        assert!(queue.submit(Frame(Arc::clone(&dropped))));
        for _ in 0..99 {
            assert!(!queue.submit(Frame(Arc::clone(&dropped))));
        }
        assert_eq!(dropped.load(Ordering::Relaxed), 99);
        drop(queue.take());
        assert_eq!(dropped.load(Ordering::Relaxed), 100);
        assert!(queue.submit(Frame(dropped)));
    }

    #[test]
    fn sqlite_limits_preserve_queries_and_integrity() {
        let directory = tempfile::tempdir().unwrap();
        let connection = Connection::open(directory.path().join("test.db")).unwrap();
        configure_sqlite(&connection).unwrap();
        assert_eq!(
            connection
                .query_row("PRAGMA cache_size", [], |r| r.get::<_, i32>(0))
                .unwrap(),
            -4096
        );
        assert_eq!(
            connection
                .query_row("PRAGMA temp_store", [], |r| r.get::<_, i32>(0))
                .unwrap(),
            1
        );
        let mmap = connection
            .query_row("PRAGMA mmap_size", [], |r| r.get::<_, i64>(0))
            .unwrap();
        assert_eq!(mmap, 0);
        connection
            .execute_batch(
                "CREATE TABLE texts(value TEXT); INSERT INTO texts VALUES('Canción'),('Amén');",
            )
            .unwrap();
        assert_eq!(
            connection
                .query_row("SELECT value FROM texts ORDER BY value LIMIT 1", [], |r| {
                    r.get::<_, String>(0)
                })
                .unwrap(),
            "Amén"
        );
        assert_eq!(
            connection
                .query_row("PRAGMA integrity_check", [], |r| r.get::<_, String>(0))
                .unwrap(),
            "ok"
        );
    }
}
