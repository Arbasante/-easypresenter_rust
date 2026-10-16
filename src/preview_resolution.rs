use gstreamer as gst;

pub const HEIGHTS: [u32; 8] = [240, 360, 480, 720, 1080, 1440, 2160, 0];

pub fn height(index: i32) -> u32 {
    HEIGHTS.get(index as usize).copied().unwrap_or(480)
}

/// Zero selects the source dimensions; smaller sources are never enlarged.
pub fn dimensions(width: u32, height: u32, limit: u32) -> (u32, u32) {
    if limit == 0 || height <= limit || height == 0 {
        return (width, height);
    }
    let scaled_width =
        ((u64::from(width) * u64::from(limit) + u64::from(height) / 2) / u64::from(height)) as u32;
    (scaled_width.max(1), limit)
}

pub fn video_caps(height: u32) -> gst::Caps {
    let caps = gst::Caps::builder("video/x-raw")
        .field("format", "RGBA")
        .field("pixel-aspect-ratio", gst::Fraction::new(1, 1));
    if height == 0 {
        caps.build()
    } else {
        caps.field("height", gst::IntRange::<i32>::new(1, height as i32))
            .build()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gst::prelude::*;

    #[test]
    fn image_resolution_preserves_aspect_and_never_upscales() {
        assert_eq!(dimensions(1920, 1080, 240), (427, 240));
        assert_eq!(dimensions(1080, 1920, 480), (270, 480));
        assert_eq!(dimensions(320, 180, 240), (320, 180));
        assert_eq!(dimensions(3840, 2160, 0), (3840, 2160));
        assert_eq!(height(-1), 480);
        assert_eq!(height(7), 0);
    }

    #[test]
    fn video_negotiates_preview_resolution_and_original_without_upscaling() {
        gst::init().unwrap();
        for (source_height, limit, expected_height) in
            [(1080, 240, 240), (180, 480, 180), (1080, 0, 1080)]
        {
            let pipeline = gst::parse::launch(&format!(
                "videotestsrc num-buffers=1 ! video/x-raw,width=1920,height={source_height},pixel-aspect-ratio=1/1 ! videoconvert ! videoscale ! capsfilter name=resolution ! appsink name=frames"
            )).unwrap().downcast::<gst::Pipeline>().unwrap();
            pipeline
                .by_name("resolution")
                .unwrap()
                .set_property("caps", video_caps(limit));
            let sink = pipeline
                .by_name("frames")
                .unwrap()
                .downcast::<gstreamer_app::AppSink>()
                .unwrap();
            pipeline.set_state(gst::State::Playing).unwrap();
            let sample = sink.try_pull_sample(gst::ClockTime::from_seconds(5));
            pipeline.set_state(gst::State::Null).unwrap();
            let sample = sample.expect("preview frame");
            let info = gstreamer_video::VideoInfo::from_caps(sample.caps().unwrap()).unwrap();
            assert_eq!(info.height(), expected_height);
            let expected_width = dimensions(1920, source_height, limit).0;
            assert!(info.width().abs_diff(expected_width) <= 1);
        }
    }
}
