/// Insert clipboard text at UTF-8 cursor offsets, replacing only the selection.
pub fn insert(
    text: &str,
    anchor: i32,
    cursor: i32,
    pasted: &str,
    single_line: bool,
) -> (String, i32) {
    let boundary = |offset: i32| {
        let mut offset = (offset.max(0) as usize).min(text.len());
        while !text.is_char_boundary(offset) {
            offset -= 1;
        }
        offset
    };
    let anchor = boundary(anchor);
    let cursor = boundary(cursor);
    let start = anchor.min(cursor);
    let end = anchor.max(cursor);
    let pasted = pasted.replace("\r\n", "\n").replace('\r', "\n");
    let pasted = if single_line {
        pasted.replace('\n', " ")
    } else {
        pasted
    };
    let mut result = String::with_capacity(text.len() - (end - start) + pasted.len());
    result.push_str(&text[..start]);
    result.push_str(&pasted);
    result.push_str(&text[end..]);
    (result, (start + pasted.len()) as i32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pastes_multiline_unicode_at_cursor_and_preserves_surrounding_text() {
        assert_eq!(
            insert("Inicio fin", 7, 7, "Señor\r\n\r\nAmén", false),
            ("Inicio Señor\n\nAménfin".into(), 20)
        );
    }

    #[test]
    fn replaces_backward_selection_and_returns_utf8_cursor_offset() {
        assert_eq!(
            insert("Una canción final", 12, 4, "oración", false),
            ("Una oración final".into(), 12)
        );
    }

    #[test]
    fn empty_field_accepts_clipboard_text_and_title_stays_single_line() {
        assert_eq!(insert("", 0, 0, "A\r\nB", false), ("A\nB".into(), 3));
        assert_eq!(insert("", 0, 0, "A\r\nB", true), ("A B".into(), 3));
    }

    #[test]
    fn stale_offsets_are_clamped_to_valid_character_boundaries() {
        assert_eq!(insert("á", -1, 99, "x", false), ("x".into(), 1));
        assert_eq!(insert("á", 1, 1, "x", false), ("xá".into(), 1));
    }
}
