// Uses the existing status payload; no extra commands or protocol changes.
export function isLiveSlide(status, detail, slide) {
  if (!status?.projector_visible || status.video || !slide?.text || status.output?.texto !== slide.text) return false;
  const reference = status.output.referencia || '';
  // Desktop appends the Bible version (for example " | RVR1960") to the reference.
  const verseReference = reference.split('|', 1)[0].trim();
  return detail.selection.kind === 'chapter'
    ? verseReference === `${detail.title}:${slide.number}`
    : reference === '';
}
