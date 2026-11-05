export const $ = id => document.getElementById(id);
let timer;
export function notice(text, error = false) {
  clearTimeout(timer);
  $('message').textContent = text;
  $('message').classList.toggle('error', error);
  if (!error) timer = setTimeout(() => { $('message').textContent = ''; }, 4500);
}
export function element(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (className) node.className = className;
  return node;
}
export function download(blob, name) {
  const url = URL.createObjectURL(blob);
  const link = element('a');
  link.href = url; link.download = name; document.body.append(link); link.click(); link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 60000);
}
