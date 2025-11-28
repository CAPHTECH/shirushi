export function countDocIdDirectives(raw: string | undefined): number {
  if (!raw) return 0;
  return raw
    .split(/\r?\n/)
    .map((line) => line.replace(/#.*/, ''))
    .filter((line) => /^\s*doc_id\s*:/.test(line))
    .length;
}
