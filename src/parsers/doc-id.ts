/**
 * Escape special regex characters in a string
 */
function escapeRegex(str: string): string {
  return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

/**
 * Count occurrences of the ID field directive in raw YAML content
 * @param raw - Raw YAML string (e.g., front matter)
 * @param idField - Field name to search for (default: 'doc_id')
 */
export function countDocIdDirectives(raw: string | undefined, idField: string = 'doc_id'): number {
  if (!raw) return 0;
  const pattern = new RegExp(`^\\s*${escapeRegex(idField)}\\s*:`);
  return raw
    .split(/\r?\n/)
    .map((line) => line.replace(/#.*/, ''))
    .filter((line) => pattern.test(line))
    .length;
}
