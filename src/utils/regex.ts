/**
 * Regex Utilities
 *
 * 正規表現関連のユーティリティ関数。
 */

/**
 * 正規表現の特殊文字をエスケープ
 *
 * @param str - エスケープする文字列
 * @returns エスケープされた文字列
 *
 * @example
 * ```typescript
 * escapeRegex('foo.bar') // => 'foo\\.bar'
 * escapeRegex('[test]')  // => '\\[test\\]'
 * ```
 */
export function escapeRegex(str: string): string {
  return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}
