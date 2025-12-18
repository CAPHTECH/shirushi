/**
 * Content Hash Utility
 *
 * SHA-256ハッシュ計算ユーティリティ。
 * ドキュメント本文のハッシュを計算し、コンテンツ整合性を検証する。
 */

import { createHash, timingSafeEqual } from 'node:crypto';

/**
 * コンテンツを正規化してからSHA-256ハッシュを計算
 *
 * @param rawContent - 正規化前のコンテンツ
 * @returns 小文字16進数64文字のハッシュ
 */
export function calculateContentHash(rawContent: string): string {
  const normalized = normalizeContentForHashing(rawContent);
  return createHash('sha256').update(normalized, 'utf8').digest('hex');
}

/**
 * コンテンツを正規化（改行統一、末尾空白除去）
 *
 * 正規化ルール:
 * 1. CRLF → LF に変換
 * 2. CR → LF に変換
 * 3. 末尾の空白・改行を除去
 *
 * @param content - 正規化前のコンテンツ
 * @returns 正規化されたコンテンツ
 */
export function normalizeContentForHashing(content: string): string {
  return content
    .replace(/\r\n/g, '\n') // CRLF → LF
    .replace(/\r/g, '\n') // CR → LF
    .trimEnd(); // 末尾空白除去
}

/**
 * ハッシュを検証（rawContentを渡す - 内部で正規化）
 *
 * タイミング攻撃を防ぐため、timingSafeEqualを使用して比較する。
 * 注意: 二重正規化を避けるため、正規化済みコンテンツは渡さないこと
 *
 * @param rawContent - 正規化前のコンテンツ
 * @param expectedHash - 期待されるハッシュ値
 * @returns ハッシュが一致すればtrue
 */
export function verifyContentHash(
  rawContent: string,
  expectedHash: string
): boolean {
  const actualHash = calculateContentHash(rawContent);
  const normalizedExpected = expectedHash.toLowerCase();

  // 長さが異なる場合は早期リターン（タイミング攻撃の観点では許容）
  if (actualHash.length !== normalizedExpected.length) {
    return false;
  }

  const actualBuffer = Buffer.from(actualHash, 'hex');
  const expectedBuffer = Buffer.from(normalizedExpected, 'hex');

  return timingSafeEqual(actualBuffer, expectedBuffer);
}
