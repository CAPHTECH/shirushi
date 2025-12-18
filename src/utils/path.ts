/**
 * Path Utility
 *
 * クロスプラットフォーム互換のパス操作ユーティリティ。
 */

import path, { posix } from 'node:path';

/**
 * パスをPOSIX形式（フォワードスラッシュ）に正規化
 *
 * Windows環境でのバックスラッシュをフォワードスラッシュに変換し、
 * インデックスファイルやMap検索でのパス比較を一貫させる。
 *
 * @param filePath - 正規化するファイルパス
 * @returns POSIX形式のパス
 */
export function normalizePath(filePath: string): string {
  return filePath.split(path.sep).join(posix.sep);
}
