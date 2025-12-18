/**
 * Content Validator
 *
 * ドキュメント本文のSHA-256ハッシュを検証し、改ざん・変更を検出する。
 * content_integrity機能が有効な場合にlintコマンドから呼び出される。
 */

import { ShirushiErrors } from '@/errors/definitions';
import { calculateContentHash, verifyContentHash } from '@/utils/content-hash';
import { normalizePath } from '@/utils/path';

import type { LintError } from '@/cli/output/reporters';
import type { IndexEntry } from '@/core/index-manager';
import type { DocumentParseResult } from '@/types/document';

/**
 * コンテンツ整合性検証結果
 */
export interface ContentValidationResult {
  /** 検出されたエラー・警告 */
  errors: LintError[];
  /** 計算されたハッシュ（パス → ハッシュ） */
  calculatedHashes: Map<string, string>;
  /** ハッシュ不一致のdoc_id一覧（ソース参照検出用） */
  mismatchedDocIds: string[];
}

/**
 * ドキュメントのコンテンツ整合性を検証
 *
 * @param documents - パースされたドキュメント一覧（contentフィールド含む）
 * @param indexByPath - パスでインデックスされたエントリ
 * @returns 検証結果
 */
export function validateContentIntegrity(
  documents: DocumentParseResult[],
  indexByPath: Map<string, IndexEntry>
): ContentValidationResult {
  const errors: LintError[] = [];
  const calculatedHashes = new Map<string, string>();
  const mismatchedDocIds: string[] = [];

  for (const doc of documents) {
    // contentフィールドがない場合はスキップ（preserveContent=falseの場合）
    if (doc.content === undefined) continue;

    // ハッシュ計算（rawContentを渡す - 内部で正規化される）
    const hash = calculateContentHash(doc.content);
    calculatedHashes.set(doc.path, hash);

    // パスを正規化してMap検索（Windows互換）
    const normalizedPath = normalizePath(doc.path);
    const indexEntry = indexByPath.get(normalizedPath);

    // インデックスにエントリがない場合はスキップ
    // （UNINDEXED_DOC_IDエラーは別の検証で報告される）
    if (!indexEntry) continue;

    // content_hashが未設定の場合は警告
    if (!indexEntry.content_hash) {
      errors.push({
        path: doc.path,
        code: ShirushiErrors.MISSING_CONTENT_HASH.code,
        message: ShirushiErrors.MISSING_CONTENT_HASH.message,
        domain: ShirushiErrors.MISSING_CONTENT_HASH.domain,
        severity: ShirushiErrors.MISSING_CONTENT_HASH.severity,
        details: {
          doc_id: doc.docId,
        },
      });
      continue;
    }

    // ハッシュ検証（rawContentを渡す）
    if (!verifyContentHash(doc.content, indexEntry.content_hash)) {
      errors.push({
        path: doc.path,
        code: ShirushiErrors.CONTENT_HASH_MISMATCH.code,
        message: `${ShirushiErrors.CONTENT_HASH_MISMATCH.message}: expected ${indexEntry.content_hash.slice(0, 8)}..., got ${hash.slice(0, 8)}...`,
        domain: ShirushiErrors.CONTENT_HASH_MISMATCH.domain,
        severity: ShirushiErrors.CONTENT_HASH_MISMATCH.severity,
        details: {
          doc_id: doc.docId,
          expected_hash: indexEntry.content_hash,
          actual_hash: hash,
        },
      });

      // ソース参照検出用にdoc_idを記録
      if (doc.docId) {
        mismatchedDocIds.push(doc.docId);
      }
    }
  }

  return { errors, calculatedHashes, mismatchedDocIds };
}
