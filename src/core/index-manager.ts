/**
 * Index Manager
 *
 * インデックスファイル（doc_index.yaml）の読み込みと整合性検証。
 * ドキュメントとインデックス間の不整合を検出する。
 *
 * 整合性チェック:
 * - MISSING_FILE_FOR_INDEX: インデックスに登録されているがファイルが存在しない
 * - UNINDEXED_DOC_ID: ドキュメントにdoc_idがあるがインデックスに未登録
 * - DOC_ID_MISMATCH_WITH_INDEX: ドキュメントのdoc_idとインデックスの値が不一致
 * - DUPLICATE_DOC_ID_IN_INDEX: インデックス内でdoc_idが重複
 */

import { existsSync } from 'node:fs';
import { readFile } from 'node:fs/promises';
import path from 'node:path';

import yaml, { JSON_SCHEMA } from 'js-yaml';
import { z } from 'zod';

import { ShirushiErrors } from '@/errors/definitions';

import type { LintError } from '@/cli/output/reporters';
import type { DocumentParseResult } from '@/types/document';

/**
 * インデックスエントリのZodスキーマ
 */
const IndexEntrySchema = z.object({
  doc_id: z.string().min(1),
  path: z.string().min(1),
  title: z.string().optional(),
  doc_type: z.string().optional(),
  status: z.string().optional(),
  version: z.string().optional(),
  owner: z.string().optional(),
  tags: z.array(z.string()).optional(),
});

/**
 * インデックスファイルのZodスキーマ
 */
const IndexFileSchema = z.object({
  documents: z.array(IndexEntrySchema),
});

/**
 * インデックスエントリ
 */
export type IndexEntry = z.infer<typeof IndexEntrySchema>;

/**
 * インデックスファイル構造
 */
export type IndexFile = z.infer<typeof IndexFileSchema>;

/**
 * 整合性検証結果
 */
export interface IndexValidationResult {
  errors: LintError[];
  indexEntries: Map<string, IndexEntry>;
  indexByDocId: Map<string, IndexEntry>;
}

const YAML_OPTIONS = { schema: JSON_SCHEMA, json: true } as const;

/**
 * インデックスファイルを読み込み
 *
 * @param indexPath - インデックスファイルのパス
 * @param cwd - ベースディレクトリ
 * @returns インデックスファイル内容、またはnull（ファイルが存在しない場合）
 * @throws Error - YAMLパースエラーまたはスキーマ検証エラー
 */
export async function loadIndexFile(
  indexPath: string,
  cwd: string = process.cwd()
): Promise<IndexFile | null> {
  const absolutePath = path.isAbsolute(indexPath)
    ? indexPath
    : path.join(cwd, indexPath);

  if (!existsSync(absolutePath)) {
    return null;
  }

  const content = await readFile(absolutePath, 'utf8');
  const parsed = yaml.load(content, YAML_OPTIONS);

  // Zodによる構造検証
  const result = IndexFileSchema.safeParse(parsed);
  if (!result.success) {
    const issues = result.error.issues
      .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
      .join(', ');
    throw new Error(`Invalid index file structure: ${issues}`);
  }

  return result.data;
}

/**
 * インデックス内の重複を検出
 */
function findDuplicatesInIndex(entries: IndexEntry[]): LintError[] {
  const errors: LintError[] = [];
  const seenDocIds = new Map<string, string>(); // doc_id → first path

  for (const entry of entries) {
    const existingPath = seenDocIds.get(entry.doc_id);
    if (existingPath) {
      errors.push({
        path: entry.path,
        code: ShirushiErrors.DUPLICATE_DOC_ID_IN_INDEX.code,
        message: `Duplicate doc_id '${entry.doc_id}' (also in ${existingPath})`,
        domain: ShirushiErrors.DUPLICATE_DOC_ID_IN_INDEX.domain,
        severity: ShirushiErrors.DUPLICATE_DOC_ID_IN_INDEX.severity,
        details: {
          doc_id: entry.doc_id,
          first_path: existingPath,
          duplicate_path: entry.path,
        },
      });
    } else {
      seenDocIds.set(entry.doc_id, entry.path);
    }
  }

  return errors;
}

/**
 * インデックスエントリのファイル存在確認
 */
function checkMissingFiles(
  entries: IndexEntry[],
  cwd: string
): LintError[] {
  const errors: LintError[] = [];

  for (const entry of entries) {
    const absolutePath = path.join(cwd, entry.path);
    if (!existsSync(absolutePath)) {
      errors.push({
        path: entry.path,
        code: ShirushiErrors.MISSING_FILE_FOR_INDEX.code,
        message: `Index entry references non-existent file: ${entry.path}`,
        domain: ShirushiErrors.MISSING_FILE_FOR_INDEX.domain,
        severity: ShirushiErrors.MISSING_FILE_FOR_INDEX.severity,
        details: {
          doc_id: entry.doc_id,
          expected_path: entry.path,
        },
      });
    }
  }

  return errors;
}

/**
 * ドキュメントとインデックスの整合性を検証
 *
 * @param documents - パースされたドキュメント一覧
 * @param indexFile - インデックスファイル内容
 * @param cwd - ベースディレクトリ
 * @returns 検証結果
 */
export function validateIndexConsistency(
  documents: DocumentParseResult[],
  indexFile: IndexFile | null,
  cwd: string = process.cwd()
): IndexValidationResult {
  const errors: LintError[] = [];

  // インデックスがない場合は空のマップを返す
  if (!indexFile) {
    // doc_idを持つドキュメントがあればUNINDEXED_DOC_IDエラー
    for (const doc of documents) {
      if (doc.docId) {
        errors.push({
          path: doc.path,
          code: ShirushiErrors.UNINDEXED_DOC_ID.code,
          message: `Document has doc_id '${doc.docId}' but index file does not exist`,
          domain: ShirushiErrors.UNINDEXED_DOC_ID.domain,
          severity: ShirushiErrors.UNINDEXED_DOC_ID.severity,
          details: { doc_id: doc.docId },
        });
      }
    }

    return {
      errors,
      indexEntries: new Map(),
      indexByDocId: new Map(),
    };
  }

  // インデックスをマップに変換
  const indexByPath = new Map<string, IndexEntry>();
  const indexByDocId = new Map<string, IndexEntry>();

  for (const entry of indexFile.documents) {
    indexByPath.set(entry.path, entry);
    indexByDocId.set(entry.doc_id, entry);
  }

  // 1. インデックス内の重複検出
  errors.push(...findDuplicatesInIndex(indexFile.documents));

  // 2. インデックスエントリのファイル存在確認
  errors.push(...checkMissingFiles(indexFile.documents, cwd));

  // 3. ドキュメントとインデックスの整合性
  for (const doc of documents) {
    if (!doc.docId) continue;

    const indexEntry = indexByPath.get(doc.path);

    if (!indexEntry) {
      // ドキュメントにdoc_idがあるがインデックスに未登録
      errors.push({
        path: doc.path,
        code: ShirushiErrors.UNINDEXED_DOC_ID.code,
        message: `Document has doc_id '${doc.docId}' but is not in index`,
        domain: ShirushiErrors.UNINDEXED_DOC_ID.domain,
        severity: ShirushiErrors.UNINDEXED_DOC_ID.severity,
        details: { doc_id: doc.docId },
      });
    } else if (indexEntry.doc_id !== doc.docId) {
      // ドキュメントのdoc_idとインデックスの値が不一致
      // doc側が真（ADR-0003）なのでインデックス側が不整合
      errors.push({
        path: doc.path,
        code: ShirushiErrors.DOC_ID_MISMATCH_WITH_INDEX.code,
        message: `Document doc_id '${doc.docId}' differs from index entry '${indexEntry.doc_id}'`,
        domain: ShirushiErrors.DOC_ID_MISMATCH_WITH_INDEX.domain,
        severity: ShirushiErrors.DOC_ID_MISMATCH_WITH_INDEX.severity,
        details: {
          document_doc_id: doc.docId,
          index_doc_id: indexEntry.doc_id,
        },
      });
    }
  }

  return {
    errors,
    indexEntries: indexByPath,
    indexByDocId,
  };
}

/**
 * インデックスファイルのパスを取得
 */
export function getIndexFilePath(
  indexFile: string | undefined,
  cwd: string = process.cwd()
): string {
  const defaultPath = 'docs/doc_index.yaml';
  const relativePath = indexFile ?? defaultPath;
  return path.isAbsolute(relativePath)
    ? relativePath
    : path.join(cwd, relativePath);
}
