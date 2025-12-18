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
import { normalizePath } from '@/utils/path';

import type { LintError } from '@/cli/output/reporters';
import type { DocumentParseResult } from '@/types/document';

/**
 * インデックスエントリのZodスキーマを動的に生成
 * @param idField - IDフィールド名（デフォルト: 'doc_id'）
 */
export function createIndexEntrySchema(idField: string = 'doc_id') {
  return z.object({
    [idField]: z.string().min(1),
    path: z.string().min(1),
    title: z.string().optional(),
    doc_type: z.string().optional(),
    status: z.string().optional(),
    version: z.string().optional(),
    owner: z.string().optional(),
    tags: z.array(z.string()).optional(),
    content_hash: z.string().length(64).optional(), // SHA-256 hex (64 chars)
  });
}

/**
 * インデックスファイルのZodスキーマを動的に生成
 * @param idField - IDフィールド名（デフォルト: 'doc_id'）
 */
export function createIndexFileSchema(idField: string = 'doc_id') {
  return z.object({
    documents: z.array(createIndexEntrySchema(idField)),
  });
}

/**
 * インデックスエントリ（動的idFieldに対応）
 *
 * doc_idは後方互換性のためオプショナルプロパティとして維持。
 * カスタムidFieldを使う場合は[idField]でアクセス。
 */
export interface IndexEntry {
  doc_id?: string; // 後方互換性のため（デフォルトのidField）
  path: string;
  title?: string;
  doc_type?: string;
  status?: string;
  version?: string;
  owner?: string;
  tags?: string[];
  content_hash?: string; // SHA-256 hash of document content
  [key: string]: string | string[] | undefined; // 動的なidフィールドやカスタムフィールド
}

/**
 * インデックスファイル構造
 */
export interface IndexFile {
  documents: IndexEntry[];
}

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
 * IndexEntryから指定されたIDフィールドの値を安全に取得
 *
 * @param entry - インデックスエントリ
 * @param idField - IDフィールド名
 * @returns IDの値（string型でない場合はundefined）
 */
export function getDocIdFromEntry(
  entry: IndexEntry,
  idField: string
): string | undefined {
  const value = entry[idField];
  return typeof value === 'string' ? value : undefined;
}

/**
 * インデックスファイルを読み込み
 *
 * @param indexPath - インデックスファイルのパス
 * @param cwd - ベースディレクトリ
 * @param idField - IDフィールド名（デフォルト: 'doc_id'）
 * @returns インデックスファイル内容、またはnull（ファイルが存在しない場合）
 * @throws Error - YAMLパースエラーまたはスキーマ検証エラー
 */
export async function loadIndexFile(
  indexPath: string,
  cwd: string = process.cwd(),
  idField: string = 'doc_id'
): Promise<IndexFile | null> {
  const absolutePath = path.isAbsolute(indexPath)
    ? indexPath
    : path.join(cwd, indexPath);

  if (!existsSync(absolutePath)) {
    return null;
  }

  const content = await readFile(absolutePath, 'utf8');
  const parsed = yaml.load(content, YAML_OPTIONS);

  // 動的スキーマによる構造検証
  const schema = createIndexFileSchema(idField);
  const result = schema.safeParse(parsed);
  if (!result.success) {
    const issues = result.error.issues
      .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
      .join(', ');
    throw new Error(`Invalid index file structure: ${issues}`);
  }

  return result.data as IndexFile;
}

/**
 * インデックス内の重複を検出
 * @param entries - インデックスエントリ
 * @param idField - IDフィールド名
 */
function findDuplicatesInIndex(
  entries: IndexEntry[],
  idField: string = 'doc_id'
): LintError[] {
  const errors: LintError[] = [];
  const seenDocIds = new Map<string, string>(); // id → first path

  for (const entry of entries) {
    const docId = getDocIdFromEntry(entry, idField);
    if (!docId) continue; // Zodバリデーション済みのため通常到達しない
    const existingPath = seenDocIds.get(docId);
    if (existingPath) {
      errors.push({
        path: entry.path,
        code: ShirushiErrors.DUPLICATE_DOC_ID_IN_INDEX.code,
        message: `Duplicate ${idField} '${docId}' (also in ${existingPath})`,
        domain: ShirushiErrors.DUPLICATE_DOC_ID_IN_INDEX.domain,
        severity: ShirushiErrors.DUPLICATE_DOC_ID_IN_INDEX.severity,
        details: {
          [idField]: docId,
          first_path: existingPath,
          duplicate_path: entry.path,
        },
      });
    } else {
      seenDocIds.set(docId, entry.path);
    }
  }

  return errors;
}

/**
 * インデックスエントリのファイル存在確認
 * @param entries - インデックスエントリ
 * @param cwd - ベースディレクトリ
 * @param idField - IDフィールド名
 */
function checkMissingFiles(
  entries: IndexEntry[],
  cwd: string,
  idField: string = 'doc_id'
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
          [idField]: entry[idField],
          expected_path: entry.path,
        },
      });
    }
  }

  return errors;
}

/**
 * インデックスがない場合のエラーを検出
 * @param documents - パースされたドキュメント一覧
 * @param idField - IDフィールド名
 */
function checkUnindexedDocumentsWithoutIndex(
  documents: DocumentParseResult[],
  idField: string
): LintError[] {
  const errors: LintError[] = [];
  for (const doc of documents) {
    if (doc.docId) {
      errors.push({
        path: doc.path,
        code: ShirushiErrors.UNINDEXED_DOC_ID.code,
        message: `Document has ${idField} '${doc.docId}' but index file does not exist`,
        domain: ShirushiErrors.UNINDEXED_DOC_ID.domain,
        severity: ShirushiErrors.UNINDEXED_DOC_ID.severity,
        details: { [idField]: doc.docId },
      });
    }
  }
  return errors;
}

/**
 * インデックスをマップに変換
 * @param indexFile - インデックスファイル
 * @param idField - IDフィールド名
 */
function buildIndexMaps(
  indexFile: IndexFile,
  idField: string
): { indexByPath: Map<string, IndexEntry>; indexByDocId: Map<string, IndexEntry> } {
  const indexByPath = new Map<string, IndexEntry>();
  const indexByDocId = new Map<string, IndexEntry>();

  for (const entry of indexFile.documents) {
    const entryDocId = getDocIdFromEntry(entry, idField);
    if (!entryDocId) continue; // Zodバリデーション済みのため通常到達しない
    indexByPath.set(entry.path, entry);
    indexByDocId.set(entryDocId, entry);
  }

  return { indexByPath, indexByDocId };
}

/**
 * ドキュメントとインデックスの整合性エラーを検出
 * @param documents - パースされたドキュメント一覧
 * @param indexByPath - パスでインデックスされたエントリ
 * @param idField - IDフィールド名
 */
function checkDocumentIndexConsistency(
  documents: DocumentParseResult[],
  indexByPath: Map<string, IndexEntry>,
  idField: string
): LintError[] {
  const errors: LintError[] = [];

  for (const doc of documents) {
    if (!doc.docId) continue;

    // Windows互換性のためパスを正規化して比較
    const normalizedPath = normalizePath(doc.path);
    const indexEntry = indexByPath.get(normalizedPath);

    if (!indexEntry) {
      errors.push({
        path: doc.path,
        code: ShirushiErrors.UNINDEXED_DOC_ID.code,
        message: `Document has ${idField} '${doc.docId}' but is not in index`,
        domain: ShirushiErrors.UNINDEXED_DOC_ID.domain,
        severity: ShirushiErrors.UNINDEXED_DOC_ID.severity,
        details: { [idField]: doc.docId },
      });
      continue;
    }

    const indexDocId = getDocIdFromEntry(indexEntry, idField);
    if (!indexDocId) continue; // Zodバリデーション済みのため通常到達しない

    if (indexDocId !== doc.docId) {
      errors.push({
        path: doc.path,
        code: ShirushiErrors.DOC_ID_MISMATCH_WITH_INDEX.code,
        message: `Document ${idField} '${doc.docId}' differs from index entry '${indexDocId}'`,
        domain: ShirushiErrors.DOC_ID_MISMATCH_WITH_INDEX.domain,
        severity: ShirushiErrors.DOC_ID_MISMATCH_WITH_INDEX.severity,
        details: {
          [`document_${idField}`]: doc.docId,
          [`index_${idField}`]: indexDocId,
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
 * @param idField - IDフィールド名（デフォルト: 'doc_id'）
 * @returns 検証結果
 */
export function validateIndexConsistency(
  documents: DocumentParseResult[],
  indexFile: IndexFile | null,
  cwd: string = process.cwd(),
  idField: string = 'doc_id'
): IndexValidationResult {
  // インデックスがない場合
  if (!indexFile) {
    return {
      errors: checkUnindexedDocumentsWithoutIndex(documents, idField),
      indexEntries: new Map(),
      indexByDocId: new Map(),
    };
  }

  // インデックスをマップに変換
  const { indexByPath, indexByDocId } = buildIndexMaps(indexFile, idField);

  // 各種検証を実行
  const errors: LintError[] = [
    ...findDuplicatesInIndex(indexFile.documents, idField),
    ...checkMissingFiles(indexFile.documents, cwd, idField),
    ...checkDocumentIndexConsistency(documents, indexByPath, idField),
  ];

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
