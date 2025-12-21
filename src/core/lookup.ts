/**
 * Document Lookup Module
 *
 * doc_idからドキュメント情報を取得する。
 * shirushi showコマンドの基盤となるコアロジック。
 *
 * @see Issue #27: shirushi show コマンド
 */

import path from 'node:path';

import { parseMarkdownFile } from '@/parsers/markdown';
import { parseYamlFile } from '@/parsers/yaml';

import {
  loadIndexFile,
  getDocIdFromEntry,
  getIndexFilePath,
} from './index-manager';

import type { IndexEntry } from './index-manager';
import type { ShirushiConfig } from '@/config/schema';
import type { DocumentMetadata, DocumentParseResult } from '@/types/document';


/**
 * Lookup結果
 */
export interface LookupResult {
  /** 成功フラグ */
  success: true;
  /** ドキュメントパス（相対パス） */
  path: string;
  /** doc_id */
  docId: string;
  /** ドキュメントメタデータ */
  metadata: DocumentMetadata;
  /** ドキュメント本文 */
  content: string;
  /** インデックスエントリ（追加情報用） */
  indexEntry: IndexEntry;
}

/**
 * Lookupエラー
 */
export interface LookupError {
  /** 成功フラグ */
  success: false;
  /** エラーコード */
  code: 'DOC_ID_NOT_FOUND' | 'INDEX_NOT_FOUND' | 'FILE_NOT_FOUND' | 'PARSE_ERROR';
  /** エラーメッセージ */
  message: string;
}

export type LookupOutcome = LookupResult | LookupError;

/**
 * Lookupオプション
 */
export interface LookupOptions {
  /** ベースディレクトリ（デフォルト: process.cwd()） */
  cwd?: string;
}

/**
 * ファイル拡張子からドキュメント種別を判定
 */
function getDocumentKind(filePath: string): 'markdown' | 'yaml' | null {
  const ext = path.extname(filePath).toLowerCase();
  if (ext === '.md') return 'markdown';
  if (ext === '.yaml' || ext === '.yml') return 'yaml';
  return null;
}

/**
 * doc_idからドキュメント情報を取得
 *
 * @param docId - 検索するdoc_id
 * @param config - Shirushi設定
 * @param options - オプション
 * @returns Lookup結果またはエラー
 *
 * @example
 * ```typescript
 * const result = await lookupDocument('PCE-SPEC-2025-0001-G', config);
 * if (result.success) {
 *   console.log(`Path: ${result.path}`);
 *   console.log(`Title: ${result.metadata.title}`);
 * } else {
 *   console.error(result.message);
 * }
 * ```
 */
export async function lookupDocument(
  docId: string,
  config: ShirushiConfig,
  options: LookupOptions = {}
): Promise<LookupOutcome> {
  const cwd = options.cwd ?? process.cwd();
  const idField = config.id_field ?? 'doc_id';

  // 1. インデックスファイルを読み込み
  const indexPath = getIndexFilePath(config.index_file, cwd);
  const indexFile = await loadIndexFile(indexPath, cwd, idField);

  if (!indexFile) {
    return {
      success: false,
      code: 'INDEX_NOT_FOUND',
      message: `Index file not found: ${config.index_file ?? 'docs/doc_index.yaml'}. Run "shirushi scan" first.`,
    };
  }

  // 2. doc_idからインデックスエントリを検索
  const indexEntry = indexFile.documents.find(
    (entry) => getDocIdFromEntry(entry, idField) === docId
  );

  if (!indexEntry) {
    return {
      success: false,
      code: 'DOC_ID_NOT_FOUND',
      message: `doc_id '${docId}' not found in index`,
    };
  }

  // 3. ドキュメントをパース
  const absolutePath = path.join(cwd, indexEntry.path);
  const kind = getDocumentKind(indexEntry.path);

  if (!kind) {
    return {
      success: false,
      code: 'PARSE_ERROR',
      message: `Unsupported document format: ${indexEntry.path}`,
    };
  }

  let parseResult: DocumentParseResult;
  try {
    if (kind === 'markdown') {
      parseResult = await parseMarkdownFile(absolutePath, idField, true);
    } else {
      parseResult = await parseYamlFile(absolutePath, idField, true);
    }
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);
    return {
      success: false,
      code: 'FILE_NOT_FOUND',
      message: `Failed to read document: ${errorMessage}`,
    };
  }

  // 4. 成功結果を返す
  return {
    success: true,
    path: indexEntry.path,
    docId,
    metadata: parseResult.metadata,
    content: parseResult.content ?? '',
    indexEntry,
  };
}
