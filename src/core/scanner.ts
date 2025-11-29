/**
 * Document Scanner
 *
 * doc_globsパターンに基づいてドキュメントを探索し、
 * 各ドキュメントをパースして結果を返す。
 *
 * 対応フォーマット:
 * - Markdown (.md) - front matterからdoc_idを抽出
 * - YAML (.yaml, .yml) - ルートオブジェクトからdoc_idを抽出
 */

import path from 'node:path';

import fg from 'fast-glob';

import { parseMarkdownFile } from '@/parsers/markdown';
import { parseYamlFile } from '@/parsers/yaml';

import type { ShirushiConfig } from '@/config/schema';
import type { DocumentParseResult } from '@/types/document';

/**
 * スキャン結果
 */
export interface ScanResult {
  /** パースされたドキュメント一覧 */
  documents: DocumentParseResult[];
  /** スキャンサマリー */
  summary: ScanSummary;
}

/**
 * スキャンサマリー
 */
export interface ScanSummary {
  /** 発見されたファイル数 */
  totalFiles: number;
  /** Markdownファイル数 */
  markdownFiles: number;
  /** YAMLファイル数 */
  yamlFiles: number;
  /** doc_idを持つドキュメント数 */
  withDocId: number;
  /** doc_idを持たないドキュメント数 */
  withoutDocId: number;
  /** パース問題のあるドキュメント数 */
  withProblems: number;
}

/**
 * スキャンオプション
 */
export interface ScanOptions {
  /** ベースディレクトリ（デフォルト: cwd） */
  cwd?: string;
  /** 特定のファイルのみをスキャン（フィルタリング用） */
  filterPaths?: string[];
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
 * 単一ファイルをパース
 */
async function parseDocument(
  filePath: string,
  cwd: string
): Promise<DocumentParseResult | null> {
  const kind = getDocumentKind(filePath);
  if (!kind) return null;

  const absolutePath = path.isAbsolute(filePath)
    ? filePath
    : path.join(cwd, filePath);
  const relativePath = path.relative(cwd, absolutePath);

  if (kind === 'markdown') {
    const result = await parseMarkdownFile(absolutePath);
    // 相対パスに正規化
    return { ...result, path: relativePath };
  } else {
    const result = await parseYamlFile(absolutePath);
    return { ...result, path: relativePath };
  }
}

/**
 * ドキュメントをスキャン
 *
 * @param config - Shirushi設定
 * @param options - スキャンオプション
 * @returns スキャン結果
 *
 * @example
 * ```typescript
 * const config = await loadConfig();
 * const result = await scanDocuments(config.config);
 *
 * console.log(`Found ${result.summary.totalFiles} documents`);
 * for (const doc of result.documents) {
 *   console.log(`${doc.path}: ${doc.docId ?? 'NO ID'}`);
 * }
 * ```
 */
export async function scanDocuments(
  config: ShirushiConfig,
  options: ScanOptions = {}
): Promise<ScanResult> {
  const cwd = options.cwd ?? process.cwd();

  // fast-globで対象ファイルを探索
  const files = await fg(config.doc_globs, {
    cwd,
    absolute: false,
    onlyFiles: true,
    dot: false,
  });

  // filterPathsが指定されていれば絞り込み
  const filterPaths = options.filterPaths;
  const targetFiles = filterPaths
    ? files.filter((f) => filterPaths.includes(f))
    : files;

  // 各ファイルを並列でパース
  const parsePromises = targetFiles.map((file) => parseDocument(file, cwd));
  const results = await Promise.all(parsePromises);

  // nullを除外（サポート外拡張子）
  const documents = results.filter(
    (r): r is DocumentParseResult => r !== null
  );

  // サマリーを計算
  const summary = calculateSummary(documents);

  return { documents, summary };
}

/**
 * サマリーを計算
 */
function calculateSummary(documents: DocumentParseResult[]): ScanSummary {
  let markdownFiles = 0;
  let yamlFiles = 0;
  let withDocId = 0;
  let withoutDocId = 0;
  let withProblems = 0;

  for (const doc of documents) {
    if (doc.kind === 'markdown') {
      markdownFiles++;
    } else {
      yamlFiles++;
    }

    if (doc.docId) {
      withDocId++;
    } else {
      withoutDocId++;
    }

    if (doc.problems.length > 0) {
      withProblems++;
    }
  }

  return {
    totalFiles: documents.length,
    markdownFiles,
    yamlFiles,
    withDocId,
    withoutDocId,
    withProblems,
  };
}

/**
 * 特定のパスのみをスキャン
 * （--changed-only用のヘルパー）
 */
export async function scanSpecificPaths(
  paths: string[],
  _config: ShirushiConfig,
  cwd: string = process.cwd()
): Promise<ScanResult> {
  const parsePromises = paths.map((file) => parseDocument(file, cwd));
  const results = await Promise.all(parsePromises);

  const documents = results.filter(
    (r): r is DocumentParseResult => r !== null
  );

  const summary = calculateSummary(documents);

  return { documents, summary };
}
