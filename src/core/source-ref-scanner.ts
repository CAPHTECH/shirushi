/**
 * Source Reference Scanner
 *
 * ソースコード内のdoc_id参照を検出する。
 * content_hash変更時に、参照元ソースファイルの確認が必要な場合に警告を出す。
 *
 * 設定例:
 * content_integrity:
 *   enabled: true
 *   source_references:
 *     - glob: "src/**\/*.ts"
 *       pattern: "@see\\s+({DOC_ID})"
 *     - glob: "**\/*.py"
 *       pattern: "# see:\\s+({DOC_ID})"
 */

import { readFile } from 'node:fs/promises';

import fg from 'fast-glob';
import { isLeft } from 'fp-ts/Either';

import { buildIdPattern } from '@/core/validator';
import { logger } from '@/utils/logger';

import type { ShirushiConfig } from '@/config/schema';

/**
 * ソースコード参照
 */
export interface SourceReference {
  /** 参照元ソースファイルパス */
  sourcePath: string;
  /** 参照先doc_id */
  docId: string;
  /** 行番号（1-indexed） */
  lineNumber: number;
  /** マッチしたglobパターン */
  patternGlob: string;
}

/**
 * ソース参照スキャン結果
 */
export interface SourceRefScanResult {
  /** 発見された参照 */
  references: SourceReference[];
  /** スキャンエラー */
  errors: { path: string; message: string }[];
}

/**
 * doc_idにマッチする正規表現パターンを生成
 *
 * id_formatから生成された正規表現を、{DOC_ID}プレースホルダーに展開する。
 *
 * @param pattern - ソース参照パターン（{DOC_ID}を含む）
 * @param config - Shirushi設定
 * @returns 展開された正規表現、またはnull（パターン生成に失敗した場合）
 */
function expandDocIdPattern(pattern: string, config: ShirushiConfig): RegExp | null {
  const patternResult = buildIdPattern(config);
  if (isLeft(patternResult)) {
    return null;
  }
  const docIdRegex = patternResult.right;
  // buildIdPatternは^...$アンカー付きのパターンを返すので、
  // 部分マッチ用にアンカーを除去
  const docIdPattern = docIdRegex.source.replace(/^\^/, '').replace(/\$$/, '');
  // {DOC_ID}をキャプチャグループ付きのdoc_idパターンに置換
  const expandedPattern = pattern.replace(/\{DOC_ID\}/g, `(${docIdPattern})`);
  return new RegExp(expandedPattern, 'g');
}

/**
 * ソースファイルからdoc_id参照をスキャン
 *
 * @param filePath - ソースファイルパス
 * @param patterns - 検索パターン
 * @param patternGlob - このファイルにマッチしたglobパターン
 * @returns 発見された参照
 */
async function scanFileForReferences(
  filePath: string,
  patterns: RegExp[],
  patternGlob: string
): Promise<SourceReference[]> {
  const content = await readFile(filePath, 'utf8');
  const lines = content.split('\n');
  const references: SourceReference[] = [];

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (!line) continue;

    for (const pattern of patterns) {
      // 各行でパターンをリセット（gフラグのlastIndexをリセット）
      pattern.lastIndex = 0;
      let match;
      while ((match = pattern.exec(line)) !== null) {
        // キャプチャグループ1がdoc_id
        const docId = match[1];
        if (docId) {
          references.push({
            sourcePath: filePath,
            docId,
            lineNumber: i + 1, // 1-indexed
            patternGlob,
          });
        }
      }
    }
  }

  return references;
}

/**
 * ソースコードからdoc_id参照をスキャン
 *
 * @param config - Shirushi設定
 * @param cwd - ベースディレクトリ
 * @returns スキャン結果
 */
export async function scanSourceReferences(
  config: ShirushiConfig,
  cwd: string
): Promise<SourceRefScanResult> {
  const sourceRefs = config.content_integrity?.source_references;
  if (!sourceRefs || sourceRefs.length === 0) {
    return { references: [], errors: [] };
  }

  const allReferences: SourceReference[] = [];
  const errors: { path: string; message: string }[] = [];

  // 各パターン設定ごとに処理
  for (const refPattern of sourceRefs) {
    try {
      // 正規表現パターンを展開
      const pattern = expandDocIdPattern(refPattern.pattern, config);
      if (!pattern) {
        errors.push({
          path: refPattern.glob,
          message: 'Failed to build doc_id pattern from id_format',
        });
        continue;
      }

      // globでファイルを取得
      const files = await fg(refPattern.glob, {
        cwd,
        absolute: false,
        onlyFiles: true,
        dot: false,
        ignore: ['node_modules/**', '**/node_modules/**'],
      });

      logger.debug('source-ref.scan', 'Scanning files for pattern', {
        glob: refPattern.glob,
        fileCount: files.length,
      });

      // 各ファイルをスキャン
      for (const file of files) {
        try {
          const filePath = `${cwd}/${file}`;
          const refs = await scanFileForReferences(filePath, [pattern], refPattern.glob);
          // パスを相対パスに変換
          for (const ref of refs) {
            ref.sourcePath = file;
            allReferences.push(ref);
          }
        } catch (error) {
          const message = error instanceof Error ? error.message : 'Unknown error';
          errors.push({ path: file, message });
        }
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Unknown error';
      errors.push({ path: refPattern.glob, message: `Pattern error: ${message}` });
    }
  }

  logger.debug('source-ref.result', 'Source reference scan completed', {
    totalReferences: allReferences.length,
    errorCount: errors.length,
  });

  return { references: allReferences, errors };
}

/**
 * 特定のdoc_idを参照しているソースファイルをフィルタ
 *
 * @param references - 全参照
 * @param docIds - フィルタするdoc_id
 * @returns フィルタされた参照
 */
export function filterReferencesByDocIds(
  references: SourceReference[],
  docIds: string[]
): SourceReference[] {
  const docIdSet = new Set(docIds);
  return references.filter((ref) => docIdSet.has(ref.docId));
}
