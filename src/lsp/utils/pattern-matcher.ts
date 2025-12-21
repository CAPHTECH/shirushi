/**
 * Pattern Matcher for doc_id in source files
 *
 * ソースファイル内の @see docid パターンをマッチングする。
 * 既存のsource-ref-scannerのパターン生成ロジックを再利用。
 *
 * @see ADR-0010: LSP Server Integration
 */

import { isLeft } from 'fp-ts/Either';

import { buildIdPattern } from '@/core/validator';

import type { ShirushiConfig } from '@/config/schema';
import type { Position } from 'vscode-languageserver';

/**
 * マッチ結果
 */
export interface DocIdMatch {
  /** マッチしたdoc_id */
  docId: string;
  /** 開始位置（0-indexed） */
  startOffset: number;
  /** 終了位置（0-indexed） */
  endOffset: number;
  /** 行番号（0-indexed） */
  line: number;
  /** 開始カラム（0-indexed） */
  startCharacter: number;
  /** 終了カラム（0-indexed） */
  endCharacter: number;
}

/**
 * デフォルトの参照パターン
 * @see {doc_id} 形式をサポート
 */
const DEFAULT_PATTERNS = ['@see\\s+({DOC_ID})'];

/**
 * 設定からdoc_idマッチング用のパターンを取得
 *
 * source_ref_patternsが設定されている場合はそれを使用し、
 * 未設定の場合はデフォルトパターンを使用する。
 */
export function getSourceRefPatterns(config: ShirushiConfig): string[] {
  const sourceRefs = config.content_integrity?.source_references;
  if (sourceRefs && sourceRefs.length > 0) {
    return sourceRefs.map((ref) => ref.pattern);
  }
  return DEFAULT_PATTERNS;
}

/**
 * doc_idパターンを正規表現に展開
 *
 * {DOC_ID}プレースホルダーをid_formatから生成した正規表現に置換する。
 */
export function expandDocIdPattern(
  pattern: string,
  config: ShirushiConfig
): RegExp | null {
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
 * テキスト行からdoc_idマッチを検出
 *
 * @param line - 検索対象の行
 * @param lineNumber - 行番号（0-indexed）
 * @param patterns - 検索パターン
 * @returns マッチ結果の配列
 */
export function findDocIdMatchesInLine(
  line: string,
  lineNumber: number,
  patterns: RegExp[]
): DocIdMatch[] {
  const matches: DocIdMatch[] = [];

  for (const pattern of patterns) {
    // 各行でパターンをリセット（gフラグのlastIndexをリセット）
    pattern.lastIndex = 0;
    let match;

    while ((match = pattern.exec(line)) !== null) {
      // キャプチャグループ1がdoc_id
      const docId = match[1];
      if (docId) {
        // doc_idの開始位置を計算（マッチ全体の開始位置 + doc_idまでのオフセット）
        const fullMatch = match[0];
        const docIdStartInMatch = fullMatch.indexOf(docId);
        const startOffset = match.index + docIdStartInMatch;
        const endOffset = startOffset + docId.length;

        matches.push({
          docId,
          startOffset,
          endOffset,
          line: lineNumber,
          startCharacter: startOffset,
          endCharacter: endOffset,
        });
      }
    }
  }

  return matches;
}

/**
 * テキスト全体からdoc_idマッチを検出
 *
 * @param text - 検索対象のテキスト
 * @param config - Shirushi設定
 * @returns マッチ結果の配列
 */
export function findAllDocIdMatches(
  text: string,
  config: ShirushiConfig
): DocIdMatch[] {
  const patterns = getSourceRefPatterns(config);
  const regexPatterns: RegExp[] = [];

  for (const pattern of patterns) {
    const regex = expandDocIdPattern(pattern, config);
    if (regex) {
      regexPatterns.push(regex);
    }
  }

  if (regexPatterns.length === 0) {
    return [];
  }

  const lines = text.split('\n');
  const allMatches: DocIdMatch[] = [];

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (line) {
      const lineMatches = findDocIdMatchesInLine(line, i, regexPatterns);
      allMatches.push(...lineMatches);
    }
  }

  return allMatches;
}

/**
 * 指定位置にあるdoc_idを検出
 *
 * @param text - 検索対象のテキスト
 * @param position - カーソル位置
 * @param config - Shirushi設定
 * @returns 位置にあるdoc_idマッチ、またはnull
 */
export function findDocIdAtPosition(
  text: string,
  position: Position,
  config: ShirushiConfig
): DocIdMatch | null {
  const lines = text.split('\n');
  const line = lines[position.line];

  if (!line) {
    return null;
  }

  const patterns = getSourceRefPatterns(config);
  const regexPatterns: RegExp[] = [];

  for (const pattern of patterns) {
    const regex = expandDocIdPattern(pattern, config);
    if (regex) {
      regexPatterns.push(regex);
    }
  }

  if (regexPatterns.length === 0) {
    return null;
  }

  const lineMatches = findDocIdMatchesInLine(line, position.line, regexPatterns);

  // カーソル位置がマッチ範囲内にあるものを探す
  for (const match of lineMatches) {
    if (
      position.character >= match.startCharacter &&
      position.character <= match.endCharacter
    ) {
      return match;
    }
  }

  return null;
}
