/**
 * Template Parser
 *
 * id_format テンプレート文字列を解析し、正規表現パターンと
 * プレースホルダー情報を生成します。
 *
 * 例: "{COMP}-{KIND}-{YEAR4}" → /^(PCE|KKS)-(SPEC|DES)-(\d{4})$/
 *
 * LDE準拠: Either型で成功/失敗を表現
 */

import { type Either, left, right } from 'fp-ts/Either';

import { escapeRegex } from '@/utils/regex';

import type { DimensionDefinition } from '@/config/schema';
import type { ShirushiErrorCode } from '@/errors/definitions';

// Dimension型
type Dimension = DimensionDefinition;
type DimensionsMap = Record<string, Dimension>;

/**
 * プレースホルダー情報
 */
export interface PlaceholderInfo {
  /** プレースホルダー名（COMP, KIND等） */
  name: string;
  /** テンプレート内の出現位置（0始まり） */
  position: number;
  /** 正規表現のキャプチャグループ番号（1始まり） */
  captureGroup: number;
}

/**
 * テンプレート解析結果
 */
export interface TemplateParseResult {
  /** プレースホルダー情報（出現順） */
  placeholders: PlaceholderInfo[];
  /** ID全体にマッチする正規表現 */
  pattern: RegExp;
  /** リテラルセグメント（プレースホルダー間の文字列） */
  literalSegments: string[];
}

/**
 * テンプレート解析エラー
 */
export interface TemplateParseError {
  code: ShirushiErrorCode;
  message: string;
  context?: Record<string, unknown>;
}

/**
 * プレースホルダーマッチ情報
 */
interface PlaceholderMatch {
  name: string;
  start: number;
  end: number;
}

/**
 * Dimensionから正規表現パターンを生成
 *
 * @param dimension - dimension定義
 * @returns キャプチャグループ付きのパターン文字列
 */
function dimensionToPattern(dimension: Dimension): string {
  switch (dimension.type) {
    case 'enum': {
      // enum値の選択肢をOR結合: (PCE|KKS|EDGE)
      const escaped = dimension.values.map(escapeRegex);
      return `(${escaped.join('|')})`;
    }

    case 'enum_from_doc_type': {
      // mapping値（変換後の値）から選択肢を生成
      const values = Object.values(dimension.mapping);
      const escaped = values.map((v) => escapeRegex(v));
      return `(${escaped.join('|')})`;
    }

    case 'year': {
      // 指定桁数の数字: (\d{4})
      return `(\\d{${dimension.digits}})`;
    }

    case 'serial': {
      // 指定桁数の数字: (\d{4})
      return `(\\d{${dimension.digits}})`;
    }

    case 'checksum': {
      // mod26AZは常に1文字のA-Z: ([A-Z])
      // 将来的に他のアルゴリズムに対応する場合はここを拡張
      return '([A-Z])';
    }

    default: {
      // exhaustive check - 将来的に新しいdimension typeが追加された場合にコンパイルエラーになる
      throw new Error(`Unknown dimension type: ${JSON.stringify(dimension)}`);
    }
  }
}

/**
 * テンプレート形式を検証
 *
 * @param template - テンプレート文字列
 * @returns エラーまたはnull（成功時）
 */
function validateTemplateFormat(template: string): TemplateParseError | null {
  // 空テンプレートチェック
  if (!template || template.length === 0) {
    return {
      code: 'INVALID_TEMPLATE',
      message: 'Template cannot be empty',
      context: { template },
    };
  }

  // ブレースの整合性チェック
  const openBraces = (template.match(/\{/g) || []).length;
  const closeBraces = (template.match(/\}/g) || []).length;
  if (openBraces !== closeBraces) {
    return {
      code: 'INVALID_TEMPLATE',
      message: 'Template has unclosed braces',
      context: { template, openBraces, closeBraces },
    };
  }

  return null;
}

/**
 * テンプレートからプレースホルダーマッチを抽出
 *
 * @param template - テンプレート文字列
 * @returns プレースホルダーマッチの配列
 */
function extractPlaceholderMatches(template: string): PlaceholderMatch[] {
  const matches: PlaceholderMatch[] = [];
  const regex = /\{([A-Za-z0-9_]+)\}/g;
  let match: RegExpExecArray | null;

  while ((match = regex.exec(template)) !== null) {
    const name = match[1];
    if (name !== undefined) {
      matches.push({
        name,
        start: match.index,
        end: match.index + match[0].length,
      });
    }
  }

  return matches;
}

/**
 * プレースホルダーマッチからパターンとプレースホルダー情報を構築
 *
 * @param template - テンプレート文字列
 * @param matches - プレースホルダーマッチの配列
 * @param dimensions - dimension定義のマップ
 * @returns 構築結果またはエラー
 */
function buildPatternFromMatches(
  template: string,
  matches: PlaceholderMatch[],
  dimensions: DimensionsMap
): Either<TemplateParseError, TemplateParseResult> {
  const placeholders: PlaceholderInfo[] = [];
  const literalSegments: string[] = [];
  const patternParts: string[] = [];
  let lastIndex = 0;
  let captureGroup = 1;

  for (const [index, m] of matches.entries()) {
    // プレースホルダー前のリテラル
    const literal = template.slice(lastIndex, m.start);
    literalSegments.push(literal);
    if (literal) {
      patternParts.push(escapeRegex(literal));
    }

    // dimension定義の存在チェック
    const dimension = dimensions[m.name];
    if (!dimension) {
      return left({
        code: 'UNDEFINED_DIMENSION',
        message: `Placeholder "${m.name}" is not defined in dimensions`,
        context: { template, placeholder: m.name, availableDimensions: Object.keys(dimensions) },
      });
    }

    // プレースホルダー情報を記録
    placeholders.push({
      name: m.name,
      position: index,
      captureGroup: captureGroup++,
    });

    // dimensionからパターンを生成
    patternParts.push(dimensionToPattern(dimension));

    lastIndex = m.end;
  }

  // 最後のリテラル
  const lastLiteral = template.slice(lastIndex);
  literalSegments.push(lastLiteral);
  if (lastLiteral) {
    patternParts.push(escapeRegex(lastLiteral));
  }

  // 完全一致の正規表現を構築
  const pattern = new RegExp(`^${patternParts.join('')}$`);

  return right({
    placeholders,
    pattern,
    literalSegments,
  });
}

/**
 * id_format テンプレートを解析
 *
 * @param template - id_format文字列（例: "{COMP}-{KIND}-{YEAR4}"）
 * @param dimensions - dimension定義のマップ
 * @returns 解析結果またはエラー
 *
 * @example
 * ```typescript
 * const result = parseTemplate('{COMP}-{KIND}', {
 *   COMP: { type: 'enum', values: ['PCE'] },
 *   KIND: { type: 'enum', values: ['SPEC'] },
 * });
 * if (isRight(result)) {
 *   console.log(result.right.pattern); // /^(PCE)-(SPEC)$/
 * }
 * ```
 */
export function parseTemplate(
  template: string,
  dimensions: DimensionsMap
): Either<TemplateParseError, TemplateParseResult> {
  // 1. テンプレート形式を検証
  const formatError = validateTemplateFormat(template);
  if (formatError) {
    return left(formatError);
  }

  // 2. プレースホルダーを抽出
  const matches = extractPlaceholderMatches(template);

  // 3. プレースホルダーの存在チェック
  if (matches.length === 0) {
    return left({
      code: 'INVALID_TEMPLATE',
      message: 'Template must contain at least one placeholder {NAME}',
      context: { template },
    });
  }

  // 4. パターンを構築
  return buildPatternFromMatches(template, matches, dimensions);
}

/**
 * doc_idからdimension値を抽出
 *
 * @param docId - ドキュメントID
 * @param parseResult - テンプレート解析結果
 * @returns dimension名 → 値 のマップ、またはnull（マッチしない場合）
 */
export function extractDimensionValues(
  docId: string,
  parseResult: TemplateParseResult
): Record<string, string> | null {
  const match = parseResult.pattern.exec(docId);
  if (!match) {
    return null;
  }

  const result: Record<string, string> = {};
  for (const placeholder of parseResult.placeholders) {
    const value = match[placeholder.captureGroup];
    if (value !== undefined) {
      result[placeholder.name] = value;
    }
  }

  return result;
}
