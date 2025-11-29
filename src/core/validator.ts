/**
 * Document ID Validator
 *
 * ドキュメントの doc_id を検証するコア機能。
 * テンプレートパーサーとdimensionハンドラを統合し、
 * ID形式の検証を行う。
 *
 * 検証フロー:
 * 1. id_formatからパターンを生成
 * 2. doc_idをパターンでパース
 * 3. 各dimensionをハンドラで検証
 * 4. checksum（あれば）を検証
 */

import {
  type Either,
  left,
  right,
  isLeft,
} from 'fp-ts/Either';

import { getDimensionRegistry, type ValidationError } from '@/dimensions';
import {
  parseTemplate,
  extractDimensionValues,
  type TemplateParseResult,
} from '@/parsers/template';

import type { ShirushiConfig, DimensionDefinition } from '@/config/schema';
import type { ShirushiErrorCode } from '@/errors/definitions';
import type { DocumentMetadata } from '@/types/document';

// 型定義
type Dimension = DimensionDefinition;

/**
 * 検証結果
 */
export interface ValidationResult {
  /** 検証成功ならtrue */
  valid: boolean;
  /** エラー一覧（valid=falseの場合） */
  errors: ValidationError[];
  /** 抽出されたdimension値（検証成功の場合） */
  parsedParts?: Record<string, string>;
}

/**
 * 検証エラー（トップレベル）
 */
export interface ValidatorError {
  code: ShirushiErrorCode;
  message: string;
  context?: Record<string, unknown>;
}

/**
 * 検証入力
 */
export interface ValidationInput {
  /** ドキュメントID */
  docId: string;
  /** ドキュメントのファイルパス（リポジトリルートからの相対パス） */
  documentPath: string;
  /** ドキュメントのメタデータ */
  documentMeta: DocumentMetadata;
}

/**
 * Dimension分類結果
 */
interface ClassifiedDimensions {
  checksumDimensions: Array<{ name: string; dimension: Dimension }>;
  otherDimensions: Array<{ name: string; dimension: Dimension }>;
}

/**
 * テンプレート解析エラーをValidationErrorに変換
 */
function templateErrorToValidationError(
  templateError: { code: ShirushiErrorCode; message: string; context?: Record<string, unknown> },
  docId: string
): ValidationError {
  const err: ValidationError = {
    code: templateError.code,
    message: templateError.message,
    dimensionName: '',
    value: docId,
  };
  if (templateError.context) {
    err.context = templateError.context;
  }
  return err;
}

/**
 * Dimensionをchecksum/その他に分類
 */
function classifyDimensions(
  template: TemplateParseResult,
  dimensions: Record<string, Dimension>
): ClassifiedDimensions {
  const checksumDimensions: Array<{ name: string; dimension: Dimension }> = [];
  const otherDimensions: Array<{ name: string; dimension: Dimension }> = [];

  for (const placeholder of template.placeholders) {
    const dimension = dimensions[placeholder.name];
    if (dimension) {
      if (dimension.type === 'checksum') {
        checksumDimensions.push({ name: placeholder.name, dimension });
      } else {
        otherDimensions.push({ name: placeholder.name, dimension });
      }
    }
  }

  return { checksumDimensions, otherDimensions };
}

/**
 * 単一dimensionを検証
 */
function validateSingleDimension(
  name: string,
  dimension: Dimension,
  parsedParts: Record<string, string>,
  input: ValidationInput
): ValidationError | null {
  const value = parsedParts[name];
  if (value === undefined) return null;

  const registry = getDimensionRegistry();
  const handler = registry.get(dimension.type);

  const result = handler.validate(value, dimension, {
    documentPath: input.documentPath,
    documentMeta: input.documentMeta,
    parsedParts,
    dimensionName: name,
  });

  return isLeft(result) ? result.left : null;
}

/**
 * 複数dimensionを検証
 */
function validateDimensions(
  dimensions: Array<{ name: string; dimension: Dimension }>,
  parsedParts: Record<string, string>,
  input: ValidationInput
): ValidationError[] {
  const errors: ValidationError[] = [];

  for (const { name, dimension } of dimensions) {
    const error = validateSingleDimension(name, dimension, parsedParts, input);
    if (error) {
      errors.push(error);
    }
  }

  return errors;
}

/**
 * doc_idを検証
 *
 * @param input - 検証対象（docId, path, metadata）
 * @param config - Shirushi設定
 * @returns 検証結果
 *
 * @example
 * ```typescript
 * const result = validateDocId(
 *   {
 *     docId: 'PCE-SPEC-2025-0001-Z',
 *     documentPath: 'docs/pce/spec.md',
 *     documentMeta: { doc_type: 'spec', created_at: '2025-01-01' },
 *   },
 *   config
 * );
 *
 * if (result.valid) {
 *   console.log('Valid:', result.parsedParts);
 * } else {
 *   console.error('Errors:', result.errors);
 * }
 * ```
 */
export function validateDocId(
  input: ValidationInput,
  config: ShirushiConfig
): ValidationResult {
  // 1. テンプレートをパース
  const templateResult = parseTemplate(config.id_format, config.dimensions);
  if (isLeft(templateResult)) {
    return {
      valid: false,
      errors: [templateErrorToValidationError(templateResult.left, input.docId)],
    };
  }

  const template = templateResult.right;

  // 2. doc_idをパターンでパース
  const parsedParts = extractDimensionValues(input.docId, template);
  if (!parsedParts) {
    return {
      valid: false,
      errors: [
        {
          code: 'MALFORMED_ID',
          message: `doc_id "${input.docId}" does not match pattern ${template.pattern}`,
          dimensionName: '',
          value: input.docId,
          expected: config.id_format,
        },
      ],
    };
  }

  // 3. Dimensionを分類
  const { checksumDimensions, otherDimensions } = classifyDimensions(
    template,
    config.dimensions
  );

  // 4. checksum以外のdimensionを検証
  const otherErrors = validateDimensions(otherDimensions, parsedParts, input);

  // 5. checksumを検証（他のdimensionが検証済みである必要がある）
  const checksumErrors = validateDimensions(checksumDimensions, parsedParts, input);

  // 結果を返す
  const errors = [...otherErrors, ...checksumErrors];
  if (errors.length > 0) {
    return { valid: false, errors };
  }

  return { valid: true, errors: [], parsedParts };
}

/**
 * 設定からID検証用の正規表現パターンを生成
 *
 * @param config - Shirushi設定
 * @returns パターンまたはエラー
 */
export function buildIdPattern(
  config: ShirushiConfig
): Either<ValidatorError, RegExp> {
  const templateResult = parseTemplate(config.id_format, config.dimensions);

  if (isLeft(templateResult)) {
    const err: ValidatorError = {
      code: templateResult.left.code,
      message: templateResult.left.message,
    };
    if (templateResult.left.context) {
      err.context = templateResult.left.context;
    }
    return left(err);
  }

  return right(templateResult.right.pattern);
}

/**
 * doc_idが有効な形式かどうかを簡易チェック
 *
 * @param docId - チェック対象のID
 * @param config - Shirushi設定
 * @returns 有効ならtrue
 */
export function isValidIdFormat(docId: string, config: ShirushiConfig): boolean {
  const patternResult = buildIdPattern(config);
  if (isLeft(patternResult)) {
    return false;
  }
  return patternResult.right.test(docId);
}

/**
 * 複数ドキュメントを一括検証
 *
 * @param inputs - 検証対象の配列
 * @param config - Shirushi設定
 * @returns 各ドキュメントの検証結果マップ（path → result）
 */
export function validateDocuments(
  inputs: ValidationInput[],
  config: ShirushiConfig
): Map<string, ValidationResult> {
  const results = new Map<string, ValidationResult>();

  for (const input of inputs) {
    const result = validateDocId(input, config);
    results.set(input.documentPath, result);
  }

  return results;
}

/**
 * 一括検証の集計結果
 */
export interface ValidationSummary {
  /** 検証したドキュメント数 */
  total: number;
  /** 検証成功数 */
  valid: number;
  /** 検証失敗数 */
  invalid: number;
  /** エラー一覧（path → errors） */
  errorsByPath: Map<string, ValidationError[]>;
}

/**
 * 検証結果を集計
 *
 * @param results - validateDocumentsの結果
 * @returns 集計結果
 */
export function summarizeResults(
  results: Map<string, ValidationResult>
): ValidationSummary {
  const errorsByPath = new Map<string, ValidationError[]>();
  let valid = 0;
  let invalid = 0;

  for (const [path, result] of results) {
    if (result.valid) {
      valid++;
    } else {
      invalid++;
      errorsByPath.set(path, result.errors);
    }
  }

  return {
    total: results.size,
    valid,
    invalid,
    errorsByPath,
  };
}
