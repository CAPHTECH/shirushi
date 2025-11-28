/**
 * Branded Types for Type-Level Safety (LDE Standard Track)
 *
 * 法則駆動工学（LDE）に準拠した Branded Types 実装。
 * fp-ts の Either を用いて、エラーハンドリングを純粋関数として表現。
 *
 * Branded types (nominal types) は構造的に同一の型を
 * コンパイル時に区別することで型安全性を高める。
 *
 * LDE Reference:
 * - Phase 2: 型による法則の具現化（不可能な状態の排除）
 * - Phase 7: Law Telemetry（法則違反の観測可能性）
 */

import createDebugLogger from 'debug';
import { type Either, isRight, left, right, map, getOrElse } from 'fp-ts/Either';
import { pipe } from 'fp-ts/function';

// Law Telemetry: 法則違反のログ出力
const lawLogger = createDebugLogger('shirushi:law:branded');

/**
 * Base brand type for creating branded types
 * 独自のブランドシンボルを使用して名義型を実現
 */
declare const brand: unique symbol;

type Brand<T, TBrand extends string> = T & {
  readonly [brand]: TBrand;
};

// ============================================================================
// Branded Type Definitions
// ============================================================================

/**
 * DocumentId: Validated document ID string
 *
 * 法則（Invariants）:
 * - Non-empty string
 *
 * Note: ID format pattern matching and checksum validation are performed
 * at a higher level (Validator) with access to configuration context.
 * This branded type ensures only the structural constraint (non-empty).
 */
export type DocumentId = Brand<string, 'DocumentId'>;

/**
 * TemplateString: Validated template format string
 *
 * 法則（Invariants）:
 * - Contains at least one placeholder
 * - All placeholders match {[A-Za-z0-9_]+} pattern
 * - No unclosed braces
 */
export type TemplateString = Brand<string, 'TemplateString'>;

/**
 * PlaceholderName: Validated placeholder name
 *
 * 法則（Invariants）:
 * - Matches [A-Za-z0-9_]+ pattern
 * - Non-empty
 * - No reserved names (e.g., 'doc_type')
 */
export type PlaceholderName = Brand<string, 'PlaceholderName'>;

/**
 * AbsoluteFilePath: Validated absolute file path
 *
 * 法則（Invariants）:
 * - Is an absolute path
 * - No '..' segments (path traversal prevention)
 * - Uses forward slashes (normalized)
 */
export type AbsoluteFilePath = Brand<string, 'AbsoluteFilePath'>;

/**
 * DimensionName: Validated dimension name
 *
 * 法則（Invariants）:
 * - Matches [A-Z][A-Z0-9_]* pattern (uppercase convention)
 * - Not a reserved name
 * - Non-empty
 */
export type DimensionName = Brand<string, 'DimensionName'>;

// ============================================================================
// Validation Error Types (Law-specific errors)
// ============================================================================

/**
 * 法則違反を表すエラー型
 * LDE Phase 7: 観測可能なエラー情報を構造化
 */
export class LawViolationError extends Error {
  constructor(
    public readonly lawName: string,
    public readonly violation: string,
    public readonly context: Record<string, unknown> = {}
  ) {
    super(`${lawName}: ${violation}`);
    this.name = 'LawViolationError';
  }
}

// ============================================================================
// Smart Constructors (Either-based - LDE Standard Track)
// ============================================================================

/**
 * 法則違反のログ出力（Law Telemetry）
 * LDE Phase 7: law.<domain>.<name>.violated 形式
 */
function logViolation(
  lawName: string,
  violation: string,
  context: Record<string, unknown>
): void {
  lawLogger('law.branded.%s.violated: %s %O', lawName, violation, context);
}

/**
 * Validates and brands a string as a DocumentId
 * Either型で成功/失敗を表現（純粋関数）
 *
 * @param value - Raw string to validate
 * @returns Either<LawViolationError, DocumentId>
 */
export function asDocumentId(
  value: string
): Either<LawViolationError, DocumentId> {
  if (typeof value !== 'string' || value.length === 0) {
    const error = new LawViolationError(
      'DocumentId',
      'must be a non-empty string',
      { value, type: typeof value }
    );
    logViolation('DocumentId', error.violation, error.context);
    return left(error);
  }
  // 追加のバリデーションロジックはここに追加可能
  return right(value as DocumentId);
}

/**
 * Validates and brands a string as a TemplateString
 * Either型で成功/失敗を表現（純粋関数）
 *
 * @param value - Raw string to validate
 * @returns Either<LawViolationError, TemplateString>
 */
export function asTemplateString(
  value: string
): Either<LawViolationError, TemplateString> {
  if (typeof value !== 'string') {
    const error = new LawViolationError('TemplateString', 'must be a string', {
      value,
      type: typeof value,
    });
    logViolation('TemplateString', error.violation, error.context);
    return left(error);
  }

  // 構造検証: 閉じていないブレースのチェック
  const openBraces = (value.match(/\{/g) || []).length;
  const closeBraces = (value.match(/\}/g) || []).length;
  if (openBraces !== closeBraces) {
    const error = new LawViolationError(
      'TemplateString',
      'has unclosed braces',
      { value, openBraces, closeBraces }
    );
    logViolation('TemplateString', error.violation, error.context);
    return left(error);
  }

  // 少なくとも1つの有効なプレースホルダーを含む必要がある
  const placeholderRegex = /\{[A-Za-z0-9_]+\}/;
  if (!placeholderRegex.test(value)) {
    const error = new LawViolationError(
      'TemplateString',
      'must contain at least one placeholder {NAME}',
      { value }
    );
    logViolation('TemplateString', error.violation, error.context);
    return left(error);
  }

  return right(value as TemplateString);
}

/**
 * Validates and brands a string as a PlaceholderName
 * Either型で成功/失敗を表現（純粋関数）
 *
 * @param value - Raw string to validate
 * @returns Either<LawViolationError, PlaceholderName>
 */
export function asPlaceholderName(
  value: string
): Either<LawViolationError, PlaceholderName> {
  if (typeof value !== 'string' || value.length === 0) {
    const error = new LawViolationError(
      'PlaceholderName',
      'must be a non-empty string',
      { value, type: typeof value }
    );
    logViolation('PlaceholderName', error.violation, error.context);
    return left(error);
  }

  const validPattern = /^[A-Za-z0-9_]+$/;
  if (!validPattern.test(value)) {
    const error = new LawViolationError(
      'PlaceholderName',
      'must match [A-Za-z0-9_]+ pattern',
      { value }
    );
    logViolation('PlaceholderName', error.violation, error.context);
    return left(error);
  }

  // 予約語チェック
  const reserved = ['doc_type'];
  if (reserved.includes(value.toLowerCase())) {
    const error = new LawViolationError(
      'PlaceholderName',
      `"${value}" is reserved`,
      { value, reserved }
    );
    logViolation('PlaceholderName', error.violation, error.context);
    return left(error);
  }

  return right(value as PlaceholderName);
}

/**
 * Validates and brands a string as an AbsoluteFilePath
 * Either型で成功/失敗を表現（純粋関数）
 *
 * @param value - Raw string to validate
 * @returns Either<LawViolationError, AbsoluteFilePath>
 */
export function asAbsoluteFilePath(
  value: string
): Either<LawViolationError, AbsoluteFilePath> {
  if (typeof value !== 'string' || value.length === 0) {
    const error = new LawViolationError(
      'AbsoluteFilePath',
      'must be a non-empty string',
      { value, type: typeof value }
    );
    logViolation('AbsoluteFilePath', error.violation, error.context);
    return left(error);
  }

  // 絶対パスチェック（Unix: /, Windows: ドライブレター）
  if (!value.startsWith('/') && !/^[A-Za-z]:/.test(value)) {
    const error = new LawViolationError(
      'AbsoluteFilePath',
      'must be an absolute path',
      { value }
    );
    logViolation('AbsoluteFilePath', error.violation, error.context);
    return left(error);
  }

  // パストラバーサル防止（ディレクトリトラバーサルパターンのみ検出）
  // "file..txt" のような正当なファイル名は許可
  const traversalPattern = /(^|[\\/])\.\.($|[\\/])/;
  if (traversalPattern.test(value)) {
    const error = new LawViolationError(
      'AbsoluteFilePath',
      'cannot contain directory traversal segments',
      { value }
    );
    logViolation('AbsoluteFilePath', error.violation, error.context);
    return left(error);
  }

  return right(value as AbsoluteFilePath);
}

/**
 * Validates and brands a string as a DimensionName
 * Either型で成功/失敗を表現（純粋関数）
 *
 * @param value - Raw string to validate
 * @returns Either<LawViolationError, DimensionName>
 */
export function asDimensionName(
  value: string
): Either<LawViolationError, DimensionName> {
  if (typeof value !== 'string' || value.length === 0) {
    const error = new LawViolationError(
      'DimensionName',
      'must be a non-empty string',
      { value, type: typeof value }
    );
    logViolation('DimensionName', error.violation, error.context);
    return left(error);
  }

  const validPattern = /^[A-Z][A-Z0-9_]*$/;
  if (!validPattern.test(value)) {
    const error = new LawViolationError(
      'DimensionName',
      'must match [A-Z][A-Z0-9_]* pattern (uppercase)',
      { value }
    );
    logViolation('DimensionName', error.violation, error.context);
    return left(error);
  }

  return right(value as DimensionName);
}

// ============================================================================
// Type Guards (Either-based)
// ============================================================================

/**
 * Checks if a value is a valid DocumentId without throwing
 */
export function isDocumentId(value: unknown): value is DocumentId {
  if (typeof value !== 'string') return false;
  return isRight(asDocumentId(value));
}

/**
 * Checks if a value is a valid TemplateString without throwing
 */
export function isTemplateString(value: unknown): value is TemplateString {
  if (typeof value !== 'string') return false;
  return isRight(asTemplateString(value));
}

/**
 * Checks if a value is a valid PlaceholderName without throwing
 */
export function isPlaceholderName(value: unknown): value is PlaceholderName {
  if (typeof value !== 'string') return false;
  return isRight(asPlaceholderName(value));
}

/**
 * Checks if a value is a valid AbsoluteFilePath without throwing
 */
export function isAbsoluteFilePath(value: unknown): value is AbsoluteFilePath {
  if (typeof value !== 'string') return false;
  return isRight(asAbsoluteFilePath(value));
}

/**
 * Checks if a value is a valid DimensionName without throwing
 */
export function isDimensionName(value: unknown): value is DimensionName {
  if (typeof value !== 'string') return false;
  return isRight(asDimensionName(value));
}

// ============================================================================
// Utility Functions (fp-ts integration)
// ============================================================================

/**
 * DocumentIdを安全に取得（失敗時はデフォルト値）
 * fp-ts パイプラインでの使用例
 */
export function getDocumentIdOrDefault(
  value: string,
  defaultValue: DocumentId
): DocumentId {
  return pipe(
    asDocumentId(value),
    getOrElse(() => defaultValue)
  );
}

/**
 * TemplateStringを変換（成功時のみ適用）
 */
export function mapTemplateString<T>(
  value: string,
  fn: (t: TemplateString) => T
): Either<LawViolationError, T> {
  return pipe(asTemplateString(value), map(fn));
}

// Re-export fp-ts utilities for convenience
export { type Either, left, right, isRight, pipe, map, getOrElse };
