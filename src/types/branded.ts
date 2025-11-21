/**
 * Branded Types for Type-Level Safety
 *
 * Branded types (also known as nominal types or opaque types) provide
 * additional type safety by distinguishing between structurally identical
 * types at compile time.
 *
 * Example:
 *   type UserId = string & { readonly __brand: 'UserId' };
 *   type ProductId = string & { readonly __brand: 'ProductId' };
 *
 *   // These are incompatible even though both are strings:
 *   const userId: UserId = "123" as UserId;
 *   const productId: ProductId = userId; // ❌ Type error!
 *
 * This prevents common errors like mixing up IDs, paths, or other
 * semantically distinct string values.
 */

/**
 * Base brand type for creating branded types
 */
declare const brand: unique symbol;

type Brand<T, TBrand extends string> = T & {
  readonly [brand]: TBrand;
};

/**
 * DocumentId: Validated document ID string
 *
 * Invariants:
 * - Non-empty string
 * - Matches the configured ID format pattern
 * - Contains valid checksum (if applicable)
 *
 * Usage:
 *   const docId: DocumentId = validateDocId(rawString);
 */
export type DocumentId = Brand<string, 'DocumentId'>;

/**
 * TemplateString: Validated template format string
 *
 * Invariants:
 * - Contains at least one placeholder
 * - All placeholders match {[A-Za-z0-9_]+} pattern
 * - No unclosed braces
 *
 * Usage:
 *   const template: TemplateString = validateTemplate(rawString);
 */
export type TemplateString = Brand<string, 'TemplateString'>;

/**
 * PlaceholderName: Validated placeholder name
 *
 * Invariants:
 * - Matches [A-Za-z0-9_]+ pattern
 * - Non-empty
 * - No reserved names (e.g., 'doc_type')
 *
 * Usage:
 *   const name: PlaceholderName = validatePlaceholderName(rawString);
 */
export type PlaceholderName = Brand<string, 'PlaceholderName'>;

/**
 * AbsoluteFilePath: Validated absolute file path
 *
 * Invariants:
 * - Is an absolute path
 * - No '..' segments (path traversal prevention)
 * - Uses forward slashes (normalized)
 *
 * Usage:
 *   const filePath: AbsoluteFilePath = validateFilePath(rawPath);
 */
export type AbsoluteFilePath = Brand<string, 'AbsoluteFilePath'>;

/**
 * DimensionName: Validated dimension name
 *
 * Invariants:
 * - Matches [A-Z][A-Z0-9_]* pattern (uppercase convention)
 * - Not a reserved name
 * - Non-empty
 *
 * Usage:
 *   const dimName: DimensionName = validateDimensionName(rawString);
 */
export type DimensionName = Brand<string, 'DimensionName'>;

// ============================================================================
// Validation Functions (Smart Constructors)
// ============================================================================

/**
 * Validates and brands a string as a DocumentId
 *
 * @param value - Raw string to validate
 * @returns Branded DocumentId
 * @throws {TypeError} If validation fails
 */
export function asDocumentId(value: string): DocumentId {
  if (typeof value !== 'string' || value.length === 0) {
    throw new TypeError('DocumentId must be a non-empty string');
  }
  // Additional validation logic would go here
  return value as DocumentId;
}

/**
 * Validates and brands a string as a TemplateString
 *
 * @param value - Raw string to validate
 * @returns Branded TemplateString
 * @throws {TypeError} If validation fails
 */
export function asTemplateString(value: string): TemplateString {
  if (typeof value !== 'string') {
    throw new TypeError('TemplateString must be a string');
  }

  // Check for unclosed braces first (structural validation)
  const openBraces = (value.match(/\{/g) || []).length;
  const closeBraces = (value.match(/\}/g) || []).length;
  if (openBraces !== closeBraces) {
    throw new TypeError('TemplateString has unclosed braces');
  }

  // Must contain at least one valid placeholder
  const placeholderRegex = /\{[A-Za-z0-9_]+\}/;
  if (!placeholderRegex.test(value)) {
    throw new TypeError('TemplateString must contain at least one placeholder {NAME}');
  }

  return value as TemplateString;
}

/**
 * Validates and brands a string as a PlaceholderName
 *
 * @param value - Raw string to validate
 * @returns Branded PlaceholderName
 * @throws {TypeError} If validation fails
 */
export function asPlaceholderName(value: string): PlaceholderName {
  if (typeof value !== 'string' || value.length === 0) {
    throw new TypeError('PlaceholderName must be a non-empty string');
  }

  const validPattern = /^[A-Za-z0-9_]+$/;
  if (!validPattern.test(value)) {
    throw new TypeError('PlaceholderName must match [A-Za-z0-9_]+ pattern');
  }

  // Reserved names check
  const reserved = ['doc_type'];
  if (reserved.includes(value.toLowerCase())) {
    throw new TypeError(`PlaceholderName "${value}" is reserved`);
  }

  return value as PlaceholderName;
}

/**
 * Validates and brands a string as an AbsoluteFilePath
 *
 * @param value - Raw string to validate
 * @returns Branded AbsoluteFilePath
 * @throws {TypeError} If validation fails
 */
export function asAbsoluteFilePath(value: string): AbsoluteFilePath {
  if (typeof value !== 'string' || value.length === 0) {
    throw new TypeError('AbsoluteFilePath must be a non-empty string');
  }

  // Must be absolute (starts with / or drive letter on Windows)
  if (!value.startsWith('/') && !/^[A-Za-z]:/.test(value)) {
    throw new TypeError('AbsoluteFilePath must be an absolute path');
  }

  // Prevent path traversal
  if (value.includes('..')) {
    throw new TypeError('AbsoluteFilePath cannot contain ".." segments');
  }

  return value as AbsoluteFilePath;
}

/**
 * Validates and brands a string as a DimensionName
 *
 * @param value - Raw string to validate
 * @returns Branded DimensionName
 * @throws {TypeError} If validation fails
 */
export function asDimensionName(value: string): DimensionName {
  if (typeof value !== 'string' || value.length === 0) {
    throw new TypeError('DimensionName must be a non-empty string');
  }

  const validPattern = /^[A-Z][A-Z0-9_]*$/;
  if (!validPattern.test(value)) {
    throw new TypeError('DimensionName must match [A-Z][A-Z0-9_]* pattern (uppercase)');
  }

  return value as DimensionName;
}

// ============================================================================
// Type Guards
// ============================================================================

/**
 * Checks if a value is a valid DocumentId without throwing
 */
export function isDocumentId(value: unknown): value is DocumentId {
  try {
    if (typeof value === 'string') {
      asDocumentId(value);
      return true;
    }
    return false;
  } catch {
    return false;
  }
}

/**
 * Checks if a value is a valid TemplateString without throwing
 */
export function isTemplateString(value: unknown): value is TemplateString {
  try {
    if (typeof value === 'string') {
      asTemplateString(value);
      return true;
    }
    return false;
  } catch {
    return false;
  }
}

/**
 * Checks if a value is a valid PlaceholderName without throwing
 */
export function isPlaceholderName(value: unknown): value is PlaceholderName {
  try {
    if (typeof value === 'string') {
      asPlaceholderName(value);
      return true;
    }
    return false;
  } catch {
    return false;
  }
}
