/**
 * Law Driven Engineering Error Definitions
 *
 * エラー（法則違反）を一元管理し、構造化された定義を提供します。
 * 各エラーは特定の「法則ドメイン」に属し、重要度とメッセージテンプレートを持ちます。
 */

/**
 * Law Domain Definition
 * 法則ドメインを定義し、エラーの発生元を明確化する
 */
export const LawDomain = {
  Config: 'config',
  Parser: 'parser',
  Validation: 'validation',
  Git: 'git',
  System: 'system',
} as const;

export type LawDomain = (typeof LawDomain)[keyof typeof LawDomain];

/**
 * Error Severity Level
 */
export const ErrorSeverity = {
  Error: 'error',
  Warning: 'warning',
  Info: 'info',
} as const;

export type ErrorSeverity = (typeof ErrorSeverity)[keyof typeof ErrorSeverity];

/**
 * Structured Error Definition
 */
export interface ErrorDefinition {
  code: string;
  message: string;
  domain: LawDomain;
  severity: ErrorSeverity;
  description?: string;
}

/**
 * Centralized Error Definitions
 * 全てのエラー（法則違反）をここで定義する
 */
export const ShirushiErrors = {
  // Parser Domain
  MISSING_ID: {
    code: 'MISSING_ID',
    message: 'doc_id is missing from front matter',
    domain: LawDomain.Parser,
    severity: ErrorSeverity.Error,
    description: 'Document must have a doc_id field in its front matter.',
  },
  MULTIPLE_IDS_IN_DOCUMENT: {
    code: 'MULTIPLE_IDS_IN_DOCUMENT',
    message: 'doc_id appears multiple times in front matter',
    domain: LawDomain.Parser,
    severity: ErrorSeverity.Error,
  },
  INVALID_DOC_ID_TYPE: {
    code: 'INVALID_DOC_ID_TYPE',
    message: 'doc_id must be a string',
    domain: LawDomain.Parser,
    severity: ErrorSeverity.Error,
  },
  INVALID_FRONT_MATTER: {
    code: 'INVALID_FRONT_MATTER',
    message: 'Failed to parse YAML front matter',
    domain: LawDomain.Parser,
    severity: ErrorSeverity.Error,
  },
  INVALID_YAML: {
    code: 'INVALID_YAML',
    message: 'Failed to parse YAML content',
    domain: LawDomain.Parser,
    severity: ErrorSeverity.Error,
  },
  UNSUPPORTED_DOCUMENT: {
    code: 'UNSUPPORTED_DOCUMENT',
    message: 'Unsupported document format',
    domain: LawDomain.Parser,
    severity: ErrorSeverity.Warning,
  },

  // Validation Domain
  INVALID_ID_FORMAT: {
    code: 'INVALID_ID_FORMAT',
    message: 'ID format does not match the configured pattern',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
    description: 'The doc_id does not match the regex pattern derived from id_format.',
  },
  MALFORMED_ID: {
    code: 'MALFORMED_ID',
    message: 'doc_id structure is malformed',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
    description: 'The doc_id cannot be parsed according to the id_format template.',
  },
  INVALID_DIMENSION_VALUE: {
    code: 'INVALID_DIMENSION_VALUE',
    message: 'Dimension value is not in allowed set',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
    description: 'The extracted dimension value is not in the configured values list.',
  },
  INVALID_ID_CHECKSUM: {
    code: 'INVALID_ID_CHECKSUM',
    message: 'Checksum does not match computed value',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
    description: 'The checksum in doc_id does not match the calculated checksum.',
  },
  DIMENSION_MISMATCH: {
    code: 'DIMENSION_MISMATCH',
    message: 'Dimension value does not match document metadata',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
    description: 'The dimension value in doc_id conflicts with document metadata (e.g., doc_type vs KIND).',
  },
  INVALID_YEAR_VALUE: {
    code: 'INVALID_YEAR_VALUE',
    message: 'Year dimension has invalid format',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
    description: 'The year value does not match the expected digit count.',
  },
  INVALID_SERIAL_VALUE: {
    code: 'INVALID_SERIAL_VALUE',
    message: 'Serial dimension has invalid format',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
    description: 'The serial value does not match the expected digit count.',
  },
  MISSING_DOC_TYPE: {
    code: 'MISSING_DOC_TYPE',
    message: 'doc_type is required but missing from metadata',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
    description: 'enum_from_doc_type dimension requires doc_type in document metadata.',
  },
  UNKNOWN_DOC_TYPE: {
    code: 'UNKNOWN_DOC_TYPE',
    message: 'doc_type is not in the mapping',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
    description: 'The doc_type value is not defined in the dimension mapping.',
  },

  // Template Domain
  INVALID_TEMPLATE: {
    code: 'INVALID_TEMPLATE',
    message: 'id_format template is invalid',
    domain: LawDomain.Config,
    severity: ErrorSeverity.Error,
    description: 'The id_format template has syntax errors or missing placeholders.',
  },
  UNDEFINED_DIMENSION: {
    code: 'UNDEFINED_DIMENSION',
    message: 'Placeholder references undefined dimension',
    domain: LawDomain.Config,
    severity: ErrorSeverity.Error,
    description: 'A placeholder in id_format does not have a corresponding dimension definition.',
  },
} as const;

export type ShirushiErrorCode = keyof typeof ShirushiErrors;
