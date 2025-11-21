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

  // Validation Domain (Reserved for future use)
  INVALID_ID_FORMAT: {
    code: 'INVALID_ID_FORMAT',
    message: 'ID format does not match the configured pattern',
    domain: LawDomain.Validation,
    severity: ErrorSeverity.Error,
  },
} as const;

export type ShirushiErrorCode = keyof typeof ShirushiErrors;
