import type {
  ErrorSeverity,
  LawDomain,
  ShirushiErrorCode,
} from '../errors/definitions.js';

export type DocumentKind = 'markdown' | 'yaml';

// Use centralized error codes
export type DocumentProblemCode = ShirushiErrorCode;

export interface DocumentProblem {
  code: DocumentProblemCode;
  message: string;
  domain: LawDomain;
  severity: ErrorSeverity;
  details?: Record<string, unknown>;
}

export interface DocumentMetadata {
  title?: string;
  doc_type?: string;
  status?: string;
  version?: string;
  owner?: string;
  superseded_by?: string;
  tags?: string[];
  [key: string]: unknown;
}

export interface DocumentParseResult {
  kind: DocumentKind;
  path: string;
  docId?: string | undefined;
  metadata: DocumentMetadata;
  problems: DocumentProblem[];
  /** ドキュメント本文（content_integrity有効時のみ） */
  content?: string;
}
