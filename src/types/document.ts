export type DocumentKind = 'markdown' | 'yaml';

export type DocumentProblemCode =
  | 'MISSING_ID'
  | 'MULTIPLE_IDS_IN_DOCUMENT'
  | 'INVALID_FRONT_MATTER'
  | 'INVALID_YAML'
  | 'UNSUPPORTED_DOCUMENT'
  | 'INVALID_DOC_ID_TYPE';

export interface DocumentProblem {
  code: DocumentProblemCode;
  message: string;
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
  docId?: string;
  metadata: DocumentMetadata;
  problems: DocumentProblem[];
}
