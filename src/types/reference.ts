/**
 * Reference Types
 *
 * 文書間参照の型定義
 *
 * Issue #15: doc_id変更時の文書間参照整合性チェック機能
 */

/**
 * 参照の種類
 * - markdown_link: Markdownリンク [text](doc_id)
 * - yaml_field: YAMLフィールド（superseded_by等）
 * - custom_pattern: カスタムパターン（reference_patternsで定義）
 */
export type ReferenceKind = 'markdown_link' | 'yaml_field' | 'custom_pattern';

/**
 * ドキュメント内で発見された参照
 *
 * 法則（Invariants）:
 * - sourcePath は常にリポジトリルートからの相対パス
 * - targetDocId は id_format にマッチする形式
 */
export interface DocumentReference {
  /** 参照元ドキュメントのパス */
  sourcePath: string;
  /** 参照先doc_id */
  targetDocId: string;
  /** 参照の種類 */
  kind: ReferenceKind;
  /** 行番号（1-indexed） */
  lineNumber?: number;
  /** フィールド名（yaml_fieldの場合） */
  fieldName?: string;
  /** パターン名（custom_patternの場合） */
  patternName?: string;
}

/**
 * 古い参照（更新が必要な参照）
 *
 * doc_idが変更された後も、旧doc_idを参照している状態。
 * これはSTALE_REFERENCEエラーとして報告される。
 */
export interface StaleReference {
  /** 参照元ドキュメントのパス */
  sourcePath: string;
  /** 古いdoc_id（参照先） */
  oldDocId: string;
  /** 新しいdoc_id（削除の場合はnull） */
  newDocId: string | null;
  /** 変更元ドキュメントのパス */
  changedDocPath: string;
  /** 参照の種類 */
  kind: ReferenceKind;
  /** 行番号 */
  lineNumber?: number;
  /** フィールド名 */
  fieldName?: string;
  /** パターン名 */
  patternName?: string;
}

/**
 * 参照スキャン結果
 */
export interface ReferenceScanResult {
  /** 発見された参照 */
  references: DocumentReference[];
  /** スキャン中のエラー */
  errors: ReferenceScanError[];
}

/**
 * 参照スキャン中のエラー
 */
export interface ReferenceScanError {
  /** エラーが発生したファイルパス */
  path: string;
  /** エラーメッセージ */
  message: string;
}

/**
 * 参照検証結果
 */
export interface ReferenceValidationResult {
  /** 古い参照の一覧 */
  staleReferences: StaleReference[];
}
