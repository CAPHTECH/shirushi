/**
 * Plugin Interface Error Definitions
 *
 * プラグインインターフェースで使用するエラー型。
 * 既存の GitError パターンに準拠。
 *
 * LDE準拠: Either型で成功/失敗を表現
 */

/**
 * DocumentSource操作エラー
 */
export interface DocumentSourceError {
  /** エラーコード */
  readonly code: string;
  /** エラーメッセージ */
  readonly message: string;
  /** 追加コンテキスト情報 */
  readonly context?: {
    /** ドキュメント参照ID */
    readonly documentId?: string;
    /** 表示用パス */
    readonly displayPath?: string;
    /** 元のエラーメッセージ */
    readonly originalError?: string;
    /** 追加情報 */
    readonly [key: string]: unknown;
  };
}

/**
 * IndexStore操作エラー
 */
export interface IndexStoreError {
  /** エラーコード */
  readonly code: string;
  /** エラーメッセージ */
  readonly message: string;
  /** 追加コンテキスト情報 */
  readonly context?: {
    /** 対象のdoc_id */
    readonly docId?: string;
    /** 対象のパス */
    readonly path?: string;
    /** 元のエラーメッセージ */
    readonly originalError?: string;
    /** 追加情報 */
    readonly [key: string]: unknown;
  };
}

/**
 * ChangeTracker操作エラー
 */
export interface ChangeTrackerError {
  /** エラーコード */
  readonly code: string;
  /** エラーメッセージ */
  readonly message: string;
  /** 追加コンテキスト情報 */
  readonly context?: {
    /** 比較対象の参照 */
    readonly baseRef?: string;
    /** 対象のパス */
    readonly path?: string;
    /** 元のエラーメッセージ */
    readonly originalError?: string;
    /** 追加情報 */
    readonly [key: string]: unknown;
  };
}

/**
 * DocumentSourceErrorを生成するヘルパー関数
 */
export function createDocumentSourceError(
  code: string,
  message: string,
  context?: DocumentSourceError['context']
): DocumentSourceError {
  if (context === undefined) {
    return { code, message };
  }
  return { code, message, context };
}

/**
 * IndexStoreErrorを生成するヘルパー関数
 */
export function createIndexStoreError(
  code: string,
  message: string,
  context?: IndexStoreError['context']
): IndexStoreError {
  if (context === undefined) {
    return { code, message };
  }
  return { code, message, context };
}

/**
 * ChangeTrackerErrorを生成するヘルパー関数
 */
export function createChangeTrackerError(
  code: string,
  message: string,
  context?: ChangeTrackerError['context']
): ChangeTrackerError {
  if (context === undefined) {
    return { code, message };
  }
  return { code, message, context };
}
