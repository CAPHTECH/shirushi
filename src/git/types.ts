/**
 * Git Operations Type Definitions
 *
 * Git連携機能の型定義。依存性注入（DI）のためのインターフェースを提供し、
 * テスト容易性を確保する。
 *
 * LDE準拠: Either型で成功/失敗を表現
 */

import { type Either } from 'fp-ts/Either';

import type { ShirushiErrorCode } from '@/errors/definitions';

/**
 * 変更検出対象ファイル
 * ChangeDetectorへの入力として使用
 */
export interface DetectionTarget {
  /** 現在のファイルパス */
  path: string;
  /** リネーム前のパス（リネームされた場合のみ） */
  oldPath?: string;
}

/**
 * Git操作エラー情報
 * Git操作失敗時のエラー詳細を構造化して表現
 */
export interface GitError {
  /** エラーコード */
  code: ShirushiErrorCode;
  /** エラーメッセージ */
  message: string;
  /** 追加コンテキスト情報 */
  context?: {
    /** 対象のGit参照 */
    ref?: string;
    /** 対象のファイルパス */
    path?: string;
    /** 元のエラーメッセージ */
    originalError?: string;
  };
}

/**
 * 変更ファイル情報
 * Git差分から取得したファイル変更情報
 */
export interface ChangedFile {
  /** ファイルパス（リポジトリルートからの相対パス） */
  path: string;
  /** 変更ステータス */
  status: 'added' | 'modified' | 'deleted' | 'renamed';
  /** リネーム前のパス（statusが'renamed'の場合のみ） */
  oldPath?: string;
}

/**
 * doc_id変更情報
 * ベースrefとの比較で検出されたdoc_id変更
 */
export interface DocIdChange {
  /** ファイルパス */
  path: string;
  /** 変更前のdoc_id（新規ファイルの場合null） */
  oldDocId: string | null;
  /** 変更後のdoc_id（削除の場合null） */
  newDocId: string | null;
  /** 変更種別 */
  changeType: 'modified' | 'added' | 'deleted';
}

/**
 * 変更検出結果
 * ChangeDetectorの出力
 */
export interface ChangeDetectionResult {
  /** doc_idが変更されたファイル */
  changedDocIds: DocIdChange[];
  /** 新規ファイル（ベースrefに存在しない） */
  newFiles: string[];
  /** 削除ファイル（現在存在しない） */
  deletedFiles: string[];
  /** 処理中に発生したエラー（処理は継続） */
  errors: GitError[];
}

/**
 * Git Operations Interface
 *
 * Git操作を抽象化するインターフェース。
 * 依存性注入により、テスト時にモック実装を注入可能。
 */
export interface GitOperations {
  /**
   * Gitリポジトリかどうかを確認
   *
   * @returns Gitリポジトリの場合Right(true)、そうでない場合Right(false)
   *          エラー時はLeft(GitError)
   */
  isGitRepository(): Promise<Either<GitError, boolean>>;

  /**
   * 指定されたGit参照が有効かどうかを確認
   *
   * @param ref - Git参照（ブランチ名、タグ名、コミットSHA等）
   * @returns 有効な場合Right(true)、無効な場合Right(false)
   *          エラー時はLeft(GitError)
   */
  isValidRef(ref: string): Promise<Either<GitError, boolean>>;

  /**
   * ファイルの内容を取得
   *
   * @param filePath - ファイルパス（リポジトリルートからの相対パス）
   * @param ref - Git参照（省略時は作業ツリーから取得）
   * @returns ファイル内容。ファイルが存在しない場合Right(null)
   *          エラー時はLeft(GitError)
   */
  getFileContent(
    filePath: string,
    ref?: string
  ): Promise<Either<GitError, string | null>>;

  /**
   * 変更されたファイルの一覧を取得
   *
   * @param baseRef - ベースGit参照（省略時はgit statusから取得）
   * @returns 変更ファイルの配列
   *          エラー時はLeft(GitError)
   */
  getChangedFiles(baseRef?: string): Promise<Either<GitError, ChangedFile[]>>;
}

/**
 * Git Operations設定
 */
export interface GitOperationsConfig {
  /** 作業ディレクトリ */
  cwd: string;
  /** タイムアウト（ミリ秒、デフォルト: 30000） */
  timeout?: number;
}
