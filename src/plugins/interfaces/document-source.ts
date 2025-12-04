/**
 * Document Source Interface
 *
 * ドキュメントの取得・列挙を抽象化するインターフェース。
 * ファイルシステム、データベース、API等の異なるソースに対応可能。
 *
 * Phase 2で FileSystemSource として現在の scanner.ts を再構成予定。
 *
 * LDE準拠: Either型で成功/失敗を表現
 */

import type { DocumentSourceError } from './errors.js';
import type { DocumentKind, DocumentMetadata } from '@/types/document';
import type { Either } from 'fp-ts/Either';



/**
 * ドキュメント参照
 * ソース内でドキュメントを一意に識別する軽量な識別子
 */
export interface DocumentReference {
  /** 一意識別子（ファイルパス、DB ID、APIリソースID等） */
  readonly id: string;
  /** 表示用パス（人間が読める形式） */
  readonly displayPath: string;
  /** ドキュメント種別 */
  readonly kind: DocumentKind;
}

/**
 * ドキュメント内容
 * ソースから取得したドキュメントのデータ
 */
export interface DocumentContent {
  /** 参照情報 */
  readonly ref: DocumentReference;
  /** 抽出されたdoc_id（存在する場合） */
  readonly docId: string | null;
  /** メタデータ */
  readonly metadata: DocumentMetadata;
  /** 生コンテンツ（assign時の書き戻し用、オプショナル） */
  readonly rawContent?: string;
}

/**
 * ドキュメントフィルタ
 * listDocuments での絞り込み条件
 */
export interface DocumentFilter {
  /** パターン（ファイルシステムの場合glob、DBの場合クエリ条件） */
  readonly patterns?: readonly string[];
  /** 特定パス（--changed-only用） */
  readonly paths?: readonly string[];
  /** メタデータフィルタ */
  readonly metadata?: Readonly<Record<string, unknown>>;
  /** 変更日時フィルタ（この日時以降に変更されたもの） */
  readonly modifiedAfter?: Date;
}

/**
 * ドキュメント更新オプション
 */
export interface DocumentUpdateOptions {
  /** 更新するdoc_id */
  readonly docId: string;
  /** 更新するメタデータ（部分更新） */
  readonly metadata?: Partial<DocumentMetadata>;
}

/**
 * ヘルスチェック結果
 */
export interface HealthCheckResult {
  /** 接続可能か */
  readonly ok: boolean;
  /** メッセージ（エラー時の詳細等） */
  readonly message?: string;
}

/**
 * DocumentSource Interface
 *
 * ドキュメントソースを抽象化するインターフェース。
 * 依存性注入により、テスト時にモック実装を注入可能。
 *
 * @example
 * ```typescript
 * // モック実装
 * const mockSource: DocumentSource = {
 *   name: 'test-source',
 *   async *listDocuments() {
 *     yield { id: '1', displayPath: 'docs/test.md', kind: 'markdown' };
 *   },
 *   async getDocument(ref) {
 *     return right({ ref, docId: 'DOC-0001', metadata: {} });
 *   },
 * };
 * ```
 */
export interface DocumentSource {
  /** ソース名（ログ・エラーメッセージ用） */
  readonly name: string;

  /**
   * ドキュメント一覧を取得
   *
   * @param filter - フィルタ条件（省略時は全件）
   * @returns ドキュメント参照の非同期イテレータ
   */
  listDocuments(filter?: DocumentFilter): AsyncIterable<DocumentReference>;

  /**
   * 単一ドキュメントの内容を取得
   *
   * @param ref - ドキュメント参照
   * @returns ドキュメント内容。存在しない場合Right(null)
   */
  getDocument(
    ref: DocumentReference
  ): Promise<Either<DocumentSourceError, DocumentContent | null>>;

  /**
   * ドキュメントを更新（assign用、オプショナル）
   * v0.2以降で本格使用予定
   *
   * @param ref - ドキュメント参照
   * @param options - 更新オプション
   * @returns 成功時Right(void)
   */
  updateDocument?(
    ref: DocumentReference,
    options: DocumentUpdateOptions
  ): Promise<Either<DocumentSourceError, void>>;

  /**
   * ソースの接続テスト（オプショナル）
   *
   * @returns ヘルスチェック結果
   */
  healthCheck?(): Promise<HealthCheckResult>;
}

/**
 * DocumentSource設定
 */
export interface DocumentSourceConfig {
  /** 作業ディレクトリ（ファイルシステムの場合） */
  readonly cwd?: string;
  /** ソース固有の追加設定 */
  readonly [key: string]: unknown;
}
