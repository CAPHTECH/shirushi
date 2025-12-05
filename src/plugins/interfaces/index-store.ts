/**
 * Index Store Interface
 *
 * インデックス管理を抽象化するインターフェース。
 * YAMLファイル、SQLite、PostgreSQL等の異なるストアに対応可能。
 *
 * Phase 2で YamlFileIndexStore として現在の index-manager.ts を再構成予定。
 *
 * ADR-0003準拠: ドキュメントが真、インデックスは派生
 * ADR-0007準拠: 明示的syncコマンドでのみ更新
 *
 * LDE準拠: Either型で成功/失敗を表現
 */

import type { IndexStoreError } from './errors.js';
import type { Either } from 'fp-ts/Either';


/**
 * プラグインインデックスエントリ
 * 既存の IndexEntry（snake_case）とは別に camelCase で定義
 * 変換ユーティリティで相互変換可能
 */
export interface PluginIndexEntry {
  /** ドキュメントID */
  readonly docId: string;
  /** ドキュメントパス（displayPath） */
  readonly path: string;
  /** タイトル */
  readonly title?: string;
  /** ドキュメント種別 */
  readonly docType?: string;
  /** ステータス */
  readonly status?: string;
  /** バージョン */
  readonly version?: string;
  /** オーナー */
  readonly owner?: string;
  /** タグ */
  readonly tags?: readonly string[];
  /** カスタムメタデータ */
  readonly extra?: Readonly<Record<string, unknown>>;
}

/**
 * 重複検出情報
 */
export interface DuplicateInfo {
  /** 重複しているdoc_id */
  readonly docId: string;
  /** 重複しているパスの一覧 */
  readonly paths: readonly string[];
}

/**
 * 重複検出レポート
 */
export interface DuplicateReport {
  /** 重複情報の配列 */
  readonly duplicates: readonly DuplicateInfo[];
}

/**
 * IndexStore Interface
 *
 * インデックスストアを抽象化するインターフェース。
 * 依存性注入により、テスト時にモック実装を注入可能。
 *
 * @example
 * ```typescript
 * // モック実装
 * const mockStore: IndexStore = {
 *   name: 'test-store',
 *   async getByDocId(docId) {
 *     return right({ docId, path: 'docs/test.md' });
 *   },
 *   async getByPath(path) {
 *     return right(null);
 *   },
 *   async *listEntries() {
 *     yield { docId: 'DOC-0001', path: 'docs/test.md' };
 *   },
 *   async upsert(entry) {
 *     return right(undefined);
 *   },
 *   async delete(docId) {
 *     return right(true);
 *   },
 *   async findDuplicates() {
 *     return right({ duplicates: [] });
 *   },
 * };
 * ```
 */
export interface IndexStore {
  /** ストア名（ログ・エラーメッセージ用） */
  readonly name: string;

  /**
   * doc_idでエントリを取得
   *
   * @param docId - 検索するdoc_id
   * @returns エントリ。存在しない場合Right(null)
   */
  getByDocId(
    docId: string
  ): Promise<Either<IndexStoreError, PluginIndexEntry | null>>;

  /**
   * パスでエントリを取得
   *
   * @param path - 検索するパス
   * @returns エントリ。存在しない場合Right(null)
   */
  getByPath(
    path: string
  ): Promise<Either<IndexStoreError, PluginIndexEntry | null>>;

  /**
   * 全エントリを取得
   *
   * @returns エントリの非同期イテレータ
   */
  listEntries(): AsyncIterable<PluginIndexEntry>;

  /**
   * エントリを追加または更新
   * ADR-0007準拠: 明示的syncコマンドでのみ呼び出し
   *
   * @param entry - 追加/更新するエントリ
   * @returns 成功時Right(void)
   */
  upsert(entry: PluginIndexEntry): Promise<Either<IndexStoreError, void>>;

  /**
   * エントリを削除
   * ADR-0007準拠: 明示的syncコマンドでのみ呼び出し
   *
   * @param docId - 削除するdoc_id
   * @returns 削除された場合Right(true)、存在しない場合Right(false)
   */
  delete(docId: string): Promise<Either<IndexStoreError, boolean>>;

  /**
   * 重複チェック
   *
   * @returns 重複検出レポート
   */
  findDuplicates(): Promise<Either<IndexStoreError, DuplicateReport>>;

  /**
   * 孤立エントリを検出（オプショナル）
   * 対応するドキュメントがないエントリを検出
   *
   * @param documentPaths - 現存するドキュメントパスの配列
   * @returns 孤立エントリのパス配列
   */
  findOrphans?(
    documentPaths: readonly string[]
  ): Promise<Either<IndexStoreError, readonly string[]>>;
}

/**
 * IndexStore設定
 */
export interface IndexStoreConfig {
  /** インデックスファイルパス（YAMLファイルの場合） */
  readonly indexPath?: string;
  /** 作業ディレクトリ */
  readonly cwd?: string;
  /** ストア固有の追加設定 */
  readonly [key: string]: unknown;
}
