/**
 * Plugin System Types
 *
 * プラグインシステムの共通型定義。
 * ShirushiPlugin、PluginConfig、PluginLoader等。
 */

import type { ChangeTracker } from './interfaces/change-tracker.js';
import type { DocumentSource } from './interfaces/document-source.js';
import type { IndexStore } from './interfaces/index-store.js';

/**
 * プラグイン設定
 * プラグイン固有の設定を保持
 */
export interface PluginConfig {
  readonly [key: string]: unknown;
}

/**
 * ShirushiPlugin Interface
 *
 * プラグインのメイン定義。
 * 1つ以上のコンポーネント（DocumentSource, IndexStore, ChangeTracker）を提供可能。
 *
 * @example
 * ```typescript
 * // PostgreSQLプラグインの例
 * const postgresPlugin: ShirushiPlugin = {
 *   name: '@shirushi/plugin-postgres',
 *   version: '0.1.0',
 *   documentSource: new PostgresDocumentSource(config),
 *   indexStore: new PostgresIndexStore(config),
 *   async initialize(config) {
 *     await pool.connect();
 *   },
 *   async dispose() {
 *     await pool.end();
 *   },
 * };
 * ```
 */
export interface ShirushiPlugin {
  /** プラグイン名（一意） */
  readonly name: string;
  /** バージョン（semver形式推奨） */
  readonly version: string;

  /** ドキュメントソース実装（オプショナル） */
  readonly documentSource?: DocumentSource;
  /** インデックスストア実装（オプショナル） */
  readonly indexStore?: IndexStore;
  /** 変更トラッカー実装（オプショナル） */
  readonly changeTracker?: ChangeTracker;

  /**
   * 初期化処理（オプショナル）
   * プラグインロード時に呼び出される
   *
   * @param config - プラグイン固有の設定
   */
  initialize?(config: PluginConfig): Promise<void>;

  /**
   * クリーンアップ処理（オプショナル）
   * プラグインアンロード時に呼び出される
   */
  dispose?(): Promise<void>;
}

/**
 * PluginLoader Interface
 *
 * プラグインの読み込み・管理を担当。
 * Phase 3以降で実装予定。
 */
export interface PluginLoader {
  /**
   * プラグインを読み込み
   *
   * @param name - プラグイン名またはパス
   * @param config - プラグイン設定（オプショナル）
   * @returns 読み込んだプラグイン
   */
  load(name: string, config?: PluginConfig): Promise<ShirushiPlugin>;

  /**
   * 読み込み済みプラグイン一覧
   *
   * @returns プラグインの配列
   */
  listLoaded(): readonly ShirushiPlugin[];

  /**
   * プラグインを解放
   *
   * @param name - プラグイン名
   */
  unload(name: string): Promise<void>;
}
