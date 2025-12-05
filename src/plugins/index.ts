/**
 * Shirushi Plugin System
 *
 * プラグインアーキテクチャのpublic API。
 *
 * @example
 * ```typescript
 * import type {
 *   DocumentSource,
 *   IndexStore,
 *   ChangeTracker,
 *   ShirushiPlugin,
 * } from '@/plugins';
 *
 * import {
 *   isDocumentSource,
 *   toPluginIndexEntry,
 * } from '@/plugins';
 * ```
 */

// インターフェースを全てre-export
export type {
  // エラー型
  DocumentSourceError,
  IndexStoreError,
  ChangeTrackerError,
  // DocumentSource
  DocumentReference,
  DocumentContent,
  DocumentFilter,
  DocumentUpdateOptions,
  HealthCheckResult,
  DocumentSource,
  DocumentSourceConfig,
  // IndexStore
  PluginIndexEntry,
  DuplicateInfo,
  DuplicateReport,
  IndexStore,
  IndexStoreConfig,
  // ChangeTracker
  PluginDocIdChange,
  PluginChangeDetectionResult,
  ChangeTracker,
  ChangeTrackerConfig,
} from './interfaces/index.js';

export {
  createDocumentSourceError,
  createIndexStoreError,
  createChangeTrackerError,
} from './interfaces/index.js';

// Plugin型
export type { PluginConfig, ShirushiPlugin, PluginLoader } from './types.js';

// 型ガード
export {
  isDocumentSource,
  isUpdatableDocumentSource,
  isIndexStore,
  isOrphanDetectableIndexStore,
  isChangeTracker,
  isRefValidatableChangeTracker,
  isShirushiPlugin,
  hasDocumentSource,
  hasIndexStore,
  hasChangeTracker,
} from './guards.js';

// 変換ユーティリティ
export {
  toPluginIndexEntry,
  toIndexEntry,
  toPluginDocIdChange,
  toDocIdChange,
  toPluginChangeDetectionResult,
  toChangeDetectionResult,
} from './compat.js';
