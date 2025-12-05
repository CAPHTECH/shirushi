/**
 * Plugin Interfaces
 *
 * プラグインアーキテクチャのインターフェース定義を re-export。
 */

// エラー型
export type {
  DocumentSourceError,
  IndexStoreError,
  ChangeTrackerError,
} from './errors.js';

export {
  createDocumentSourceError,
  createIndexStoreError,
  createChangeTrackerError,
} from './errors.js';

// DocumentSource
export type {
  DocumentReference,
  DocumentContent,
  DocumentFilter,
  DocumentUpdateOptions,
  HealthCheckResult,
  DocumentSource,
  DocumentSourceConfig,
} from './document-source.js';

// IndexStore
export type {
  PluginIndexEntry,
  DuplicateInfo,
  DuplicateReport,
  IndexStore,
  IndexStoreConfig,
} from './index-store.js';

// ChangeTracker
export type {
  PluginDocIdChange,
  PluginChangeDetectionResult,
  ChangeTracker,
  ChangeTrackerConfig,
} from './change-tracker.js';
