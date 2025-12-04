/**
 * Plugin Type Guards
 *
 * プラグインインターフェースの型ガード関数。
 * ランタイムでの型チェックに使用。
 */

import type { ChangeTracker } from './interfaces/change-tracker.js';
import type { DocumentSource } from './interfaces/document-source.js';
import type { IndexStore } from './interfaces/index-store.js';
import type { ShirushiPlugin } from './types.js';

/**
 * DocumentSourceかどうかをチェック
 */
export function isDocumentSource(obj: unknown): obj is DocumentSource {
  return (
    typeof obj === 'object' &&
    obj !== null &&
    'name' in obj &&
    typeof (obj as DocumentSource).name === 'string' &&
    'listDocuments' in obj &&
    typeof (obj as DocumentSource).listDocuments === 'function' &&
    'getDocument' in obj &&
    typeof (obj as DocumentSource).getDocument === 'function'
  );
}

/**
 * 更新可能なDocumentSourceかどうかをチェック
 */
export function isUpdatableDocumentSource(
  source: DocumentSource
): source is DocumentSource & Required<Pick<DocumentSource, 'updateDocument'>> {
  return typeof source.updateDocument === 'function';
}

/**
 * IndexStoreかどうかをチェック
 */
export function isIndexStore(obj: unknown): obj is IndexStore {
  return (
    typeof obj === 'object' &&
    obj !== null &&
    'name' in obj &&
    typeof (obj as IndexStore).name === 'string' &&
    'getByDocId' in obj &&
    typeof (obj as IndexStore).getByDocId === 'function' &&
    'getByPath' in obj &&
    typeof (obj as IndexStore).getByPath === 'function' &&
    'listEntries' in obj &&
    typeof (obj as IndexStore).listEntries === 'function' &&
    'upsert' in obj &&
    typeof (obj as IndexStore).upsert === 'function' &&
    'delete' in obj &&
    typeof (obj as IndexStore).delete === 'function' &&
    'findDuplicates' in obj &&
    typeof (obj as IndexStore).findDuplicates === 'function'
  );
}

/**
 * 孤立エントリ検出可能なIndexStoreかどうかをチェック
 */
export function isOrphanDetectableIndexStore(
  store: IndexStore
): store is IndexStore & Required<Pick<IndexStore, 'findOrphans'>> {
  return typeof store.findOrphans === 'function';
}

/**
 * ChangeTrackerかどうかをチェック
 */
export function isChangeTracker(obj: unknown): obj is ChangeTracker {
  return (
    typeof obj === 'object' &&
    obj !== null &&
    'name' in obj &&
    typeof (obj as ChangeTracker).name === 'string' &&
    'detectChanges' in obj &&
    typeof (obj as ChangeTracker).detectChanges === 'function' &&
    'isAvailable' in obj &&
    typeof (obj as ChangeTracker).isAvailable === 'function'
  );
}

/**
 * 参照検証可能なChangeTrackerかどうかをチェック
 */
export function isRefValidatableChangeTracker(
  tracker: ChangeTracker
): tracker is ChangeTracker & Required<Pick<ChangeTracker, 'isValidRef'>> {
  return typeof tracker.isValidRef === 'function';
}

/**
 * ShirushiPluginかどうかをチェック
 */
export function isShirushiPlugin(obj: unknown): obj is ShirushiPlugin {
  return (
    typeof obj === 'object' &&
    obj !== null &&
    'name' in obj &&
    typeof (obj as ShirushiPlugin).name === 'string' &&
    'version' in obj &&
    typeof (obj as ShirushiPlugin).version === 'string'
  );
}

/**
 * プラグインがDocumentSourceを提供しているかチェック
 */
export function hasDocumentSource(
  plugin: ShirushiPlugin
): plugin is ShirushiPlugin & { documentSource: DocumentSource } {
  return (
    plugin.documentSource !== undefined &&
    isDocumentSource(plugin.documentSource)
  );
}

/**
 * プラグインがIndexStoreを提供しているかチェック
 */
export function hasIndexStore(
  plugin: ShirushiPlugin
): plugin is ShirushiPlugin & { indexStore: IndexStore } {
  return plugin.indexStore !== undefined && isIndexStore(plugin.indexStore);
}

/**
 * プラグインがChangeTrackerを提供しているかチェック
 */
export function hasChangeTracker(
  plugin: ShirushiPlugin
): plugin is ShirushiPlugin & { changeTracker: ChangeTracker } {
  return (
    plugin.changeTracker !== undefined && isChangeTracker(plugin.changeTracker)
  );
}
