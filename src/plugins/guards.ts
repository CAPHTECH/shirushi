/**
 * Plugin Type Guards
 *
 * プラグインインターフェースの型ガード関数。
 * ランタイムでの型チェックに使用。
 *
 * @remarks
 * これらの型ガードは構造的な存在チェックのみを行い、
 * メソッドの戻り値型（Promise<Either<...>>等）は検証しません。
 * プラグイン開発者は、インターフェースの型定義に従って
 * 正しい戻り値を返す責任があります。
 */

import type { ChangeTracker } from './interfaces/change-tracker.js';
import type { DocumentSource } from './interfaces/document-source.js';
import type { IndexStore } from './interfaces/index-store.js';
import type { ShirushiPlugin } from './types.js';

// ============================================================
// Helper Functions (complexity軽減のため分離)
// ============================================================

/**
 * オブジェクトかつnullでないことをチェック
 */
function isNonNullObject(obj: unknown): obj is Record<string, unknown> {
  return typeof obj === 'object' && obj !== null;
}

/**
 * 指定プロパティが存在し、string型であることをチェック
 */
function hasStringProperty(obj: Record<string, unknown>, key: string): boolean {
  return key in obj && typeof obj[key] === 'string';
}

/**
 * 指定プロパティが存在し、function型であることをチェック
 */
function hasFunctionProperty(
  obj: Record<string, unknown>,
  key: string
): boolean {
  return key in obj && typeof obj[key] === 'function';
}

/**
 * 複数のプロパティがすべてfunction型であることをチェック
 */
function hasAllFunctionProperties(
  obj: Record<string, unknown>,
  keys: readonly string[]
): boolean {
  return keys.every((key) => hasFunctionProperty(obj, key));
}

// ============================================================
// Main Type Guards
// ============================================================

/**
 * DocumentSourceかどうかをチェック
 *
 * @remarks
 * 以下のプロパティの存在と型のみを検証します：
 * - name: string
 * - listDocuments: function
 * - getDocument: function
 *
 * 戻り値の型（AsyncIterable、Promise<Either<...>>）は検証されません。
 *
 * @param obj - チェック対象のオブジェクト
 * @returns DocumentSourceの場合true
 *
 * @example
 * ```typescript
 * if (isDocumentSource(plugin.documentSource)) {
 *   // plugin.documentSource は DocumentSource 型として使用可能
 *   for await (const doc of plugin.documentSource.listDocuments()) {
 *     // ...
 *   }
 * }
 * ```
 */
export function isDocumentSource(obj: unknown): obj is DocumentSource {
  if (!isNonNullObject(obj)) return false;

  return (
    hasStringProperty(obj, 'name') &&
    hasAllFunctionProperties(obj, ['listDocuments', 'getDocument'])
  );
}

/**
 * 更新可能なDocumentSourceかどうかをチェック
 *
 * @remarks
 * updateDocumentメソッドが存在することを検証します。
 *
 * @param source - チェック対象のDocumentSource
 * @returns updateDocumentが利用可能な場合true
 */
export function isUpdatableDocumentSource(
  source: DocumentSource
): source is DocumentSource & Required<Pick<DocumentSource, 'updateDocument'>> {
  return typeof source.updateDocument === 'function';
}

/**
 * IndexStoreかどうかをチェック
 *
 * @remarks
 * 以下のプロパティの存在と型のみを検証します：
 * - name: string
 * - getByDocId, getByPath, listEntries, upsert, delete, findDuplicates: function
 *
 * 戻り値の型（Promise<Either<...>>、AsyncIterable）は検証されません。
 *
 * @param obj - チェック対象のオブジェクト
 * @returns IndexStoreの場合true
 */
export function isIndexStore(obj: unknown): obj is IndexStore {
  if (!isNonNullObject(obj)) return false;

  const requiredMethods = [
    'getByDocId',
    'getByPath',
    'listEntries',
    'upsert',
    'delete',
    'findDuplicates',
  ] as const;

  return (
    hasStringProperty(obj, 'name') &&
    hasAllFunctionProperties(obj, requiredMethods)
  );
}

/**
 * 孤立エントリ検出可能なIndexStoreかどうかをチェック
 *
 * @param store - チェック対象のIndexStore
 * @returns findOrphansが利用可能な場合true
 */
export function isOrphanDetectableIndexStore(
  store: IndexStore
): store is IndexStore & Required<Pick<IndexStore, 'findOrphans'>> {
  return typeof store.findOrphans === 'function';
}

/**
 * ChangeTrackerかどうかをチェック
 *
 * @remarks
 * 以下のプロパティの存在と型のみを検証します：
 * - name: string
 * - detectChanges, isAvailable: function
 *
 * 戻り値の型は検証されません。
 *
 * @param obj - チェック対象のオブジェクト
 * @returns ChangeTrackerの場合true
 */
export function isChangeTracker(obj: unknown): obj is ChangeTracker {
  if (!isNonNullObject(obj)) return false;

  return (
    hasStringProperty(obj, 'name') &&
    hasAllFunctionProperties(obj, ['detectChanges', 'isAvailable'])
  );
}

/**
 * 参照検証可能なChangeTrackerかどうかをチェック
 *
 * @param tracker - チェック対象のChangeTracker
 * @returns isValidRefが利用可能な場合true
 */
export function isRefValidatableChangeTracker(
  tracker: ChangeTracker
): tracker is ChangeTracker & Required<Pick<ChangeTracker, 'isValidRef'>> {
  return typeof tracker.isValidRef === 'function';
}

/**
 * ShirushiPluginかどうかをチェック
 *
 * @remarks
 * 以下のプロパティの存在と型のみを検証します：
 * - name: string
 * - version: string
 *
 * オプショナルなプロパティ（documentSource等）は検証されません。
 *
 * @param obj - チェック対象のオブジェクト
 * @returns ShirushiPluginの場合true
 */
export function isShirushiPlugin(obj: unknown): obj is ShirushiPlugin {
  if (!isNonNullObject(obj)) return false;

  return hasStringProperty(obj, 'name') && hasStringProperty(obj, 'version');
}

/**
 * プラグインがDocumentSourceを提供しているかチェック
 *
 * @param plugin - チェック対象のプラグイン
 * @returns documentSourceが利用可能な場合true
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
 *
 * @param plugin - チェック対象のプラグイン
 * @returns indexStoreが利用可能な場合true
 */
export function hasIndexStore(
  plugin: ShirushiPlugin
): plugin is ShirushiPlugin & { indexStore: IndexStore } {
  return plugin.indexStore !== undefined && isIndexStore(plugin.indexStore);
}

/**
 * プラグインがChangeTrackerを提供しているかチェック
 *
 * @param plugin - チェック対象のプラグイン
 * @returns changeTrackerが利用可能な場合true
 */
export function hasChangeTracker(
  plugin: ShirushiPlugin
): plugin is ShirushiPlugin & { changeTracker: ChangeTracker } {
  return (
    plugin.changeTracker !== undefined && isChangeTracker(plugin.changeTracker)
  );
}
