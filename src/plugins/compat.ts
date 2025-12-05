/**
 * Plugin Compatibility Utilities
 *
 * 既存型（snake_case）とプラグイン型（camelCase）の変換ユーティリティ。
 * Phase 2以降でデフォルト実装との統合に使用。
 */

import type {
  PluginDocIdChange,
  PluginChangeDetectionResult,
} from './interfaces/change-tracker.js';
import type { PluginIndexEntry } from './interfaces/index-store.js';
import type { IndexEntry } from '@/core/index-manager';
import type { DocIdChange, ChangeDetectionResult } from '@/git/types';


/**
 * IndexEntry (snake_case) → PluginIndexEntry (camelCase)
 *
 * @param entry - IndexEntry to convert
 * @param idField - IDフィールド名（デフォルト: 'doc_id'）
 * @throws Error if ID field is undefined
 */
export function toPluginIndexEntry(
  entry: IndexEntry,
  idField: string = 'doc_id'
): PluginIndexEntry {
  const docId = entry[idField];
  if (typeof docId !== 'string') {
    throw new Error(`IndexEntry missing ${idField}: ${entry.path}`);
  }
  const result: PluginIndexEntry = {
    docId,
    path: entry.path,
  };
  if (entry.title !== undefined) {
    (result as { title: string }).title = entry.title;
  }
  if (entry.doc_type !== undefined) {
    (result as { docType: string }).docType = entry.doc_type;
  }
  if (entry.status !== undefined) {
    (result as { status: string }).status = entry.status;
  }
  if (entry.version !== undefined) {
    (result as { version: string }).version = entry.version;
  }
  if (entry.owner !== undefined) {
    (result as { owner: string }).owner = entry.owner;
  }
  if (entry.tags !== undefined) {
    // 防御的コピー: プラグイン側での配列改変を防止
    (result as { tags: readonly string[] }).tags = [...entry.tags];
  }
  // NOTE: IndexEntry には extra フィールドが存在しないため変換不可
  // PluginIndexEntry.extra はプラグイン内部でのみ使用される
  return result;
}

/**
 * PluginIndexEntry (camelCase) → IndexEntry (snake_case)
 *
 * @param entry - PluginIndexEntry to convert
 * @param idField - IDフィールド名（デフォルト: 'doc_id'）
 *
 * NOTE: PluginIndexEntry.extra は IndexEntry に対応するフィールドがないため
 * 変換時に失われる。extra はプラグイン内部でのみ使用すること。
 */
export function toIndexEntry(
  entry: PluginIndexEntry,
  idField: string = 'doc_id'
): IndexEntry {
  const result: IndexEntry = {
    [idField]: entry.docId,
    path: entry.path,
  };
  if (entry.title !== undefined) {
    result.title = entry.title;
  }
  if (entry.docType !== undefined) {
    result.doc_type = entry.docType;
  }
  if (entry.status !== undefined) {
    result.status = entry.status;
  }
  if (entry.version !== undefined) {
    result.version = entry.version;
  }
  if (entry.owner !== undefined) {
    result.owner = entry.owner;
  }
  if (entry.tags !== undefined) {
    // 防御的コピー: 元の配列への影響を防止
    result.tags = [...entry.tags];
  }
  return result;
}

/**
 * DocIdChange → PluginDocIdChange
 */
export function toPluginDocIdChange(change: DocIdChange): PluginDocIdChange {
  return {
    path: change.path,
    oldDocId: change.oldDocId,
    newDocId: change.newDocId,
    changeType: change.changeType,
  };
}

/**
 * PluginDocIdChange → DocIdChange
 */
export function toDocIdChange(change: PluginDocIdChange): DocIdChange {
  return {
    path: change.path,
    oldDocId: change.oldDocId,
    newDocId: change.newDocId,
    changeType: change.changeType,
  };
}

/**
 * ChangeDetectionResult → PluginChangeDetectionResult
 * Note: errors (GitError[]) → warnings (string[]) に変換
 */
export function toPluginChangeDetectionResult(
  result: ChangeDetectionResult
): PluginChangeDetectionResult {
  return {
    changedDocIds: result.changedDocIds.map(toPluginDocIdChange),
    newDocuments: [...result.newFiles],
    deletedDocuments: [...result.deletedFiles],
    warnings: result.errors.map((e) => e.message),
  };
}

/**
 * PluginChangeDetectionResult → ChangeDetectionResult
 * Note: warnings (string[]) → errors (GitError[]) に変換
 */
export function toChangeDetectionResult(
  result: PluginChangeDetectionResult
): ChangeDetectionResult {
  return {
    changedDocIds: result.changedDocIds.map(toDocIdChange),
    newFiles: [...result.newDocuments],
    deletedFiles: [...result.deletedDocuments],
    errors: result.warnings.map((message) => ({
      code: 'GIT_OPERATION_FAILED' as const,
      message,
    })),
  };
}
