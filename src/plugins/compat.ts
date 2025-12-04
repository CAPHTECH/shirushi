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
 */
export function toPluginIndexEntry(entry: IndexEntry): PluginIndexEntry {
  const result: PluginIndexEntry = {
    docId: entry.doc_id,
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
    (result as { tags: readonly string[] }).tags = entry.tags;
  }
  return result;
}

/**
 * PluginIndexEntry (camelCase) → IndexEntry (snake_case)
 */
export function toIndexEntry(entry: PluginIndexEntry): IndexEntry {
  return {
    doc_id: entry.docId,
    path: entry.path,
    title: entry.title,
    doc_type: entry.docType,
    status: entry.status,
    version: entry.version,
    owner: entry.owner,
    tags: entry.tags ? [...entry.tags] : undefined,
  };
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
