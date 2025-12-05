/**
 * Change Tracker Interface
 *
 * 変更検出を抽象化するインターフェース。
 * Git diff、監査ログ、タイムスタンプ比較等の異なる検出方式に対応可能。
 *
 * Phase 2で GitChangeTracker として現在の change-detector.ts を再構成予定。
 *
 * LDE準拠: Either型で成功/失敗を表現
 */

import type { DocumentSource } from './document-source.js';
import type { ChangeTrackerError } from './errors.js';
import type { Either } from 'fp-ts/Either';


/**
 * プラグインdoc_id変更情報
 * 既存の DocIdChange（src/git/types.ts）と互換
 */
export interface PluginDocIdChange {
  /** ドキュメントパス */
  readonly path: string;
  /** 変更前のdoc_id（新規の場合null） */
  readonly oldDocId: string | null;
  /** 変更後のdoc_id（削除の場合null） */
  readonly newDocId: string | null;
  /** 変更種別 */
  readonly changeType: 'added' | 'modified' | 'deleted';
}

/**
 * プラグイン変更検出結果
 * 既存の ChangeDetectionResult（src/git/types.ts）と互換
 */
export interface PluginChangeDetectionResult {
  /** doc_idが変更されたドキュメント */
  readonly changedDocIds: readonly PluginDocIdChange[];
  /** 新規ドキュメントのパス */
  readonly newDocuments: readonly string[];
  /** 削除されたドキュメントのパス */
  readonly deletedDocuments: readonly string[];
  /** 処理中に発生した警告（処理は継続） */
  readonly warnings: readonly string[];
}

/**
 * ChangeTracker Interface
 *
 * 変更トラッカーを抽象化するインターフェース。
 * 依存性注入により、テスト時にモック実装を注入可能。
 *
 * @example
 * ```typescript
 * // モック実装
 * const mockTracker: ChangeTracker = {
 *   name: 'test-tracker',
 *   async detectChanges(baseRef, source) {
 *     return right({
 *       changedDocIds: [],
 *       newDocuments: [],
 *       deletedDocuments: [],
 *       warnings: [],
 *     });
 *   },
 *   async isAvailable() {
 *     return true;
 *   },
 * };
 * ```
 */
export interface ChangeTracker {
  /** トラッカー名（ログ・エラーメッセージ用） */
  readonly name: string;

  /**
   * ベース参照からの変更を検出
   *
   * @param baseRef - 比較対象の参照（Git ref、タイムスタンプ、リビジョン番号等）
   * @param source - ドキュメントソース（現在の状態取得用）
   * @returns 変更検出結果
   */
  detectChanges(
    baseRef: string,
    source: DocumentSource
  ): Promise<Either<ChangeTrackerError, PluginChangeDetectionResult>>;

  /**
   * 変更追跡が利用可能かチェック
   *
   * @returns 利用可能な場合true
   */
  isAvailable(): Promise<boolean>;

  /**
   * ベース参照が有効かチェック（オプショナル）
   *
   * @param ref - チェックする参照
   * @returns 有効な場合true
   */
  isValidRef?(ref: string): Promise<boolean>;
}

/**
 * ChangeTracker設定
 */
export interface ChangeTrackerConfig {
  /** 作業ディレクトリ */
  readonly cwd?: string;
  /** トラッカー固有の追加設定 */
  readonly [key: string]: unknown;
}
