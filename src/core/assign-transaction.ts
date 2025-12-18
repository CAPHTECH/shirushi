/**
 * Assign Transaction
 *
 * assignコマンドのトランザクション管理。
 * ファイル書き込み前に元内容をメモリに保持し、
 * エラー発生時にロールバックを実行する。
 *
 * トランザクションフロー:
 * 1. 準備フェーズ: 対象ファイルの元内容をバックアップ
 * 2. 実行フェーズ: ファイル書き込みを順次実行
 * 3. 完了フェーズ: 成功時はそのまま終了、失敗時はロールバック
 */

import { existsSync, unlinkSync } from 'node:fs';
import path from 'node:path';

import { type Either, isLeft, left, right } from 'fp-ts/Either';

import {
  readFileContent,
  writeFileContent,
  writeDocIdToDocument,
  type WriteError,
} from '@/core/document-writer';
import {
  readIndexContent,
  writeIndexContent,
  appendToIndex,
  type NewIndexEntry,
  type IndexWriteError,
} from '@/core/index-writer';
import { logger } from '@/utils/logger';

import type { DocumentKind } from '@/types/document';

/**
 * 変更レコード
 */
export interface ChangeRecord {
  /** ファイルパス */
  path: string;
  /** 元のファイル内容 */
  originalContent: string;
  /** 生成されたdoc_id */
  generatedDocId: string;
  /** ドキュメント種別 */
  kind: DocumentKind;
}

/**
 * トランザクションコンテキスト
 */
export interface TransactionContext {
  /** 変更レコード（パス → レコード） */
  changes: Map<string, ChangeRecord>;
  /** 書き込み完了したパス */
  appliedPaths: Set<string>;
  /** インデックスファイルの元内容（null = ファイルが存在しなかった） */
  indexBackup: string | null;
  /** インデックスファイルのパス */
  indexPath: string;
  /** ベースディレクトリ */
  cwd: string;
  /** IDフィールド名 */
  idField: string;
}

/**
 * ロールバックエラー
 */
export interface RollbackError {
  code: string;
  message: string;
  failedPaths: string[];
}

/**
 * トランザクションコンテキストを作成
 */
export function createTransactionContext(
  indexPath: string,
  cwd: string,
  idField: string = 'doc_id'
): TransactionContext {
  return {
    changes: new Map(),
    appliedPaths: new Set(),
    indexBackup: null,
    indexPath,
    cwd,
    idField,
  };
}

/**
 * 変更レコードを準備（元内容のバックアップ）
 *
 * @param context - トランザクションコンテキスト
 * @param filePath - ファイルの絶対パス
 * @param docId - 生成されたdoc_id
 * @param kind - ドキュメント種別
 * @returns 成功またはエラー
 */
export async function prepareChange(
  context: TransactionContext,
  filePath: string,
  docId: string,
  kind: DocumentKind
): Promise<Either<WriteError, void>> {
  // 元内容を読み取り
  const contentResult = await readFileContent(filePath);
  if (isLeft(contentResult)) {
    return contentResult;
  }

  // 変更レコードを登録
  context.changes.set(filePath, {
    path: filePath,
    originalContent: contentResult.right,
    generatedDocId: docId,
    kind,
  });

  return right(undefined);
}

/**
 * インデックスのバックアップを準備
 *
 * @param context - トランザクションコンテキスト
 * @returns 成功またはエラー
 */
export async function prepareIndexBackup(
  context: TransactionContext
): Promise<Either<IndexWriteError, void>> {
  const result = await readIndexContent(context.indexPath, context.cwd);
  if (isLeft(result)) {
    return result;
  }
  context.indexBackup = result.right;
  return right(undefined);
}

/**
 * 変更を適用（ファイル書き込み）
 *
 * 各ファイルに対して書き込みを実行し、成功したパスを記録する。
 * エラー発生時は即座にロールバックを試みる。
 *
 * @param context - トランザクションコンテキスト
 * @returns 成功またはエラー
 */
export async function applyChanges(
  context: TransactionContext
): Promise<Either<WriteError, void>> {
  for (const [filePath, record] of context.changes) {
    const result = await writeDocIdToDocument(
      filePath,
      record.generatedDocId,
      record.kind,
      context.idField
    );

    if (isLeft(result)) {
      // エラー発生、ロールバックを試みる
      logger.warn('assign.transaction', 'Write failed, initiating rollback', {
        path: filePath,
        error: result.left.message,
      });
      const rollbackResult = await rollback(context);
      if (isLeft(rollbackResult)) {
        logger.error('assign.transaction', 'Rollback failed', {
          failedPaths: rollbackResult.left.failedPaths,
        });
        return left({
          ...result.left,
          message: `${result.left.message}. CRITICAL: Rollback also failed for ${rollbackResult.left.failedPaths.length} file(s): ${rollbackResult.left.failedPaths.join(', ')}`,
        });
      }
      return result;
    }

    context.appliedPaths.add(filePath);
  }

  return right(undefined);
}

/**
 * インデックスを更新
 *
 * @param context - トランザクションコンテキスト
 * @param entries - 追加するエントリ
 * @returns 成功またはエラー
 */
export async function applyIndexUpdate(
  context: TransactionContext,
  entries: NewIndexEntry[]
): Promise<Either<IndexWriteError, void>> {
  const result = await appendToIndex(
    context.indexPath,
    entries,
    context.cwd,
    context.idField
  );

  if (isLeft(result)) {
    // インデックス更新失敗、全体をロールバック
    logger.warn('assign.transaction', 'Index update failed, initiating rollback', {
      error: result.left.message,
    });
    const rollbackResult = await rollback(context);
    if (isLeft(rollbackResult)) {
      logger.error('assign.transaction', 'Rollback failed', {
        failedPaths: rollbackResult.left.failedPaths,
      });
      return left({
        ...result.left,
        message: `${result.left.message}. CRITICAL: Rollback also failed for ${rollbackResult.left.failedPaths.length} file(s): ${rollbackResult.left.failedPaths.join(', ')}`,
      });
    }
    return result;
  }

  return right(undefined);
}

/**
 * ロールバックを実行
 *
 * 書き込み済みのファイルを元に戻す。
 * ロールバック自体が失敗した場合はエラーを返す。
 *
 * @param context - トランザクションコンテキスト
 * @returns 成功またはロールバックエラー
 */
export async function rollback(
  context: TransactionContext
): Promise<Either<RollbackError, void>> {
  const failedPaths: string[] = [];

  logger.debug('assign.rollback', 'Starting rollback', {
    appliedCount: context.appliedPaths.size,
  });

  // 書き込み済みファイルを逆順で復元
  const appliedList = Array.from(context.appliedPaths).reverse();
  for (const filePath of appliedList) {
    const record = context.changes.get(filePath);
    if (!record) continue;

    const result = await writeFileContent(filePath, record.originalContent);
    if (isLeft(result)) {
      failedPaths.push(filePath);
      logger.error('assign.rollback', 'Failed to restore file', {
        path: filePath,
        error: result.left.message,
      });
    } else {
      logger.debug('assign.rollback', 'File restored', { path: filePath });
    }
  }

  // インデックスを復元または削除
  if (context.indexBackup !== null) {
    // 既存ファイルの復元
    const indexResult = await writeIndexContent(
      context.indexPath,
      context.indexBackup,
      context.cwd
    );
    if (isLeft(indexResult)) {
      failedPaths.push(context.indexPath);
      logger.error('assign.rollback', 'Failed to restore index', {
        error: indexResult.left.message,
      });
    }
  } else {
    // 新規作成されたインデックスファイルを削除
    const absolutePath = path.isAbsolute(context.indexPath)
      ? context.indexPath
      : path.join(context.cwd, context.indexPath);
    if (existsSync(absolutePath)) {
      try {
        unlinkSync(absolutePath);
        logger.debug('assign.rollback', 'Removed newly created index file', {
          path: absolutePath,
        });
      } catch (e) {
        failedPaths.push(absolutePath);
        logger.error('assign.rollback', 'Failed to remove newly created index', {
          path: absolutePath,
          error: e instanceof Error ? e.message : String(e),
        });
      }
    }
  }

  if (failedPaths.length > 0) {
    return left({
      code: 'ASSIGN_ROLLBACK_FAILED',
      message: `Failed to rollback ${failedPaths.length} file(s)`,
      failedPaths,
    });
  }

  logger.debug('assign.rollback', 'Rollback completed successfully');
  return right(undefined);
}
