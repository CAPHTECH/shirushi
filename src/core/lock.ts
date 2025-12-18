/**
 * Lock Manager
 *
 * ファイルベースのロック機構を提供。
 * 並行実行による競合状態を防止する。
 *
 * 使用方法:
 * 1. acquireLock() でロックを取得
 * 2. 処理を実行
 * 3. releaseLock() でロックを解放
 */

import { existsSync, readFileSync, unlinkSync, writeFileSync } from 'node:fs';
import path from 'node:path';

import { type Either, left, right } from 'fp-ts/Either';

const LOCK_FILE_NAME = '.shirushi.lock';

/**
 * ロック取得エラー
 */
export interface LockError {
  code: string;
  message: string;
  existingPid?: number;
}

/**
 * ロック情報
 */
interface LockInfo {
  pid: number;
  timestamp: number;
  command: string;
}

/**
 * ロックを取得
 *
 * @param cwd - ベースディレクトリ
 * @param command - 実行中のコマンド名（ログ用）
 * @returns 成功またはエラー
 */
export function acquireLock(
  cwd: string,
  command: string = 'assign'
): Either<LockError, void> {
  const lockPath = path.join(cwd, LOCK_FILE_NAME);

  // 既存のロックファイルをチェック
  if (existsSync(lockPath)) {
    try {
      const content = readFileSync(lockPath, 'utf8');
      const lockInfo = JSON.parse(content) as LockInfo;

      // プロセスがまだ実行中かチェック（簡易チェック）
      // Note: プロセスが異常終了した場合のstaleロック対策
      if (isProcessRunning(lockInfo.pid)) {
        return left({
          code: 'LOCK_HELD',
          message: `Another shirushi process (PID: ${lockInfo.pid}) is running. If this is not the case, delete ${LOCK_FILE_NAME} manually.`,
          existingPid: lockInfo.pid,
        });
      }

      // staleロック（プロセスが存在しない）の場合は削除
      unlinkSync(lockPath);
    } catch {
      // ロックファイルが破損している場合は削除
      try {
        unlinkSync(lockPath);
      } catch {
        // 削除に失敗しても続行
      }
    }
  }

  // 新しいロックファイルを作成
  const lockInfo: LockInfo = {
    pid: process.pid,
    timestamp: Date.now(),
    command,
  };

  try {
    writeFileSync(lockPath, JSON.stringify(lockInfo, null, 2), {
      encoding: 'utf8',
      flag: 'wx', // 排他的作成（ファイルが存在する場合は失敗）
    });
    return right(undefined);
  } catch (error) {
    // 別プロセスが先にロックを取得した可能性
    return left({
      code: 'LOCK_FAILED',
      message: `Failed to acquire lock: ${error instanceof Error ? error.message : 'Unknown error'}`,
    });
  }
}

/**
 * ロックを解放
 *
 * @param cwd - ベースディレクトリ
 */
export function releaseLock(cwd: string): void {
  const lockPath = path.join(cwd, LOCK_FILE_NAME);

  if (existsSync(lockPath)) {
    try {
      // 自分のロックかどうか確認
      const content = readFileSync(lockPath, 'utf8');
      const lockInfo = JSON.parse(content) as LockInfo;

      if (lockInfo.pid === process.pid) {
        unlinkSync(lockPath);
      }
    } catch {
      // エラーが発生しても無視（ベストエフォート）
    }
  }
}

/**
 * プロセスが実行中かチェック
 *
 * @param pid - プロセスID
 * @returns 実行中ならtrue
 */
function isProcessRunning(pid: number): boolean {
  try {
    // シグナル0を送信してプロセスの存在を確認
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}
