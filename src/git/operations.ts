/**
 * Git Operations Implementation
 *
 * simple-gitライブラリをラップし、GitOperationsインターフェースを実装する。
 * Either型で成功/失敗を表現し、エラーハンドリングを統一する。
 *
 * LDE準拠: 副作用をEither型でラップ
 */

import { left, right, type Either } from 'fp-ts/Either';
import simpleGit, {
  type SimpleGit,
  type SimpleGitOptions,
  type StatusResult,
} from 'simple-git';

import { ShirushiErrors } from '@/errors/definitions';

import type {
  ChangedFile,
  GitError,
  GitOperations,
  GitOperationsConfig,
} from './types';

/**
 * GitErrorを生成するヘルパー関数
 */
function createGitError(
  code: keyof typeof ShirushiErrors,
  error: unknown,
  context?: GitError['context']
): GitError {
  const errorDef = ShirushiErrors[code];
  const originalError = error instanceof Error ? error.message : String(error);
  return {
    code,
    message: `${errorDef.message}: ${originalError}`,
    context: {
      ...context,
      originalError,
    },
  };
}

/**
 * SimpleGit Operations Implementation
 *
 * simple-gitライブラリを使用したGitOperationsの実装。
 * テスト時はモック実装に差し替え可能。
 */
export class SimpleGitOperations implements GitOperations {
  private git: SimpleGit;
  private cwd: string;

  constructor(config: GitOperationsConfig) {
    this.cwd = config.cwd;
    const options: Partial<SimpleGitOptions> = {
      baseDir: config.cwd,
      timeout: { block: config.timeout ?? 30000 },
    };
    this.git = simpleGit(options);
  }

  /**
   * Gitリポジトリかどうかを確認
   */
  async isGitRepository(): Promise<Either<GitError, boolean>> {
    try {
      const isRepo = await this.git.checkIsRepo();
      return right(isRepo);
    } catch (error) {
      // "not a git repository"エラーはfalseとして返す（エラーではない）
      if (this.isNotGitRepoError(error)) {
        return right(false);
      }
      return left(createGitError('GIT_OPERATION_FAILED', error));
    }
  }

  /**
   * 指定されたGit参照が有効かどうかを確認
   */
  async isValidRef(ref: string): Promise<Either<GitError, boolean>> {
    try {
      await this.git.revparse([ref]);
      return right(true);
    } catch {
      // 無効な参照はfalseとして返す（エラーではない）
      return right(false);
    }
  }

  /**
   * ファイルの内容を取得
   */
  async getFileContent(
    filePath: string,
    ref?: string
  ): Promise<Either<GitError, string | null>> {
    try {
      if (!ref) {
        // 作業ツリーから読み込み
        const fs = await import('node:fs/promises');
        const path = await import('node:path');
        const fullPath = path.join(this.cwd, filePath);
        try {
          const content = await fs.readFile(fullPath, 'utf-8');
          return right(content);
        } catch {
          // ファイルが存在しない場合はnullを返す
          return right(null);
        }
      }

      // 指定されたrefからgit showで取得
      const content = await this.git.show([`${ref}:${filePath}`]);
      return right(content);
    } catch (error) {
      // ファイルが存在しない場合はnullを返す（エラーではない）
      if (this.isFileNotFoundError(error)) {
        return right(null);
      }
      return left(
        createGitError('GIT_OPERATION_FAILED', error, {
          ...(ref ? { ref } : {}),
          path: filePath,
        })
      );
    }
  }

  /**
   * 変更されたファイルの一覧を取得
   */
  async getChangedFiles(
    baseRef?: string
  ): Promise<Either<GitError, ChangedFile[]>> {
    try {
      if (baseRef) {
        // baseRefとHEADの差分を取得
        const diff = await this.git.diff([
          '--name-status',
          baseRef,
          'HEAD',
        ]);
        return right(this.parseDiffNameStatus(diff));
      }

      // git statusから変更ファイルを取得（staged + unstaged + untracked）
      const status = await this.git.status();
      return right(this.statusToChangedFiles(status));
    } catch (error) {
      return left(createGitError('GIT_OPERATION_FAILED', error));
    }
  }

  /**
   * "not a git repository"エラーかどうかを判定
   */
  private isNotGitRepoError(error: unknown): boolean {
    const msg = error instanceof Error ? error.message : String(error);
    return msg.toLowerCase().includes('not a git repository');
  }

  /**
   * ファイルが存在しないエラーかどうかを判定
   */
  private isFileNotFoundError(error: unknown): boolean {
    const msg = error instanceof Error ? error.message : String(error);
    return (
      msg.includes('does not exist') ||
      msg.includes('path') && msg.includes('exist') ||
      msg.includes('fatal: path')
    );
  }

  /**
   * git diff --name-status の出力をパース
   *
   * フォーマット: "STATUS\tPATH" または "STATUS\tOLD_PATH\tNEW_PATH"（リネーム）
   */
  private parseDiffNameStatus(output: string): ChangedFile[] {
    if (!output.trim()) return [];

    return output
      .trim()
      .split('\n')
      .map((line) => {
        const [status, ...pathParts] = line.split('\t');
        const firstPath = pathParts[0] ?? '';

        switch (status?.charAt(0)) {
          case 'A':
            return { path: firstPath, status: 'added' as const };
          case 'D':
            return { path: firstPath, status: 'deleted' as const };
          case 'M':
            return { path: firstPath, status: 'modified' as const };
          case 'R':
            // リネーム: R100\toldPath\tnewPath
            return {
              path: pathParts[1] ?? firstPath,
              status: 'renamed' as const,
              oldPath: firstPath,
            };
          default:
            return { path: firstPath, status: 'modified' as const };
        }
      })
      .filter((f) => f.path); // 空パスを除外
  }

  /**
   * git status結果をChangedFile配列に変換
   */
  private statusToChangedFiles(status: StatusResult): ChangedFile[] {
    const files: ChangedFile[] = [];
    const seen = new Set<string>();

    // ステージングされたファイル
    for (const file of status.created) {
      if (!seen.has(file)) {
        files.push({ path: file, status: 'added' });
        seen.add(file);
      }
    }

    for (const file of status.modified) {
      if (!seen.has(file)) {
        files.push({ path: file, status: 'modified' });
        seen.add(file);
      }
    }

    for (const file of status.deleted) {
      if (!seen.has(file)) {
        files.push({ path: file, status: 'deleted' });
        seen.add(file);
      }
    }

    // リネームされたファイル
    for (const renamed of status.renamed) {
      if (!seen.has(renamed.to)) {
        files.push({
          path: renamed.to,
          status: 'renamed',
          oldPath: renamed.from,
        });
        seen.add(renamed.to);
      }
    }

    // 未追跡ファイル（新規）
    for (const file of status.not_added) {
      if (!seen.has(file)) {
        files.push({ path: file, status: 'added' });
        seen.add(file);
      }
    }

    return files;
  }
}

/**
 * GitOperationsファクトリ関数
 *
 * @param config - 設定
 * @returns GitOperations実装
 */
export function createGitOperations(config: GitOperationsConfig): GitOperations {
  return new SimpleGitOperations(config);
}
