/**
 * Git Operations Integration Tests
 *
 * SimpleGitOperationsの統合テスト。
 * 実際のGitリポジトリを作成して、Git操作をテストする。
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { isRight } from 'fp-ts/Either';
import simpleGit from 'simple-git';
import { describe, it, expect, beforeEach, afterEach } from 'vitest';

import { SimpleGitOperations } from '@/git/operations';

// テスト用一時ディレクトリ（各テストでユニーク）
let TEST_DIR: string;
let testCounter = 0;

describe('SimpleGitOperations Integration', () => {
  let gitOps: SimpleGitOperations;
  let git: ReturnType<typeof simpleGit>;

  beforeEach(async () => {
    testCounter++;
    TEST_DIR = path.join(
      process.cwd(),
      `tests/.tmp/git-ops-${testCounter}-${Date.now()}`
    );
    await mkdir(TEST_DIR, { recursive: true });
    git = simpleGit(TEST_DIR);
    // 新規Gitリポジトリを初期化
    await git.init();
    await git.addConfig('user.email', 'test@example.com');
    await git.addConfig('user.name', 'Test User');

    gitOps = new SimpleGitOperations({ cwd: TEST_DIR });
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
  });

  describe('isGitRepository', () => {
    it('should return true for initialized git repo', async () => {
      const result = await gitOps.isGitRepository();

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(true);
      }
    });

    it('should return false for non-git directory', async () => {
      // Gitリポジトリ外の別ディレクトリを作成（/tmp配下で確実にGitリポジトリ外）
      const nonGitDir = path.join('/tmp', `shirushi-non-git-${Date.now()}`);
      await mkdir(nonGitDir, { recursive: true });

      try {
        const nonGitOps = new SimpleGitOperations({ cwd: nonGitDir });
        const result = await nonGitOps.isGitRepository();

        expect(isRight(result)).toBe(true);
        if (isRight(result)) {
          expect(result.right).toBe(false);
        }
      } finally {
        await rm(nonGitDir, { recursive: true, force: true });
      }
    });
  });

  describe('isValidRef', () => {
    it('should return true for valid branch after commit', async () => {
      // ファイルを作成してコミット
      await writeFile(path.join(TEST_DIR, 'README.md'), '# Test');
      await git.add('.');
      await git.commit('Initial commit');

      // mainまたはmasterブランチが存在するはず
      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      const result = await gitOps.isValidRef(mainBranch);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(true);
      }
    });

    it('should return false for non-existent ref', async () => {
      // コミットを作成
      await writeFile(path.join(TEST_DIR, 'README.md'), '# Test');
      await git.add('.');
      await git.commit('Initial commit');

      const result = await gitOps.isValidRef('non-existent-branch');

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(false);
      }
    });
  });

  describe('getFileContent', () => {
    it('should return file content at specific ref', async () => {
      // 初期コミット
      await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
      await writeFile(path.join(TEST_DIR, 'docs/test.md'), '# Original');
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      // ファイル内容を変更
      await writeFile(path.join(TEST_DIR, 'docs/test.md'), '# Modified');

      // 古いコミットの内容を取得
      const result = await gitOps.getFileContent('docs/test.md', mainBranch);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('# Original');
      }
    });

    it('should return null for non-existent file at ref', async () => {
      // コミットを作成
      await writeFile(path.join(TEST_DIR, 'README.md'), '# Test');
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      const result = await gitOps.getFileContent('non-existent.md', mainBranch);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBeNull();
      }
    });

    it('should return current working copy when ref is not specified', async () => {
      // コミットを作成
      await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
      await writeFile(path.join(TEST_DIR, 'docs/test.md'), '# Original');
      await git.add('.');
      await git.commit('Initial commit');

      // ワーキングコピーを変更
      await writeFile(path.join(TEST_DIR, 'docs/test.md'), '# Working Copy');

      const result = await gitOps.getFileContent('docs/test.md');

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('# Working Copy');
      }
    });
  });

  describe('getChangedFiles', () => {
    it('should return diff files when comparing with base ref', async () => {
      // 初期コミット
      await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
      await writeFile(path.join(TEST_DIR, 'docs/existing.md'), '# Existing');
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      // 新しいコミットを作成
      await writeFile(path.join(TEST_DIR, 'docs/new.md'), '# New');
      await writeFile(path.join(TEST_DIR, 'docs/existing.md'), '# Modified');
      await git.add('.');
      await git.commit('Add and modify files');

      const result = await gitOps.getChangedFiles(`${mainBranch  }~1`);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.length).toBeGreaterThanOrEqual(1);
        const paths = result.right.map((f) => f.path);
        expect(paths).toContain('docs/new.md');
        expect(paths).toContain('docs/existing.md');
      }
    });

    it('should return uncommitted changes when no base ref', async () => {
      // 初期コミット
      await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
      await writeFile(path.join(TEST_DIR, 'docs/committed.md'), '# Committed');
      await git.add('.');
      await git.commit('Initial commit');

      // 未コミットの変更
      await writeFile(path.join(TEST_DIR, 'docs/uncommitted.md'), '# New');
      await writeFile(path.join(TEST_DIR, 'docs/committed.md'), '# Modified');

      const result = await gitOps.getChangedFiles();

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        const paths = result.right.map((f) => f.path);
        expect(paths).toContain('docs/uncommitted.md');
        expect(paths).toContain('docs/committed.md');
      }
    });

    it('should detect deleted files', async () => {
      // 初期コミット
      await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
      await writeFile(path.join(TEST_DIR, 'docs/to-delete.md'), '# Delete me');
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      // ファイルを削除してコミット
      await rm(path.join(TEST_DIR, 'docs/to-delete.md'));
      await git.add('.');
      await git.commit('Delete file');

      const result = await gitOps.getChangedFiles(`${mainBranch  }~1`);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        const deletedFile = result.right.find(
          (f) => f.path === 'docs/to-delete.md'
        );
        expect(deletedFile).toBeDefined();
        expect(deletedFile?.status).toBe('deleted');
      }
    });
  });
});
