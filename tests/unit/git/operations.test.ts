/**
 * Git Operations Unit Tests
 *
 * SimpleGitOperationsクラスのユニットテスト。
 * simple-gitをモックして、ビジネスロジックをテストする。
 */

import { isLeft, isRight } from 'fp-ts/Either';
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';

// モックインスタンスを事前に定義
const mockGitInstance = {
  checkIsRepo: vi.fn(),
  revparse: vi.fn(),
  show: vi.fn(),
  diff: vi.fn(),
  status: vi.fn(),
};

// simple-gitをモック（ファクトリ関数をモック）
vi.mock('simple-git', () => ({
    default: vi.fn(() => mockGitInstance),
  }));

// モック後にインポート
import { SimpleGitOperations } from '@/git/operations';

describe('SimpleGitOperations', () => {
  let gitOps: SimpleGitOperations;

  beforeEach(() => {
    // 各テスト前にモックをリセット
    vi.clearAllMocks();
    gitOps = new SimpleGitOperations({ cwd: '/test/path' });
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('isGitRepository', () => {
    it('should return Right(true) for valid git repo', async () => {
      mockGitInstance.checkIsRepo.mockResolvedValue(true);

      const result = await gitOps.isGitRepository();

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(true);
      }
    });

    it('should return Right(false) for non-git directory', async () => {
      mockGitInstance.checkIsRepo.mockResolvedValue(false);

      const result = await gitOps.isGitRepository();

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(false);
      }
    });

    it('should return Right(false) for "not a git repository" error', async () => {
      mockGitInstance.checkIsRepo.mockRejectedValue(
        new Error('fatal: not a git repository')
      );

      const result = await gitOps.isGitRepository();

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(false);
      }
    });

    it('should return Left(error) for unexpected failures', async () => {
      mockGitInstance.checkIsRepo.mockRejectedValue(new Error('Network error'));

      const result = await gitOps.isGitRepository();

      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('GIT_OPERATION_FAILED');
        expect(result.left.message).toContain('Network error');
      }
    });
  });

  describe('isValidRef', () => {
    it('should return Right(true) for valid branch name', async () => {
      mockGitInstance.revparse.mockResolvedValue('abc123');

      const result = await gitOps.isValidRef('main');

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(true);
      }
      expect(mockGitInstance.revparse).toHaveBeenCalledWith(['main']);
    });

    it('should return Right(true) for valid commit SHA', async () => {
      mockGitInstance.revparse.mockResolvedValue('abc1234567890');

      const result = await gitOps.isValidRef('abc1234567890');

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(true);
      }
    });

    it('should return Right(false) for invalid ref', async () => {
      mockGitInstance.revparse.mockRejectedValue(new Error('unknown revision'));

      const result = await gitOps.isValidRef('non-existent-branch');

      // 無効な参照はRight(false)として返す（エラーではない）
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(false);
      }
    });
  });

  describe('getFileContent', () => {
    it('should return file content at specific ref', async () => {
      const fileContent = '---\ndoc_id: TEST-0001\n---\n# Content';
      mockGitInstance.show.mockResolvedValue(fileContent);

      const result = await gitOps.getFileContent('docs/test.md', 'main');

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(fileContent);
      }
      expect(mockGitInstance.show).toHaveBeenCalledWith(['main:docs/test.md']);
    });

    it('should return Right(null) for non-existent file at ref', async () => {
      mockGitInstance.show.mockRejectedValue(
        new Error('fatal: path does not exist in main')
      );

      const result = await gitOps.getFileContent('docs/missing.md', 'main');

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBeNull();
      }
    });

    it('should return Left(error) for unexpected git failures', async () => {
      mockGitInstance.show.mockRejectedValue(new Error('Permission denied'));

      const result = await gitOps.getFileContent('docs/test.md', 'main');

      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('GIT_OPERATION_FAILED');
        expect(result.left.context?.ref).toBe('main');
        expect(result.left.context?.path).toBe('docs/test.md');
      }
    });
  });

  describe('getChangedFiles', () => {
    it('should return diff files when baseRef is provided', async () => {
      const diffOutput = 'A\tdocs/new.md\nM\tdocs/modified.md\nD\tdocs/deleted.md';
      mockGitInstance.diff.mockResolvedValue(diffOutput);

      const result = await gitOps.getChangedFiles('main');

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toHaveLength(3);
        expect(result.right).toContainEqual({
          path: 'docs/new.md',
          status: 'added',
        });
        expect(result.right).toContainEqual({
          path: 'docs/modified.md',
          status: 'modified',
        });
        expect(result.right).toContainEqual({
          path: 'docs/deleted.md',
          status: 'deleted',
        });
      }
      expect(mockGitInstance.diff).toHaveBeenCalledWith([
        '--name-status',
        'main',
        'HEAD',
      ]);
    });

    it('should handle renamed files in diff', async () => {
      const diffOutput = 'R100\told/path.md\tnew/path.md';
      mockGitInstance.diff.mockResolvedValue(diffOutput);

      const result = await gitOps.getChangedFiles('main');

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toHaveLength(1);
        expect(result.right[0]).toEqual({
          path: 'new/path.md',
          status: 'renamed',
          oldPath: 'old/path.md',
        });
      }
    });

    it('should return git status when baseRef is not provided', async () => {
      mockGitInstance.status.mockResolvedValue({
        created: ['docs/new.md'],
        modified: ['docs/modified.md'],
        deleted: ['docs/deleted.md'],
        renamed: [{ from: 'old.md', to: 'new.md' }],
        not_added: ['docs/untracked.md'],
        files: [],
        staged: [],
        conflicted: [],
      });

      const result = await gitOps.getChangedFiles();

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toHaveLength(5);
        expect(result.right).toContainEqual({
          path: 'docs/new.md',
          status: 'added',
        });
        expect(result.right).toContainEqual({
          path: 'docs/modified.md',
          status: 'modified',
        });
        expect(result.right).toContainEqual({
          path: 'docs/deleted.md',
          status: 'deleted',
        });
        expect(result.right).toContainEqual({
          path: 'new.md',
          status: 'renamed',
          oldPath: 'old.md',
        });
        expect(result.right).toContainEqual({
          path: 'docs/untracked.md',
          status: 'added',
        });
      }
    });

    it('should return empty array when no changes', async () => {
      mockGitInstance.diff.mockResolvedValue('');

      const result = await gitOps.getChangedFiles('main');

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toHaveLength(0);
      }
    });

    it('should return Left(error) for git failures', async () => {
      mockGitInstance.diff.mockRejectedValue(new Error('Git diff failed'));

      const result = await gitOps.getChangedFiles('main');

      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('GIT_OPERATION_FAILED');
      }
    });

    it('should deduplicate files appearing in multiple status categories', async () => {
      mockGitInstance.status.mockResolvedValue({
        created: ['docs/file.md'],
        modified: ['docs/file.md'], // Same file in both
        deleted: [],
        renamed: [],
        not_added: [],
        files: [],
        staged: [],
        conflicted: [],
      });

      const result = await gitOps.getChangedFiles();

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // Should only appear once
        expect(result.right).toHaveLength(1);
        expect(result.right[0].path).toBe('docs/file.md');
      }
    });
  });
});
