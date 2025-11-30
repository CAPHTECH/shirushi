/**
 * Change Detector Unit Tests
 *
 * ChangeDetectorクラスのユニットテスト。
 * GitOperationsをモックして、変更検出ロジックをテストする。
 */

import { isRight, left, right } from 'fp-ts/Either';
import { describe, it, expect, vi } from 'vitest';

import { ChangeDetector } from '@/git/change-detector';

import type { GitError, GitOperations } from '@/git/types';

/**
 * モックGitOperationsを作成
 */
function createMockGitOps(
  overrides: Partial<GitOperations> = {}
): GitOperations {
  return {
    isGitRepository: vi.fn().mockResolvedValue(right(true)),
    isValidRef: vi.fn().mockResolvedValue(right(true)),
    getFileContent: vi.fn().mockResolvedValue(right(null)),
    getChangedFiles: vi.fn().mockResolvedValue(right([])),
    ...overrides,
  };
}

describe('ChangeDetector', () => {
  describe('detectDocIdChanges', () => {
    it('should detect doc_id modification in markdown file', async () => {
      const baseContent = `---
doc_id: DOC-0001
title: Original
---
# Content`;

      const currentContent = `---
doc_id: DOC-9999
title: Modified
---
# Content`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          if (ref === 'main') {
            return Promise.resolve(right(baseContent));
          }
          return Promise.resolve(right(currentContent));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/test.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0]).toEqual({
          path: 'docs/test.md',
          oldDocId: 'DOC-0001',
          newDocId: 'DOC-9999',
          changeType: 'modified',
        });
        expect(result.right.newFiles).toHaveLength(0);
        expect(result.right.deletedFiles).toHaveLength(0);
      }
    });

    it('should detect doc_id modification in yaml file', async () => {
      const baseContent = `doc_id: SPEC-0001
title: Original`;

      const currentContent = `doc_id: SPEC-0002
title: Modified`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          if (ref === 'main') {
            return Promise.resolve(right(baseContent));
          }
          return Promise.resolve(right(currentContent));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/spec.yaml' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0].oldDocId).toBe('SPEC-0001');
        expect(result.right.changedDocIds[0].newDocId).toBe('SPEC-0002');
      }
    });

    it('should identify new files (not in base ref)', async () => {
      const currentContent = `---
doc_id: DOC-0001
---
# New file`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          if (ref === 'main') {
            // File doesn't exist at base ref
            return Promise.resolve(right(null));
          }
          return Promise.resolve(right(currentContent));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/new.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.newFiles).toContain('docs/new.md');
        expect(result.right.changedDocIds).toHaveLength(0);
      }
    });

    it('should identify deleted files', async () => {
      const baseContent = `---
doc_id: DOC-0001
---
# Deleted file`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          if (ref === 'main') {
            return Promise.resolve(right(baseContent));
          }
          // File doesn't exist currently
          return Promise.resolve(right(null));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/deleted.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.deletedFiles).toContain('docs/deleted.md');
        expect(result.right.changedDocIds).toHaveLength(0);
      }
    });

    it('should not report unchanged doc_id', async () => {
      const content = `---
doc_id: DOC-0001
title: Unchanged
---
# Content`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockResolvedValue(right(content)),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/unchanged.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.changedDocIds).toHaveLength(0);
        expect(result.right.newFiles).toHaveLength(0);
        expect(result.right.deletedFiles).toHaveLength(0);
      }
    });

    it('should handle file with no doc_id in either version', async () => {
      const content = `---
title: No doc_id
---
# Content`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockResolvedValue(right(content)),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/no-id.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // No change detected (both versions have null doc_id)
        expect(result.right.changedDocIds).toHaveLength(0);
      }
    });

    it('should detect doc_id added to existing file', async () => {
      const baseContent = `---
title: No doc_id
---
# Content`;

      const currentContent = `---
doc_id: DOC-0001
title: With doc_id now
---
# Content`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          if (ref === 'main') {
            return Promise.resolve(right(baseContent));
          }
          return Promise.resolve(right(currentContent));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/added-id.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // doc_id change from null to DOC-0001
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0].oldDocId).toBeNull();
        expect(result.right.changedDocIds[0].newDocId).toBe('DOC-0001');
      }
    });

    it('should detect doc_id removed from file', async () => {
      const baseContent = `---
doc_id: DOC-0001
title: With doc_id
---
# Content`;

      const currentContent = `---
title: Without doc_id now
---
# Content`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          if (ref === 'main') {
            return Promise.resolve(right(baseContent));
          }
          return Promise.resolve(right(currentContent));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/removed-id.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // doc_id change from DOC-0001 to null
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0].oldDocId).toBe('DOC-0001');
        expect(result.right.changedDocIds[0].newDocId).toBeNull();
      }
    });

    it('should process multiple files in batch', async () => {
      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          if (path === 'docs/a.md') {
            if (ref === 'main') return Promise.resolve(right(null));
            return Promise.resolve(right('---\ndoc_id: A-0001\n---'));
          }
          if (path === 'docs/b.md') {
            return Promise.resolve(right('---\ndoc_id: B-0001\n---'));
          }
          if (path === 'docs/c.md') {
            if (ref === 'main')
              return Promise.resolve(right('---\ndoc_id: C-0001\n---'));
            return Promise.resolve(right('---\ndoc_id: C-9999\n---'));
          }
          return Promise.resolve(right(null));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/a.md' }, // new file
        { path: 'docs/b.md' }, // unchanged
        { path: 'docs/c.md' }, // modified
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.newFiles).toContain('docs/a.md');
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0].path).toBe('docs/c.md');
      }
    });

    it('should continue processing after individual file errors', async () => {
      const gitError: GitError = {
        code: 'GIT_OPERATION_FAILED',
        message: 'Failed to read file',
      };

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          if (path === 'docs/error.md') {
            return Promise.resolve(left(gitError));
          }
          if (path === 'docs/valid.md') {
            if (ref === 'main')
              return Promise.resolve(right('---\ndoc_id: V-0001\n---'));
            return Promise.resolve(right('---\ndoc_id: V-9999\n---'));
          }
          return Promise.resolve(right(null));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/error.md' },
        { path: 'docs/valid.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // Error is collected
        expect(result.right.errors).toHaveLength(1);
        expect(result.right.errors[0].code).toBe('GIT_OPERATION_FAILED');
        // Valid file is still processed
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0].path).toBe('docs/valid.md');
      }
    });

    it('should handle .yml extension', async () => {
      const baseContent = `doc_id: SPEC-0001
title: Original`;

      const currentContent = `doc_id: SPEC-0002
title: Modified`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          if (ref === 'main') {
            return Promise.resolve(right(baseContent));
          }
          return Promise.resolve(right(currentContent));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/spec.yml' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.changedDocIds).toHaveLength(1);
      }
    });

    it('should return null doc_id for unsupported file types', async () => {
      const content = 'Some content';

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockResolvedValue(right(content)),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/file.txt' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // No changes detected (both doc_ids are null)
        expect(result.right.changedDocIds).toHaveLength(0);
      }
    });

    it('should detect doc_id modification in renamed file using oldPath', async () => {
      // ファイルがリネームされ、かつdoc_idも変更されたケース
      // oldPath を使用してベースrefのコンテンツを取得する
      const baseContent = `---
doc_id: DOC-0001
title: Old Name
---
# Content`;

      const currentContent = `---
doc_id: DOC-9999
title: New Name
---
# Content`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          // ベースrefでは旧パス (docs/old.md) を参照
          if (path === 'docs/old.md' && ref === 'main') {
            return Promise.resolve(right(baseContent));
          }
          // 現在は新パス (docs/new.md) を参照
          if (path === 'docs/new.md' && !ref) {
            return Promise.resolve(right(currentContent));
          }
          // 新パスはベースrefに存在しない
          if (path === 'docs/new.md' && ref === 'main') {
            return Promise.resolve(right(null));
          }
          return Promise.resolve(right(null));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      // oldPath を指定することで、リネーム前のパスからベースコンテンツを取得
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/new.md', oldPath: 'docs/old.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // リネームされたファイルでdoc_id変更を検出
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0]).toEqual({
          path: 'docs/new.md',
          oldDocId: 'DOC-0001',
          newDocId: 'DOC-9999',
          changeType: 'modified',
        });
        // 新規ファイルとして誤検出されていない
        expect(result.right.newFiles).toHaveLength(0);
      }
    });

    it('should not report change for renamed file with unchanged doc_id', async () => {
      // ファイルがリネームされたが、doc_idは変更されていないケース
      const content = `---
doc_id: DOC-0001
title: Same ID
---
# Content`;

      const mockGitOps = createMockGitOps({
        getFileContent: vi.fn().mockImplementation((path, ref) => {
          // ベースrefでは旧パスからコンテンツを取得
          if (path === 'docs/old.md' && ref === 'main') {
            return Promise.resolve(right(content));
          }
          // 現在は新パスからコンテンツを取得
          if (path === 'docs/new.md' && !ref) {
            return Promise.resolve(right(content));
          }
          return Promise.resolve(right(null));
        }),
      });

      const detector = new ChangeDetector(mockGitOps);
      const result = await detector.detectDocIdChanges('main', [
        { path: 'docs/new.md', oldPath: 'docs/old.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // doc_idは同じなので変更なし
        expect(result.right.changedDocIds).toHaveLength(0);
        expect(result.right.newFiles).toHaveLength(0);
        expect(result.right.deletedFiles).toHaveLength(0);
      }
    });
  });
});
