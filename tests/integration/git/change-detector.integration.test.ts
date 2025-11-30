/**
 * Change Detector Integration Tests
 *
 * ChangeDetectorの統合テスト。
 * 実際のGitリポジトリを使用してdoc_id変更検出をテストする。
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { isRight } from 'fp-ts/Either';
import simpleGit from 'simple-git';
import { describe, it, expect, beforeEach, afterEach } from 'vitest';

import { createChangeDetector, createGitOperations } from '@/git';

// テスト用一時ディレクトリ（各テストでユニーク）
let TEST_DIR: string;
let testCounter = 0;

describe('ChangeDetector Integration', () => {
  let git: ReturnType<typeof simpleGit>;

  beforeEach(async () => {
    testCounter++;
    TEST_DIR = path.join(
      process.cwd(),
      `tests/.tmp/git-change-detector-${testCounter}-${Date.now()}`
    );
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
    git = simpleGit(TEST_DIR);
    await git.init();
    await git.addConfig('user.email', 'test@example.com');
    await git.addConfig('user.name', 'Test User');
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
  });

  describe('detectDocIdChanges', () => {
    it('should detect doc_id modification in markdown file', async () => {
      // 初期コミット - 元のdoc_id
      const originalContent = `---
doc_id: DOC-0001
title: Original Document
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/test.md'), originalContent);
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      // doc_idを変更してコミット
      const modifiedContent = `---
doc_id: DOC-9999
title: Modified Document
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/test.md'), modifiedContent);
      await git.add('.');
      await git.commit('Change doc_id');

      // 変更検出
      const gitOps = createGitOperations({ cwd: TEST_DIR });
      const detector = createChangeDetector(gitOps);
      const result = await detector.detectDocIdChanges(`${mainBranch}~1`, [
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
      }
    });

    it('should detect doc_id modification in yaml file', async () => {
      // 初期コミット
      const originalContent = `doc_id: SPEC-0001
title: Original Spec
`;
      await writeFile(path.join(TEST_DIR, 'docs/spec.yaml'), originalContent);
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      // doc_idを変更
      const modifiedContent = `doc_id: SPEC-0002
title: Modified Spec
`;
      await writeFile(path.join(TEST_DIR, 'docs/spec.yaml'), modifiedContent);
      await git.add('.');
      await git.commit('Change doc_id');

      const gitOps = createGitOperations({ cwd: TEST_DIR });
      const detector = createChangeDetector(gitOps);
      const result = await detector.detectDocIdChanges(`${mainBranch}~1`, [
        { path: 'docs/spec.yaml' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0].oldDocId).toBe('SPEC-0001');
        expect(result.right.changedDocIds[0].newDocId).toBe('SPEC-0002');
      }
    });

    it('should identify new files', async () => {
      // 初期コミット（空のREADME）
      await writeFile(path.join(TEST_DIR, 'README.md'), '# Test');
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      // 新規ファイルを追加
      const newContent = `---
doc_id: DOC-0001
title: New Document
---

# New
`;
      await writeFile(path.join(TEST_DIR, 'docs/new.md'), newContent);
      await git.add('.');
      await git.commit('Add new document');

      const gitOps = createGitOperations({ cwd: TEST_DIR });
      const detector = createChangeDetector(gitOps);
      const result = await detector.detectDocIdChanges(`${mainBranch}~1`, [
        { path: 'docs/new.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.newFiles).toContain('docs/new.md');
        expect(result.right.changedDocIds).toHaveLength(0);
      }
    });

    it('should not report unchanged doc_id', async () => {
      // ファイルを作成してコミット
      const content = `---
doc_id: DOC-0001
title: Document
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/unchanged.md'), content);
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      // doc_id以外を変更
      const modifiedContent = `---
doc_id: DOC-0001
title: Updated Title
description: Added description
---

# Updated Content
`;
      await writeFile(
        path.join(TEST_DIR, 'docs/unchanged.md'),
        modifiedContent
      );
      await git.add('.');
      await git.commit('Update content but not doc_id');

      const gitOps = createGitOperations({ cwd: TEST_DIR });
      const detector = createChangeDetector(gitOps);
      const result = await detector.detectDocIdChanges(`${mainBranch}~1`, [
        { path: 'docs/unchanged.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // doc_idが変わっていないので、changedDocIdsは空
        expect(result.right.changedDocIds).toHaveLength(0);
        expect(result.right.newFiles).toHaveLength(0);
        expect(result.right.deletedFiles).toHaveLength(0);
      }
    });

    it('should detect doc_id added to existing file', async () => {
      // doc_idなしでコミット
      const originalContent = `---
title: No ID Yet
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/add-id.md'), originalContent);
      await git.add('.');
      await git.commit('Initial commit without doc_id');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      // doc_idを追加
      const withIdContent = `---
doc_id: DOC-0001
title: Now With ID
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/add-id.md'), withIdContent);
      await git.add('.');
      await git.commit('Add doc_id');

      const gitOps = createGitOperations({ cwd: TEST_DIR });
      const detector = createChangeDetector(gitOps);
      const result = await detector.detectDocIdChanges(`${mainBranch}~1`, [
        { path: 'docs/add-id.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0].oldDocId).toBeNull();
        expect(result.right.changedDocIds[0].newDocId).toBe('DOC-0001');
      }
    });

    it('should process multiple files', async () => {
      // 複数ファイルを作成
      const doc1 = `---
doc_id: DOC-0001
title: Doc 1
---
# Doc 1
`;
      const doc2 = `---
doc_id: DOC-0002
title: Doc 2
---
# Doc 2
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1);
      await writeFile(path.join(TEST_DIR, 'docs/doc2.md'), doc2);
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const mainBranch = branches.current;

      // doc1を変更、doc2はそのまま
      const doc1Modified = `---
doc_id: DOC-9999
title: Doc 1 Modified
---
# Doc 1 Modified
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Modified);
      await git.add('.');
      await git.commit('Modify doc1');

      const gitOps = createGitOperations({ cwd: TEST_DIR });
      const detector = createChangeDetector(gitOps);
      const result = await detector.detectDocIdChanges(`${mainBranch}~1`, [
        { path: 'docs/doc1.md' },
        { path: 'docs/doc2.md' },
      ]);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // doc1のみ変更検出
        expect(result.right.changedDocIds).toHaveLength(1);
        expect(result.right.changedDocIds[0].path).toBe('docs/doc1.md');
      }
    });
  });
});
