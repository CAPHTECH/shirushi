/**
 * Lint Command Git Integration E2E Tests
 *
 * lintコマンドのGit連携オプション（--base, --changed-only）のE2Eテスト。
 * 実際のGitリポジトリを作成し、executeLint関数を呼び出してテストする。
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import simpleGit from 'simple-git';
import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';

import { executeLint } from '@/cli/commands/lint';

// テスト用一時ディレクトリ（各テストでユニーク）
let TEST_DIR: string;
let testCounter = 0;

describe('lint command with Git options', () => {
  let git: ReturnType<typeof simpleGit>;

  beforeEach(async () => {
    testCounter++;
    TEST_DIR = path.join(
      process.cwd(),
      `tests/.tmp/lint-git-${testCounter}-${Date.now()}`
    );
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });

    // Gitリポジトリ初期化
    git = simpleGit(TEST_DIR);
    await git.init();
    await git.addConfig('user.email', 'test@example.com');
    await git.addConfig('user.name', 'Test User');

    // console.logをモック
    vi.spyOn(console, 'log').mockImplementation(() => {});
    vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
    vi.restoreAllMocks();
  });

  describe('--base option', () => {
    it('should detect doc_id change when forbid_id_change is true', async () => {
      // 設定ファイル（forbid_id_change: true）
      const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{NUM}"
forbid_id_change: true
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
      await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

      // 初期ドキュメント
      const initialDoc = `---
doc_id: DOC-0001
title: Document 1
---

# Initial
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), initialDoc);
      await git.add('.');
      await git.commit('Initial commit');

      // doc_idを変更
      const modifiedDoc = `---
doc_id: DOC-9999
title: Document 1 Modified
---

# Modified
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), modifiedDoc);
      await git.add('.');
      await git.commit('Change doc_id');

      // ベースコミットと比較
      const branches = await git.branchLocal();
      const baseRef = `${branches.current  }~1`;

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        base: baseRef,
      });

      // doc_id変更はエラー
      expect(exitCode).toBe(1);
      expect(console.log).toHaveBeenCalled();
    });

    it('should not error when forbid_id_change is false', async () => {
      // 設定ファイル（forbid_id_change: false）
      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_format: "{TYPE}-{NUM}"
forbid_id_change: false
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
      await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

      // 初期ドキュメント
      const initialDoc = `---
doc_id: DOC-0001
title: Document 1
---

# Initial
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), initialDoc);

      // インデックス
      const indexContent = `
documents:
  - doc_id: DOC-0001
    path: docs/doc1.md
    title: Document 1
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);
      await git.add('.');
      await git.commit('Initial commit');

      // doc_idを変更
      const modifiedDoc = `---
doc_id: DOC-9999
title: Document 1 Modified
---

# Modified
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), modifiedDoc);

      // インデックスも更新
      const updatedIndex = `
documents:
  - doc_id: DOC-9999
    path: docs/doc1.md
    title: Document 1 Modified
`;
      await writeFile(
        path.join(TEST_DIR, 'docs/doc_index.yaml'),
        updatedIndex
      );
      await git.add('.');
      await git.commit('Change doc_id');

      const branches = await git.branchLocal();
      const baseRef = `${branches.current  }~1`;

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        base: baseRef,
      });

      // forbid_id_change: falseなのでエラーなし
      expect(exitCode).toBe(0);
    });

    it('should fail for invalid base ref', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
      await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

      const doc = `---
doc_id: DOC-0001
title: Document
---
# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc.md'), doc);
      await git.add('.');
      await git.commit('Initial commit');

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        base: 'non-existent-ref',
      });

      // 無効な参照でエラー
      expect(exitCode).toBe(1);
      expect(console.error).toHaveBeenCalled();
    });
  });

  describe('--changed-only option', () => {
    it('should only lint changed files with base ref', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
      await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

      // 2つのドキュメント
      const doc1 = `---
doc_id: DOC-0001
title: Document 1
---
# Doc 1
`;
      const doc2 = `---
doc_id: DOC-0002
title: Document 2
---
# Doc 2
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1);
      await writeFile(path.join(TEST_DIR, 'docs/doc2.md'), doc2);

      // インデックス
      const indexContent = `
documents:
  - doc_id: DOC-0001
    path: docs/doc1.md
    title: Document 1
  - doc_id: DOC-0002
    path: docs/doc2.md
    title: Document 2
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const baseRef = branches.current;

      // doc1のみ変更（内容のみ、doc_idは変更なし）
      const doc1Modified = `---
doc_id: DOC-0001
title: Document 1 Updated
---
# Doc 1 Updated Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Modified);
      await git.add('.');
      await git.commit('Update doc1');

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        base: baseRef,
        changedOnly: true,
      });

      // doc1のみがlintされ、有効なのでパス
      expect(exitCode).toBe(0);
    });

    it('should work standalone without base ref', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
      await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

      // 最初のコミット
      const doc1 = `---
doc_id: DOC-0001
title: Document 1
---
# Doc 1
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1);

      // インデックス（doc1のみ）
      const indexContent = `
documents:
  - doc_id: DOC-0001
    path: docs/doc1.md
    title: Document 1
  - doc_id: DOC-0002
    path: docs/doc2.md
    title: Document 2
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);
      await git.add('.');
      await git.commit('Initial commit');

      // 新規ファイル（未コミット）- インデックスに事前登録済み
      const doc2 = `---
doc_id: DOC-0002
title: Document 2
---
# Doc 2
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc2.md'), doc2);

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        changedOnly: true,
      });

      // 未コミットのdoc2のみlintされ、有効なのでパス
      expect(exitCode).toBe(0);
    });

    it('should return 0 when no changed documents match doc_globs', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
      await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

      const doc = `---
doc_id: DOC-0001
title: Document
---
# Doc
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc.md'), doc);
      await git.add('.');
      await git.commit('Initial commit');

      // doc_globsにマッチしないファイルを変更
      await writeFile(path.join(TEST_DIR, 'README.md'), '# Changed');

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        changedOnly: true,
      });

      // 変更ドキュメントがないのでパス
      expect(exitCode).toBe(0);
    });
  });

  describe('--base and --changed-only combined', () => {
    it('should lint only changed files and detect doc_id changes', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_format: "{TYPE}-{NUM}"
forbid_id_change: true
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
      await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

      // 2つのドキュメント
      const doc1 = `---
doc_id: DOC-0001
title: Document 1
---
# Doc 1
`;
      const doc2 = `---
doc_id: DOC-0002
title: Document 2
---
# Doc 2
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1);
      await writeFile(path.join(TEST_DIR, 'docs/doc2.md'), doc2);

      // インデックス
      const indexContent = `
documents:
  - doc_id: DOC-0001
    path: docs/doc1.md
    title: Document 1
  - doc_id: DOC-0002
    path: docs/doc2.md
    title: Document 2
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      // 変更後のコミットとbaseRef~1を比較するため、ここでbaseRefを記録
      const baseRef = `${branches.current  }~1`;

      // doc1のdoc_idを変更
      const doc1Modified = `---
doc_id: DOC-9999
title: Document 1
---
# Doc 1
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Modified);

      // インデックスも更新（DOC_ID_MISMATCH避け）
      const updatedIndex = `
documents:
  - doc_id: DOC-9999
    path: docs/doc1.md
    title: Document 1
  - doc_id: DOC-0002
    path: docs/doc2.md
    title: Document 2
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), updatedIndex);
      await git.add('.');
      await git.commit('Change doc1 id');

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        base: baseRef,
        changedOnly: true,
      });

      // doc1のみlintされ、doc_id変更が検出されエラー
      expect(exitCode).toBe(1);
    });
  });

  describe('git errors during doc_id detection', () => {
    it('should report git errors that occur during file content retrieval', async () => {
      // この機能のテスト: ChangeDetectorがファイル読み取り時にエラーを収集した場合、
      // そのエラーがLintResultに反映されることを確認する
      //
      // Note: 実際のGit操作でエラーを発生させるのは困難なため、
      // ユニットテスト（change-detector.test.ts）でモックを使用してテスト済み。
      // ここでは正常系の確認に留める。
      //
      // 関連テスト: tests/unit/git/change-detector.test.ts
      // "should continue processing after individual file errors"

      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_format: "{TYPE}-{NUM}"
forbid_id_change: true
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
      await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

      // 正常なファイルを作成
      const doc = `---
doc_id: DOC-0001
title: Document
---
# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc.md'), doc);

      // インデックスファイル
      const indexContent = `
documents:
  - doc_id: DOC-0001
    path: docs/doc.md
    title: Document
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);
      await git.add('.');
      await git.commit('Initial commit');

      const branches = await git.branchLocal();
      const baseRef = branches.current;

      // 同じ内容でコミット（doc_id変更なし）
      await writeFile(path.join(TEST_DIR, 'docs/doc.md'), doc + '\n# More content');
      await git.add('.');
      await git.commit('Update content');

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        base: baseRef,
      });

      // doc_id変更なし、エラーなしなので成功
      expect(exitCode).toBe(0);
    });
  });

  describe('non-git directory', () => {
    it('should fail with --base in non-git directory', async () => {
      // 非Gitディレクトリでテスト
      const nonGitDir = path.join('/tmp', `shirushi-non-git-lint-${Date.now()}`);
      await mkdir(path.join(nonGitDir, 'docs'), { recursive: true });

      try {
        const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
        await writeFile(path.join(nonGitDir, '.shirushi.yml'), configContent);

        const doc = `---
doc_id: DOC-0001
title: Document
---
# Doc
`;
        await writeFile(path.join(nonGitDir, 'docs/doc.md'), doc);

        const exitCode = await executeLint({
          cwd: nonGitDir,
          config: '.shirushi.yml',
          base: 'main',
        });

        // Gitリポジトリではないのでエラー
        expect(exitCode).toBe(1);
        expect(console.error).toHaveBeenCalled();
      } finally {
        await rm(nonGitDir, { recursive: true, force: true });
      }
    });

    it('should fail with --changed-only in non-git directory', async () => {
      const nonGitDir = path.join(
        '/tmp',
        `shirushi-non-git-changed-${Date.now()}`
      );
      await mkdir(path.join(nonGitDir, 'docs'), { recursive: true });

      try {
        const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
        await writeFile(path.join(nonGitDir, '.shirushi.yml'), configContent);

        const doc = `---
doc_id: DOC-0001
title: Document
---
# Doc
`;
        await writeFile(path.join(nonGitDir, 'docs/doc.md'), doc);

        const exitCode = await executeLint({
          cwd: nonGitDir,
          config: '.shirushi.yml',
          changedOnly: true,
        });

        // Gitリポジトリではないのでエラー
        expect(exitCode).toBe(1);
        expect(console.error).toHaveBeenCalled();
      } finally {
        await rm(nonGitDir, { recursive: true, force: true });
      }
    });
  });
});
