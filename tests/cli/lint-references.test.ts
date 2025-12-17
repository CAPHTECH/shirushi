/**
 * Lint Command Reference Check E2E Tests
 *
 * lintコマンドの参照整合性チェック（--check-references）のE2Eテスト。
 * 実際のGitリポジトリを作成し、executeLint関数を呼び出してテストする。
 *
 * Issue #15: doc_id変更時の文書間参照整合性チェック機能
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import simpleGit from 'simple-git';
import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';

import { executeLint } from '@/cli/commands/lint';

// テスト用一時ディレクトリ（各テストでユニーク）
let TEST_DIR: string;
let testCounter = 0;

describe('lint command with --check-references option', () => {
  let git: ReturnType<typeof simpleGit>;

  beforeEach(async () => {
    testCounter++;
    TEST_DIR = path.join(
      process.cwd(),
      `tests/.tmp/lint-references-${testCounter}-${Date.now()}`
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

  it('should detect stale reference when doc_id is changed', async () => {
    // 設定ファイル
    const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{NUM}"
forbid_id_change: true
reference_fields:
  - superseded_by
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

    // ドキュメント1（参照される側）
    const doc1Initial = `---
doc_id: DOC-0001
title: Document 1
---

# Document 1
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Initial);

    // ドキュメント2（参照する側）
    const doc2 = `---
doc_id: DOC-0002
title: Document 2
---

# Document 2

See [Document 1](DOC-0001) for details.
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc2.md'), doc2);

    await git.add('.');
    await git.commit('Initial commit');

    // ドキュメント1のdoc_idを変更
    const doc1Modified = `---
doc_id: DOC-9999
title: Document 1 Modified
---

# Document 1 Modified
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Modified);
    await git.add('.');
    await git.commit('Change doc_id');

    // ベースコミットと比較
    const branches = await git.branchLocal();
    const baseRef = `${branches.current}~1`;

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      base: baseRef,
      checkReferences: true,
    });

    // doc_id変更 + 古い参照の両方がエラー
    expect(exitCode).toBe(1);
  });

  it('should not error when --check-references is used without doc_id changes', async () => {
    // 設定ファイル
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

    // ドキュメント1
    const doc1 = `---
doc_id: DOC-0001
title: Document 1
---

# Document 1
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1);

    // ドキュメント2
    const doc2 = `---
doc_id: DOC-0002
title: Document 2
---

# Document 2

See [Document 1](DOC-0001) for details.
`;
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

    // コンテンツの変更（doc_idは変更しない）
    const doc1Modified = `---
doc_id: DOC-0001
title: Document 1 Updated
---

# Document 1 Updated

New content.
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Modified);
    await git.add('.');
    await git.commit('Update content');

    // ベースコミットと比較
    const branches = await git.branchLocal();
    const baseRef = `${branches.current}~1`;

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      base: baseRef,
      checkReferences: true,
    });

    // doc_id変更なし、参照も有効 → エラーなし
    expect(exitCode).toBe(0);
  });

  it('should require --base option when using --check-references', async () => {
    // 設定ファイル
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

    // ドキュメント
    const doc = `---
doc_id: DOC-0001
title: Document 1
---

# Document 1
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc);

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

    // --base なしで --check-references を使用
    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      checkReferences: true,
      // base is not specified
    });

    // エラーで終了
    expect(exitCode).toBe(1);
    expect(console.error).toHaveBeenCalledWith(
      'Error: --check-references requires --base option'
    );
  });

  it('should detect stale reference in YAML field', async () => {
    // 設定ファイル
    const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{NUM}"
forbid_id_change: true
reference_fields:
  - superseded_by
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

    // ドキュメント1（参照される側）
    const doc1Initial = `---
doc_id: DOC-0001
title: Document 1
---

# Document 1
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Initial);

    // ドキュメント2（YAMLフィールドで参照）
    const doc2 = `---
doc_id: DOC-0002
title: Document 2
superseded_by: DOC-0001
---

# Document 2
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc2.md'), doc2);

    await git.add('.');
    await git.commit('Initial commit');

    // ドキュメント1のdoc_idを変更
    const doc1Modified = `---
doc_id: DOC-9999
title: Document 1 Modified
---

# Document 1 Modified
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Modified);
    await git.add('.');
    await git.commit('Change doc_id');

    // ベースコミットと比較
    const branches = await git.branchLocal();
    const baseRef = `${branches.current}~1`;

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      base: baseRef,
      checkReferences: true,
    });

    // YAMLフィールドの古い参照もエラー
    expect(exitCode).toBe(1);
  });

  it('should ignore references in code blocks', async () => {
    // 設定ファイル
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

    // ドキュメント1（参照される側）
    const doc1Initial = `---
doc_id: DOC-0001
title: Document 1
---

# Document 1
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Initial);

    // ドキュメント2（コードブロック内でのみ参照）
    const doc2 = `---
doc_id: DOC-0002
title: Document 2
---

# Document 2

\`\`\`markdown
Example: [link](DOC-0001)
\`\`\`
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc2.md'), doc2);

    await git.add('.');
    await git.commit('Initial commit');

    // ドキュメント1のdoc_idを変更
    const doc1Modified = `---
doc_id: DOC-9999
title: Document 1 Modified
---

# Document 1 Modified
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Modified);
    await git.add('.');
    await git.commit('Change doc_id');

    // ベースコミットと比較
    const branches = await git.branchLocal();
    const baseRef = `${branches.current}~1`;

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      base: baseRef,
      checkReferences: true,
    });

    // コードブロック内の参照は無視されるので、doc_id変更のみエラー
    // （DOC_ID_CHANGEDは報告されるが、STALE_REFERENCEは報告されない）
    expect(exitCode).toBe(1);

    // console.logの引数を確認して、STALE_REFERENCEが含まれていないことを確認
    const calls = (console.log as ReturnType<typeof vi.fn>).mock.calls;
    const output = calls.map((call) => call.join(' ')).join('\n');
    expect(output).not.toContain('STALE_REFERENCE');
    expect(output).toContain('DOC_ID_CHANGED');
  });

  it('should detect stale reference even when forbid_id_change is false', async () => {
    // Issue #15: forbid_id_change=false でも --check-references で
    // STALE_REFERENCE を検出できることを確認
    const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{NUM}"
forbid_id_change: false
reference_fields:
  - superseded_by
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

    // ドキュメント1（参照される側）
    const doc1Initial = `---
doc_id: DOC-0001
title: Document 1
---

# Document 1
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Initial);

    // ドキュメント2（参照する側）
    const doc2 = `---
doc_id: DOC-0002
title: Document 2
---

# Document 2

See [Document 1](DOC-0001) for details.
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc2.md'), doc2);

    await git.add('.');
    await git.commit('Initial commit');

    // ドキュメント1のdoc_idを変更
    const doc1Modified = `---
doc_id: DOC-9999
title: Document 1 Modified
---

# Document 1 Modified
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1Modified);
    await git.add('.');
    await git.commit('Change doc_id');

    // ベースコミットと比較
    const branches = await git.branchLocal();
    const baseRef = `${branches.current}~1`;

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      base: baseRef,
      checkReferences: true,
    });

    // forbid_id_change=false なので DOC_ID_CHANGED は報告されないが、
    // STALE_REFERENCE は報告される
    expect(exitCode).toBe(1);

    const calls = (console.log as ReturnType<typeof vi.fn>).mock.calls;
    const output = calls.map((call) => call.join(' ')).join('\n');
    expect(output).not.toContain('DOC_ID_CHANGED');
    expect(output).toContain('STALE_REFERENCE');
  });
});
