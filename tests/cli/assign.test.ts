/**
 * Assign Command E2E Tests
 *
 * assignコマンドのE2Eテスト。
 * 実際のexecuteAssign関数を呼び出してID生成・書き込みロジックをテストする。
 */

import { mkdir, writeFile, rm, readFile } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';

import { executeAssign } from '@/cli/commands/assign';

// テスト用一時ディレクトリ
const TEST_DIR = path.join(process.cwd(), 'tests/.tmp/assign');

describe('assign command', () => {
  beforeEach(async () => {
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
    // console.logをモック
    vi.spyOn(console, 'log').mockImplementation(() => {});
    vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
    vi.restoreAllMocks();
  });

  it('should return 0 when no documents need assignment', async () => {
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

    // 既にdoc_idがあるドキュメント
    const doc = `---
doc_id: DOC-0001
title: Existing Document
---

# Existing
`;
    await writeFile(path.join(TEST_DIR, 'docs/existing.md'), doc);

    // インデックス
    const indexContent = `
documents:
  - doc_id: DOC-0001
    path: docs/existing.md
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(0);
    expect(console.log).toHaveBeenCalled();
  });

  it('should assign doc_id to document without one', async () => {
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

    // doc_idなしのドキュメント
    const doc = `---
title: New Document
---

# New
`;
    await writeFile(path.join(TEST_DIR, 'docs/new.md'), doc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(0);

    // ファイルにdoc_idが書き込まれたことを確認
    const content = await readFile(path.join(TEST_DIR, 'docs/new.md'), 'utf8');
    expect(content).toContain('doc_id: DOC-0001');
  });

  it('should not modify files in dry-run mode', async () => {
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

    // doc_idなしのドキュメント
    const originalDoc = `---
title: New Document
---

# New
`;
    await writeFile(path.join(TEST_DIR, 'docs/new.md'), originalDoc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      dryRun: true,
    });

    expect(exitCode).toBe(0);

    // ファイルが変更されていないことを確認
    const content = await readFile(path.join(TEST_DIR, 'docs/new.md'), 'utf8');
    expect(content).not.toContain('doc_id');
    expect(content).toBe(originalDoc);
  });

  it('should increment serial numbers correctly', async () => {
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

    // 既存ドキュメント
    const existing = `---
doc_id: DOC-0001
title: Existing
---

# Existing
`;
    await writeFile(path.join(TEST_DIR, 'docs/existing.md'), existing);

    // 新規ドキュメント
    const newDoc = `---
title: New Document
---

# New
`;
    await writeFile(path.join(TEST_DIR, 'docs/new.md'), newDoc);

    // インデックス（既存エントリあり）
    const indexContent = `
documents:
  - doc_id: DOC-0001
    path: docs/existing.md
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(0);

    // 新規ドキュメントにDOC-0002が割り当てられたことを確認
    const content = await readFile(path.join(TEST_DIR, 'docs/new.md'), 'utf8');
    expect(content).toContain('doc_id: DOC-0002');
  });

  it('should assign with checksum dimension', async () => {
    const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_format: "{TYPE}-{NUM}-{CHK}"
dimensions:
  TYPE:
    type: enum
    values: ["DOC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
  CHK:
    type: checksum
    algo: mod26AZ
    of: ["TYPE", "NUM"]
`;
    await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

    // doc_idなしのドキュメント
    const doc = `---
title: New Document
---

# New
`;
    await writeFile(path.join(TEST_DIR, 'docs/new.md'), doc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(0);

    // ファイルにdoc_idが書き込まれたことを確認（チェックサム付き）
    const content = await readFile(path.join(TEST_DIR, 'docs/new.md'), 'utf8');
    // DOC-0001-X の形式（Xはチェックサム）
    expect(content).toMatch(/doc_id: DOC-0001-[A-Z]/);
  });

  it('should update index file after assignment', async () => {
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

    // doc_idなしのドキュメント
    const doc = `---
title: New Document
---

# New
`;
    await writeFile(path.join(TEST_DIR, 'docs/new.md'), doc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    // インデックスが更新されたことを確認
    const indexAfter = await readFile(
      path.join(TEST_DIR, 'docs/doc_index.yaml'),
      'utf8'
    );
    expect(indexAfter).toContain('DOC-0001');
    expect(indexAfter).toContain('docs/new.md');
  });

  it('should handle enum_from_doc_type dimension', async () => {
    const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum_from_doc_type
    mapping:
      spec: SPEC
      design: DES
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
    await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

    // doc_typeありのドキュメント
    const doc = `---
title: Specification
doc_type: spec
---

# Spec
`;
    await writeFile(path.join(TEST_DIR, 'docs/spec.md'), doc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(0);

    // SPECが使用されたことを確認
    const content = await readFile(path.join(TEST_DIR, 'docs/spec.md'), 'utf8');
    expect(content).toContain('doc_id: SPEC-0001');
  });

  it('should skip documents with missing required metadata', async () => {
    const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum_from_doc_type
    mapping:
      spec: SPEC
      design: DES
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
    await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

    // doc_typeなしのドキュメント
    const doc = `---
title: No Type
---

# No Type
`;
    await writeFile(path.join(TEST_DIR, 'docs/no-type.md'), doc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    // エラーがあるため終了コード1
    expect(exitCode).toBe(1);

    // ファイルにdoc_idが書き込まれていないことを確認
    const content = await readFile(
      path.join(TEST_DIR, 'docs/no-type.md'),
      'utf8'
    );
    expect(content).not.toContain('doc_id');
  });

  it('should assign to YAML files', async () => {
    const configContent = `
doc_globs:
  - "docs/**/*.yaml"
index_file: "docs/doc_index.yaml"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["CFG"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
    await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

    // YAMLドキュメント（doc_idなし）
    const doc = `title: Config File
settings:
  key: value
`;
    await writeFile(path.join(TEST_DIR, 'docs/config.yaml'), doc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(0);

    // YAMLファイルにdoc_idが書き込まれたことを確認
    const content = await readFile(
      path.join(TEST_DIR, 'docs/config.yaml'),
      'utf8'
    );
    expect(content).toContain('doc_id: CFG-0001');
  });

  it('should output JSON format', async () => {
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

    // doc_idなしのドキュメント
    const doc = `---
title: New Document
---

# New
`;
    await writeFile(path.join(TEST_DIR, 'docs/new.md'), doc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      format: 'json',
    });

    // JSON形式で出力されることを確認
    expect(console.log).toHaveBeenCalled();
    const logCall = vi.mocked(console.log).mock.calls[0];
    if (logCall && logCall[0]) {
      const output = JSON.parse(logCall[0] as string);
      expect(output).toHaveProperty('assigned');
      expect(output).toHaveProperty('summary');
    }
  });

  it('should acquire and release lock correctly', async () => {
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

    // doc_idなしのドキュメント
    const doc = `---
title: New Document
---

# New
`;
    await writeFile(path.join(TEST_DIR, 'docs/new.md'), doc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    // 実行後、ロックファイルが残っていないことを確認
    const { existsSync } = await import('node:fs');
    const lockPath = path.join(TEST_DIR, '.shirushi.lock');

    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(0);
    expect(existsSync(lockPath)).toBe(false);
  });

  it('should not create lock file in dry-run mode', async () => {
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

    const doc = `---
title: New Document
---

# New
`;
    await writeFile(path.join(TEST_DIR, 'docs/new.md'), doc);

    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const { existsSync } = await import('node:fs');
    const lockPath = path.join(TEST_DIR, '.shirushi.lock');

    // dry-runではロックファイルを作成しない
    const exitCode = await executeAssign({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      dryRun: true,
    });

    expect(exitCode).toBe(0);
    expect(existsSync(lockPath)).toBe(false);

    // ファイルが変更されていないことも確認
    const content = await readFile(path.join(TEST_DIR, 'docs/new.md'), 'utf8');
    expect(content).not.toContain('doc_id');
  });
});
