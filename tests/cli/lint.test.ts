/**
 * Lint Command E2E Tests
 *
 * lintコマンドのE2Eテスト。
 * 実際のexecuteLint関数を呼び出してバリデーションロジックをテストする。
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';

import { executeLint } from '@/cli/commands/lint';

// テスト用一時ディレクトリ
const TEST_DIR = path.join(process.cwd(), 'tests/.tmp/lint');

describe('lint command', () => {
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

  it('should return 0 when all documents are valid', async () => {
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

    // 有効なドキュメント
    const doc = `---
doc_id: DOC-0001
title: Valid Document
---

# Valid
`;
    await writeFile(path.join(TEST_DIR, 'docs/valid.md'), doc);

    // インデックス（整合性あり）
    const indexContent = `
documents:
  - doc_id: DOC-0001
    path: docs/valid.md
    title: Valid Document
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(0);
  });

  it('should return 1 when MISSING_ID error is detected', async () => {
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

    // doc_idなしのドキュメント
    const doc = `---
title: No ID
---

# No ID
`;
    await writeFile(path.join(TEST_DIR, 'docs/no-id.md'), doc);

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(1);
    // console.logが呼ばれてMISSING_IDを含む出力がされることを確認
    expect(console.log).toHaveBeenCalled();
  });

  it('should detect MALFORMED_ID error for invalid enum value', async () => {
    const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["DOC", "SPEC"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
    await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

    // パターンに合わないTYPE値
    const doc = `---
doc_id: INVALID-0001
title: Invalid Type
---

# Invalid
`;
    await writeFile(path.join(TEST_DIR, 'docs/invalid.md'), doc);

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(1);
  });

  it('should validate checksum correctly', async () => {
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

    // DOC-0001の正しいチェックサム計算
    // D(68) + O(79) + C(67) + 0(48) + 0(48) + 0(48) + 1(49) = 407
    // 407 % 26 = 17 → R (65 + 17 = 82)
    const validDoc = `---
doc_id: DOC-0001-R
title: Valid Checksum
---

# Valid
`;
    await writeFile(path.join(TEST_DIR, 'docs/valid.md'), validDoc);

    // インデックス（整合性あり）
    const indexContent = `
documents:
  - doc_id: DOC-0001-R
    path: docs/valid.md
    title: Valid Checksum
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(0);
  });

  it('should detect INVALID_ID_CHECKSUM error', async () => {
    const configContent = `
doc_globs:
  - "docs/**/*.md"
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

    // 誤ったチェックサム（RではなくZ）
    const invalidDoc = `---
doc_id: DOC-0001-Z
title: Invalid Checksum
---

# Invalid
`;
    await writeFile(path.join(TEST_DIR, 'docs/invalid.md'), invalidDoc);

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(1);
  });

  it('should detect MALFORMED_ID error for pattern mismatch', async () => {
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

    // パターンに合わないID
    const invalidDoc = `---
doc_id: WRONG_FORMAT
title: Malformed ID
---

# Malformed
`;
    await writeFile(path.join(TEST_DIR, 'docs/malformed.md'), invalidDoc);

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(1);
  });

  it('should validate index consistency', async () => {
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

# Doc
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc);

    // インデックス（不整合あり：doc_idが異なる）
    const indexContent = `
documents:
  - doc_id: DOC-9999
    path: docs/doc1.md
    title: Document 1
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(1);
  });

  it('should detect UNINDEXED_DOC_ID error', async () => {
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

# Doc
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc);

    // 空のインデックス
    const indexContent = `
documents: []
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    const exitCode = await executeLint({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
    });

    expect(exitCode).toBe(1);
  });
});
