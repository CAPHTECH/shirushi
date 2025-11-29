/**
 * Scan Command E2E Tests
 *
 * scanコマンドのE2Eテスト。
 * 実際のexecuteScan関数を呼び出してスキャン機能をテストする。
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';

import { executeScan } from '@/cli/commands/scan';

// テスト用一時ディレクトリ
const TEST_DIR = path.join(process.cwd(), 'tests/.tmp/scan');

describe('scan command', () => {
  let consoleOutput: string[] = [];

  beforeEach(async () => {
    // テスト用ディレクトリを作成
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
    // console.logをモックして出力をキャプチャ
    consoleOutput = [];
    vi.spyOn(console, 'log').mockImplementation((msg: string) => {
      consoleOutput.push(msg);
    });
    vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(async () => {
    // クリーンアップ
    await rm(TEST_DIR, { recursive: true, force: true });
    vi.restoreAllMocks();
  });

  it('should scan documents with doc_id', async () => {
    // 設定ファイルを作成
    const configContent = `
doc_globs:
  - "docs/**/*.md"
id_format: "{TYPE}-{YEAR}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["SPEC", "DOC"]
  YEAR:
    type: year
    digits: 4
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE", "YEAR"]
`;
    await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

    // テスト用Markdownファイルを作成
    const doc = `---
doc_id: SPEC-2025-0001
title: Test Document
status: active
---

# Test Document
`;
    await writeFile(path.join(TEST_DIR, 'docs/test.md'), doc);

    const exitCode = await executeScan({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      format: 'json',
    });

    expect(exitCode).toBe(0);
    expect(consoleOutput.length).toBeGreaterThan(0);
    // JSON出力をパースして確認
    const output = JSON.parse(consoleOutput[0]);
    expect(output.documents).toHaveLength(1);
    expect(output.documents[0].doc_id).toBe('SPEC-2025-0001');
    expect(output.summary.totalFiles).toBe(1);
    expect(output.summary.withDocId).toBe(1);
  });

  it('should handle documents without doc_id', async () => {
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
title: No ID Document
---

# No ID
`;
    await writeFile(path.join(TEST_DIR, 'docs/no-id.md'), doc);

    const exitCode = await executeScan({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      format: 'json',
    });

    expect(exitCode).toBe(0);
    const output = JSON.parse(consoleOutput[0]);
    expect(output.documents[0].doc_id).toBeNull();
    expect(output.summary.withoutDocId).toBe(1);
  });

  it('should scan multiple documents', async () => {
    const configContent = `
doc_globs:
  - "docs/**/*.md"
  - "docs/**/*.yaml"
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

    // 複数のドキュメント
    await writeFile(
      path.join(TEST_DIR, 'docs/doc1.md'),
      `---
doc_id: DOC-0001
title: Document 1
---
# Doc 1`
    );

    await writeFile(
      path.join(TEST_DIR, 'docs/doc2.md'),
      `---
doc_id: SPEC-0001
title: Document 2
---
# Doc 2`
    );

    await writeFile(
      path.join(TEST_DIR, 'docs/data.yaml'),
      `doc_id: DOC-0002
title: YAML Data`
    );

    const exitCode = await executeScan({
      cwd: TEST_DIR,
      config: '.shirushi.yml',
      format: 'json',
    });

    expect(exitCode).toBe(0);
    const output = JSON.parse(consoleOutput[0]);
    expect(output.documents).toHaveLength(3);
    expect(output.summary.markdownFiles).toBe(2);
    expect(output.summary.yamlFiles).toBe(1);
    expect(output.summary.withDocId).toBe(3);
  });
});
