/**
 * Scan Command E2E Tests
 *
 * scanコマンドのE2Eテスト。
 * 実際のファイルシステムとCLI実行をテストする。
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach } from 'vitest';

import { loadConfig } from '@/config/loader';
import { scanDocuments } from '@/core/scanner';

// テスト用一時ディレクトリ
const TEST_DIR = path.join(process.cwd(), 'tests/.tmp/scan');

describe('scan command', () => {
  beforeEach(async () => {
    // テスト用ディレクトリを作成
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
  });

  afterEach(async () => {
    // クリーンアップ
    await rm(TEST_DIR, { recursive: true, force: true });
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

    // 設定を読み込み
    const { config } = await loadConfig({
      cwd: TEST_DIR,
      configPath: '.shirushi.yml',
    });

    // スキャン実行
    const result = await scanDocuments(config, { cwd: TEST_DIR });

    expect(result.documents).toHaveLength(1);
    expect(result.documents[0].docId).toBe('SPEC-2025-0001');
    expect(result.documents[0].metadata.title).toBe('Test Document');
    expect(result.summary.totalFiles).toBe(1);
    expect(result.summary.withDocId).toBe(1);
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

    const { config } = await loadConfig({
      cwd: TEST_DIR,
      configPath: '.shirushi.yml',
    });

    const result = await scanDocuments(config, { cwd: TEST_DIR });

    expect(result.documents[0].docId).toBeUndefined();
    expect(result.summary.withoutDocId).toBe(1);
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

    const { config } = await loadConfig({
      cwd: TEST_DIR,
      configPath: '.shirushi.yml',
    });

    const result = await scanDocuments(config, { cwd: TEST_DIR });

    expect(result.documents).toHaveLength(3);
    expect(result.summary.markdownFiles).toBe(2);
    expect(result.summary.yamlFiles).toBe(1);
    expect(result.summary.withDocId).toBe(3);
  });
});
