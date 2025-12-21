/**
 * Show Command E2E Tests
 *
 * showコマンドのE2Eテスト。
 * executeShow関数を呼び出してドキュメント表示機能をテストする。
 *
 * @see Issue #27: shirushi show コマンド
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';

import { executeShow } from '@/cli/commands/show';

// テスト用一時ディレクトリ
const TEST_DIR = path.join(process.cwd(), 'tests/.tmp/show');

describe('show command', () => {
  let consoleOutput: string[] = [];
  let consoleErrors: string[] = [];

  beforeEach(async () => {
    // テスト用ディレクトリを作成
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });

    // console.log/errorをモックして出力をキャプチャ
    consoleOutput = [];
    consoleErrors = [];
    vi.spyOn(console, 'log').mockImplementation((msg: string) => {
      consoleOutput.push(msg);
    });
    vi.spyOn(console, 'error').mockImplementation((msg: string) => {
      consoleErrors.push(msg);
    });
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
    vi.restoreAllMocks();
  });

  /**
   * テスト用の設定とドキュメントをセットアップ
   */
  async function setupTestEnv() {
    // 設定ファイル
    const configContent = `
doc_globs:
  - "docs/**/*.md"
  - "docs/**/*.yaml"
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

    // インデックスファイル
    const indexContent = `documents:
  - doc_id: SPEC-2025-0001
    path: docs/spec.md
    title: 仕様書
  - doc_id: DOC-2025-0001
    path: docs/data.yaml
    title: データファイル
`;
    await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

    // Markdownドキュメント
    const mdContent = `---
doc_id: SPEC-2025-0001
title: 仕様書
status: active
doc_type: spec
owner: John Doe
tags:
  - important
  - v1
---

# 仕様書

これは仕様書の本文です。

## セクション1

詳細な説明がここに入ります。
`;
    await writeFile(path.join(TEST_DIR, 'docs/spec.md'), mdContent);

    // YAMLドキュメント
    const yamlContent = `doc_id: DOC-2025-0001
title: データファイル
status: draft
doc_type: data
`;
    await writeFile(path.join(TEST_DIR, 'docs/data.yaml'), yamlContent);
  }

  describe('正常系', () => {
    it('doc_idでドキュメント情報を表示できる（table形式）', async () => {
      await setupTestEnv();

      const exitCode = await executeShow('SPEC-2025-0001', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        format: 'table',
      });

      expect(exitCode).toBe(0);
      expect(consoleOutput.length).toBeGreaterThan(0);
      const output = consoleOutput[0];
      expect(output).toContain('Path:');
      expect(output).toContain('docs/spec.md');
      expect(output).toContain('Title:');
      expect(output).toContain('仕様書');
      expect(output).toContain('Status:');
      expect(output).toContain('active');
    });

    it('--json オプションでJSON形式で出力できる', async () => {
      await setupTestEnv();

      const exitCode = await executeShow('SPEC-2025-0001', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        format: 'json',
      });

      expect(exitCode).toBe(0);
      const output = JSON.parse(consoleOutput[0]);
      expect(output.doc_id).toBe('SPEC-2025-0001');
      expect(output.path).toBe('docs/spec.md');
      expect(output.title).toBe('仕様書');
      expect(output.status).toBe('active');
      expect(output.content).toContain('仕様書');
    });

    it('--yaml オプションでYAML形式で出力できる', async () => {
      await setupTestEnv();

      const exitCode = await executeShow('SPEC-2025-0001', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        format: 'yaml',
      });

      expect(exitCode).toBe(0);
      const output = consoleOutput[0];
      expect(output).toContain('doc_id: SPEC-2025-0001');
      expect(output).toContain('path: docs/spec.md');
      expect(output).toContain('title: 仕様書');
    });

    it('--path-only オプションでパスのみ出力できる', async () => {
      await setupTestEnv();

      const exitCode = await executeShow('SPEC-2025-0001', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        pathOnly: true,
      });

      expect(exitCode).toBe(0);
      expect(consoleOutput[0]).toBe('docs/spec.md');
    });

    it('--meta-only オプションでメタデータのみ出力できる', async () => {
      await setupTestEnv();

      const exitCode = await executeShow('SPEC-2025-0001', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        metaOnly: true,
      });

      expect(exitCode).toBe(0);
      const output = consoleOutput[0];
      expect(output).toContain('Path:');
      expect(output).toContain('Title:');
      // 本文区切り "---" がないことを確認
      expect(output.split('\n').filter((line: string) => line === '---').length).toBe(0);
    });

    it('YAMLドキュメントも取得できる', async () => {
      await setupTestEnv();

      const exitCode = await executeShow('DOC-2025-0001', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        format: 'json',
      });

      expect(exitCode).toBe(0);
      const output = JSON.parse(consoleOutput[0]);
      expect(output.doc_id).toBe('DOC-2025-0001');
      expect(output.path).toBe('docs/data.yaml');
      expect(output.title).toBe('データファイル');
    });
  });

  describe('エラー系', () => {
    it('存在しないdoc_idはエラー', async () => {
      await setupTestEnv();

      const exitCode = await executeShow('NONEXISTENT-ID', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      expect(exitCode).toBe(1);
      expect(consoleErrors[0]).toContain("'NONEXISTENT-ID'");
      expect(consoleErrors[0]).toContain('not found');
    });

    it('インデックスファイルがない場合はエラー', async () => {
      // 設定ファイルのみ作成
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

      const exitCode = await executeShow('DOC-0001', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      expect(exitCode).toBe(1);
      expect(consoleErrors[0]).toContain('Index file not found');
    });

    it('設定ファイルがない場合はエラー', async () => {
      const exitCode = await executeShow('DOC-0001', {
        cwd: TEST_DIR,
      });

      expect(exitCode).toBe(1);
    });
  });

  describe('出力フォーマット詳細', () => {
    it('tagsを正しく表示する（table形式）', async () => {
      await setupTestEnv();

      const exitCode = await executeShow('SPEC-2025-0001', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        format: 'table',
      });

      expect(exitCode).toBe(0);
      const output = consoleOutput[0];
      expect(output).toContain('Tags:');
      expect(output).toContain('important');
      expect(output).toContain('v1');
    });

    it('ownerを正しく表示する（table形式）', async () => {
      await setupTestEnv();

      const exitCode = await executeShow('SPEC-2025-0001', {
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        format: 'table',
      });

      expect(exitCode).toBe(0);
      const output = consoleOutput[0];
      expect(output).toContain('Owner:');
      expect(output).toContain('John Doe');
    });
  });
});
