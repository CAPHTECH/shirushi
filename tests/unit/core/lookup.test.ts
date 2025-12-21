/**
 * Document Lookup Module Tests
 *
 * lookupDocument関数のユニットテスト。
 * doc_idからドキュメント情報を取得する機能をテストする。
 *
 * @see Issue #27: shirushi show コマンド
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach } from 'vitest';

import { lookupDocument } from '@/core/lookup';

import type { ShirushiConfig } from '@/config/schema';

// テスト用一時ディレクトリ
const TEST_DIR = path.join(process.cwd(), 'tests/.tmp/lookup');

// 基本設定
const createConfig = (overrides: Partial<ShirushiConfig> = {}): ShirushiConfig => ({
  id_format: '{TYPE}-{YEAR}-{NUM}',
  doc_globs: ['docs/**/*.md', 'docs/**/*.yaml'],
  dimensions: {
    TYPE: { type: 'enum', values: ['SPEC', 'DOC'] },
    YEAR: { type: 'year', digits: 4, source: 'created_at' },
    NUM: { type: 'serial', digits: 4, scope: ['TYPE', 'YEAR'] },
  },
  index_file: 'docs/doc_index.yaml',
  id_field: 'doc_id',
  forbid_id_change: true,
  allow_missing_id_in_new_files: false,
  reference_fields: ['superseded_by'],
  reference_patterns: [{ name: 'markdown_link', pattern: '\\[.*?\\]\\({DOC_ID}\\)' }],
  ...overrides,
});

describe('lookupDocument', () => {
  beforeEach(async () => {
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
  });

  describe('正常系', () => {
    it('doc_idからMarkdownドキュメント情報を取得できる', async () => {
      // インデックスファイル作成
      const indexContent = `documents:
  - doc_id: SPEC-2025-0001
    path: docs/spec.md
    title: 仕様書
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      // ドキュメント作成
      const docContent = `---
doc_id: SPEC-2025-0001
title: 仕様書
status: active
---

# 仕様書本文

これは仕様書の本文です。
`;
      await writeFile(path.join(TEST_DIR, 'docs/spec.md'), docContent);

      const config = createConfig();
      const result = await lookupDocument('SPEC-2025-0001', config, { cwd: TEST_DIR });

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.docId).toBe('SPEC-2025-0001');
        expect(result.path).toBe('docs/spec.md');
        expect(result.metadata.title).toBe('仕様書');
        expect(result.metadata.status).toBe('active');
        expect(result.content).toContain('仕様書本文');
        expect(result.indexEntry.doc_id).toBe('SPEC-2025-0001');
      }
    });

    it('doc_idからYAMLドキュメント情報を取得できる', async () => {
      const indexContent = `documents:
  - doc_id: DOC-2025-0001
    path: docs/data.yaml
    title: データファイル
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      const docContent = `doc_id: DOC-2025-0001
title: データファイル
status: draft
description: |
  これはYAMLデータファイルです。
`;
      await writeFile(path.join(TEST_DIR, 'docs/data.yaml'), docContent);

      const config = createConfig();
      const result = await lookupDocument('DOC-2025-0001', config, { cwd: TEST_DIR });

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.docId).toBe('DOC-2025-0001');
        expect(result.path).toBe('docs/data.yaml');
        expect(result.metadata.title).toBe('データファイル');
        expect(result.metadata.status).toBe('draft');
      }
    });

    it('カスタムid_fieldを使用してドキュメントを取得できる', async () => {
      const indexContent = `documents:
  - document_id: SPEC-2025-0001
    path: docs/spec.md
    title: 仕様書
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      const docContent = `---
document_id: SPEC-2025-0001
title: 仕様書
---

# 本文
`;
      await writeFile(path.join(TEST_DIR, 'docs/spec.md'), docContent);

      const config = createConfig({ id_field: 'document_id' });
      const result = await lookupDocument('SPEC-2025-0001', config, { cwd: TEST_DIR });

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.docId).toBe('SPEC-2025-0001');
      }
    });
  });

  describe('エラー系', () => {
    it('インデックスファイルが存在しない場合はINDEX_NOT_FOUNDエラー', async () => {
      const config = createConfig();
      const result = await lookupDocument('SPEC-2025-0001', config, { cwd: TEST_DIR });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.code).toBe('INDEX_NOT_FOUND');
        expect(result.message).toContain('Index file not found');
      }
    });

    it('doc_idが存在しない場合はDOC_ID_NOT_FOUNDエラー', async () => {
      const indexContent = `documents:
  - doc_id: SPEC-2025-0001
    path: docs/spec.md
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      const config = createConfig();
      const result = await lookupDocument('NONEXISTENT-ID', config, { cwd: TEST_DIR });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.code).toBe('DOC_ID_NOT_FOUND');
        expect(result.message).toContain("'NONEXISTENT-ID'");
      }
    });

    it('ファイルが存在しない場合はFILE_NOT_FOUNDエラー', async () => {
      const indexContent = `documents:
  - doc_id: SPEC-2025-0001
    path: docs/missing.md
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      const config = createConfig();
      const result = await lookupDocument('SPEC-2025-0001', config, { cwd: TEST_DIR });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.code).toBe('FILE_NOT_FOUND');
      }
    });
  });
});
