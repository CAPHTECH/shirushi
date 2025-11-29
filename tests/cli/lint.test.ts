/**
 * Lint Command E2E Tests
 *
 * lintコマンドのE2Eテスト。
 * バリデーションロジックをテストする。
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import path from 'node:path';
import { mkdir, writeFile, rm } from 'node:fs/promises';
import { scanDocuments } from '@/core/scanner';
import { validateDocId } from '@/core/validator';
import { loadConfig } from '@/config/loader';
import {
  loadIndexFile,
  validateIndexConsistency,
} from '@/core/index-manager';
import { problemToLintError, validationErrorToLintError } from '@/cli/output/reporters';

import type { LintError } from '@/cli/output/reporters';

// テスト用一時ディレクトリ
const TEST_DIR = path.join(process.cwd(), 'tests/.tmp/lint');

/**
 * ドキュメントをスキャンしてlintエラーを収集
 */
async function collectLintErrors(testDir: string): Promise<LintError[]> {
  const { config } = await loadConfig({
    cwd: testDir,
    configPath: '.shirushi.yml',
  });

  const scanResult = await scanDocuments(config, { cwd: testDir });
  const errors: LintError[] = [];

  for (const doc of scanResult.documents) {
    // パース時の問題
    for (const problem of doc.problems) {
      errors.push(problemToLintError(doc.path, problem));
    }

    // doc_idがあれば検証
    if (doc.docId) {
      const validationResult = validateDocId(
        {
          docId: doc.docId,
          documentPath: doc.path,
          documentMeta: doc.metadata,
        },
        config
      );

      if (!validationResult.valid) {
        for (const error of validationResult.errors) {
          errors.push(validationErrorToLintError(doc.path, error));
        }
      }
    }
  }

  // インデックス整合性を検証
  try {
    const indexFile = await loadIndexFile(config.index_file, testDir);
    const indexResult = validateIndexConsistency(
      scanResult.documents,
      indexFile,
      testDir
    );
    errors.push(...indexResult.errors);
  } catch {
    // インデックスファイルなしは許容
  }

  return errors;
}

describe('lint command', () => {
  beforeEach(async () => {
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
  });

  it('should return no errors when all documents are valid', async () => {
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

    const errors = await collectLintErrors(TEST_DIR);
    const fatalErrors = errors.filter((e) => e.severity === 'error');

    expect(fatalErrors).toHaveLength(0);
  });

  it('should detect MISSING_ID error', async () => {
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

    const errors = await collectLintErrors(TEST_DIR);

    expect(errors).toEqual(
      expect.arrayContaining([expect.objectContaining({ code: 'MISSING_ID' })])
    );
  });

  it('should detect MALFORMED_ID error for invalid enum value', async () => {
    // 注意: enumタイプの場合、パターン自体が値リストから生成されるため、
    // 許可されていない値はパターンマッチ段階でMALFORMED_IDエラーになる
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

    const errors = await collectLintErrors(TEST_DIR);

    expect(errors).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ code: 'MALFORMED_ID' }),
      ])
    );
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

    const errors = await collectLintErrors(TEST_DIR);
    const fatalErrors = errors.filter((e) => e.severity === 'error');

    expect(fatalErrors).toHaveLength(0);
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

    const errors = await collectLintErrors(TEST_DIR);

    expect(errors).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ code: 'INVALID_ID_CHECKSUM' }),
      ])
    );
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

    const errors = await collectLintErrors(TEST_DIR);

    expect(errors).toEqual(
      expect.arrayContaining([expect.objectContaining({ code: 'MALFORMED_ID' })])
    );
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

    const errors = await collectLintErrors(TEST_DIR);

    expect(errors).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ code: 'DOC_ID_MISMATCH_WITH_INDEX' }),
      ])
    );
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

    const errors = await collectLintErrors(TEST_DIR);

    expect(errors).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ code: 'UNINDEXED_DOC_ID' }),
      ])
    );
  });
});
