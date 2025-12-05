/**
 * Custom id_field Integration Tests
 *
 * カスタムIDフィールド名（id_field設定）を使用した統合テスト。
 * デフォルトの`doc_id`以外のフィールド名での動作を検証する。
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';

import { executeLint } from '@/cli/commands/lint';
import { executeScan } from '@/cli/commands/scan';

const TEST_DIR = path.join(process.cwd(), 'tests/.tmp/custom-id-field');

describe('custom id_field integration', () => {
  beforeEach(async () => {
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
    vi.spyOn(console, 'log').mockImplementation(() => {});
    vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
    vi.restoreAllMocks();
  });

  describe('scan command with custom id_field', () => {
    it('should scan documents using custom id_field "document_id"', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
id_field: "document_id"
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

      // カスタムフィールド名を使用したドキュメント
      const doc = `---
document_id: DOC-0001
title: Custom Field Document
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/custom.md'), doc);

      const result = await executeScan({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        format: 'json',
      });

      expect(result).toBe(0);
    });

    it('should detect MISSING_ID when custom id_field is not present', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
id_field: "document_id"
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

      // doc_idがあるがdocument_idがないドキュメント
      const doc = `---
doc_id: DOC-0001
title: Wrong Field Name
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/wrong-field.md'), doc);

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      // document_idフィールドがないためMISSING_IDエラー
      expect(exitCode).toBe(1);
    });
  });

  describe('lint command with custom id_field', () => {
    it('should validate documents using custom id_field "identifier"', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_field: "identifier"
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

      const doc = `---
identifier: DOC-0001
title: Valid Document
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/valid.md'), doc);

      // カスタムフィールド名を使用したインデックス
      const indexContent = `
documents:
  - identifier: DOC-0001
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

    it('should detect DOC_ID_MISMATCH_WITH_INDEX for custom id_field', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_field: "identifier"
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
identifier: DOC-0001
title: Document
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc.md'), doc);

      // インデックスのidentifierが異なる
      const indexContent = `
documents:
  - identifier: DOC-9999
    path: docs/doc.md
    title: Document
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      expect(exitCode).toBe(1);
    });

    it('should validate checksum with custom id_field', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_field: "doc_identifier"
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

      // DOC-0001の正しいチェックサム: R
      const doc = `---
doc_identifier: DOC-0001-R
title: Valid Checksum
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/checksum.md'), doc);

      const indexContent = `
documents:
  - doc_identifier: DOC-0001-R
    path: docs/checksum.md
    title: Valid Checksum
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      expect(exitCode).toBe(0);
    });
  });

  describe('YAML documents with custom id_field', () => {
    it('should parse YAML documents with custom id_field', async () => {
      // Create config subdirectory to separate from index file
      await mkdir(path.join(TEST_DIR, 'docs/config'), { recursive: true });

      const configContent = `
doc_globs:
  - "docs/config/**/*.yaml"
index_file: "docs/doc_index.yaml"
id_field: "yaml_id"
id_format: "{TYPE}-{NUM}"
dimensions:
  TYPE:
    type: enum
    values: ["CONF"]
  NUM:
    type: serial
    digits: 4
    scope: ["TYPE"]
`;
      await writeFile(path.join(TEST_DIR, '.shirushi.yml'), configContent);

      const yamlDoc = `yaml_id: CONF-0001
title: Configuration
settings:
  key: value
`;
      await writeFile(path.join(TEST_DIR, 'docs/config/config.yaml'), yamlDoc);

      const indexContent = `
documents:
  - yaml_id: CONF-0001
    path: docs/config/config.yaml
    title: Configuration
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      expect(exitCode).toBe(0);
    });
  });

  describe('edge cases', () => {
    it('should handle underscore in custom id_field name', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_field: "my_custom_doc_id"
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
my_custom_doc_id: DOC-0001
title: Underscore Field
---

# Content
`;
      await writeFile(path.join(TEST_DIR, 'docs/underscore.md'), doc);

      const indexContent = `
documents:
  - my_custom_doc_id: DOC-0001
    path: docs/underscore.md
    title: Underscore Field
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      expect(exitCode).toBe(0);
    });

    it('should handle multiple documents with custom id_field', async () => {
      const configContent = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_field: "item_id"
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

      const doc1 = `---
item_id: DOC-0001
title: First Document
---

# First
`;
      const doc2 = `---
item_id: DOC-0002
title: Second Document
---

# Second
`;
      const doc3 = `---
item_id: SPEC-0001
title: First Spec
---

# Spec
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc1.md'), doc1);
      await writeFile(path.join(TEST_DIR, 'docs/doc2.md'), doc2);
      await writeFile(path.join(TEST_DIR, 'docs/spec1.md'), doc3);

      const indexContent = `
documents:
  - item_id: DOC-0001
    path: docs/doc1.md
    title: First Document
  - item_id: DOC-0002
    path: docs/doc2.md
    title: Second Document
  - item_id: SPEC-0001
    path: docs/spec1.md
    title: First Spec
`;
      await writeFile(path.join(TEST_DIR, 'docs/doc_index.yaml'), indexContent);

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      expect(exitCode).toBe(0);
    });
  });
});
