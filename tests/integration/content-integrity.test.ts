/**
 * Content Integrity Integration Tests
 */

import { mkdir, writeFile, rm, readFile } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach } from 'vitest';

import { executeLint } from '@/cli/commands/lint';
import { executeRehash } from '@/cli/commands/rehash';
import { calculateContentHash } from '@/utils/content-hash';

const TEST_DIR = path.join(process.cwd(), 'tests', '.tmp', 'content-integrity');

describe('content-integrity integration', () => {
  beforeEach(async () => {
    await mkdir(path.join(TEST_DIR, 'docs'), { recursive: true });
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
  });

  const createConfig = async (contentIntegrityEnabled: boolean = true) => {
    const config = `
doc_globs:
  - "docs/**/*.md"
index_file: "docs/doc_index.yaml"
id_field: "doc_id"
id_format: "{KIND}-{YEAR4}-{SER4}"
dimensions:
  KIND:
    type: enum
    values: ["SPEC", "API"]
  YEAR4:
    type: year
    digits: 4
    source: "created_at"
  SER4:
    type: serial
    digits: 4
    scope: ["KIND", "YEAR4"]
forbid_id_change: true
allow_missing_id_in_new_files: false
${contentIntegrityEnabled ? `
content_integrity:
  enabled: true
  algorithm: sha256
` : ''}
`;
    await writeFile(path.join(TEST_DIR, '.shirushi.yml'), config);
  };

  const createDocument = async (filename: string, docId: string, content: string) => {
    // gray-matterはフロントマター後の改行を除去した内容を返す
    // 実際のbody: "{content}" (先頭改行なし)
    const frontmatter = `---
doc_id: ${docId}
created_at: "2025-01-01"
---
${content}`;
    await writeFile(path.join(TEST_DIR, 'docs', filename), frontmatter);
    return content; // gray-matter extracts content without leading newline
  };

  const createIndex = async (entries: Array<{ doc_id: string; path: string; content_hash?: string }>) => {
    const yaml = `documents:
${entries.map(e => `  - doc_id: ${e.doc_id}
    path: ${e.path}${e.content_hash ? `
    content_hash: ${e.content_hash}` : ''}`).join('\n')}
`;
    await writeFile(path.join(TEST_DIR, 'docs', 'doc_index.yaml'), yaml);
  };

  describe('lint with content_integrity', () => {
    it('should pass when content hash matches', async () => {
      await createConfig(true);
      const content = await createDocument('spec.md', 'SPEC-2025-0001', 'Document content');
      const hash = calculateContentHash(content);

      await createIndex([
        { doc_id: 'SPEC-2025-0001', path: 'docs/spec.md', content_hash: hash },
      ]);

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        quiet: true,
      });

      expect(exitCode).toBe(0);
    });

    it('should fail when content hash mismatches', async () => {
      await createConfig(true);
      await createDocument('spec.md', 'SPEC-2025-0001', 'New content');
      const oldHash = calculateContentHash('Old content');

      await createIndex([
        { doc_id: 'SPEC-2025-0001', path: 'docs/spec.md', content_hash: oldHash },
      ]);

      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        quiet: true,
      });

      expect(exitCode).toBe(1);
    });

    it('should warn when content_hash is missing from index', async () => {
      await createConfig(true);
      await createDocument('spec.md', 'SPEC-2025-0001', 'Document content');

      await createIndex([
        { doc_id: 'SPEC-2025-0001', path: 'docs/spec.md' }, // no content_hash
      ]);

      // MISSING_CONTENT_HASH is a warning, not error, so lint should pass
      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        quiet: true,
      });

      expect(exitCode).toBe(0);
    });

    it('should not check content when content_integrity is disabled', async () => {
      await createConfig(false);
      await createDocument('spec.md', 'SPEC-2025-0001', 'New content');
      const wrongHash = 'a'.repeat(64);

      await createIndex([
        { doc_id: 'SPEC-2025-0001', path: 'docs/spec.md', content_hash: wrongHash },
      ]);

      // Should pass because content_integrity is disabled
      const exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        quiet: true,
      });

      expect(exitCode).toBe(0);
    });
  });

  describe('rehash command', () => {
    it('should add content_hash to index entries', async () => {
      await createConfig(true);
      const content = await createDocument('spec.md', 'SPEC-2025-0001', 'Document content');

      await createIndex([
        { doc_id: 'SPEC-2025-0001', path: 'docs/spec.md' }, // no hash initially
      ]);

      const exitCode = await executeRehash({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      expect(exitCode).toBe(0);

      // Verify hash was added
      const indexContent = await readFile(path.join(TEST_DIR, 'docs', 'doc_index.yaml'), 'utf8');
      const expectedHash = calculateContentHash(content);
      expect(indexContent).toContain(`content_hash: ${expectedHash}`);
    });

    it('should update changed content_hash', async () => {
      await createConfig(true);
      const content = await createDocument('spec.md', 'SPEC-2025-0001', 'New content');
      const oldHash = calculateContentHash('Old content');

      await createIndex([
        { doc_id: 'SPEC-2025-0001', path: 'docs/spec.md', content_hash: oldHash },
      ]);

      const exitCode = await executeRehash({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
      });

      expect(exitCode).toBe(0);

      // Verify hash was updated
      const indexContent = await readFile(path.join(TEST_DIR, 'docs', 'doc_index.yaml'), 'utf8');
      const newHash = calculateContentHash(content);
      expect(indexContent).toContain(`content_hash: ${newHash}`);
      expect(indexContent).not.toContain(oldHash);
    });

    it('should not modify file in dry-run mode', async () => {
      await createConfig(true);
      await createDocument('spec.md', 'SPEC-2025-0001', 'Document content');

      await createIndex([
        { doc_id: 'SPEC-2025-0001', path: 'docs/spec.md' },
      ]);

      const indexBefore = await readFile(path.join(TEST_DIR, 'docs', 'doc_index.yaml'), 'utf8');

      const exitCode = await executeRehash({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        dryRun: true,
      });

      expect(exitCode).toBe(0);

      const indexAfter = await readFile(path.join(TEST_DIR, 'docs', 'doc_index.yaml'), 'utf8');
      expect(indexAfter).toBe(indexBefore);
    });
  });

  describe('E2E workflow', () => {
    it('should detect content change after initial rehash', async () => {
      await createConfig(true);

      // 1. Create document and index
      await createDocument('spec.md', 'SPEC-2025-0001', 'Initial content');
      await createIndex([
        { doc_id: 'SPEC-2025-0001', path: 'docs/spec.md' },
      ]);

      // 2. Run rehash to add hash
      await executeRehash({ cwd: TEST_DIR, config: '.shirushi.yml' });

      // 3. Verify lint passes
      let exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        quiet: true,
      });
      expect(exitCode).toBe(0);

      // 4. Modify document content
      await createDocument('spec.md', 'SPEC-2025-0001', 'Modified content');

      // 5. Verify lint fails (content changed)
      exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        quiet: true,
      });
      expect(exitCode).toBe(1);

      // 6. Run rehash to update hash
      await executeRehash({ cwd: TEST_DIR, config: '.shirushi.yml' });

      // 7. Verify lint passes again
      exitCode = await executeLint({
        cwd: TEST_DIR,
        config: '.shirushi.yml',
        quiet: true,
      });
      expect(exitCode).toBe(0);
    });
  });
});
