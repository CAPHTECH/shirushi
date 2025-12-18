/**
 * Source Reference Scanner Tests
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach } from 'vitest';

import { scanSourceReferences, filterReferencesByDocIds } from '@/core/source-ref-scanner';

import type { ShirushiConfig } from '@/config/schema';
import type { SourceReference } from '@/core/source-ref-scanner';

const TEST_DIR = path.join(process.cwd(), 'tests', '.tmp', 'source-ref');

describe('source-ref-scanner', () => {
  beforeEach(async () => {
    await mkdir(path.join(TEST_DIR, 'src'), { recursive: true });
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
  });

  const createConfig = (sourceRefs?: ShirushiConfig['content_integrity']['source_references']): ShirushiConfig => ({
    id_format: '{KIND}-{YEAR4}-{SER4}',
    doc_globs: ['docs/**/*.md'],
    dimensions: {
      KIND: { type: 'enum', values: ['SPEC', 'API'] },
      YEAR4: { type: 'year', digits: 4, source: 'created_at' },
      SER4: { type: 'serial', digits: 4, scope: ['KIND', 'YEAR4'] },
    },
    index_file: 'docs/doc_index.yaml',
    id_field: 'doc_id',
    forbid_id_change: true,
    allow_missing_id_in_new_files: false,
    reference_fields: [],
    reference_patterns: [],
    content_integrity: {
      enabled: true,
      algorithm: 'sha256',
      source_references: sourceRefs,
    },
  });

  describe('scanSourceReferences', () => {
    it('should return empty result when source_references is not configured', async () => {
      const config = createConfig(undefined);
      const result = await scanSourceReferences(config, TEST_DIR);

      expect(result.references).toHaveLength(0);
      expect(result.errors).toHaveLength(0);
    });

    it('should return empty result when source_references is empty array', async () => {
      const config = createConfig([]);
      const result = await scanSourceReferences(config, TEST_DIR);

      expect(result.references).toHaveLength(0);
      expect(result.errors).toHaveLength(0);
    });

    it('should detect @see pattern in source files', async () => {
      await writeFile(
        path.join(TEST_DIR, 'src', 'test.ts'),
        `
/**
 * @see SPEC-2025-0001
 */
export function foo() {}
`
      );

      const config = createConfig([
        { glob: 'src/**/*.ts', pattern: '@see\\s+({DOC_ID})' },
      ]);

      const result = await scanSourceReferences(config, TEST_DIR);

      expect(result.references).toHaveLength(1);
      expect(result.references[0]?.docId).toBe('SPEC-2025-0001');
      expect(result.references[0]?.sourcePath).toBe('src/test.ts');
      expect(result.references[0]?.lineNumber).toBe(3);
    });

    it('should detect multiple references in single file', async () => {
      await writeFile(
        path.join(TEST_DIR, 'src', 'multi.ts'),
        `
// @see SPEC-2025-0001
// @see API-2025-0002
`
      );

      const config = createConfig([
        { glob: 'src/**/*.ts', pattern: '@see\\s+({DOC_ID})' },
      ]);

      const result = await scanSourceReferences(config, TEST_DIR);

      expect(result.references).toHaveLength(2);
      expect(result.references.map(r => r.docId)).toContain('SPEC-2025-0001');
      expect(result.references.map(r => r.docId)).toContain('API-2025-0002');
    });

    it('should detect references across multiple files', async () => {
      await writeFile(
        path.join(TEST_DIR, 'src', 'file1.ts'),
        '// @see SPEC-2025-0001'
      );
      await writeFile(
        path.join(TEST_DIR, 'src', 'file2.ts'),
        '// @see API-2025-0002'
      );

      const config = createConfig([
        { glob: 'src/**/*.ts', pattern: '@see\\s+({DOC_ID})' },
      ]);

      const result = await scanSourceReferences(config, TEST_DIR);

      expect(result.references).toHaveLength(2);
    });

    it('should handle custom pattern (ref: format)', async () => {
      await writeFile(
        path.join(TEST_DIR, 'src', 'test.ts'),
        '// ref: SPEC-2025-0001'
      );

      const config = createConfig([
        { glob: 'src/**/*.ts', pattern: 'ref:\\s+({DOC_ID})' },
      ]);

      const result = await scanSourceReferences(config, TEST_DIR);

      expect(result.references).toHaveLength(1);
      expect(result.references[0]?.docId).toBe('SPEC-2025-0001');
    });

    it('should filter files by glob pattern', async () => {
      await writeFile(
        path.join(TEST_DIR, 'src', 'test.ts'),
        '// @see SPEC-2025-0001'
      );
      await writeFile(
        path.join(TEST_DIR, 'src', 'test.js'),
        '// @see API-2025-0002'
      );

      const config = createConfig([
        { glob: 'src/**/*.ts', pattern: '@see\\s+({DOC_ID})' }, // only .ts
      ]);

      const result = await scanSourceReferences(config, TEST_DIR);

      expect(result.references).toHaveLength(1);
      expect(result.references[0]?.docId).toBe('SPEC-2025-0001');
    });

    it('should handle multiple pattern configurations', async () => {
      await writeFile(
        path.join(TEST_DIR, 'src', 'test.ts'),
        '// @see SPEC-2025-0001'
      );
      await mkdir(path.join(TEST_DIR, 'scripts'), { recursive: true });
      await writeFile(
        path.join(TEST_DIR, 'scripts', 'test.py'),
        '# doc: API-2025-0002'
      );

      const config = createConfig([
        { glob: 'src/**/*.ts', pattern: '@see\\s+({DOC_ID})' },
        { glob: 'scripts/**/*.py', pattern: '# doc:\\s+({DOC_ID})' },
      ]);

      const result = await scanSourceReferences(config, TEST_DIR);

      expect(result.references).toHaveLength(2);
    });

    it('should not match invalid doc_id format', async () => {
      await writeFile(
        path.join(TEST_DIR, 'src', 'test.ts'),
        '// @see INVALID-ID-123'
      );

      const config = createConfig([
        { glob: 'src/**/*.ts', pattern: '@see\\s+({DOC_ID})' },
      ]);

      const result = await scanSourceReferences(config, TEST_DIR);

      expect(result.references).toHaveLength(0);
    });

    it('should return correct line numbers', async () => {
      await writeFile(
        path.join(TEST_DIR, 'src', 'test.ts'),
        `line 1
line 2
// @see SPEC-2025-0001
line 4
// @see API-2025-0002
`
      );

      const config = createConfig([
        { glob: 'src/**/*.ts', pattern: '@see\\s+({DOC_ID})' },
      ]);

      const result = await scanSourceReferences(config, TEST_DIR);

      const specRef = result.references.find(r => r.docId === 'SPEC-2025-0001');
      const apiRef = result.references.find(r => r.docId === 'API-2025-0002');

      expect(specRef?.lineNumber).toBe(3);
      expect(apiRef?.lineNumber).toBe(5);
    });
  });

  describe('filterReferencesByDocIds', () => {
    it('should filter references by doc_id list', () => {
      const references: SourceReference[] = [
        { sourcePath: 'src/a.ts', docId: 'SPEC-2025-0001', lineNumber: 1, patternGlob: '**/*.ts' },
        { sourcePath: 'src/b.ts', docId: 'API-2025-0002', lineNumber: 1, patternGlob: '**/*.ts' },
        { sourcePath: 'src/c.ts', docId: 'SPEC-2025-0001', lineNumber: 5, patternGlob: '**/*.ts' },
      ];

      const filtered = filterReferencesByDocIds(references, ['SPEC-2025-0001']);

      expect(filtered).toHaveLength(2);
      expect(filtered.every(r => r.docId === 'SPEC-2025-0001')).toBe(true);
    });

    it('should return empty array when no matches', () => {
      const references: SourceReference[] = [
        { sourcePath: 'src/a.ts', docId: 'SPEC-2025-0001', lineNumber: 1, patternGlob: '**/*.ts' },
      ];

      const filtered = filterReferencesByDocIds(references, ['OTHER-001']);

      expect(filtered).toHaveLength(0);
    });

    it('should handle multiple doc_ids in filter', () => {
      const references: SourceReference[] = [
        { sourcePath: 'src/a.ts', docId: 'SPEC-2025-0001', lineNumber: 1, patternGlob: '**/*.ts' },
        { sourcePath: 'src/b.ts', docId: 'API-2025-0002', lineNumber: 1, patternGlob: '**/*.ts' },
        { sourcePath: 'src/c.ts', docId: 'OTHER-0001', lineNumber: 1, patternGlob: '**/*.ts' },
      ];

      const filtered = filterReferencesByDocIds(references, ['SPEC-2025-0001', 'API-2025-0002']);

      expect(filtered).toHaveLength(2);
    });

    it('should handle empty references array', () => {
      const filtered = filterReferencesByDocIds([], ['SPEC-2025-0001']);
      expect(filtered).toHaveLength(0);
    });

    it('should handle empty doc_ids array', () => {
      const references: SourceReference[] = [
        { sourcePath: 'src/a.ts', docId: 'SPEC-2025-0001', lineNumber: 1, patternGlob: '**/*.ts' },
      ];

      const filtered = filterReferencesByDocIds(references, []);

      expect(filtered).toHaveLength(0);
    });
  });
});
