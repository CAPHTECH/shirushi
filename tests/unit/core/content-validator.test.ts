/**
 * Content Validator Tests
 */

import { describe, it, expect } from 'vitest';

import { validateContentIntegrity } from '@/core/content-validator';
import { calculateContentHash } from '@/utils/content-hash';

import type { IndexEntry } from '@/core/index-manager';
import type { DocumentParseResult } from '@/types/document';

describe('content-validator', () => {
  describe('validateContentIntegrity', () => {
    it('should return no errors when hashes match', () => {
      const content = 'test content';
      const hash = calculateContentHash(content);

      const documents: DocumentParseResult[] = [
        {
          kind: 'markdown',
          path: 'docs/test.md',
          docId: 'TEST-001',
          metadata: {},
          problems: [],
          content,
        },
      ];

      const indexByPath = new Map<string, IndexEntry>([
        ['docs/test.md', { doc_id: 'TEST-001', path: 'docs/test.md', content_hash: hash }],
      ]);

      const result = validateContentIntegrity(documents, indexByPath);

      expect(result.errors).toHaveLength(0);
      expect(result.calculatedHashes.get('docs/test.md')).toBe(hash);
      expect(result.mismatchedDocIds).toHaveLength(0);
    });

    it('should return CONTENT_HASH_MISMATCH when hashes differ', () => {
      const documents: DocumentParseResult[] = [
        {
          kind: 'markdown',
          path: 'docs/test.md',
          docId: 'TEST-001',
          metadata: {},
          problems: [],
          content: 'new content',
        },
      ];

      const oldHash = calculateContentHash('old content');
      const indexByPath = new Map<string, IndexEntry>([
        ['docs/test.md', { doc_id: 'TEST-001', path: 'docs/test.md', content_hash: oldHash }],
      ]);

      const result = validateContentIntegrity(documents, indexByPath);

      expect(result.errors).toHaveLength(1);
      expect(result.errors[0]?.code).toBe('CONTENT_HASH_MISMATCH');
      expect(result.errors[0]?.path).toBe('docs/test.md');
      expect(result.mismatchedDocIds).toContain('TEST-001');
    });

    it('should return MISSING_CONTENT_HASH when index entry has no hash', () => {
      const documents: DocumentParseResult[] = [
        {
          kind: 'markdown',
          path: 'docs/test.md',
          docId: 'TEST-001',
          metadata: {},
          problems: [],
          content: 'some content',
        },
      ];

      const indexByPath = new Map<string, IndexEntry>([
        ['docs/test.md', { doc_id: 'TEST-001', path: 'docs/test.md' }], // no content_hash
      ]);

      const result = validateContentIntegrity(documents, indexByPath);

      expect(result.errors).toHaveLength(1);
      expect(result.errors[0]?.code).toBe('MISSING_CONTENT_HASH');
      expect(result.errors[0]?.severity).toBe('warning');
    });

    it('should skip documents without content field', () => {
      const documents: DocumentParseResult[] = [
        {
          kind: 'markdown',
          path: 'docs/test.md',
          docId: 'TEST-001',
          metadata: {},
          problems: [],
          // no content field
        },
      ];

      const indexByPath = new Map<string, IndexEntry>([
        ['docs/test.md', { doc_id: 'TEST-001', path: 'docs/test.md', content_hash: 'somehash' }],
      ]);

      const result = validateContentIntegrity(documents, indexByPath);

      expect(result.errors).toHaveLength(0);
      expect(result.calculatedHashes.size).toBe(0);
    });

    it('should skip documents not in index', () => {
      const documents: DocumentParseResult[] = [
        {
          kind: 'markdown',
          path: 'docs/new.md',
          docId: 'TEST-002',
          metadata: {},
          problems: [],
          content: 'new document',
        },
      ];

      const indexByPath = new Map<string, IndexEntry>(); // empty index

      const result = validateContentIntegrity(documents, indexByPath);

      expect(result.errors).toHaveLength(0);
      // Hash should still be calculated
      expect(result.calculatedHashes.has('docs/new.md')).toBe(true);
    });

    it('should handle Windows-style paths (backslash normalization)', () => {
      const content = 'test content';
      const hash = calculateContentHash(content);

      const documents: DocumentParseResult[] = [
        {
          kind: 'markdown',
          path: 'docs\\subfolder\\test.md', // Windows path
          docId: 'TEST-001',
          metadata: {},
          problems: [],
          content,
        },
      ];

      const indexByPath = new Map<string, IndexEntry>([
        ['docs/subfolder/test.md', { doc_id: 'TEST-001', path: 'docs/subfolder/test.md', content_hash: hash }],
      ]);

      const result = validateContentIntegrity(documents, indexByPath);

      expect(result.errors).toHaveLength(0);
    });

    it('should handle multiple documents', () => {
      const content1 = 'content 1';
      const content2 = 'content 2';
      const hash1 = calculateContentHash(content1);
      const hash2 = calculateContentHash(content2);

      const documents: DocumentParseResult[] = [
        {
          kind: 'markdown',
          path: 'docs/doc1.md',
          docId: 'TEST-001',
          metadata: {},
          problems: [],
          content: content1,
        },
        {
          kind: 'markdown',
          path: 'docs/doc2.md',
          docId: 'TEST-002',
          metadata: {},
          problems: [],
          content: content2,
        },
      ];

      const indexByPath = new Map<string, IndexEntry>([
        ['docs/doc1.md', { doc_id: 'TEST-001', path: 'docs/doc1.md', content_hash: hash1 }],
        ['docs/doc2.md', { doc_id: 'TEST-002', path: 'docs/doc2.md', content_hash: hash2 }],
      ]);

      const result = validateContentIntegrity(documents, indexByPath);

      expect(result.errors).toHaveLength(0);
      expect(result.calculatedHashes.size).toBe(2);
    });

    it('should collect multiple mismatched doc_ids', () => {
      const documents: DocumentParseResult[] = [
        {
          kind: 'markdown',
          path: 'docs/doc1.md',
          docId: 'TEST-001',
          metadata: {},
          problems: [],
          content: 'new content 1',
        },
        {
          kind: 'markdown',
          path: 'docs/doc2.md',
          docId: 'TEST-002',
          metadata: {},
          problems: [],
          content: 'new content 2',
        },
      ];

      const oldHash = calculateContentHash('old');
      const indexByPath = new Map<string, IndexEntry>([
        ['docs/doc1.md', { doc_id: 'TEST-001', path: 'docs/doc1.md', content_hash: oldHash }],
        ['docs/doc2.md', { doc_id: 'TEST-002', path: 'docs/doc2.md', content_hash: oldHash }],
      ]);

      const result = validateContentIntegrity(documents, indexByPath);

      expect(result.errors).toHaveLength(2);
      expect(result.mismatchedDocIds).toContain('TEST-001');
      expect(result.mismatchedDocIds).toContain('TEST-002');
    });

    it('should handle YAML documents', () => {
      const content = 'key: value\nother: data';
      const hash = calculateContentHash(content);

      const documents: DocumentParseResult[] = [
        {
          kind: 'yaml',
          path: 'docs/config.yaml',
          docId: 'CFG-001',
          metadata: { key: 'value', other: 'data' },
          problems: [],
          content,
        },
      ];

      const indexByPath = new Map<string, IndexEntry>([
        ['docs/config.yaml', { doc_id: 'CFG-001', path: 'docs/config.yaml', content_hash: hash }],
      ]);

      const result = validateContentIntegrity(documents, indexByPath);

      expect(result.errors).toHaveLength(0);
    });
  });
});
