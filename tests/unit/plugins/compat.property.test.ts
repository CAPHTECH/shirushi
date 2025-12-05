/**
 * Plugin Compatibility Utilities - Property-Based Tests
 *
 * fast-check を使用した変換関数のラウンドトリップテスト。
 * 任意の入力に対して、変換の可逆性を検証します。
 */

import * as fc from 'fast-check';
import { describe, it, expect } from 'vitest';

import {
  toPluginIndexEntry,
  toIndexEntry,
  toPluginDocIdChange,
  toDocIdChange,
} from '@/plugins/compat';

import type { IndexEntry } from '@/core/index-manager';
import type { DocIdChange } from '@/git/types';
import type { PluginIndexEntry, PluginDocIdChange } from '@/plugins';

// ============================================================
// Arbitrary Generators
// ============================================================

/**
 * IndexEntry 用の Arbitrary
 */
const indexEntryArbitrary: fc.Arbitrary<IndexEntry> = fc.record({
  doc_id: fc.string({ minLength: 1 }),
  path: fc.string({ minLength: 1 }),
  title: fc.option(fc.string(), { nil: undefined }),
  doc_type: fc.option(fc.string(), { nil: undefined }),
  status: fc.option(fc.string(), { nil: undefined }),
  version: fc.option(fc.string(), { nil: undefined }),
  owner: fc.option(fc.string(), { nil: undefined }),
  tags: fc.option(fc.array(fc.string()), { nil: undefined }),
});

/**
 * PluginIndexEntry 用の Arbitrary
 */
const pluginIndexEntryArbitrary: fc.Arbitrary<PluginIndexEntry> = fc.record({
  docId: fc.string({ minLength: 1 }),
  path: fc.string({ minLength: 1 }),
  title: fc.option(fc.string(), { nil: undefined }),
  docType: fc.option(fc.string(), { nil: undefined }),
  status: fc.option(fc.string(), { nil: undefined }),
  version: fc.option(fc.string(), { nil: undefined }),
  owner: fc.option(fc.string(), { nil: undefined }),
  tags: fc.option(fc.array(fc.string()), { nil: undefined }),
  // extra は IndexEntry に対応がないため、ラウンドトリップテストでは除外
});

/**
 * DocIdChange 用の Arbitrary
 */
const docIdChangeArbitrary: fc.Arbitrary<DocIdChange> = fc.record({
  path: fc.string({ minLength: 1 }),
  oldDocId: fc.oneof(fc.string(), fc.constant(null)),
  newDocId: fc.oneof(fc.string(), fc.constant(null)),
  changeType: fc.constantFrom('added', 'modified', 'deleted'),
});

/**
 * PluginDocIdChange 用の Arbitrary
 */
const pluginDocIdChangeArbitrary: fc.Arbitrary<PluginDocIdChange> = fc.record({
  path: fc.string({ minLength: 1 }),
  oldDocId: fc.oneof(fc.string(), fc.constant(null)),
  newDocId: fc.oneof(fc.string(), fc.constant(null)),
  changeType: fc.constantFrom('added', 'modified', 'deleted'),
});

// ============================================================
// Property-Based Tests
// ============================================================

describe('Plugin Compatibility - Property-Based Tests', () => {
  describe('IndexEntry ↔ PluginIndexEntry Round-Trip', () => {
    it('toIndexEntry(toPluginIndexEntry(entry)) should equal original entry', () => {
      fc.assert(
        fc.property(indexEntryArbitrary, (entry) => {
          const pluginEntry = toPluginIndexEntry(entry);
          const backToEntry = toIndexEntry(pluginEntry);

          // 必須フィールドの等価性
          expect(backToEntry.doc_id).toBe(entry.doc_id);
          expect(backToEntry.path).toBe(entry.path);

          // オプショナルフィールドの等価性
          expect(backToEntry.title).toBe(entry.title);
          expect(backToEntry.doc_type).toBe(entry.doc_type);
          expect(backToEntry.status).toBe(entry.status);
          expect(backToEntry.version).toBe(entry.version);
          expect(backToEntry.owner).toBe(entry.owner);

          // tags は防御的コピーされるため、値の等価性で比較
          if (entry.tags === undefined) {
            expect(backToEntry.tags).toBeUndefined();
          } else {
            expect(backToEntry.tags).toEqual(entry.tags);
            // 異なる参照であることを確認（防御的コピーの検証）
            expect(backToEntry.tags).not.toBe(entry.tags);
          }
        }),
        { numRuns: 100 }
      );
    });

    it('toPluginIndexEntry(toIndexEntry(pluginEntry)) should preserve data', () => {
      fc.assert(
        fc.property(pluginIndexEntryArbitrary, (pluginEntry) => {
          const indexEntry = toIndexEntry(pluginEntry);
          const backToPlugin = toPluginIndexEntry(indexEntry);

          expect(backToPlugin.docId).toBe(pluginEntry.docId);
          expect(backToPlugin.path).toBe(pluginEntry.path);
          expect(backToPlugin.title).toBe(pluginEntry.title);
          expect(backToPlugin.docType).toBe(pluginEntry.docType);
          expect(backToPlugin.status).toBe(pluginEntry.status);
          expect(backToPlugin.version).toBe(pluginEntry.version);
          expect(backToPlugin.owner).toBe(pluginEntry.owner);

          if (pluginEntry.tags === undefined) {
            expect(backToPlugin.tags).toBeUndefined();
          } else {
            expect(backToPlugin.tags).toEqual(pluginEntry.tags);
          }
        }),
        { numRuns: 100 }
      );
    });

    it('should preserve empty arrays correctly', () => {
      const entry: IndexEntry = {
        doc_id: 'DOC-0001',
        path: 'docs/test.md',
        tags: [],
      };

      const pluginEntry = toPluginIndexEntry(entry);
      const backToEntry = toIndexEntry(pluginEntry);

      expect(backToEntry.tags).toEqual([]);
      expect(backToEntry.tags).not.toBe(entry.tags); // 防御的コピー
    });
  });

  describe('DocIdChange ↔ PluginDocIdChange Round-Trip', () => {
    it('toDocIdChange(toPluginDocIdChange(change)) should equal original', () => {
      fc.assert(
        fc.property(docIdChangeArbitrary, (change) => {
          const pluginChange = toPluginDocIdChange(change);
          const backToChange = toDocIdChange(pluginChange);

          expect(backToChange.path).toBe(change.path);
          expect(backToChange.oldDocId).toBe(change.oldDocId);
          expect(backToChange.newDocId).toBe(change.newDocId);
          expect(backToChange.changeType).toBe(change.changeType);
        }),
        { numRuns: 100 }
      );
    });

    it('toPluginDocIdChange(toDocIdChange(pluginChange)) should preserve data', () => {
      fc.assert(
        fc.property(pluginDocIdChangeArbitrary, (pluginChange) => {
          const change = toDocIdChange(pluginChange);
          const backToPlugin = toPluginDocIdChange(change);

          expect(backToPlugin.path).toBe(pluginChange.path);
          expect(backToPlugin.oldDocId).toBe(pluginChange.oldDocId);
          expect(backToPlugin.newDocId).toBe(pluginChange.newDocId);
          expect(backToPlugin.changeType).toBe(pluginChange.changeType);
        }),
        { numRuns: 100 }
      );
    });
  });

  describe('Defensive Copy Verification', () => {
    it('modifying returned tags array should not affect original', () => {
      fc.assert(
        fc.property(
          fc.array(fc.string(), { minLength: 1, maxLength: 10 }),
          (tags) => {
            const original: IndexEntry = {
              doc_id: 'DOC-0001',
              path: 'docs/test.md',
              tags: [...tags],
            };

            const pluginEntry = toPluginIndexEntry(original);

            // 返却された配列を変更しても元のデータに影響しない
            if (pluginEntry.tags) {
              const mutableTags = pluginEntry.tags as string[];
              mutableTags.push('INJECTED');
              expect(original.tags).not.toContain('INJECTED');
            }
          }
        ),
        { numRuns: 50 }
      );
    });

    it('modifying source tags after conversion should not affect result', () => {
      const tags = ['tag1', 'tag2'];
      const original: IndexEntry = {
        doc_id: 'DOC-0001',
        path: 'docs/test.md',
        tags,
      };

      const pluginEntry = toPluginIndexEntry(original);

      // 元の配列を変更
      tags.push('INJECTED');

      // 変換結果は影響を受けない
      expect(pluginEntry.tags).toEqual(['tag1', 'tag2']);
    });
  });

  describe('Edge Cases', () => {
    it('should handle minimal IndexEntry', () => {
      fc.assert(
        fc.property(
          fc.string({ minLength: 1 }),
          fc.string({ minLength: 1 }),
          (docId, path) => {
            const minimal: IndexEntry = { doc_id: docId, path };
            const converted = toPluginIndexEntry(minimal);
            const backToOriginal = toIndexEntry(converted);

            expect(backToOriginal.doc_id).toBe(docId);
            expect(backToOriginal.path).toBe(path);
            expect(backToOriginal.title).toBeUndefined();
            expect(backToOriginal.tags).toBeUndefined();
          }
        ),
        { numRuns: 50 }
      );
    });

    it('should handle special characters in strings', () => {
      fc.assert(
        fc.property(
          fc.unicodeString({ minLength: 1 }),
          fc.unicodeString({ minLength: 1 }),
          (docId, path) => {
            const entry: IndexEntry = { doc_id: docId, path };
            const converted = toPluginIndexEntry(entry);
            const backToOriginal = toIndexEntry(converted);

            expect(backToOriginal.doc_id).toBe(docId);
            expect(backToOriginal.path).toBe(path);
          }
        ),
        { numRuns: 50 }
      );
    });
  });
});
