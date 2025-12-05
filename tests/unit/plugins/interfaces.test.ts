/**
 * Plugin Interfaces Tests
 *
 * プラグインインターフェースの型安全性と互換性をテスト
 */

import { left, right, isLeft, isRight } from 'fp-ts/Either';
import { describe, it, expect } from 'vitest';


import {
  isDocumentSource,
  isUpdatableDocumentSource,
  isIndexStore,
  isOrphanDetectableIndexStore,
  isChangeTracker,
  isRefValidatableChangeTracker,
  isShirushiPlugin,
  hasDocumentSource,
  hasIndexStore,
  hasChangeTracker,
} from '@/plugins';
import {
  toPluginIndexEntry,
  toIndexEntry,
  toPluginDocIdChange,
  toDocIdChange,
  toPluginChangeDetectionResult,
  toChangeDetectionResult,
} from '@/plugins';

import type { IndexEntry } from '@/core/index-manager';
import type { DocIdChange, ChangeDetectionResult } from '@/git/types';
import type {
  DocumentSource,
  DocumentReference,
  DocumentContent,
  IndexStore,
  PluginIndexEntry,
  ChangeTracker,
  PluginChangeDetectionResult,
  ShirushiPlugin,
} from '@/plugins';

describe('Plugin Interfaces', () => {
  describe('DocumentSource', () => {
    it('should accept valid mock implementation', async () => {
      const mockRef: DocumentReference = {
        id: '1',
        displayPath: 'docs/test.md',
        kind: 'markdown',
      };

      const mockContent: DocumentContent = {
        ref: mockRef,
        docId: 'DOC-0001',
        metadata: { title: 'Test Document' },
      };

      const mockSource: DocumentSource = {
        name: 'test-source',
        async *listDocuments() {
          yield mockRef;
        },
        async getDocument(_ref) {
          return right(mockContent);
        },
      };

      expect(mockSource.name).toBe('test-source');

      // listDocuments should yield documents
      const docs: DocumentReference[] = [];
      for await (const doc of mockSource.listDocuments()) {
        docs.push(doc);
      }
      expect(docs).toHaveLength(1);
      expect(docs[0]).toEqual(mockRef);

      // getDocument should return content
      const result = await mockSource.getDocument(mockRef);
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toEqual(mockContent);
      }
    });

    it('should handle errors with Left', async () => {
      const errorSource: DocumentSource = {
        name: 'error-source',
        async *listDocuments() {
          // Empty generator
        },
        async getDocument() {
          return left({
            code: 'DOCUMENT_SOURCE_ERROR',
            message: 'Connection failed',
            context: { originalError: 'Network timeout' },
          });
        },
      };

      const result = await errorSource.getDocument({
        id: '1',
        displayPath: 'test.md',
        kind: 'markdown',
      });
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('DOCUMENT_SOURCE_ERROR');
      }
    });
  });

  describe('IndexStore', () => {
    it('should accept valid mock implementation', async () => {
      const mockEntry: PluginIndexEntry = {
        docId: 'DOC-0001',
        path: 'docs/test.md',
        title: 'Test',
        docType: 'spec',
      };

      const mockStore: IndexStore = {
        name: 'test-store',
        async getByDocId(docId) {
          return docId === 'DOC-0001' ? right(mockEntry) : right(null);
        },
        async getByPath(path) {
          return path === 'docs/test.md' ? right(mockEntry) : right(null);
        },
        async *listEntries() {
          yield mockEntry;
        },
        async upsert(_entry) {
          return right(undefined);
        },
        async delete(_docId) {
          return right(true);
        },
        async findDuplicates() {
          return right({ duplicates: [] });
        },
      };

      expect(mockStore.name).toBe('test-store');

      // getByDocId
      const byIdResult = await mockStore.getByDocId('DOC-0001');
      expect(isRight(byIdResult)).toBe(true);
      if (isRight(byIdResult)) {
        expect(byIdResult.right).toEqual(mockEntry);
      }

      // listEntries
      const entries: PluginIndexEntry[] = [];
      for await (const entry of mockStore.listEntries()) {
        entries.push(entry);
      }
      expect(entries).toHaveLength(1);
    });
  });

  describe('ChangeTracker', () => {
    it('should accept valid mock implementation', async () => {
      const mockResult: PluginChangeDetectionResult = {
        changedDocIds: [],
        newDocuments: [],
        deletedDocuments: [],
        warnings: [],
      };

      const mockSource: DocumentSource = {
        name: 'mock-source',
        async *listDocuments() {},
        async getDocument() {
          return right(null);
        },
      };

      const mockTracker: ChangeTracker = {
        name: 'test-tracker',
        async detectChanges(_baseRef, _source) {
          return right(mockResult);
        },
        async isAvailable() {
          return true;
        },
      };

      expect(mockTracker.name).toBe('test-tracker');

      const isAvail = await mockTracker.isAvailable();
      expect(isAvail).toBe(true);

      const result = await mockTracker.detectChanges('main', mockSource);
      expect(isRight(result)).toBe(true);
    });
  });
});

describe('Type Guards', () => {
  describe('isDocumentSource', () => {
    it('should return true for valid DocumentSource', () => {
      const valid: DocumentSource = {
        name: 'test',
        async *listDocuments() {},
        async getDocument() {
          return right(null);
        },
      };
      expect(isDocumentSource(valid)).toBe(true);
    });

    it('should return false for invalid objects', () => {
      expect(isDocumentSource(null)).toBe(false);
      expect(isDocumentSource(undefined)).toBe(false);
      expect(isDocumentSource({})).toBe(false);
      expect(isDocumentSource({ name: 'test' })).toBe(false);
    });
  });

  describe('isUpdatableDocumentSource', () => {
    it('should detect updateDocument method', () => {
      const withUpdate: DocumentSource = {
        name: 'test',
        async *listDocuments() {},
        async getDocument() {
          return right(null);
        },
        async updateDocument() {
          return right(undefined);
        },
      };
      const withoutUpdate: DocumentSource = {
        name: 'test',
        async *listDocuments() {},
        async getDocument() {
          return right(null);
        },
      };

      expect(isUpdatableDocumentSource(withUpdate)).toBe(true);
      expect(isUpdatableDocumentSource(withoutUpdate)).toBe(false);
    });
  });

  describe('isIndexStore', () => {
    it('should return true for valid IndexStore', () => {
      const valid: IndexStore = {
        name: 'test',
        async getByDocId() {
          return right(null);
        },
        async getByPath() {
          return right(null);
        },
        async *listEntries() {},
        async upsert() {
          return right(undefined);
        },
        async delete() {
          return right(false);
        },
        async findDuplicates() {
          return right({ duplicates: [] });
        },
      };
      expect(isIndexStore(valid)).toBe(true);
    });

    it('should return false for invalid objects', () => {
      expect(isIndexStore(null)).toBe(false);
      expect(isIndexStore({ name: 'test' })).toBe(false);
    });
  });

  describe('isOrphanDetectableIndexStore', () => {
    it('should detect findOrphans method', () => {
      const withOrphans: IndexStore = {
        name: 'test',
        async getByDocId() {
          return right(null);
        },
        async getByPath() {
          return right(null);
        },
        async *listEntries() {},
        async upsert() {
          return right(undefined);
        },
        async delete() {
          return right(false);
        },
        async findDuplicates() {
          return right({ duplicates: [] });
        },
        async findOrphans() {
          return right([]);
        },
      };
      const withoutOrphans: IndexStore = {
        name: 'test',
        async getByDocId() {
          return right(null);
        },
        async getByPath() {
          return right(null);
        },
        async *listEntries() {},
        async upsert() {
          return right(undefined);
        },
        async delete() {
          return right(false);
        },
        async findDuplicates() {
          return right({ duplicates: [] });
        },
      };

      expect(isOrphanDetectableIndexStore(withOrphans)).toBe(true);
      expect(isOrphanDetectableIndexStore(withoutOrphans)).toBe(false);
    });
  });

  describe('isChangeTracker', () => {
    it('should return true for valid ChangeTracker', () => {
      const valid: ChangeTracker = {
        name: 'test',
        async detectChanges() {
          return right({
            changedDocIds: [],
            newDocuments: [],
            deletedDocuments: [],
            warnings: [],
          });
        },
        async isAvailable() {
          return true;
        },
      };
      expect(isChangeTracker(valid)).toBe(true);
    });

    it('should return false for invalid objects', () => {
      expect(isChangeTracker(null)).toBe(false);
      expect(isChangeTracker({ name: 'test' })).toBe(false);
    });
  });

  describe('isRefValidatableChangeTracker', () => {
    it('should detect isValidRef method', () => {
      const withValidRef: ChangeTracker = {
        name: 'test',
        async detectChanges() {
          return right({
            changedDocIds: [],
            newDocuments: [],
            deletedDocuments: [],
            warnings: [],
          });
        },
        async isAvailable() {
          return true;
        },
        async isValidRef() {
          return true;
        },
      };
      const withoutValidRef: ChangeTracker = {
        name: 'test',
        async detectChanges() {
          return right({
            changedDocIds: [],
            newDocuments: [],
            deletedDocuments: [],
            warnings: [],
          });
        },
        async isAvailable() {
          return true;
        },
      };

      expect(isRefValidatableChangeTracker(withValidRef)).toBe(true);
      expect(isRefValidatableChangeTracker(withoutValidRef)).toBe(false);
    });
  });

  describe('isShirushiPlugin', () => {
    it('should return true for valid ShirushiPlugin', () => {
      const valid: ShirushiPlugin = {
        name: 'test-plugin',
        version: '1.0.0',
      };
      expect(isShirushiPlugin(valid)).toBe(true);
    });

    it('should return false for invalid objects', () => {
      expect(isShirushiPlugin(null)).toBe(false);
      expect(isShirushiPlugin({ name: 'test' })).toBe(false);
    });
  });

  describe('hasDocumentSource/hasIndexStore/hasChangeTracker', () => {
    it('should detect plugin capabilities', () => {
      const fullPlugin: ShirushiPlugin = {
        name: 'full-plugin',
        version: '1.0.0',
        documentSource: {
          name: 'ds',
          async *listDocuments() {},
          async getDocument() {
            return right(null);
          },
        },
        indexStore: {
          name: 'is',
          async getByDocId() {
            return right(null);
          },
          async getByPath() {
            return right(null);
          },
          async *listEntries() {},
          async upsert() {
            return right(undefined);
          },
          async delete() {
            return right(false);
          },
          async findDuplicates() {
            return right({ duplicates: [] });
          },
        },
        changeTracker: {
          name: 'ct',
          async detectChanges() {
            return right({
              changedDocIds: [],
              newDocuments: [],
              deletedDocuments: [],
              warnings: [],
            });
          },
          async isAvailable() {
            return true;
          },
        },
      };

      const minimalPlugin: ShirushiPlugin = {
        name: 'minimal-plugin',
        version: '1.0.0',
      };

      expect(hasDocumentSource(fullPlugin)).toBe(true);
      expect(hasIndexStore(fullPlugin)).toBe(true);
      expect(hasChangeTracker(fullPlugin)).toBe(true);

      expect(hasDocumentSource(minimalPlugin)).toBe(false);
      expect(hasIndexStore(minimalPlugin)).toBe(false);
      expect(hasChangeTracker(minimalPlugin)).toBe(false);
    });
  });
});

describe('Compatibility Utilities', () => {
  describe('IndexEntry conversion', () => {
    it('should convert IndexEntry to PluginIndexEntry', () => {
      const indexEntry: IndexEntry = {
        doc_id: 'DOC-0001',
        path: 'docs/test.md',
        title: 'Test',
        doc_type: 'spec',
        status: 'draft',
        version: '1.0.0',
        owner: 'owner',
        tags: ['tag1', 'tag2'],
      };

      const pluginEntry = toPluginIndexEntry(indexEntry);

      expect(pluginEntry.docId).toBe('DOC-0001');
      expect(pluginEntry.path).toBe('docs/test.md');
      expect(pluginEntry.title).toBe('Test');
      expect(pluginEntry.docType).toBe('spec');
      expect(pluginEntry.status).toBe('draft');
      expect(pluginEntry.version).toBe('1.0.0');
      expect(pluginEntry.owner).toBe('owner');
      expect(pluginEntry.tags).toEqual(['tag1', 'tag2']);
    });

    it('should convert PluginIndexEntry to IndexEntry', () => {
      const pluginEntry: PluginIndexEntry = {
        docId: 'DOC-0002',
        path: 'docs/other.md',
        title: 'Other',
        docType: 'guide',
      };

      const indexEntry = toIndexEntry(pluginEntry);

      expect(indexEntry.doc_id).toBe('DOC-0002');
      expect(indexEntry.path).toBe('docs/other.md');
      expect(indexEntry.title).toBe('Other');
      expect(indexEntry.doc_type).toBe('guide');
    });

    it('should handle undefined optional fields', () => {
      const minimalEntry: IndexEntry = {
        doc_id: 'DOC-MIN',
        path: 'docs/min.md',
      };

      const pluginEntry = toPluginIndexEntry(minimalEntry);
      const backToIndex = toIndexEntry(pluginEntry);

      expect(pluginEntry.docId).toBe('DOC-MIN');
      expect(pluginEntry.title).toBeUndefined();
      expect(backToIndex.doc_id).toBe('DOC-MIN');
      expect(backToIndex.title).toBeUndefined();
    });
  });

  describe('DocIdChange conversion', () => {
    it('should convert DocIdChange to PluginDocIdChange', () => {
      const change: DocIdChange = {
        path: 'docs/test.md',
        oldDocId: 'OLD-001',
        newDocId: 'NEW-001',
        changeType: 'modified',
      };

      const pluginChange = toPluginDocIdChange(change);

      expect(pluginChange.path).toBe('docs/test.md');
      expect(pluginChange.oldDocId).toBe('OLD-001');
      expect(pluginChange.newDocId).toBe('NEW-001');
      expect(pluginChange.changeType).toBe('modified');
    });

    it('should convert PluginDocIdChange to DocIdChange', () => {
      const pluginChange = {
        path: 'docs/new.md',
        oldDocId: null,
        newDocId: 'NEW-002',
        changeType: 'added' as const,
      };

      const change = toDocIdChange(pluginChange);

      expect(change.path).toBe('docs/new.md');
      expect(change.oldDocId).toBeNull();
      expect(change.newDocId).toBe('NEW-002');
      expect(change.changeType).toBe('added');
    });
  });

  describe('ChangeDetectionResult conversion', () => {
    it('should convert ChangeDetectionResult to PluginChangeDetectionResult', () => {
      const result: ChangeDetectionResult = {
        changedDocIds: [
          {
            path: 'docs/test.md',
            oldDocId: 'OLD',
            newDocId: 'NEW',
            changeType: 'modified',
          },
        ],
        newFiles: ['docs/new.md'],
        deletedFiles: ['docs/old.md'],
        errors: [
          {
            code: 'GIT_ERROR',
            message: 'Failed to read file',
          },
        ],
      };

      const pluginResult = toPluginChangeDetectionResult(result);

      expect(pluginResult.changedDocIds).toHaveLength(1);
      expect(pluginResult.newDocuments).toEqual(['docs/new.md']);
      expect(pluginResult.deletedDocuments).toEqual(['docs/old.md']);
      expect(pluginResult.warnings).toEqual(['Failed to read file']);
    });

    it('should convert PluginChangeDetectionResult to ChangeDetectionResult', () => {
      const pluginResult = {
        changedDocIds: [
          {
            path: 'docs/test.md',
            oldDocId: 'OLD',
            newDocId: 'NEW',
            changeType: 'modified' as const,
          },
        ],
        newDocuments: ['docs/new.md'],
        deletedDocuments: ['docs/old.md'],
        warnings: ['Warning message'],
      };

      const result = toChangeDetectionResult(pluginResult);

      expect(result.changedDocIds).toHaveLength(1);
      expect(result.newFiles).toEqual(['docs/new.md']);
      expect(result.deletedFiles).toEqual(['docs/old.md']);
      expect(result.errors).toHaveLength(1);
      expect(result.errors[0].message).toBe('Warning message');
    });
  });
});
