/**
 * Reference Validator Unit Tests
 *
 * 参照検証機能のテスト。
 * Issue #15: doc_id変更時の文書間参照整合性チェック機能
 */

import { describe, it, expect } from 'vitest';

import {
  validateReferences,
  buildChangedDocIdsMap,
  excludeSelfReferences,
} from '@/core/reference-validator';

import type { DocumentReference, StaleReference } from '@/types/reference';

describe('validateReferences', () => {
  it('変更されたdoc_idへの参照をStaleReferenceとして検出する', () => {
    const references: DocumentReference[] = [
      {
        sourcePath: 'docs/guide.md',
        targetDocId: 'PCE-SPEC-2025-0001-Z',
        kind: 'markdown_link',
        lineNumber: 10,
      },
      {
        sourcePath: 'docs/another.md',
        targetDocId: 'PCE-SPEC-2025-0002-A',
        kind: 'yaml_field',
        fieldName: 'superseded_by',
      },
    ];

    const context = {
      changedDocIds: new Map([
        [
          'PCE-SPEC-2025-0001-Z',
          {
            newDocId: 'PCE-SPEC-2025-0001-Y',
            changedDocPath: 'docs/spec.md',
          },
        ],
      ]),
    };

    const result = validateReferences(references, context);

    expect(result.staleReferences).toHaveLength(1);
    expect(result.staleReferences[0]).toEqual({
      sourcePath: 'docs/guide.md',
      oldDocId: 'PCE-SPEC-2025-0001-Z',
      newDocId: 'PCE-SPEC-2025-0001-Y',
      changedDocPath: 'docs/spec.md',
      kind: 'markdown_link',
      lineNumber: 10,
    });
  });

  it('変更されていないdoc_idへの参照は検出しない', () => {
    const references: DocumentReference[] = [
      {
        sourcePath: 'docs/guide.md',
        targetDocId: 'PCE-SPEC-2025-0001-Z',
        kind: 'markdown_link',
        lineNumber: 10,
      },
    ];

    const context = {
      changedDocIds: new Map([
        [
          'PCE-SPEC-2025-0002-A', // 別のdoc_id
          {
            newDocId: 'PCE-SPEC-2025-0002-B',
            changedDocPath: 'docs/other.md',
          },
        ],
      ]),
    };

    const result = validateReferences(references, context);

    expect(result.staleReferences).toHaveLength(0);
  });

  it('空の参照リストでは空の結果を返す', () => {
    const references: DocumentReference[] = [];
    const context = {
      changedDocIds: new Map([
        [
          'PCE-SPEC-2025-0001-Z',
          {
            newDocId: 'PCE-SPEC-2025-0001-Y',
            changedDocPath: 'docs/spec.md',
          },
        ],
      ]),
    };

    const result = validateReferences(references, context);

    expect(result.staleReferences).toHaveLength(0);
  });

  it('削除されたdoc_idへの参照も検出する（newDocIdがnull）', () => {
    const references: DocumentReference[] = [
      {
        sourcePath: 'docs/guide.md',
        targetDocId: 'PCE-SPEC-2025-0001-Z',
        kind: 'markdown_link',
        lineNumber: 10,
      },
    ];

    const context = {
      changedDocIds: new Map([
        [
          'PCE-SPEC-2025-0001-Z',
          {
            newDocId: null, // 削除
            changedDocPath: 'docs/spec.md',
          },
        ],
      ]),
    };

    const result = validateReferences(references, context);

    expect(result.staleReferences).toHaveLength(1);
    expect(result.staleReferences[0]?.newDocId).toBeNull();
  });

  it('custom_patternの参照も正しく検出する', () => {
    const references: DocumentReference[] = [
      {
        sourcePath: 'docs/guide.md',
        targetDocId: 'PCE-SPEC-2025-0001-Z',
        kind: 'custom_pattern',
        lineNumber: 15,
        patternName: 'ref_tag',
      },
    ];

    const context = {
      changedDocIds: new Map([
        [
          'PCE-SPEC-2025-0001-Z',
          {
            newDocId: 'PCE-SPEC-2025-0001-Y',
            changedDocPath: 'docs/spec.md',
          },
        ],
      ]),
    };

    const result = validateReferences(references, context);

    expect(result.staleReferences).toHaveLength(1);
    expect(result.staleReferences[0]).toEqual({
      sourcePath: 'docs/guide.md',
      oldDocId: 'PCE-SPEC-2025-0001-Z',
      newDocId: 'PCE-SPEC-2025-0001-Y',
      changedDocPath: 'docs/spec.md',
      kind: 'custom_pattern',
      lineNumber: 15,
      patternName: 'ref_tag',
    });
  });
});

describe('buildChangedDocIdsMap', () => {
  it('変更されたdoc_idのマップを構築する', () => {
    const baseDocIds = new Map([
      ['docs/spec.md', 'PCE-SPEC-2025-0001-Z'],
      ['docs/design.md', 'BACK-DES-2024-0001-A'],
    ]);

    const currentDocIds = new Map([
      ['docs/spec.md', 'PCE-SPEC-2025-0001-Y'], // 変更
      ['docs/design.md', 'BACK-DES-2024-0001-A'], // 変更なし
    ]);

    const result = buildChangedDocIdsMap(baseDocIds, currentDocIds);

    expect(result.size).toBe(1);
    expect(result.get('PCE-SPEC-2025-0001-Z')).toEqual({
      newDocId: 'PCE-SPEC-2025-0001-Y',
      changedDocPath: 'docs/spec.md',
    });
  });

  it('削除されたファイルは無視する', () => {
    const baseDocIds = new Map([
      ['docs/spec.md', 'PCE-SPEC-2025-0001-Z'],
      ['docs/deleted.md', 'PCE-SPEC-2025-0002-A'],
    ]);

    const currentDocIds = new Map([
      ['docs/spec.md', 'PCE-SPEC-2025-0001-Z'],
      // docs/deleted.md は現在のマップに存在しない
    ]);

    const result = buildChangedDocIdsMap(baseDocIds, currentDocIds);

    expect(result.size).toBe(0);
  });

  it('新規ファイルは変更として検出しない', () => {
    const baseDocIds = new Map([['docs/spec.md', 'PCE-SPEC-2025-0001-Z']]);

    const currentDocIds = new Map([
      ['docs/spec.md', 'PCE-SPEC-2025-0001-Z'],
      ['docs/new.md', 'PCE-SPEC-2025-0003-C'], // 新規
    ]);

    const result = buildChangedDocIdsMap(baseDocIds, currentDocIds);

    expect(result.size).toBe(0);
  });

  it('空のマップでは空の結果を返す', () => {
    const baseDocIds = new Map<string, string>();
    const currentDocIds = new Map<string, string>();

    const result = buildChangedDocIdsMap(baseDocIds, currentDocIds);

    expect(result.size).toBe(0);
  });
});

describe('excludeSelfReferences', () => {
  it('自己参照を除外する', () => {
    const staleReferences: StaleReference[] = [
      {
        sourcePath: 'docs/spec.md', // 同じパス
        oldDocId: 'PCE-SPEC-2025-0001-Z',
        newDocId: 'PCE-SPEC-2025-0001-Y',
        changedDocPath: 'docs/spec.md', // 同じパス
        kind: 'markdown_link',
      },
      {
        sourcePath: 'docs/guide.md', // 異なるパス
        oldDocId: 'PCE-SPEC-2025-0001-Z',
        newDocId: 'PCE-SPEC-2025-0001-Y',
        changedDocPath: 'docs/spec.md',
        kind: 'markdown_link',
      },
    ];

    const result = excludeSelfReferences(staleReferences);

    expect(result).toHaveLength(1);
    expect(result[0]?.sourcePath).toBe('docs/guide.md');
  });

  it('自己参照がない場合はすべて保持する', () => {
    const staleReferences: StaleReference[] = [
      {
        sourcePath: 'docs/guide.md',
        oldDocId: 'PCE-SPEC-2025-0001-Z',
        newDocId: 'PCE-SPEC-2025-0001-Y',
        changedDocPath: 'docs/spec.md',
        kind: 'markdown_link',
      },
      {
        sourcePath: 'docs/another.md',
        oldDocId: 'PCE-SPEC-2025-0001-Z',
        newDocId: 'PCE-SPEC-2025-0001-Y',
        changedDocPath: 'docs/spec.md',
        kind: 'yaml_field',
      },
    ];

    const result = excludeSelfReferences(staleReferences);

    expect(result).toHaveLength(2);
  });

  it('空配列では空配列を返す', () => {
    const result = excludeSelfReferences([]);

    expect(result).toHaveLength(0);
  });
});
