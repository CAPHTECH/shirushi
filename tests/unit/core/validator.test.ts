/**
 * Validator Unit Tests
 *
 * doc_id検証機能のテスト。
 */

import { isLeft } from 'fp-ts/Either';
import { describe, it, expect } from 'vitest';

import {
  validateDocId,
  isValidIdFormat,
  validateDocuments,
  summarizeResults,
  buildIdPattern,
} from '@/core/validator';

import type { ShirushiConfig } from '@/config/schema';

// テスト用の設定ファクトリ
function createTestConfig(
  overrides: Partial<ShirushiConfig> = {}
): ShirushiConfig {
  return {
    id_format: '{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}',
    doc_globs: ['docs/**/*.md'],
    dimensions: {
      COMP: { type: 'enum', values: ['PCE', 'KKS', 'EDGE'] },
      KIND: {
        type: 'enum_from_doc_type',
        mapping: { spec: 'SPEC', design: 'DES', memo: 'MEMO' },
      },
      YEAR4: { type: 'year', digits: 4, source: 'created_at' },
      SER4: { type: 'serial', digits: 4, scope: ['COMP', 'KIND', 'YEAR4'] },
      CHK1: {
        type: 'checksum',
        algo: 'mod26AZ',
        of: ['COMP', 'KIND', 'YEAR4', 'SER4'],
      },
    },
    index_file: 'docs/doc_index.yaml',
    forbid_id_change: true,
    allow_missing_id_in_new_files: false,
    ...overrides,
  };
}

describe('validateDocId', () => {
  describe('正常系: 有効なID', () => {
    it('全てのdimensionが有効なIDを検証成功する', () => {
      const config = createTestConfig();
      const result = validateDocId(
        {
          docId: 'PCE-SPEC-2025-0001-Z',
          documentPath: 'docs/pce/spec.md',
          documentMeta: { doc_type: 'spec', created_at: '2025-01-01' },
        },
        config
      );

      expect(result.valid).toBe(true);
      expect(result.errors).toHaveLength(0);
      expect(result.parsedParts).toEqual({
        COMP: 'PCE',
        KIND: 'SPEC',
        YEAR4: '2025',
        SER4: '0001',
        CHK1: 'Z',
      });
    });

    it('異なる有効な値の組み合わせを検証成功する', () => {
      const config = createTestConfig();
      // 手計算: "KKSDES20240123" のchecksum
      // K(75)+K(75)+S(83)+D(68)+E(69)+S(83)+2(50)+0(48)+2(50)+4(52)+0(48)+1(49)+2(50)+3(51) = 851
      // 851 mod 26 = 19 → T (65+19=84)
      const result = validateDocId(
        {
          docId: 'KKS-DES-2024-0123-T',
          documentPath: 'docs/kakusill/design.md',
          documentMeta: { doc_type: 'design', created_at: '2024-06-15' },
        },
        config
      );

      expect(result.valid).toBe(true);
    });
  });

  describe('異常系: 無効なID形式', () => {
    it('パターンにマッチしないIDを検証失敗する', () => {
      const config = createTestConfig();
      const result = validateDocId(
        {
          docId: 'INVALID-ID',
          documentPath: 'docs/test.md',
          documentMeta: {},
        },
        config
      );

      expect(result.valid).toBe(false);
      expect(result.errors).toHaveLength(1);
      expect(result.errors[0]?.code).toBe('MALFORMED_ID');
    });

    it('空のIDを検証失敗する', () => {
      const config = createTestConfig();
      const result = validateDocId(
        {
          docId: '',
          documentPath: 'docs/test.md',
          documentMeta: {},
        },
        config
      );

      expect(result.valid).toBe(false);
    });
  });

  describe('異常系: dimension検証エラー', () => {
    it('enum値が不正な場合エラーを返す', () => {
      const config = createTestConfig();
      const result = validateDocId(
        {
          docId: 'XXX-SPEC-2025-0001-Z', // XXXは無効
          documentPath: 'docs/test.md',
          documentMeta: { doc_type: 'spec' },
        },
        config
      );

      expect(result.valid).toBe(false);
    });

    it('doc_typeがない場合エラーを返す', () => {
      const config = createTestConfig();
      const result = validateDocId(
        {
          docId: 'PCE-SPEC-2025-0001-Z',
          documentPath: 'docs/test.md',
          documentMeta: {}, // doc_typeなし
        },
        config
      );

      expect(result.valid).toBe(false);
      expect(
        result.errors.some((e) => e.code === 'MISSING_DOC_TYPE')
      ).toBe(true);
    });

    it('checksumが不正な場合エラーを返す', () => {
      const config = createTestConfig();
      const result = validateDocId(
        {
          docId: 'PCE-SPEC-2025-0001-A', // Aは不正（正しくはZ）
          documentPath: 'docs/test.md',
          documentMeta: { doc_type: 'spec' },
        },
        config
      );

      expect(result.valid).toBe(false);
      expect(
        result.errors.some((e) => e.code === 'INVALID_ID_CHECKSUM')
      ).toBe(true);
    });
  });
});

describe('isValidIdFormat', () => {
  it('有効なID形式を判定する', () => {
    const config = createTestConfig();
    expect(isValidIdFormat('PCE-SPEC-2025-0001-Z', config)).toBe(true);
    expect(isValidIdFormat('INVALID', config)).toBe(false);
  });
});

describe('buildIdPattern', () => {
  it('設定から正規表現パターンを生成する', () => {
    const config = createTestConfig();
    const result = buildIdPattern(config);

    expect(isLeft(result)).toBe(false);
    if (!isLeft(result)) {
      expect(result.right.test('PCE-SPEC-2025-0001-Z')).toBe(true);
      expect(result.right.test('INVALID')).toBe(false);
    }
  });
});

describe('validateDocuments', () => {
  it('複数ドキュメントを一括検証する', () => {
    const config = createTestConfig();
    const inputs = [
      {
        docId: 'PCE-SPEC-2025-0001-Z',
        documentPath: 'docs/pce/spec1.md',
        documentMeta: { doc_type: 'spec' },
      },
      {
        docId: 'KKS-DES-2024-0123-T',
        documentPath: 'docs/kakusill/design.md',
        documentMeta: { doc_type: 'design' },
      },
      {
        docId: 'INVALID',
        documentPath: 'docs/invalid.md',
        documentMeta: {},
      },
    ];

    const results = validateDocuments(inputs, config);

    expect(results.size).toBe(3);
    expect(results.get('docs/pce/spec1.md')?.valid).toBe(true);
    expect(results.get('docs/kakusill/design.md')?.valid).toBe(true);
    expect(results.get('docs/invalid.md')?.valid).toBe(false);
  });
});

describe('summarizeResults', () => {
  it('検証結果を集計する', () => {
    const config = createTestConfig();
    const inputs = [
      {
        docId: 'PCE-SPEC-2025-0001-Z',
        documentPath: 'docs/pce/spec1.md',
        documentMeta: { doc_type: 'spec' },
      },
      {
        docId: 'INVALID',
        documentPath: 'docs/invalid.md',
        documentMeta: {},
      },
    ];

    const results = validateDocuments(inputs, config);
    const summary = summarizeResults(results);

    expect(summary.total).toBe(2);
    expect(summary.valid).toBe(1);
    expect(summary.invalid).toBe(1);
    expect(summary.errorsByPath.has('docs/invalid.md')).toBe(true);
  });
});

describe('シンプルな設定', () => {
  it('enum + yearのみの設定で検証できる', () => {
    const config: ShirushiConfig = {
      id_format: '{COMP}-{YEAR4}',
      doc_globs: ['docs/**/*.md'],
      dimensions: {
        COMP: { type: 'enum', values: ['DOC'] },
        YEAR4: { type: 'year', digits: 4, source: 'now' },
      },
      index_file: 'docs/doc_index.yaml',
      forbid_id_change: true,
      allow_missing_id_in_new_files: false,
    };

    const result = validateDocId(
      {
        docId: 'DOC-2025',
        documentPath: 'docs/test.md',
        documentMeta: {},
      },
      config
    );

    expect(result.valid).toBe(true);
  });
});
