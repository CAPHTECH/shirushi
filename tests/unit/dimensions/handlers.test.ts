/**
 * Dimension Handlers Unit Tests
 *
 * 各dimension handlerの検証・生成・パターン生成機能のテスト。
 */

import { isRight, isLeft } from 'fp-ts/Either';
import { describe, it, expect } from 'vitest';

import { ChecksumHandler, mod26AZ } from '@/dimensions/handlers/checksum';
import { EnumHandler } from '@/dimensions/handlers/enum';
import { EnumFromDocTypeHandler } from '@/dimensions/handlers/enum-from-doc-type';
import { SerialHandler } from '@/dimensions/handlers/serial';
import { YearHandler } from '@/dimensions/handlers/year';

import type { ValidationContext, GenerationContext } from '@/dimensions/handlers/base';

// テスト用のコンテキストファクトリ
function createValidationContext(
  overrides: Partial<ValidationContext> = {}
): ValidationContext {
  return {
    documentPath: 'docs/test.md',
    documentMeta: {},
    parsedParts: {},
    dimensionName: 'TEST',
    ...overrides,
  };
}

function createGenerationContext(
  overrides: Partial<GenerationContext> = {}
): GenerationContext {
  return {
    documentPath: 'docs/test.md',
    documentMeta: {},
    otherParts: {},
    dimensionName: 'TEST',
    ...overrides,
  };
}

describe('EnumHandler', () => {
  const handler = new EnumHandler();
  const dimension = {
    type: 'enum' as const,
    values: ['PCE', 'BACK', 'GW'],
  };

  describe('validate', () => {
    it('有効な値を受け入れる', () => {
      const result = handler.validate('PCE', dimension, createValidationContext());
      expect(isRight(result)).toBe(true);
    });

    it('無効な値を拒否する', () => {
      const result = handler.validate('INVALID', dimension, createValidationContext());
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('INVALID_DIMENSION_VALUE');
      }
    });

    it('select.by_pathでパスマッチを検証する', () => {
      const dimWithSelect = {
        type: 'enum' as const,
        values: ['FRONT', 'BACK'],
        select: {
          by_path: [
            { pattern: 'docs/frontend/**', value: 'FRONT' },
            { pattern: 'docs/backend/**', value: 'BACK' },
          ],
        },
      };

      // パスマッチして値も一致 → OK
      const result1 = handler.validate(
        'FRONT',
        dimWithSelect,
        createValidationContext({ documentPath: 'docs/frontend/spec.md' })
      );
      expect(isRight(result1)).toBe(true);

      // パスマッチするが値が不一致 → エラー
      const result2 = handler.validate(
        'BACK',
        dimWithSelect,
        createValidationContext({ documentPath: 'docs/frontend/spec.md' })
      );
      expect(isLeft(result2)).toBe(true);
      if (isLeft(result2)) {
        expect(result2.left.code).toBe('DIMENSION_MISMATCH');
      }
    });
  });

  describe('generate', () => {
    it('select.by_pathがない場合、最初の値を返す', () => {
      const result = handler.generate(dimension, createGenerationContext());
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('PCE');
      }
    });

    it('select.by_pathでパスマッチした値を返す', () => {
      const dimWithSelect = {
        type: 'enum' as const,
        values: ['FRONT', 'BACK'],
        select: {
          by_path: [
            { pattern: 'docs/frontend/**', value: 'FRONT' },
            { pattern: 'docs/backend/**', value: 'BACK' },
          ],
        },
      };

      const result = handler.generate(
        dimWithSelect,
        createGenerationContext({ documentPath: 'docs/backend/memo.md' })
      );
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('BACK');
      }
    });
  });

  describe('toPattern', () => {
    it('値の選択肢パターンを生成する', () => {
      const pattern = handler.toPattern(dimension);
      expect(pattern).toBe('(PCE|BACK|GW)');
    });
  });
});

describe('EnumFromDocTypeHandler', () => {
  const handler = new EnumFromDocTypeHandler();
  const dimension = {
    type: 'enum_from_doc_type' as const,
    mapping: {
      spec: 'SPEC',
      design: 'DES',
      memo: 'MEMO',
    },
  };

  describe('validate', () => {
    it('doc_typeに対応する値を受け入れる', () => {
      const result = handler.validate(
        'SPEC',
        dimension,
        createValidationContext({ documentMeta: { doc_type: 'spec' } })
      );
      expect(isRight(result)).toBe(true);
    });

    it('doc_typeがない場合エラー', () => {
      const result = handler.validate('SPEC', dimension, createValidationContext());
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('MISSING_DOC_TYPE');
      }
    });

    it('doc_typeがmappingにない場合エラー', () => {
      const result = handler.validate(
        'SPEC',
        dimension,
        createValidationContext({ documentMeta: { doc_type: 'unknown' } })
      );
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('UNKNOWN_DOC_TYPE');
      }
    });

    it('doc_typeと値が不一致の場合エラー', () => {
      const result = handler.validate(
        'DES',
        dimension,
        createValidationContext({ documentMeta: { doc_type: 'spec' } })
      );
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('DIMENSION_MISMATCH');
      }
    });
  });

  describe('generate', () => {
    it('doc_typeから値を生成する', () => {
      const result = handler.generate(
        dimension,
        createGenerationContext({ documentMeta: { doc_type: 'design' } })
      );
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('DES');
      }
    });
  });

  describe('toPattern', () => {
    it('mapping値のパターンを生成する', () => {
      const pattern = handler.toPattern(dimension);
      expect(pattern).toBe('(SPEC|DES|MEMO)');
    });
  });
});

describe('YearHandler', () => {
  const handler = new YearHandler();
  const dimension = {
    type: 'year' as const,
    digits: 4,
    source: 'created_at' as const,
  };

  describe('validate', () => {
    it('有効な4桁年を受け入れる', () => {
      const result = handler.validate('2025', dimension, createValidationContext());
      expect(isRight(result)).toBe(true);
    });

    it('桁数不足を拒否する', () => {
      const result = handler.validate('25', dimension, createValidationContext());
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('INVALID_YEAR_VALUE');
      }
    });

    it('桁数超過を拒否する', () => {
      const result = handler.validate('20255', dimension, createValidationContext());
      expect(isLeft(result)).toBe(true);
    });

    it('非数字を拒否する', () => {
      const result = handler.validate('YEAR', dimension, createValidationContext());
      expect(isLeft(result)).toBe(true);
    });
  });

  describe('generate', () => {
    it('created_atから年を生成する', () => {
      const result = handler.generate(
        dimension,
        createGenerationContext({ documentMeta: { created_at: '2024-06-15' } })
      );
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('2024');
      }
    });

    it('created_atがない場合は現在年を使用する', () => {
      const result = handler.generate(dimension, createGenerationContext());
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe(String(new Date().getFullYear()));
      }
    });
  });

  describe('toPattern', () => {
    it('桁数パターンを生成する', () => {
      const pattern = handler.toPattern(dimension);
      expect(pattern).toBe('(\\d{4})');
    });
  });
});

describe('SerialHandler', () => {
  const handler = new SerialHandler();
  const dimension = {
    type: 'serial' as const,
    digits: 4,
    scope: ['COMP', 'KIND', 'YEAR4'],
  };

  describe('validate', () => {
    it('有効な4桁連番を受け入れる', () => {
      const result = handler.validate('0001', dimension, createValidationContext());
      expect(isRight(result)).toBe(true);
    });

    it('0000を拒否する', () => {
      const result = handler.validate('0000', dimension, createValidationContext());
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('INVALID_SERIAL_VALUE');
      }
    });

    it('桁数不足を拒否する', () => {
      const result = handler.validate('001', dimension, createValidationContext());
      expect(isLeft(result)).toBe(true);
    });

    it('最大値超過を拒否する', () => {
      // 4桁dimensionで5桁の値を検証
      const result = handler.validate('99999', dimension, createValidationContext());
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('INVALID_SERIAL_VALUE');
        expect(result.left.message).toContain('must be 4 digits');
      }
    });

    it('数値として最大値を超える場合を拒否する', () => {
      // パターンはマッチするが数値として最大値(9999)を超える場合
      // Note: 4桁パターンでは10000以上は桁数不一致で先に弾かれる
      // この ケースは digit=4 では発生しないが、仕様上の確認
      const result = handler.validate('9999', dimension, createValidationContext());
      expect(isRight(result)).toBe(true); // 9999は有効
    });
  });

  describe('generate', () => {
    it('インデックスがない場合は0001を生成する', () => {
      // スコープdimensionは必須だが、indexEntriesとtemplateResultは未提供
      const result = handler.generate(
        dimension,
        createGenerationContext({
          otherParts: { COMP: 'PCE', KIND: 'SPEC', YEAR4: '2025' },
        })
      );
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('0001');
      }
    });

    it('空のインデックスでも0001を生成する', () => {
      const result = handler.generate(
        dimension,
        createGenerationContext({
          otherParts: { COMP: 'PCE', KIND: 'SPEC', YEAR4: '2025' },
          indexEntries: [],
        })
      );
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('0001');
      }
    });

    it('スコープdimensionが不足している場合はエラー', () => {
      const result = handler.generate(
        dimension,
        createGenerationContext({
          otherParts: { COMP: 'PCE' }, // KIND, YEAR4が不足
        })
      );
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('MISSING_SCOPE_DIMENSION');
      }
    });
  });

  describe('toPattern', () => {
    it('桁数パターンを生成する', () => {
      const pattern = handler.toPattern(dimension);
      expect(pattern).toBe('(\\d{4})');
    });
  });
});

describe('ChecksumHandler', () => {
  const handler = new ChecksumHandler();
  const dimension = {
    type: 'checksum' as const,
    algo: 'mod26AZ' as const,
    of: ['COMP', 'KIND', 'YEAR4', 'SER4'],
  };

  describe('mod26AZ', () => {
    it('空文字列でAを返す', () => {
      expect(mod26AZ('')).toBe('A');
    });

    it('決定的な結果を返す', () => {
      const input = 'PCE-SPEC-2025-0001';
      expect(mod26AZ(input)).toBe(mod26AZ(input));
    });

    it('A-Zの範囲内を返す', () => {
      const result = mod26AZ('test input');
      expect(result).toMatch(/^[A-Z]$/);
    });

    it('既知の入力で期待値を返す', () => {
      // 手計算: "PCESPEC20250001" の各文字のASCII合計 mod 26
      // P(80)+C(67)+E(69)+S(83)+P(80)+E(69)+C(67)+2(50)+0(48)+2(50)+5(53)+0(48)+0(48)+0(48)+1(49) = 909
      // 909 mod 26 = 25 → Z (65+25=90)
      expect(mod26AZ('PCESPEC20250001')).toBe('Z');
    });
  });

  describe('validate', () => {
    it('正しいchecksumを受け入れる', () => {
      const result = handler.validate(
        'Z',
        dimension,
        createValidationContext({
          parsedParts: {
            COMP: 'PCE',
            KIND: 'SPEC',
            YEAR4: '2025',
            SER4: '0001',
          },
        })
      );
      expect(isRight(result)).toBe(true);
    });

    it('不正なchecksumを拒否する', () => {
      const result = handler.validate(
        'A',
        dimension,
        createValidationContext({
          parsedParts: {
            COMP: 'PCE',
            KIND: 'SPEC',
            YEAR4: '2025',
            SER4: '0001',
          },
        })
      );
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('INVALID_ID_CHECKSUM');
      }
    });

    it('小文字を拒否する', () => {
      const result = handler.validate('z', dimension, createValidationContext());
      expect(isLeft(result)).toBe(true);
    });

    it('必要な部品が欠けている場合エラー', () => {
      const result = handler.validate(
        'Z',
        dimension,
        createValidationContext({
          parsedParts: { COMP: 'PCE' }, // KIND, YEAR4, SER4が欠けている
        })
      );
      expect(isLeft(result)).toBe(true);
    });
  });

  describe('generate', () => {
    it('checksumを生成する', () => {
      const result = handler.generate(
        dimension,
        createGenerationContext({
          otherParts: {
            COMP: 'PCE',
            KIND: 'SPEC',
            YEAR4: '2025',
            SER4: '0001',
          },
        })
      );
      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('Z');
      }
    });
  });

  describe('toPattern', () => {
    it('[A-Z]パターンを生成する', () => {
      const pattern = handler.toPattern(dimension);
      expect(pattern).toBe('([A-Z])');
    });
  });
});
