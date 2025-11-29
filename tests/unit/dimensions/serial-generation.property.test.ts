/**
 * Serial Number Generation - Property-Based Tests
 *
 * TLA+仕様の不変条件をfast-checkでテストする。
 * オラクル実装と比較して実装の正確性を検証する。
 */

import * as fc from 'fast-check';
import { isRight, isLeft } from 'fp-ts/Either';
import { describe, it, expect } from 'vitest';

import { SerialHandler } from '@/dimensions/handlers/serial';
import { parseTemplate } from '@/parsers/template';

import {
  oracleNextSerial,
  extractSerialsInScope,
  buildScopeKeyOracle,
} from './serial-oracle';

import type { IndexEntry } from '@/core/index-manager';
import type { GenerationContext } from '@/dimensions/handlers/base';
import type { TemplateParseResult } from '@/parsers/template';

// テスト用の固定dimension定義
const testDimensions = {
  COMP: { type: 'enum' as const, values: ['PCE', 'KKS'] },
  KIND: { type: 'enum' as const, values: ['SPEC', 'DES'] },
  YEAR4: { type: 'year' as const, digits: 4, source: 'current' as const },
  SER4: { type: 'serial' as const, digits: 4, scope: ['COMP', 'KIND', 'YEAR4'] },
  CHK1: { type: 'checksum' as const, algo: 'mod26AZ' as const, of: ['COMP', 'KIND', 'YEAR4', 'SER4'] },
};

const testIdFormat = '{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}';

// テンプレート解析結果をキャッシュ
let cachedTemplateResult: TemplateParseResult | null = null;
function getTemplateResult(): TemplateParseResult {
  if (!cachedTemplateResult) {
    const result = parseTemplate(testIdFormat, testDimensions);
    if (isLeft(result)) {
      throw new Error('Failed to parse template');
    }
    cachedTemplateResult = result.right;
  }
  return cachedTemplateResult;
}

// Arbitrary generators
const compArb = fc.constantFrom('PCE', 'KKS');
const kindArb = fc.constantFrom('SPEC', 'DES');
const yearArb = fc.integer({ min: 2020, max: 2030 }).map(String);
const serialArb = fc.integer({ min: 1, max: 9999 });
const checksumArb = fc.constantFrom(...'ABCDEFGHIJKLMNOPQRSTUVWXYZ'.split(''));

// doc_id生成arbitrary（簡易版）
const docIdArb = fc
  .tuple(compArb, kindArb, yearArb, serialArb, checksumArb)
  .map(([comp, kind, year, serial, chk]) => {
    const serialStr = String(serial).padStart(4, '0');
    return `${comp}-${kind}-${year}-${serialStr}-${chk}`;
  });

// IndexEntry生成arbitrary
const indexEntryArb = docIdArb.map(
  (docId): IndexEntry => ({
    doc_id: docId,
    path: `docs/${docId.toLowerCase().replace(/-/g, '/')}.md`,
  })
);

// スコープを構成するotherParts生成arbitrary
const scopePartsArb = fc.tuple(compArb, kindArb, yearArb).map(([comp, kind, year]) => ({
  COMP: comp,
  KIND: kind,
  YEAR4: year,
}));

// GenerationContext生成arbitrary
function createTestContext(
  indexEntries: IndexEntry[],
  otherParts: Record<string, string>
): GenerationContext {
  return {
    documentPath: 'docs/test.md',
    documentMeta: {},
    otherParts,
    dimensionName: 'SER4',
    indexEntries,
    templateResult: getTemplateResult(),
  };
}

describe('SerialHandler.generate (Property-Based)', () => {
  const handler = new SerialHandler();
  const dimension = {
    type: 'serial' as const,
    digits: 4,
    scope: ['COMP', 'KIND', 'YEAR4'],
  };

  describe('TLA+ Invariant: Uniqueness', () => {
    it('生成値はスコープ内の既存値に含まれない', () => {
      fc.assert(
        fc.property(
          fc.array(indexEntryArb, { minLength: 0, maxLength: 10 }),
          scopePartsArb,
          (entries, otherParts) => {
            const context = createTestContext(entries, otherParts);
            const scopeKey = `${otherParts.COMP}-${otherParts.KIND}-${otherParts.YEAR4}`;

            // 既存のシリアル番号を取得
            const existingSerials = extractSerialsInScope(
              entries.map((e) => e.doc_id),
              getTemplateResult(),
              dimension.scope,
              scopeKey,
              'SER4'
            );

            const result = handler.generate(dimension, context);

            if (isRight(result)) {
              const generated = parseInt(result.right, 10);
              // 生成値が既存値に含まれないことを確認
              return !existingSerials.includes(generated);
            }
            // エラーの場合は別のテストで検証
            return true;
          }
        ),
        { numRuns: 100 }
      );
    });
  });

  describe('TLA+ Invariant: Monotonicity', () => {
    it('生成値 > max(既存値)', () => {
      fc.assert(
        fc.property(
          fc.array(indexEntryArb, { minLength: 0, maxLength: 10 }),
          scopePartsArb,
          (entries, otherParts) => {
            const context = createTestContext(entries, otherParts);
            const scopeKey = `${otherParts.COMP}-${otherParts.KIND}-${otherParts.YEAR4}`;

            // 既存のシリアル番号を取得
            const existingSerials = extractSerialsInScope(
              entries.map((e) => e.doc_id),
              getTemplateResult(),
              dimension.scope,
              scopeKey,
              'SER4'
            );
            const maxExisting = existingSerials.length > 0 ? Math.max(...existingSerials) : 0;

            const result = handler.generate(dimension, context);

            if (isRight(result)) {
              const generated = parseInt(result.right, 10);
              // 生成値が最大値より大きいことを確認
              return generated > maxExisting;
            }
            return true;
          }
        ),
        { numRuns: 100 }
      );
    });
  });

  describe('TLA+ Invariant: NoOverflow', () => {
    it('オーバーフロー時はエラーを返す', () => {
      // 9999まで埋まったインデックスを作成
      const maxSerialEntries: IndexEntry[] = [
        { doc_id: 'PCE-SPEC-2025-9999-A', path: 'docs/max.md' },
      ];

      const context = createTestContext(maxSerialEntries, {
        COMP: 'PCE',
        KIND: 'SPEC',
        YEAR4: '2025',
      });

      const result = handler.generate(dimension, context);

      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('SERIAL_OVERFLOW');
      }
    });

    it('境界値（9998）では成功する', () => {
      const almostMaxEntries: IndexEntry[] = [
        { doc_id: 'PCE-SPEC-2025-9998-A', path: 'docs/almostmax.md' },
      ];

      const context = createTestContext(almostMaxEntries, {
        COMP: 'PCE',
        KIND: 'SPEC',
        YEAR4: '2025',
      });

      const result = handler.generate(dimension, context);

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right).toBe('9999');
      }
    });
  });

  describe('TLA+ Invariant: ScopeFiltering', () => {
    it('異なるスコープのエントリは結果に影響しない', () => {
      fc.assert(
        fc.property(
          fc.array(indexEntryArb, { minLength: 1, maxLength: 10 }),
          scopePartsArb,
          (entries, targetParts) => {
            // 対象スコープのエントリのみをフィルタ
            // Note: スコープキーはドキュメント目的で保持（実際のフィルタリングは個別比較で実施）
            const _targetScopeKey = `${targetParts.COMP}-${targetParts.KIND}-${targetParts.YEAR4}`;
            void _targetScopeKey; // unused-vars回避
            const relevantEntries = entries.filter((e) => {
              const values = e.doc_id.split('-');
              return values[0] === targetParts.COMP &&
                     values[1] === targetParts.KIND &&
                     values[2] === targetParts.YEAR4;
            });

            // 全エントリでのコンテキスト
            const fullContext = createTestContext(entries, targetParts);
            // 関連エントリのみでのコンテキスト
            const relevantContext = createTestContext(relevantEntries, targetParts);

            const fullResult = handler.generate(dimension, fullContext);
            const relevantResult = handler.generate(dimension, relevantContext);

            // 両方成功した場合、結果は同じであるべき
            if (isRight(fullResult) && isRight(relevantResult)) {
              return fullResult.right === relevantResult.right;
            }
            // 両方エラーの場合も同様
            if (isLeft(fullResult) && isLeft(relevantResult)) {
              return fullResult.left.code === relevantResult.left.code;
            }
            // 一方のみ成功/失敗は不一致
            return false;
          }
        ),
        { numRuns: 50 }
      );
    });
  });

  describe('Oracle Comparison', () => {
    it('実装がオラクルと一致する', () => {
      fc.assert(
        fc.property(
          fc.array(indexEntryArb, { minLength: 0, maxLength: 10 }),
          scopePartsArb,
          (entries, otherParts) => {
            const context = createTestContext(entries, otherParts);

            // スコープキーを構築
            const scopeKeyResult = buildScopeKeyOracle(dimension.scope, otherParts);
            if (isLeft(scopeKeyResult)) {
              // スコープキー構築失敗はテスト対象外
              return true;
            }
            const scopeKey = scopeKeyResult.right;

            // オラクルで期待値を計算
            const expected = oracleNextSerial(
              scopeKey,
              entries.map((e) => e.doc_id),
              getTemplateResult(),
              dimension.scope,
              'SER4',
              dimension.digits
            );

            // 実装で実際の値を計算
            const actual = handler.generate(dimension, context);

            // 比較
            if (isRight(expected)) {
              if (!isRight(actual)) return false;
              return parseInt(actual.right, 10) === expected.right;
            } else {
              // オラクルがオーバーフローなら実装もオーバーフロー
              return isLeft(actual) && actual.left.code === 'SERIAL_OVERFLOW';
            }
          }
        ),
        { numRuns: 100 }
      );
    });
  });
});

describe('Edge Cases', () => {
  const handler = new SerialHandler();
  const dimension = {
    type: 'serial' as const,
    digits: 4,
    scope: ['COMP', 'KIND', 'YEAR4'],
  };

  it('ギャップがある場合も正しくmax+1を返す（ADR-0006）', () => {
    // 1, 5, 100 という飛び番のインデックス
    const gappedEntries: IndexEntry[] = [
      { doc_id: 'PCE-SPEC-2025-0001-A', path: 'docs/1.md' },
      { doc_id: 'PCE-SPEC-2025-0005-A', path: 'docs/5.md' },
      { doc_id: 'PCE-SPEC-2025-0100-A', path: 'docs/100.md' },
    ];

    const context: GenerationContext = {
      documentPath: 'docs/test.md',
      documentMeta: {},
      otherParts: { COMP: 'PCE', KIND: 'SPEC', YEAR4: '2025' },
      dimensionName: 'SER4',
      indexEntries: gappedEntries,
      templateResult: getTemplateResult(),
    };

    const result = handler.generate(dimension, context);

    expect(isRight(result)).toBe(true);
    if (isRight(result)) {
      // 最大値100の次、101を返すべき
      expect(result.right).toBe('0101');
    }
  });

  it('パースできないdoc_idは無視される', () => {
    const mixedEntries: IndexEntry[] = [
      { doc_id: 'PCE-SPEC-2025-0001-A', path: 'docs/valid.md' },
      { doc_id: 'INVALID-FORMAT', path: 'docs/invalid.md' },
      { doc_id: 'PCE-SPEC-2025-0002-B', path: 'docs/valid2.md' },
    ];

    const context: GenerationContext = {
      documentPath: 'docs/test.md',
      documentMeta: {},
      otherParts: { COMP: 'PCE', KIND: 'SPEC', YEAR4: '2025' },
      dimensionName: 'SER4',
      indexEntries: mixedEntries,
      templateResult: getTemplateResult(),
    };

    const result = handler.generate(dimension, context);

    expect(isRight(result)).toBe(true);
    if (isRight(result)) {
      // 有効なエントリ(1, 2)の最大値2の次、3を返すべき
      expect(result.right).toBe('0003');
    }
  });
});
