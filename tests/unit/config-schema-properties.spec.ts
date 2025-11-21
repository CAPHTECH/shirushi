/**
 * Property-based tests for config/schema.ts
 *
 * Tests the mathematical properties of extractTemplatePlaceholders()
 * using fast-check for generative testing.
 */

import * as fc from 'fast-check';
import { describe, expect, it } from 'vitest';

import { extractTemplatePlaceholders } from '@/config/schema.js';

describe('config/schema - Property-Based Tests', () => {
  describe('extractTemplatePlaceholders', () => {
    // Arbitrary: Valid placeholder names (alphanumeric + underscore)
    const placeholderNameArb = fc.stringMatching(/^[A-Za-z0-9_]{1,20}$/);

    /**
     * Property 1: No Duplicates
     * ∀ template: 結果配列に重複要素は含まれない
     */
    it('property: result contains no duplicates', () => {
      fc.assert(
        fc.property(fc.string(), (template) => {
          const result = extractTemplatePlaceholders(template);
          const uniqueResult = [...new Set(result)];
          expect(result).toEqual(uniqueResult);
        })
      );
    });

    /**
     * Property 2: Determinism (Pure Function)
     * ∀ template: 同じ入力は常に同じ出力を生成する
     */
    it('property: deterministic output for same input', () => {
      fc.assert(
        fc.property(fc.string(), (template) => {
          const result1 = extractTemplatePlaceholders(template);
          const result2 = extractTemplatePlaceholders(template);
          expect(result1).toEqual(result2);
        })
      );
    });

    /**
     * Property 3: Order Preservation
     * ∀ template: プレースホルダーの出現順序が保持される
     */
    it('property: preserves order of first occurrence', () => {
      fc.assert(
        fc.property(
          fc.tuple(placeholderNameArb, placeholderNameArb, placeholderNameArb)
            .filter(([a, b, c]) => a !== b && b !== c && a !== c),
          ([name1, name2, name3]) => {
            const template = `{${name1}}-{${name2}}-{${name3}}`;
            const result = extractTemplatePlaceholders(template);

            // 最初の出現順序が保持されることを検証
            const idx1 = result.indexOf(name1);
            const idx2 = result.indexOf(name2);
            const idx3 = result.indexOf(name3);

            expect(idx1).toBeLessThan(idx2);
            expect(idx2).toBeLessThan(idx3);
          }
        )
      );
    });

    /**
     * Property 4: Completeness
     * ∀ valid placeholder: すべてのプレースホルダーが抽出される
     */
    it('property: extracts all valid placeholders', () => {
      fc.assert(
        fc.property(
          fc.array(placeholderNameArb, { minLength: 1, maxLength: 5 }),
          (names) => {
            const uniqueNames = [...new Set(names)];
            const template = uniqueNames.map((n) => `{${n}}`).join('-');
            const result = extractTemplatePlaceholders(template);

            expect(result).toEqual(uniqueNames);
          }
        )
      );
    });

    /**
     * Property 5: Empty Input
     * 空文字列またはプレースホルダーがない場合は空配列
     */
    it('property: returns empty array for no placeholders', () => {
      fc.assert(
        fc.property(
          fc.stringMatching(/^[^{}]*$/), // No braces
          (template) => {
            const result = extractTemplatePlaceholders(template);
            expect(result).toEqual([]);
          }
        )
      );
    });

    /**
     * Property 6: Ignores Duplicates
     * 同じプレースホルダーが複数回出現しても、結果には1回のみ含まれる
     */
    it('property: deduplicates repeated placeholders', () => {
      fc.assert(
        fc.property(
          fc.tuple(placeholderNameArb, fc.integer({ min: 2, max: 5 })),
          ([name, count]) => {
            const template = Array(count).fill(`{${name}}`).join('-');
            const result = extractTemplatePlaceholders(template);

            expect(result).toEqual([name]);
            expect(result.length).toBe(1);
          }
        )
      );
    });

    /**
     * Property 7: Valid Format Only
     * 不正な形式は抽出されない
     * 注: 現在の実装では [A-Za-z0-9_]+ なので、数字で始まるのも有効
     */
    it('property: only extracts valid placeholder format', () => {
      const invalidTemplates = [
        '{invalid-name}',  // ハイフン含む
        '{invalid.name}',  // ドット含む
        '{}',  // 空
        '{  }',  // スペースのみ
        '{invalid name}', // スペース含む
      ];

      invalidTemplates.forEach((template) => {
        const result = extractTemplatePlaceholders(template);
        expect(result.length).toBe(0);
      });

      // 数字で始まるのは有効（現在の仕様）
      const validWithDigit = '{1VALID}';
      const result = extractTemplatePlaceholders(validWithDigit);
      expect(result).toEqual(['1VALID']);
    });

    /**
     * Property 8: Length Invariant
     * 結果の長さは、ユニークなプレースホルダー数以下
     */
    it('property: result length <= unique placeholders in input', () => {
      fc.assert(
        fc.property(fc.string(), (template) => {
          const result = extractTemplatePlaceholders(template);
          const placeholderMatches = template.match(/\{([A-Za-z0-9_]+)\}/g) ?? [];

          expect(result.length).toBeLessThanOrEqual(placeholderMatches.length);
        })
      );
    });
  });
});
