/**
 * Property-based tests for branded types (LDE Standard Track)
 *
 * Tests the validation invariants and type safety of branded types
 * using fast-check for generative testing.
 *
 * LDE Phase 3: Property-based Testing
 * - 法則を「性質」としてテスト記述
 */

import * as fc from 'fast-check';
import { isLeft, isRight } from 'fp-ts/Either';
import { describe, expect, it } from 'vitest';

import {
  asAbsoluteFilePath,
  asDimensionName,
  asDocumentId,
  asPlaceholderName,
  asTemplateString,
  isAbsoluteFilePath,
  isDocumentId,
  isPlaceholderName,
  isTemplateString,
  LawViolationError,
} from '@/types/branded.js';

describe('branded types - Property-Based Tests (LDE)', () => {
  describe('TemplateString', () => {
    // Arbitrary: Valid placeholder name
    const placeholderNameArb = fc.stringMatching(/^[A-Za-z0-9_]{1,20}$/);

    // Arbitrary: Valid template string
    const validTemplateArb = fc
      .array(placeholderNameArb, { minLength: 1, maxLength: 5 })
      .map((names) => names.map((n) => `{${n}}`).join('-'));

    /**
     * Property: All valid templates should return Right
     * 法則: 有効なテンプレートは常に Right を返す
     */
    it('property: accepts all valid template strings (returns Right)', () => {
      fc.assert(
        fc.property(validTemplateArb, (template) => {
          const result = asTemplateString(template);
          expect(isRight(result)).toBe(true);
          expect(isTemplateString(template)).toBe(true);
        })
      );
    });

    /**
     * Property: Templates without placeholders should return Left
     * 法則: プレースホルダーのないテンプレートは Left を返す
     */
    it('property: rejects strings without placeholders (returns Left)', () => {
      fc.assert(
        fc.property(fc.stringMatching(/^[^{}]*$/), (str) => {
          if (str.length > 0) {
            const result = asTemplateString(str);
            expect(isLeft(result)).toBe(true);
            expect(isTemplateString(str)).toBe(false);
          }
        })
      );
    });

    /**
     * Property: Templates with unclosed braces should return Left with specific error
     * 法則: 閉じていないブレースを持つテンプレートは Left を返す
     */
    it('property: rejects templates with unclosed braces (returns Left)', () => {
      const invalidTemplates = ['{VALID', 'VALID}', '{VALID}}}', '{{{VALID}'];

      invalidTemplates.forEach((template) => {
        const result = asTemplateString(template);
        expect(isLeft(result)).toBe(true);
        if (isLeft(result)) {
          expect(result.left).toBeInstanceOf(LawViolationError);
          expect(result.left.violation).toMatch(/unclosed braces/);
        }
        expect(isTemplateString(template)).toBe(false);
      });
    });

    /**
     * Property: Validation is deterministic
     * 法則: バリデーションは決定論的（同じ入力に対して同じ結果）
     */
    it('property: validation is deterministic', () => {
      fc.assert(
        fc.property(fc.string(), (str) => {
          const result1 = isTemplateString(str);
          const result2 = isTemplateString(str);
          expect(result1).toBe(result2);
        })
      );
    });
  });

  describe('DocumentId', () => {
    // Arbitrary: Valid non-empty string for document ID
    const validDocIdArb = fc.stringMatching(/^[A-Za-z0-9_-]{1,50}$/);

    /**
     * Property: All non-empty strings should return Right
     * 法則: 空でない文字列は Right を返す
     */
    it('property: accepts all non-empty strings (returns Right)', () => {
      fc.assert(
        fc.property(validDocIdArb, (docId) => {
          const result = asDocumentId(docId);
          expect(isRight(result)).toBe(true);
          expect(isDocumentId(docId)).toBe(true);
        })
      );
    });

    /**
     * Property: Empty strings should return Left
     * 法則: 空文字列は Left を返す
     */
    it('property: rejects empty strings (returns Left)', () => {
      const result = asDocumentId('');
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left).toBeInstanceOf(LawViolationError);
        expect(result.left.lawName).toBe('DocumentId');
      }
      expect(isDocumentId('')).toBe(false);
    });

    /**
     * Property: Validation is deterministic
     * 法則: バリデーションは決定論的
     */
    it('property: validation is deterministic', () => {
      fc.assert(
        fc.property(fc.string(), (str) => {
          const result1 = isDocumentId(str);
          const result2 = isDocumentId(str);
          expect(result1).toBe(result2);
        })
      );
    });

    /**
     * Property: Right values preserve input string
     * 法則: Right の値は入力文字列を保持する
     */
    it('property: Right values contain the input string', () => {
      fc.assert(
        fc.property(validDocIdArb, (docId) => {
          const result = asDocumentId(docId);
          if (isRight(result)) {
            expect(result.right as string).toBe(docId);
          }
        })
      );
    });
  });

  describe('AbsoluteFilePath', () => {
    // Arbitrary: Valid path segment (excludes ".." which is traversal)
    // Pattern: starts with alphanumeric, may contain dots but not ".." as whole segment
    const validSegmentArb = fc
      .stringMatching(/^[a-zA-Z0-9][a-zA-Z0-9_.-]{0,19}$/)
      .filter((s) => s !== '..' && !s.startsWith('..') && !s.endsWith('..'));

    // Arbitrary: Valid Unix absolute path (without traversal)
    const validUnixPathArb = fc
      .array(validSegmentArb, { minLength: 1, maxLength: 5 })
      .map((segments) => `/${segments.join('/')}`);

    // Arbitrary: Valid Windows absolute path (without traversal)
    const validWindowsPathArb = fc
      .tuple(
        fc.constantFrom('C:', 'D:', 'E:'),
        fc.array(validSegmentArb, { minLength: 1, maxLength: 5 })
      )
      .map(([drive, segments]) => `${drive}\\${segments.join('\\')}`);


    /**
     * Property: Valid Unix absolute paths should return Right
     * 法則: 有効な Unix 絶対パスは Right を返す
     */
    it('property: accepts valid Unix absolute paths (returns Right)', () => {
      fc.assert(
        fc.property(validUnixPathArb, (path) => {
          const result = asAbsoluteFilePath(path);
          expect(isRight(result)).toBe(true);
          expect(isAbsoluteFilePath(path)).toBe(true);
        })
      );
    });

    /**
     * Property: Valid Windows absolute paths should return Right
     * 法則: 有効な Windows 絶対パスは Right を返す
     */
    it('property: accepts valid Windows absolute paths (returns Right)', () => {
      fc.assert(
        fc.property(validWindowsPathArb, (path) => {
          const result = asAbsoluteFilePath(path);
          expect(isRight(result)).toBe(true);
          expect(isAbsoluteFilePath(path)).toBe(true);
        })
      );
    });

    /**
     * Property: Relative paths should return Left
     * 法則: 相対パスは Left を返す
     */
    it('property: rejects relative paths (returns Left)', () => {
      const relativePaths = ['./file.txt', 'folder/file.txt', 'file.txt'];

      relativePaths.forEach((path) => {
        const result = asAbsoluteFilePath(path);
        expect(isLeft(result)).toBe(true);
        if (isLeft(result)) {
          expect(result.left).toBeInstanceOf(LawViolationError);
          expect(result.left.violation).toMatch(/absolute path/);
        }
        expect(isAbsoluteFilePath(path)).toBe(false);
      });
    });

    /**
     * Property: Directory traversal patterns should return Left
     * 法則: ディレクトリトラバーサルパターンは Left を返す
     */
    it('property: rejects directory traversal patterns (returns Left)', () => {
      const traversalPaths = [
        '/path/../etc/passwd',
        '/path/to/..', // ends with ..
        'C:\\path\\..\\etc',
        '/..', // starts with ..
      ];

      traversalPaths.forEach((path) => {
        const result = asAbsoluteFilePath(path);
        expect(isLeft(result)).toBe(true);
        if (isLeft(result)) {
          expect(result.left).toBeInstanceOf(LawViolationError);
          expect(result.left.violation).toMatch(/traversal/);
        }
        expect(isAbsoluteFilePath(path)).toBe(false);
      });
    });

    /**
     * Property: Paths with double dots in filenames should be allowed
     * 法則: ファイル名に連続ドットを含むパスは許可される
     */
    it('property: allows double dots in filenames (not traversal)', () => {
      const validPathsWithDoubleDots = [
        '/path/to/file..txt',
        '/path/to/file...name',
        'C:\\path\\file..txt',
      ];

      validPathsWithDoubleDots.forEach((path) => {
        const result = asAbsoluteFilePath(path);
        expect(isRight(result)).toBe(true);
        expect(isAbsoluteFilePath(path)).toBe(true);
      });
    });

    /**
     * Property: Empty strings should return Left
     * 法則: 空文字列は Left を返す
     */
    it('property: rejects empty strings (returns Left)', () => {
      const result = asAbsoluteFilePath('');
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left).toBeInstanceOf(LawViolationError);
      }
      expect(isAbsoluteFilePath('')).toBe(false);
    });

    /**
     * Property: Validation is deterministic
     * 法則: バリデーションは決定論的
     */
    it('property: validation is deterministic', () => {
      fc.assert(
        fc.property(fc.string(), (str) => {
          const result1 = isAbsoluteFilePath(str);
          const result2 = isAbsoluteFilePath(str);
          expect(result1).toBe(result2);
        })
      );
    });
  });

  describe('PlaceholderName', () => {
    // Arbitrary: Valid placeholder name
    const validNameArb = fc.stringMatching(/^[A-Za-z0-9_]{1,20}$/);

    /**
     * Property: All valid names should return Right
     * 法則: 有効なプレースホルダー名は Right を返す
     */
    it('property: accepts all valid placeholder names (returns Right)', () => {
      fc.assert(
        fc.property(validNameArb, (name) => {
          // Skip reserved names
          if (!['doc_type'].includes(name.toLowerCase())) {
            const result = asPlaceholderName(name);
            expect(isRight(result)).toBe(true);
            expect(isPlaceholderName(name)).toBe(true);
          }
        })
      );
    });

    /**
     * Property: Names with invalid characters should return Left
     * 法則: 無効な文字を含む名前は Left を返す
     */
    it('property: rejects names with invalid characters (returns Left)', () => {
      const invalidChars = ['-', '.', ' ', '/', '@', '!'];

      fc.assert(
        fc.property(
          fc.tuple(
            fc.stringMatching(/^[A-Za-z0-9_]{0,10}$/),
            fc.constantFrom(...invalidChars),
            fc.stringMatching(/^[A-Za-z0-9_]{0,10}$/)
          ),
          ([prefix, invalidChar, suffix]) => {
            const name = `${prefix}${invalidChar}${suffix}`;
            if (name.length > 0) {
              const result = asPlaceholderName(name);
              expect(isLeft(result)).toBe(true);
              expect(isPlaceholderName(name)).toBe(false);
            }
          }
        )
      );
    });

    /**
     * Property: Reserved names should return Left with 'reserved' message
     * 法則: 予約語は Left を返す
     */
    it('property: rejects reserved names (case-insensitive)', () => {
      const reserved = ['doc_type', 'DOC_TYPE', 'Doc_Type'];

      reserved.forEach((name) => {
        const result = asPlaceholderName(name);
        expect(isLeft(result)).toBe(true);
        if (isLeft(result)) {
          expect(result.left).toBeInstanceOf(LawViolationError);
          expect(result.left.violation).toMatch(/reserved/);
        }
        expect(isPlaceholderName(name)).toBe(false);
      });
    });

    /**
     * Property: Empty strings should return Left
     * 法則: 空文字列は Left を返す
     */
    it('property: rejects empty strings (returns Left)', () => {
      const result = asPlaceholderName('');
      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left).toBeInstanceOf(LawViolationError);
      }
      expect(isPlaceholderName('')).toBe(false);
    });
  });

  describe('DimensionName', () => {
    // Arbitrary: Valid dimension name (uppercase convention)
    const validDimensionArb = fc.stringMatching(/^[A-Z][A-Z0-9_]{0,19}$/);

    /**
     * Property: All valid dimension names should return Right
     * 法則: 有効な次元名は Right を返す
     */
    it('property: accepts all valid uppercase dimension names (returns Right)', () => {
      fc.assert(
        fc.property(validDimensionArb, (name) => {
          const result = asDimensionName(name);
          expect(isRight(result)).toBe(true);
        })
      );
    });

    /**
     * Property: Lowercase names should return Left
     * 法則: 小文字の次元名は Left を返す
     */
    it('property: rejects lowercase dimension names (returns Left)', () => {
      fc.assert(
        fc.property(fc.stringMatching(/^[a-z][a-z0-9_]{0,19}$/), (name) => {
          const result = asDimensionName(name);
          expect(isLeft(result)).toBe(true);
        })
      );
    });

    /**
     * Property: Names starting with digits should return Left
     * 法則: 数字で始まる名前は Left を返す
     */
    it('property: rejects names starting with digits (returns Left)', () => {
      fc.assert(
        fc.property(
          fc.tuple(
            fc.integer({ min: 0, max: 9 }),
            fc.stringMatching(/^[A-Z0-9_]{0,18}$/)
          ),
          ([digit, suffix]) => {
            const name = `${digit}${suffix}`;
            const result = asDimensionName(name);
            expect(isLeft(result)).toBe(true);
          }
        )
      );
    });
  });

  describe('Type Safety (LDE Phase 2)', () => {
    /**
     * Property: Type guards are conservative (no false positives)
     * 法則: 型ガードは Right を返す場合のみ true を返す
     */
    it('property: type guards have no false positives', () => {
      fc.assert(
        fc.property(fc.string(), (str) => {
          if (isTemplateString(str)) {
            const result = asTemplateString(str);
            expect(isRight(result)).toBe(true);
          }

          if (isPlaceholderName(str)) {
            const result = asPlaceholderName(str);
            expect(isRight(result)).toBe(true);
          }
        })
      );
    });

    /**
     * Property: Constructors always return Either (never crash)
     * 法則: コンストラクタは常に Either を返す（クラッシュしない）
     */
    it('property: constructors always return Either (never crash)', () => {
      fc.assert(
        fc.property(fc.string(), (str) => {
          const result = asPlaceholderName(str);
          // Either must be Left or Right
          expect(isLeft(result) || isRight(result)).toBe(true);
        })
      );
    });

    /**
     * Property: Right values contain valid branded types
     * 法則: Right の値は有効なブランド型を含む
     */
    it('property: Right values contain the input string', () => {
      fc.assert(
        fc.property(fc.stringMatching(/^[A-Za-z0-9_]{1,10}$/), (str) => {
          // Skip reserved names
          if (['doc_type'].includes(str.toLowerCase())) {
            return;
          }
          const result = asPlaceholderName(str);
          if (isRight(result)) {
            // The branded type should be equal to the input
            expect(result.right as string).toBe(str);
          }
        })
      );
    });

    /**
     * Property: Left values contain LawViolationError
     * 法則: Left の値は LawViolationError を含む
     */
    it('property: Left values contain LawViolationError', () => {
      fc.assert(
        fc.property(fc.string(), (str) => {
          const result = asPlaceholderName(str);
          if (isLeft(result)) {
            expect(result.left).toBeInstanceOf(LawViolationError);
            expect(result.left.lawName).toBe('PlaceholderName');
          }
        })
      );
    });
  });
});
