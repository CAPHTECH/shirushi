/**
 * Property-based tests for branded types
 *
 * Tests the validation invariants and type safety of branded types
 * using fast-check for generative testing.
 */

import * as fc from 'fast-check';
import { describe, expect, it } from 'vitest';

import {
  asDimensionName,
  asPlaceholderName,
  asTemplateString,
  isPlaceholderName,
  isTemplateString,
} from '@/types/branded.js';

describe('branded types - Property-Based Tests', () => {
  describe('TemplateString', () => {
    // Arbitrary: Valid placeholder name
    const placeholderNameArb = fc.stringMatching(/^[A-Za-z0-9_]{1,20}$/);

    // Arbitrary: Valid template string
    const validTemplateArb = fc
      .array(placeholderNameArb, { minLength: 1, maxLength: 5 })
      .map((names) => names.map((n) => `{${n}}`).join('-'));

    /**
     * Property: All valid templates should be accepted
     */
    it('property: accepts all valid template strings', () => {
      fc.assert(
        fc.property(validTemplateArb, (template) => {
          expect(() => asTemplateString(template)).not.toThrow();
          expect(isTemplateString(template)).toBe(true);
        })
      );
    });

    /**
     * Property: Templates without placeholders should be rejected
     */
    it('property: rejects strings without placeholders', () => {
      fc.assert(
        fc.property(fc.stringMatching(/^[^{}]*$/), (str) => {
          if (str.length > 0) {
            expect(() => asTemplateString(str)).toThrow(TypeError);
            expect(isTemplateString(str)).toBe(false);
          }
        })
      );
    });

    /**
     * Property: Templates with unclosed braces should be rejected
     */
    it('property: rejects templates with unclosed braces', () => {
      const invalidTemplates = ['{VALID', 'VALID}', '{VALID}}}', '{{{VALID}'];

      invalidTemplates.forEach((template) => {
        expect(() => asTemplateString(template)).toThrow(/unclosed braces/);
        expect(isTemplateString(template)).toBe(false);
      });
    });

    /**
     * Property: Validation is deterministic
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

  describe('PlaceholderName', () => {
    // Arbitrary: Valid placeholder name
    const validNameArb = fc.stringMatching(/^[A-Za-z0-9_]{1,20}$/);

    /**
     * Property: All valid names should be accepted
     */
    it('property: accepts all valid placeholder names', () => {
      fc.assert(
        fc.property(validNameArb, (name) => {
          // Skip reserved names
          if (!['doc_type'].includes(name.toLowerCase())) {
            expect(() => asPlaceholderName(name)).not.toThrow();
            expect(isPlaceholderName(name)).toBe(true);
          }
        })
      );
    });

    /**
     * Property: Names with invalid characters should be rejected
     */
    it('property: rejects names with invalid characters', () => {
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
              expect(() => asPlaceholderName(name)).toThrow(TypeError);
              expect(isPlaceholderName(name)).toBe(false);
            }
          }
        )
      );
    });

    /**
     * Property: Reserved names should be rejected
     */
    it('property: rejects reserved names (case-insensitive)', () => {
      const reserved = ['doc_type', 'DOC_TYPE', 'Doc_Type'];

      reserved.forEach((name) => {
        expect(() => asPlaceholderName(name)).toThrow(/reserved/);
        expect(isPlaceholderName(name)).toBe(false);
      });
    });

    /**
     * Property: Empty strings should be rejected
     */
    it('property: rejects empty strings', () => {
      expect(() => asPlaceholderName('')).toThrow(TypeError);
      expect(isPlaceholderName('')).toBe(false);
    });
  });

  describe('DimensionName', () => {
    // Arbitrary: Valid dimension name (uppercase convention)
    const validDimensionArb = fc.stringMatching(/^[A-Z][A-Z0-9_]{0,19}$/);

    /**
     * Property: All valid dimension names should be accepted
     */
    it('property: accepts all valid uppercase dimension names', () => {
      fc.assert(
        fc.property(validDimensionArb, (name) => {
          expect(() => asDimensionName(name)).not.toThrow();
        })
      );
    });

    /**
     * Property: Lowercase names should be rejected
     */
    it('property: rejects lowercase dimension names', () => {
      fc.assert(
        fc.property(fc.stringMatching(/^[a-z][a-z0-9_]{0,19}$/), (name) => {
          expect(() => asDimensionName(name)).toThrow(TypeError);
        })
      );
    });

    /**
     * Property: Names starting with digits should be rejected
     */
    it('property: rejects names starting with digits', () => {
      fc.assert(
        fc.property(
          fc.tuple(fc.integer({ min: 0, max: 9 }), fc.stringMatching(/^[A-Z0-9_]{0,18}$/)),
          ([digit, suffix]) => {
            const name = `${digit}${suffix}`;
            expect(() => asDimensionName(name)).toThrow(TypeError);
          }
        )
      );
    });
  });

  describe('Type Safety', () => {
    /**
     * Property: Type guards are conservative (no false positives)
     *
     * If a type guard returns true, the constructor should not throw.
     */
    it('property: type guards have no false positives', () => {
      fc.assert(
        fc.property(fc.string(), (str) => {
          if (isTemplateString(str)) {
            expect(() => asTemplateString(str)).not.toThrow();
          }

          if (isPlaceholderName(str)) {
            expect(() => asPlaceholderName(str)).not.toThrow();
          }
        })
      );
    });

    /**
     * Property: Constructors are total (always return or throw)
     *
     * No constructor should crash or return undefined.
     */
    it('property: constructors never crash silently', () => {
      fc.assert(
        fc.property(fc.string(), (str) => {
          try {
            const result = asPlaceholderName(str);
            expect(typeof result).toBe('string');
          } catch (error) {
            expect(error).toBeInstanceOf(TypeError);
          }
        })
      );
    });
  });
});
