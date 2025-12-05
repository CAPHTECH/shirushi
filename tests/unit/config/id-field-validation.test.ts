/**
 * id_field Validation Tests
 *
 * id_field設定のバリデーションテスト。
 * 不正なフィールド名に対するエラーを検証する。
 */

import { describe, it, expect } from 'vitest';

import { ConfigSchema } from '@/config/schema';

describe('id_field validation', () => {
  const baseConfig = {
    doc_globs: ['docs/**/*.md'],
    id_format: '{TYPE}-{NUM}',
    dimensions: {
      TYPE: { type: 'enum', values: ['DOC'] },
      NUM: { type: 'serial', digits: 4, scope: ['TYPE'] },
    },
  };

  describe('valid id_field values', () => {
    it('should accept default "doc_id"', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'doc_id',
      });
      expect(result.success).toBe(true);
    });

    it('should accept snake_case identifier', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'my_custom_id',
      });
      expect(result.success).toBe(true);
    });

    it('should accept camelCase identifier', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'documentId',
      });
      expect(result.success).toBe(true);
    });

    it('should accept identifier starting with underscore', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: '_privateId',
      });
      expect(result.success).toBe(true);
    });

    it('should accept identifier with numbers', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'id2',
      });
      expect(result.success).toBe(true);
    });

    it('should accept single letter', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'x',
      });
      expect(result.success).toBe(true);
    });

    it('should use default when id_field is not specified', () => {
      const result = ConfigSchema.safeParse(baseConfig);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.data.id_field).toBe('doc_id');
      }
    });
  });

  describe('invalid id_field values', () => {
    it('should reject empty string', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: '',
      });
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error.issues.some(i => i.message.includes('empty'))).toBe(true);
      }
    });

    it('should reject identifier starting with number', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: '123invalid',
      });
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error.issues.some(i => i.message.includes('valid identifier'))).toBe(true);
      }
    });

    it('should reject identifier with hyphen', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'doc-id',
      });
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error.issues.some(i => i.message.includes('valid identifier'))).toBe(true);
      }
    });

    it('should reject identifier with space', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'doc id',
      });
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error.issues.some(i => i.message.includes('valid identifier'))).toBe(true);
      }
    });

    it('should reject identifier with special characters', () => {
      const specialChars = ['doc.id', 'doc@id', 'doc$id', 'doc!id', 'doc#id'];

      for (const id_field of specialChars) {
        const result = ConfigSchema.safeParse({
          ...baseConfig,
          id_field,
        });
        expect(result.success).toBe(false);
        if (!result.success) {
          expect(result.error.issues.some(i => i.message.includes('valid identifier'))).toBe(true);
        }
      }
    });

    it('should reject identifier with only numbers after valid start', () => {
      // This should actually be valid: a123 matches [a-zA-Z_][a-zA-Z0-9_]*
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'a123',
      });
      expect(result.success).toBe(true);
    });

    it('should reject identifier with Japanese characters', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'ドキュメントID',
      });
      expect(result.success).toBe(false);
    });

    it('should reject identifier with emoji', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'doc_id_📄',
      });
      expect(result.success).toBe(false);
    });
  });

  describe('edge cases', () => {
    it('should accept long identifier', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'this_is_a_very_long_identifier_name_that_should_still_be_valid',
      });
      expect(result.success).toBe(true);
    });

    it('should accept all uppercase', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'DOCUMENT_ID',
      });
      expect(result.success).toBe(true);
    });

    it('should accept mixed case with underscores and numbers', () => {
      const result = ConfigSchema.safeParse({
        ...baseConfig,
        id_field: 'Doc_ID_v2_Final',
      });
      expect(result.success).toBe(true);
    });
  });
});
