/**
 * Checksum Validator Tests
 *
 * ADR-0009: チェックサムをdoc_idから分離して別フィールドに
 *
 * @see docs/adr/0009-separate-checksum-from-doc-id.md
 */

import { describe, it, expect } from 'vitest';

import {
  validateSeparateChecksum,
  computeChecksum,
  usesSeparateChecksum,
  usesLegacyChecksum,
  stripChecksumFromDocId,
} from '@/core/checksum-validator';

import type { ShirushiConfig } from '@/config/schema';

// 新形式の設定（checksumブロックあり）
const newFormatConfig: ShirushiConfig = {
  id_format: '{COMP}-{KIND}-{YEAR4}-{SER4}',
  doc_globs: ['docs/**/*.md'],
  dimensions: {
    COMP: { type: 'enum', values: ['PCE', 'BACK'] },
    KIND: { type: 'enum', values: ['SPEC', 'ADR'] },
    YEAR4: { type: 'year', digits: 4, source: 'created_at' },
    SER4: { type: 'serial', digits: 4, scope: ['COMP', 'KIND', 'YEAR4'] },
  },
  index_file: 'docs/doc_index.yaml',
  id_field: 'doc_id',
  forbid_id_change: true,
  allow_missing_id_in_new_files: false,
  reference_fields: ['superseded_by'],
  reference_patterns: [{ name: 'markdown_link', pattern: '\\[.*?\\]\\({DOC_ID}\\)' }],
  checksum: {
    field: 'checksum',
    algo: 'mod26AZ',
    of: ['COMP', 'KIND', 'YEAR4', 'SER4'],
  },
};

// 旧形式の設定（id_formatにchecksum dimension含む）
const legacyFormatConfig: ShirushiConfig = {
  id_format: '{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}',
  doc_globs: ['docs/**/*.md'],
  dimensions: {
    COMP: { type: 'enum', values: ['PCE', 'BACK'] },
    KIND: { type: 'enum', values: ['SPEC', 'ADR'] },
    YEAR4: { type: 'year', digits: 4, source: 'created_at' },
    SER4: { type: 'serial', digits: 4, scope: ['COMP', 'KIND', 'YEAR4'] },
    CHK1: { type: 'checksum', algo: 'mod26AZ', of: ['COMP', 'KIND', 'YEAR4', 'SER4'] },
  },
  index_file: 'docs/doc_index.yaml',
  id_field: 'doc_id',
  forbid_id_change: true,
  allow_missing_id_in_new_files: false,
  reference_fields: ['superseded_by'],
  reference_patterns: [{ name: 'markdown_link', pattern: '\\[.*?\\]\\({DOC_ID}\\)' }],
};

// チェックサムなしの設定
const noChecksumConfig: ShirushiConfig = {
  id_format: '{COMP}-{KIND}-{YEAR4}-{SER4}',
  doc_globs: ['docs/**/*.md'],
  dimensions: {
    COMP: { type: 'enum', values: ['PCE', 'BACK'] },
    KIND: { type: 'enum', values: ['SPEC', 'ADR'] },
    YEAR4: { type: 'year', digits: 4, source: 'created_at' },
    SER4: { type: 'serial', digits: 4, scope: ['COMP', 'KIND', 'YEAR4'] },
  },
  index_file: 'docs/doc_index.yaml',
  id_field: 'doc_id',
  forbid_id_change: true,
  allow_missing_id_in_new_files: false,
  reference_fields: ['superseded_by'],
  reference_patterns: [{ name: 'markdown_link', pattern: '\\[.*?\\]\\({DOC_ID}\\)' }],
};

describe('checksum-validator', () => {
  describe('usesSeparateChecksum', () => {
    it('should return true for new format config', () => {
      expect(usesSeparateChecksum(newFormatConfig)).toBe(true);
    });

    it('should return false for legacy format config', () => {
      expect(usesSeparateChecksum(legacyFormatConfig)).toBe(false);
    });

    it('should return false for no checksum config', () => {
      expect(usesSeparateChecksum(noChecksumConfig)).toBe(false);
    });
  });

  describe('usesLegacyChecksum', () => {
    it('should return false for new format config', () => {
      expect(usesLegacyChecksum(newFormatConfig)).toBe(false);
    });

    it('should return true for legacy format config', () => {
      expect(usesLegacyChecksum(legacyFormatConfig)).toBe(true);
    });

    it('should return false for no checksum config', () => {
      expect(usesLegacyChecksum(noChecksumConfig)).toBe(false);
    });
  });

  describe('computeChecksum', () => {
    it('should compute checksum for valid doc_id', () => {
      const result = computeChecksum('PCE-SPEC-2025-0001', newFormatConfig, newFormatConfig.checksum!);
      expect(result._tag).toBe('Right');
      if (result._tag === 'Right') {
        expect(result.right).toMatch(/^[A-Z]$/);
      }
    });

    it('should return error for malformed doc_id', () => {
      const result = computeChecksum('INVALID-ID', newFormatConfig, newFormatConfig.checksum!);
      expect(result._tag).toBe('Left');
    });
  });

  describe('validateSeparateChecksum', () => {
    it('should pass for valid checksum', () => {
      // まずチェックサムを計算
      const computeResult = computeChecksum('PCE-SPEC-2025-0001', newFormatConfig, newFormatConfig.checksum!);
      expect(computeResult._tag).toBe('Right');
      const expectedChecksum = computeResult._tag === 'Right' ? computeResult.right : 'X';

      const result = validateSeparateChecksum(
        'PCE-SPEC-2025-0001',
        { checksum: expectedChecksum },
        newFormatConfig
      );
      expect(result.valid).toBe(true);
    });

    it('should fail for missing checksum field', () => {
      const result = validateSeparateChecksum(
        'PCE-SPEC-2025-0001',
        {},
        newFormatConfig
      );
      expect(result.valid).toBe(false);
      expect(result.error?.code).toBe('MISSING_CHECKSUM');
    });

    it('should fail for invalid checksum value', () => {
      const result = validateSeparateChecksum(
        'PCE-SPEC-2025-0001',
        { checksum: 'X' },
        newFormatConfig
      );
      // チェックサムが一致しない場合はエラー（Xが正しいチェックサムでない限り）
      // 実際の期待値をテストするため、まず正しい値を計算
      const computeResult = computeChecksum('PCE-SPEC-2025-0001', newFormatConfig, newFormatConfig.checksum!);
      if (computeResult._tag === 'Right' && computeResult.right !== 'X') {
        expect(result.valid).toBe(false);
        expect(result.error?.code).toBe('INVALID_CHECKSUM');
      }
    });

    it('should skip validation for legacy format config', () => {
      // 旧形式の設定ではスキップされる
      const result = validateSeparateChecksum(
        'PCE-SPEC-2025-0001-G',
        {},
        legacyFormatConfig
      );
      expect(result.valid).toBe(true);
    });

    it('should skip validation for no checksum config', () => {
      const result = validateSeparateChecksum(
        'PCE-SPEC-2025-0001',
        {},
        noChecksumConfig
      );
      expect(result.valid).toBe(true);
    });
  });

  describe('stripChecksumFromDocId', () => {
    it('should strip checksum from legacy format doc_id', () => {
      const result = stripChecksumFromDocId('PCE-SPEC-2025-0001-G', legacyFormatConfig);
      expect(result).toBe('PCE-SPEC-2025-0001');
    });

    it('should return doc_id unchanged for new format config', () => {
      const result = stripChecksumFromDocId('PCE-SPEC-2025-0001', newFormatConfig);
      expect(result).toBe('PCE-SPEC-2025-0001');
    });

    it('should return doc_id unchanged for no checksum config', () => {
      const result = stripChecksumFromDocId('PCE-SPEC-2025-0001', noChecksumConfig);
      expect(result).toBe('PCE-SPEC-2025-0001');
    });

    it('should return null for null input', () => {
      const result = stripChecksumFromDocId(null, legacyFormatConfig);
      expect(result).toBe(null);
    });
  });
});
