/**
 * Content Hash Utility Tests
 */

import { describe, it, expect } from 'vitest';

import {
  calculateContentHash,
  normalizeContentForHashing,
  verifyContentHash,
} from '@/utils/content-hash';

describe('content-hash', () => {
  describe('normalizeContentForHashing', () => {
    it('should convert CRLF to LF', () => {
      const input = 'line1\r\nline2\r\nline3';
      const result = normalizeContentForHashing(input);
      expect(result).toBe('line1\nline2\nline3');
    });

    it('should convert CR to LF', () => {
      const input = 'line1\rline2\rline3';
      const result = normalizeContentForHashing(input);
      expect(result).toBe('line1\nline2\nline3');
    });

    it('should handle mixed line endings', () => {
      const input = 'line1\r\nline2\rline3\nline4';
      const result = normalizeContentForHashing(input);
      expect(result).toBe('line1\nline2\nline3\nline4');
    });

    it('should trim trailing whitespace', () => {
      const input = 'content\n\n\n';
      const result = normalizeContentForHashing(input);
      expect(result).toBe('content');
    });

    it('should trim trailing spaces and newlines', () => {
      const input = 'content   \n  \n';
      const result = normalizeContentForHashing(input);
      // trimEnd removes all trailing whitespace including newlines
      expect(result).toBe('content');
    });

    it('should handle empty string', () => {
      const result = normalizeContentForHashing('');
      expect(result).toBe('');
    });

    it('should preserve internal whitespace', () => {
      const input = 'line1\n  indented\n\nwith blank line';
      const result = normalizeContentForHashing(input);
      expect(result).toBe('line1\n  indented\n\nwith blank line');
    });
  });

  describe('calculateContentHash', () => {
    it('should return 64 character hex string', () => {
      const result = calculateContentHash('test content');
      expect(result).toHaveLength(64);
      expect(result).toMatch(/^[0-9a-f]{64}$/);
    });

    it('should return consistent hash for same content', () => {
      const content = 'hello world';
      const hash1 = calculateContentHash(content);
      const hash2 = calculateContentHash(content);
      expect(hash1).toBe(hash2);
    });

    it('should return different hash for different content', () => {
      const hash1 = calculateContentHash('content A');
      const hash2 = calculateContentHash('content B');
      expect(hash1).not.toBe(hash2);
    });

    it('should normalize before hashing (CRLF vs LF)', () => {
      const hashCRLF = calculateContentHash('line1\r\nline2');
      const hashLF = calculateContentHash('line1\nline2');
      expect(hashCRLF).toBe(hashLF);
    });

    it('should normalize before hashing (trailing whitespace)', () => {
      const hash1 = calculateContentHash('content\n\n');
      const hash2 = calculateContentHash('content');
      expect(hash1).toBe(hash2);
    });

    it('should handle empty string', () => {
      const result = calculateContentHash('');
      expect(result).toHaveLength(64);
      // SHA-256 of empty string
      expect(result).toBe('e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855');
    });

    it('should handle Unicode content', () => {
      const content = '日本語テスト 🎉 emoji';
      const result = calculateContentHash(content);
      expect(result).toHaveLength(64);
      // Same content should produce same hash
      expect(calculateContentHash(content)).toBe(result);
    });

    it('should handle BOM character', () => {
      const withBOM = '\uFEFFcontent';
      const withoutBOM = 'content';
      // BOM is NOT stripped by normalizeContentForHashing
      // It should produce different hashes
      const hashWithBOM = calculateContentHash(withBOM);
      const hashWithoutBOM = calculateContentHash(withoutBOM);
      expect(hashWithBOM).not.toBe(hashWithoutBOM);
    });
  });

  describe('verifyContentHash', () => {
    it('should return true for matching hash', () => {
      const content = 'test content';
      const hash = calculateContentHash(content);
      expect(verifyContentHash(content, hash)).toBe(true);
    });

    it('should return false for non-matching hash', () => {
      const content = 'test content';
      const wrongHash = 'a'.repeat(64);
      expect(verifyContentHash(content, wrongHash)).toBe(false);
    });

    it('should be case-insensitive for hash comparison', () => {
      const content = 'test';
      const hash = calculateContentHash(content);
      const upperHash = hash.toUpperCase();
      expect(verifyContentHash(content, upperHash)).toBe(true);
    });

    it('should handle normalization differences', () => {
      const contentCRLF = 'line1\r\nline2';
      const hashFromLF = calculateContentHash('line1\nline2');
      expect(verifyContentHash(contentCRLF, hashFromLF)).toBe(true);
    });
  });

  describe('edge cases', () => {
    it('should handle very long content', () => {
      const longContent = 'x'.repeat(1000000); // 1MB of 'x'
      const result = calculateContentHash(longContent);
      expect(result).toHaveLength(64);
    });

    it('should handle content with null bytes', () => {
      const content = 'before\x00after';
      const result = calculateContentHash(content);
      expect(result).toHaveLength(64);
    });

    it('should handle content with only whitespace', () => {
      const content = '   \n\t\n   ';
      const result = calculateContentHash(content);
      // After normalization and trimEnd, this should be just spaces and tab
      expect(result).toHaveLength(64);
    });
  });
});
