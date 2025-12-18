/**
 * YAML Parser Tests (preserveContent functionality)
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';
import { parseYamlFile, parseYamlContent } from '@/parsers/yaml';

const TEST_DIR = path.join(process.cwd(), 'tests', '.tmp', 'yaml-parser');

describe('yaml parser', () => {
  describe('parseYamlContent', () => {
    describe('preserveContent option', () => {
      it('should include content field when preserveContent is true', () => {
        const yaml = `doc_id: TEST-001
title: Test Document
status: draft`;

        const result = parseYamlContent('test.yaml', yaml, 'doc_id', true);

        expect(result.content).toBeDefined();
        // Content should be doc_id-excluded YAML, re-serialized
        expect(result.content).not.toContain('TEST-001');
        expect(result.content).toContain('title:');
        expect(result.content).toContain('status:');
      });

      it('should not include content field when preserveContent is false', () => {
        const yaml = `doc_id: TEST-001
title: Test Document`;

        const result = parseYamlContent('test.yaml', yaml, 'doc_id', false);

        expect(result.content).toBeUndefined();
      });

      it('should not include content field when preserveContent is not specified', () => {
        const yaml = `doc_id: TEST-001
title: Test Document`;

        const result = parseYamlContent('test.yaml', yaml, 'doc_id');

        expect(result.content).toBeUndefined();
      });

      it('should exclude doc_id from content (using sortKeys for determinism)', () => {
        const yaml = `doc_id: TEST-001
zebra: last
alpha: first`;

        const result = parseYamlContent('test.yaml', yaml, 'doc_id', true);

        expect(result.content).toBeDefined();
        // sortKeys: true means alpha should come before zebra
        const lines = result.content!.split('\n').filter((l) => l.trim());
        expect(lines[0]).toContain('alpha');
        expect(lines[1]).toContain('zebra');
      });

      it('should produce consistent hash for same content regardless of key order', () => {
        const yaml1 = `doc_id: TEST-001
b: 2
a: 1`;

        const yaml2 = `doc_id: TEST-001
a: 1
b: 2`;

        const result1 = parseYamlContent('test.yaml', yaml1, 'doc_id', true);
        const result2 = parseYamlContent('test.yaml', yaml2, 'doc_id', true);

        // Both should produce the same content due to sortKeys
        expect(result1.content).toBe(result2.content);
      });

      it('should handle nested objects', () => {
        const yaml = `doc_id: TEST-001
nested:
  key1: value1
  key2: value2`;

        const result = parseYamlContent('test.yaml', yaml, 'doc_id', true);

        expect(result.content).toBeDefined();
        expect(result.content).toContain('nested:');
        expect(result.content).toContain('key1:');
      });

      it('should handle arrays', () => {
        const yaml = `doc_id: TEST-001
items:
  - item1
  - item2`;

        const result = parseYamlContent('test.yaml', yaml, 'doc_id', true);

        expect(result.content).toBeDefined();
        expect(result.content).toContain('items:');
        expect(result.content).toContain('- item1');
      });

      it('should handle empty content (only doc_id)', () => {
        const yaml = `doc_id: TEST-001`;

        const result = parseYamlContent('test.yaml', yaml, 'doc_id', true);

        expect(result.content).toBeDefined();
        // Content should be empty or just '{}' after excluding doc_id
        expect(result.content!.trim()).toBe('{}');
      });

      it('should handle special characters in values', () => {
        const yaml = `doc_id: TEST-001
description: "日本語テスト 🎉 emoji"`;

        const result = parseYamlContent('test.yaml', yaml, 'doc_id', true);

        expect(result.content).toBeDefined();
        expect(result.content).toContain('日本語テスト');
      });

      it('should use custom id_field', () => {
        const yaml = `custom_id: TEST-001
title: Test`;

        const result = parseYamlContent('test.yaml', yaml, 'custom_id', true);

        expect(result.docId).toBe('TEST-001');
        expect(result.content).toBeDefined();
        expect(result.content).not.toContain('TEST-001');
        expect(result.content).toContain('title:');
      });
    });
  });

  describe('parseYamlFile', () => {
    beforeEach(async () => {
      await mkdir(TEST_DIR, { recursive: true });
    });

    afterEach(async () => {
      await rm(TEST_DIR, { recursive: true, force: true });
    });

    it('should include content field when preserveContent is true', async () => {
      const filePath = path.join(TEST_DIR, 'test.yaml');
      await writeFile(
        filePath,
        `doc_id: TEST-001
title: From File`
      );

      const result = await parseYamlFile(filePath, 'doc_id', true);

      expect(result.content).toBeDefined();
      expect(result.content).toContain('title:');
    });

    it('should not include content field when preserveContent is false', async () => {
      const filePath = path.join(TEST_DIR, 'test.yaml');
      await writeFile(
        filePath,
        `doc_id: TEST-001
title: From File`
      );

      const result = await parseYamlFile(filePath, 'doc_id', false);

      expect(result.content).toBeUndefined();
    });
  });
});
