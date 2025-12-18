/**
 * Markdown Parser Tests (preserveContent functionality)
 */

import { mkdir, writeFile, rm } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach } from 'vitest';

import { parseMarkdownFile, parseMarkdownContent } from '@/parsers/markdown';

const TEST_DIR = path.join(process.cwd(), 'tests', '.tmp', 'markdown-parser');

describe('markdown parser', () => {
  describe('parseMarkdownContent', () => {
    describe('preserveContent option', () => {
      it('should include content field when preserveContent is true', () => {
        const markdown = `---
doc_id: TEST-001
---
This is the body content.`;

        const result = parseMarkdownContent('test.md', markdown, 'doc_id', true);

        expect(result.content).toBeDefined();
        expect(result.content).toBe('This is the body content.');
      });

      it('should not include content field when preserveContent is false', () => {
        const markdown = `---
doc_id: TEST-001
---
This is the body content.`;

        const result = parseMarkdownContent('test.md', markdown, 'doc_id', false);

        expect(result.content).toBeUndefined();
      });

      it('should not include content field when preserveContent is not specified', () => {
        const markdown = `---
doc_id: TEST-001
---
This is the body content.`;

        const result = parseMarkdownContent('test.md', markdown, 'doc_id');

        expect(result.content).toBeUndefined();
      });

      it('should preserve multiline content', () => {
        const markdown = `---
doc_id: TEST-001
---
Line 1
Line 2
Line 3`;

        const result = parseMarkdownContent('test.md', markdown, 'doc_id', true);

        expect(result.content).toBe('Line 1\nLine 2\nLine 3');
      });

      it('should preserve content with code blocks', () => {
        const markdown = `---
doc_id: TEST-001
---
Some text

\`\`\`typescript
const x = 1;
\`\`\`

More text`;

        const result = parseMarkdownContent('test.md', markdown, 'doc_id', true);

        expect(result.content).toContain('```typescript');
        expect(result.content).toContain('const x = 1;');
      });

      it('should handle empty body content', () => {
        const markdown = `---
doc_id: TEST-001
---`;

        const result = parseMarkdownContent('test.md', markdown, 'doc_id', true);

        expect(result.content).toBe('');
      });

      it('should handle content with special characters', () => {
        const markdown = `---
doc_id: TEST-001
---
日本語テスト 🎉 emoji & special <chars>`;

        const result = parseMarkdownContent('test.md', markdown, 'doc_id', true);

        expect(result.content).toBe('日本語テスト 🎉 emoji & special <chars>');
      });
    });
  });

  describe('parseMarkdownFile', () => {
    beforeEach(async () => {
      await mkdir(TEST_DIR, { recursive: true });
    });

    afterEach(async () => {
      await rm(TEST_DIR, { recursive: true, force: true });
    });

    it('should include content field when preserveContent is true', async () => {
      const filePath = path.join(TEST_DIR, 'test.md');
      await writeFile(filePath, `---
doc_id: TEST-001
---
File body content.`);

      const result = await parseMarkdownFile(filePath, 'doc_id', true);

      expect(result.content).toBe('File body content.');
    });

    it('should not include content field when preserveContent is false', async () => {
      const filePath = path.join(TEST_DIR, 'test.md');
      await writeFile(filePath, `---
doc_id: TEST-001
---
File body content.`);

      const result = await parseMarkdownFile(filePath, 'doc_id', false);

      expect(result.content).toBeUndefined();
    });

    it('should handle files with CRLF line endings', async () => {
      const filePath = path.join(TEST_DIR, 'test.md');
      await writeFile(filePath, '---\r\ndoc_id: TEST-001\r\n---\r\nLine 1\r\nLine 2');

      const result = await parseMarkdownFile(filePath, 'doc_id', true);

      expect(result.docId).toBe('TEST-001');
      expect(result.content).toBeDefined();
    });

    it('should handle files with BOM', async () => {
      const filePath = path.join(TEST_DIR, 'test.md');
      await writeFile(filePath, '\uFEFF---\ndoc_id: TEST-001\n---\nBOM content');

      const result = await parseMarkdownFile(filePath, 'doc_id', true);

      expect(result.docId).toBe('TEST-001');
      expect(result.content).toBe('BOM content');
    });
  });
});
