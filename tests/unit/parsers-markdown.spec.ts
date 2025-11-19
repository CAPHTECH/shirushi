import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { parseMarkdownFile, parseMarkdownContent } from '@/parsers/markdown.js';

const fixture = (name: string) =>
  path.resolve('tests/fixtures/doc-discovery/basic/docs', name);

describe('parsers/markdown', () => {
  it('parses doc_id and metadata from markdown front matter', async () => {
    const result = await parseMarkdownFile(fixture('spec-good.md'));

    expect(result.docId).toBe('SHI-SPEC-2025-0001-A');
    expect(result.metadata.title).toBe('Good Spec');
    expect(result.problems).toHaveLength(0);
  });

  it('reports missing doc_id', async () => {
    const result = await parseMarkdownFile(fixture('spec-missing.md'));

    expect(result.docId).toBeUndefined();
    expect(result.problems.some((p) => p.code === 'MISSING_ID')).toBe(true);
  });

  it('reports multiple doc_id entries', async () => {
    const result = await parseMarkdownFile(fixture('spec-multi.md'));

    expect(result.problems.some((p) => p.code === 'MULTIPLE_IDS_IN_DOCUMENT')).toBe(true);
  });

  it('reports invalid front matter syntax', () => {
    const malformed = ['---', 'doc_id: [', 'title: bad'].join('\n');
    const result = parseMarkdownContent('virtual.md', malformed);

    expect(result.problems.some((p) => p.code === 'INVALID_FRONT_MATTER')).toBe(true);
  });
});
