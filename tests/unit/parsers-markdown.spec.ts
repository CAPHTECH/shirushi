import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { parseMarkdownFile, parseMarkdownContent } from '@/parsers/markdown.js';
import { MAX_YAML_ALIAS_BUDGET } from '@/parsers/yaml-safety.js';

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

  it('reports missing doc_id when front matter does not exist', async () => {
    const result = await parseMarkdownFile(fixture('plain.md'));

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

  it('detects front matter after BOM and blank lines', () => {
    const doc = ['\uFEFF', '', '---', 'doc_id: TEST-123', 'title: BOM Spec', '---', '', '# Title'].join('\n');

    const result = parseMarkdownContent('bom.md', doc);

    expect(result.docId).toBe('TEST-123');
    expect(result.problems).toHaveLength(0);
  });

  it('does not count doc_id occurrences inside comments', () => {
    const doc = [
      '---',
      'doc_id: TEST-123',
      '# doc_id: SHOULD_NOT_COUNT',
      'title: Valid',
      '---',
      '',
      '# Body',
    ].join('\n');

    const result = parseMarkdownContent('comment.md', doc);

    expect(result.problems.some((p) => p.code === 'MULTIPLE_IDS_IN_DOCUMENT')).toBe(false);
    expect(result.docId).toBe('TEST-123');
  });

  it('rejects yaml execution tags inside front matter', () => {
    const doc = [
      '---',
      'doc_id: !!js/function >',
      '  function () { return "pwn"; }',
      '---',
      '',
      '# Malicious',
    ].join('\n');

    const result = parseMarkdownContent('evil.md', doc);

    expect(result.docId).toBeUndefined();
    expect(result.problems.some((p) => p.code === 'INVALID_FRONT_MATTER')).toBe(true);
  });

  it('rejects front matter with excessive YAML aliases', () => {
    const aliasBudget = MAX_YAML_ALIAS_BUDGET + 5;
    const anchors = Array.from({ length: aliasBudget }, (_, index) => `&a${index} node${index}: value${index}`).join('\n');
    const doc = ['---', anchors, 'doc_id: SHI-ALIAS-0001', '---', '', '# Body'].join('\n');

    const result = parseMarkdownContent('alias.md', doc);

    expect(result.docId).toBeUndefined();
    expect(result.problems.some((p) => p.code === 'INVALID_FRONT_MATTER')).toBe(true);
  });
});
