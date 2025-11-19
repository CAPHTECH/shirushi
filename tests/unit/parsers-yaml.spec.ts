import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { parseYamlFile, parseYamlContent } from '@/parsers/yaml.js';

const fixture = (name: string) =>
  path.resolve('tests/fixtures/doc-discovery/basic/docs', name);

describe('parsers/yaml', () => {
  it('parses YAML document with doc_id', async () => {
    const result = await parseYamlFile(fixture('spec.yaml'));

    expect(result.docId).toBe('SHI-SPEC-2025-0004-C');
    expect(result.metadata.title).toBe('YAML Spec');
  });

  it('reports missing doc_id', async () => {
    const result = await parseYamlFile(fixture('spec-missing.yaml'));
    expect(result.problems.some((p) => p.code === 'MISSING_ID')).toBe(true);
  });

  it('reports duplicate doc_id definitions', async () => {
    const result = await parseYamlFile(fixture('spec-duplicate.yaml'));
    expect(result.problems.some((p) => p.code === 'MULTIPLE_IDS_IN_DOCUMENT')).toBe(true);
  });

  it('reports invalid YAML syntax', () => {
    const malformed = 'doc_id: [unterminated';
    const result = parseYamlContent('virtual.yaml', malformed);
    expect(result.problems.some((p) => p.code === 'INVALID_YAML')).toBe(true);
  });

  it('reports invalid YAML when root is not an object', async () => {
    const result = await parseYamlFile(fixture('yaml-scalar.yaml'));
    expect(result.problems.some((p) => p.code === 'INVALID_YAML')).toBe(true);
  });
});
