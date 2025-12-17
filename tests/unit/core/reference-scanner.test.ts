/**
 * Reference Scanner Unit Tests
 *
 * 参照スキャン機能のテスト。
 * Issue #15: doc_id変更時の文書間参照整合性チェック機能
 */

import { describe, it, expect } from 'vitest';

import {
  removeCodeBlocks,
  buildDocIdPattern,
  extractMarkdownLinks,
  extractYamlFieldReferences,
  extractCustomPatternReferences,
} from '@/core/reference-scanner';

import type { ShirushiConfig, ReferencePattern } from '@/config/schema';

// テスト用の設定ファクトリ
function createTestConfig(
  overrides: Partial<ShirushiConfig> = {}
): ShirushiConfig {
  return {
    id_format: '{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}',
    doc_globs: ['docs/**/*.md'],
    dimensions: {
      COMP: { type: 'enum', values: ['PCE', 'BACK', 'GW'] },
      KIND: {
        type: 'enum_from_doc_type',
        mapping: { spec: 'SPEC', design: 'DES', memo: 'MEMO' },
      },
      YEAR4: { type: 'year', digits: 4, source: 'created_at' },
      SER4: { type: 'serial', digits: 4, scope: ['COMP', 'KIND', 'YEAR4'] },
      CHK1: {
        type: 'checksum',
        algo: 'mod26AZ',
        of: ['COMP', 'KIND', 'YEAR4', 'SER4'],
      },
    },
    index_file: 'docs/doc_index.yaml',
    forbid_id_change: true,
    allow_missing_id_in_new_files: false,
    reference_fields: ['superseded_by', 'related_docs'],
    reference_patterns: [
      { name: 'markdown_link', pattern: '\\[.*?\\]\\({DOC_ID}\\)' },
    ],
    ...overrides,
  };
}

describe('removeCodeBlocks', () => {
  it('コードブロックを除去する', () => {
    const content = `# Title

Some text with [link](PCE-SPEC-2025-0001-Z)

\`\`\`typescript
// This should be removed
const docId = 'PCE-SPEC-2025-0002-A';
\`\`\`

More text with [another link](PCE-SPEC-2025-0003-B)
`;

    const result = removeCodeBlocks(content);

    expect(result).toContain('[link](PCE-SPEC-2025-0001-Z)');
    expect(result).toContain('[another link](PCE-SPEC-2025-0003-B)');
    expect(result).not.toContain('PCE-SPEC-2025-0002-A');
  });

  it('インラインコードを除去する', () => {
    const content = `See \`PCE-SPEC-2025-0001-Z\` for details. Also [link](PCE-SPEC-2025-0002-A).`;

    const result = removeCodeBlocks(content);

    expect(result).not.toContain('PCE-SPEC-2025-0001-Z');
    expect(result).toContain('[link](PCE-SPEC-2025-0002-A)');
  });

  it('空のコードブロックを処理する（行番号維持のため改行は保持）', () => {
    const content = `\`\`\`
\`\`\``;

    const result = removeCodeBlocks(content);

    // 空のコードブロックは1行のため、1つの改行が保持される
    expect(result).toBe('\n');
  });
});

describe('buildDocIdPattern', () => {
  // ヘルパー関数: グローバルフラグ付きRegExpのテスト用
  // lastIndexをリセットしてからテスト
  function testPattern(pattern: RegExp, input: string): boolean {
    pattern.lastIndex = 0;
    return pattern.test(input);
  }

  it('設定からdoc_idパターンを生成する', () => {
    const config = createTestConfig();
    const pattern = buildDocIdPattern(config);

    // 有効なdoc_idにマッチする
    expect(testPattern(pattern, 'PCE-SPEC-2025-0001-Z')).toBe(true);
    expect(testPattern(pattern, 'BACK-DES-2024-0123-H')).toBe(true);
    expect(testPattern(pattern, 'GW-MEMO-2025-9999-A')).toBe(true);

    // 無効なdoc_idにはマッチしない
    expect(testPattern(pattern, 'INVALID-ID')).toBe(false);
    expect(testPattern(pattern, 'PCE-SPEC')).toBe(false);
    expect(testPattern(pattern, 'PCE-SPEC-2025-0001')).toBe(false);
  });

  it('enumの値を正しく処理する', () => {
    const config = createTestConfig({
      dimensions: {
        COMP: { type: 'enum', values: ['A', 'B', 'C'] },
        KIND: { type: 'enum', values: ['X', 'Y'] },
        YEAR4: { type: 'year', digits: 4, source: 'created_at' },
        SER4: { type: 'serial', digits: 4, scope: ['COMP'] },
        CHK1: { type: 'checksum', algo: 'mod26AZ', of: ['COMP'] },
      },
    });
    const pattern = buildDocIdPattern(config);

    expect(testPattern(pattern, 'A-X-2025-0001-Z')).toBe(true);
    expect(testPattern(pattern, 'B-Y-2025-0001-Z')).toBe(true);
    expect(testPattern(pattern, 'D-X-2025-0001-Z')).toBe(false); // D is not in enum
  });
});

describe('extractMarkdownLinks', () => {
  it('Markdownリンクからdoc_id参照を抽出する', () => {
    const config = createTestConfig();
    const pattern = buildDocIdPattern(config);
    const content = `
# Document

See [specification](PCE-SPEC-2025-0001-Z) for details.
Also check [design doc](BACK-DES-2024-0123-H).
`;

    const refs = extractMarkdownLinks(content, 'docs/test.md', pattern);

    expect(refs).toHaveLength(2);
    expect(refs[0]).toEqual({
      sourcePath: 'docs/test.md',
      targetDocId: 'PCE-SPEC-2025-0001-Z',
      kind: 'markdown_link',
      lineNumber: 4,
    });
    expect(refs[1]).toEqual({
      sourcePath: 'docs/test.md',
      targetDocId: 'BACK-DES-2024-0123-H',
      kind: 'markdown_link',
      lineNumber: 5,
    });
  });

  it('コードブロック内のリンクを除外する', () => {
    const config = createTestConfig();
    const pattern = buildDocIdPattern(config);
    const content = `
# Document

See [specification](PCE-SPEC-2025-0001-Z) for details.

\`\`\`markdown
Example: [link](PCE-SPEC-2025-0002-A)
\`\`\`

After code block.
`;

    const refs = extractMarkdownLinks(content, 'docs/test.md', pattern);

    expect(refs).toHaveLength(1);
    expect(refs[0]?.targetDocId).toBe('PCE-SPEC-2025-0001-Z');
  });

  it('通常のURLはdoc_idとして抽出しない', () => {
    const config = createTestConfig();
    const pattern = buildDocIdPattern(config);
    const content = `
[Google](https://google.com)
[GitHub](https://github.com/CAPHTECH/shirushi)
[valid doc](PCE-SPEC-2025-0001-Z)
`;

    const refs = extractMarkdownLinks(content, 'docs/test.md', pattern);

    expect(refs).toHaveLength(1);
    expect(refs[0]?.targetDocId).toBe('PCE-SPEC-2025-0001-Z');
  });
});

describe('extractYamlFieldReferences', () => {
  it('YAMLフィールドからdoc_id参照を抽出する', () => {
    const config = createTestConfig();
    const pattern = buildDocIdPattern(config);
    const metadata = {
      superseded_by: 'PCE-SPEC-2025-0001-Z',
      related_docs: ['BACK-DES-2024-0123-H', 'GW-MEMO-2025-0001-A'],
    };

    const refs = extractYamlFieldReferences(
      metadata,
      'docs/test.md',
      config.reference_fields,
      pattern
    );

    expect(refs).toHaveLength(3);
    expect(refs[0]).toEqual({
      sourcePath: 'docs/test.md',
      targetDocId: 'PCE-SPEC-2025-0001-Z',
      kind: 'yaml_field',
      fieldName: 'superseded_by',
    });
    expect(refs[1]).toEqual({
      sourcePath: 'docs/test.md',
      targetDocId: 'BACK-DES-2024-0123-H',
      kind: 'yaml_field',
      fieldName: 'related_docs',
    });
    expect(refs[2]).toEqual({
      sourcePath: 'docs/test.md',
      targetDocId: 'GW-MEMO-2025-0001-A',
      kind: 'yaml_field',
      fieldName: 'related_docs',
    });
  });

  it('参照フィールドが存在しない場合は空配列を返す', () => {
    const config = createTestConfig();
    const pattern = buildDocIdPattern(config);
    const metadata = {
      title: 'Test Document',
      description: 'Some description',
    };

    const refs = extractYamlFieldReferences(
      metadata,
      'docs/test.md',
      config.reference_fields,
      pattern
    );

    expect(refs).toHaveLength(0);
  });

  it('doc_idパターンにマッチしない値は無視する', () => {
    const config = createTestConfig();
    const pattern = buildDocIdPattern(config);
    const metadata = {
      superseded_by: 'not-a-doc-id',
      related_docs: ['also-invalid', 'PCE-SPEC-2025-0001-Z'],
    };

    const refs = extractYamlFieldReferences(
      metadata,
      'docs/test.md',
      config.reference_fields,
      pattern
    );

    expect(refs).toHaveLength(1);
    expect(refs[0]?.targetDocId).toBe('PCE-SPEC-2025-0001-Z');
  });
});

describe('extractCustomPatternReferences', () => {
  it('カスタムパターンからdoc_id参照を抽出する', () => {
    const config = createTestConfig();
    const docIdPattern = buildDocIdPattern(config);
    const patterns: ReferencePattern[] = [
      { name: 'ref_tag', pattern: '@ref\\s+{DOC_ID}' },
    ];
    const content = `
# Document

@ref PCE-SPEC-2025-0001-Z
Some text here.
@ref BACK-DES-2024-0123-H
`;

    const refs = extractCustomPatternReferences(
      content,
      'docs/test.md',
      patterns,
      docIdPattern
    );

    expect(refs).toHaveLength(2);
    expect(refs[0]).toEqual({
      sourcePath: 'docs/test.md',
      targetDocId: 'PCE-SPEC-2025-0001-Z',
      kind: 'custom_pattern',
      lineNumber: 4,
      patternName: 'ref_tag',
    });
    expect(refs[1]).toEqual({
      sourcePath: 'docs/test.md',
      targetDocId: 'BACK-DES-2024-0123-H',
      kind: 'custom_pattern',
      lineNumber: 6,
      patternName: 'ref_tag',
    });
  });

  it('コードブロック内のマッチを除外する', () => {
    const config = createTestConfig();
    const docIdPattern = buildDocIdPattern(config);
    const patterns: ReferencePattern[] = [
      { name: 'ref_tag', pattern: '@ref\\s+{DOC_ID}' },
    ];
    const content = `
@ref PCE-SPEC-2025-0001-Z

\`\`\`
@ref PCE-SPEC-2025-0002-A
\`\`\`
`;

    const refs = extractCustomPatternReferences(
      content,
      'docs/test.md',
      patterns,
      docIdPattern
    );

    expect(refs).toHaveLength(1);
    expect(refs[0]?.targetDocId).toBe('PCE-SPEC-2025-0001-Z');
  });

  it('無効なパターンをスキップする', () => {
    const config = createTestConfig();
    const docIdPattern = buildDocIdPattern(config);
    const patterns: ReferencePattern[] = [
      { name: 'invalid', pattern: '[invalid regex(' }, // 無効な正規表現
      { name: 'valid', pattern: '@ref\\s+{DOC_ID}' },
    ];
    const content = `@ref PCE-SPEC-2025-0001-Z`;

    const refs = extractCustomPatternReferences(
      content,
      'docs/test.md',
      patterns,
      docIdPattern
    );

    // 有効なパターンのみ処理される
    expect(refs).toHaveLength(1);
    expect(refs[0]?.patternName).toBe('valid');
  });
});
