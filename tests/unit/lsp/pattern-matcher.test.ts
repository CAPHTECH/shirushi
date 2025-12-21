/**
 * Pattern Matcher Tests
 *
 * LSP用のdoc_idパターンマッチングのテスト
 *
 * @see ADR-0010: LSP Server Integration
 */

import { describe, it, expect } from 'vitest';

import {
  expandDocIdPattern,
  findDocIdMatchesInLine,
  findAllDocIdMatches,
  findDocIdAtPosition,
  getSourceRefPatterns,
} from '@/lsp/utils/pattern-matcher';

import type { ShirushiConfig } from '@/config/schema';

/**
 * テスト用の最小設定を作成
 */
function createTestConfig(overrides: Partial<ShirushiConfig> = {}): ShirushiConfig {
  return {
    id_format: '{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}',
    doc_globs: ['docs/**/*.md'],
    dimensions: {
      COMP: {
        type: 'enum',
        values: ['SHI', 'PCE', 'API'],
      },
      KIND: {
        type: 'enum',
        values: ['SPEC', 'ADR', 'GUIDE'],
      },
      YEAR4: {
        type: 'year',
        digits: 4,
      },
      SER4: {
        type: 'serial',
        digits: 4,
        scope: ['COMP', 'KIND'],
      },
      CHK1: {
        type: 'checksum',
        digits: 1,
        algorithm: 'mod26AZ',
        source: ['COMP', 'KIND', 'YEAR4', 'SER4'],
      },
    },
    index_file: 'docs/doc_index.yaml',
    forbid_id_change: true,
    allow_missing_id_in_new_files: false,
    serial_start: 1,
    ...overrides,
  };
}

describe('getSourceRefPatterns', () => {
  it('デフォルトパターンを返す（source_references未設定時）', () => {
    const config = createTestConfig();
    const patterns = getSourceRefPatterns(config);

    expect(patterns).toHaveLength(1);
    expect(patterns[0]).toContain('@see');
  });

  it('設定されたパターンを返す', () => {
    const config = createTestConfig({
      content_integrity: {
        enabled: true,
        source_references: [
          { glob: 'src/**/*.ts', pattern: '@see\\s+({DOC_ID})' },
          { glob: 'src/**/*.py', pattern: '#\\s+ref:\\s+({DOC_ID})' },
        ],
      },
    });
    const patterns = getSourceRefPatterns(config);

    expect(patterns).toHaveLength(2);
    expect(patterns[0]).toContain('@see');
    expect(patterns[1]).toContain('ref:');
  });
});

describe('expandDocIdPattern', () => {
  it('{DOC_ID}プレースホルダーを正規表現に展開する', () => {
    const config = createTestConfig();
    const regex = expandDocIdPattern('@see\\s+({DOC_ID})', config);

    expect(regex).not.toBeNull();
    expect(regex!.source).toContain('SHI|PCE|API');
  });

  it('展開された正規表現がdoc_idにマッチする', () => {
    const config = createTestConfig();
    const regex = expandDocIdPattern('@see\\s+({DOC_ID})', config);

    expect(regex).not.toBeNull();

    const match = regex!.exec('@see SHI-SPEC-2025-0001-G');
    expect(match).not.toBeNull();
    expect(match![1]).toBe('SHI-SPEC-2025-0001-G');
  });
});

describe('findDocIdMatchesInLine', () => {
  it('行内のdoc_idマッチを検出する', () => {
    const config = createTestConfig();
    const regex = expandDocIdPattern('@see\\s+({DOC_ID})', config);

    expect(regex).not.toBeNull();

    const matches = findDocIdMatchesInLine(
      '// @see SHI-SPEC-2025-0001-G このドキュメントを参照',
      0,
      [regex!]
    );

    expect(matches).toHaveLength(1);
    expect(matches[0]!.docId).toBe('SHI-SPEC-2025-0001-G');
    expect(matches[0]!.line).toBe(0);
  });

  it('複数のマッチを検出する', () => {
    const config = createTestConfig();
    const regex = expandDocIdPattern('@see\\s+({DOC_ID})', config);

    expect(regex).not.toBeNull();

    const matches = findDocIdMatchesInLine(
      '// @see SHI-SPEC-2025-0001-G @see PCE-ADR-2025-0002-H',
      5,
      [regex!]
    );

    expect(matches).toHaveLength(2);
    expect(matches[0]!.docId).toBe('SHI-SPEC-2025-0001-G');
    expect(matches[1]!.docId).toBe('PCE-ADR-2025-0002-H');
    expect(matches[0]!.line).toBe(5);
  });

  it('マッチがない場合は空配列を返す', () => {
    const config = createTestConfig();
    const regex = expandDocIdPattern('@see\\s+({DOC_ID})', config);

    expect(regex).not.toBeNull();

    const matches = findDocIdMatchesInLine(
      '// 普通のコメント',
      0,
      [regex!]
    );

    expect(matches).toHaveLength(0);
  });
});

describe('findAllDocIdMatches', () => {
  it('複数行のテキストからすべてのマッチを検出する', () => {
    const config = createTestConfig();

    const text = `
/**
 * 認証モジュール
 * @see SHI-SPEC-2025-0001-G
 */
function authenticate() {
  // @see PCE-ADR-2025-0002-H
}
`;

    const matches = findAllDocIdMatches(text, config);

    expect(matches).toHaveLength(2);
    expect(matches[0]!.docId).toBe('SHI-SPEC-2025-0001-G');
    expect(matches[1]!.docId).toBe('PCE-ADR-2025-0002-H');
  });
});

describe('findDocIdAtPosition', () => {
  const config = createTestConfig();

  it('カーソル位置にあるdoc_idを検出する', () => {
    const text = '// @see SHI-SPEC-2025-0001-G';
    //            0123456789012345678901234567

    // doc_idの開始位置（S）
    const match = findDocIdAtPosition(
      text,
      { line: 0, character: 8 },
      config
    );

    expect(match).not.toBeNull();
    expect(match!.docId).toBe('SHI-SPEC-2025-0001-G');
  });

  it('doc_idの途中にカーソルがある場合も検出する', () => {
    const text = '// @see SHI-SPEC-2025-0001-G';

    // doc_idの中間位置
    const match = findDocIdAtPosition(
      text,
      { line: 0, character: 15 },
      config
    );

    expect(match).not.toBeNull();
    expect(match!.docId).toBe('SHI-SPEC-2025-0001-G');
  });

  it('doc_id外にカーソルがある場合はnullを返す', () => {
    const text = '// @see SHI-SPEC-2025-0001-G';

    // コメント記号の位置
    const match = findDocIdAtPosition(
      text,
      { line: 0, character: 0 },
      config
    );

    expect(match).toBeNull();
  });

  it('複数行テキストで正しい行を検出する', () => {
    const text = `line 0
// @see SHI-SPEC-2025-0001-G
line 2`;

    const match = findDocIdAtPosition(
      text,
      { line: 1, character: 10 },
      config
    );

    expect(match).not.toBeNull();
    expect(match!.docId).toBe('SHI-SPEC-2025-0001-G');
    expect(match!.line).toBe(1);
  });
});
