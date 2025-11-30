/**
 * Template Parser Unit Tests
 *
 * id_format テンプレートから正規表現とプレースホルダー情報を
 * 生成するパーサーのテスト。TDD: テスト先行で実装。
 */

import { isRight, isLeft } from 'fp-ts/Either';
import { describe, it, expect } from 'vitest';

import { parseTemplate } from '@/parsers/template';

describe('parseTemplate', () => {
  describe('正常系: 基本的なテンプレート解析', () => {
    it('単一プレースホルダーを解析できる', () => {
      const result = parseTemplate('{COMP}', {
        COMP: { type: 'enum', values: ['PCE', 'BACK'] },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.placeholders).toHaveLength(1);
        expect(result.right.placeholders[0].name).toBe('COMP');
        expect(result.right.placeholders[0].position).toBe(0);
      }
    });

    it('複数プレースホルダーを順序保持で解析できる', () => {
      const result = parseTemplate('{COMP}-{KIND}-{YEAR4}', {
        COMP: { type: 'enum', values: ['PCE'] },
        KIND: { type: 'enum', values: ['SPEC'] },
        YEAR4: { type: 'year', digits: 4, source: 'created_at' },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.placeholders).toHaveLength(3);
        expect(result.right.placeholders[0].name).toBe('COMP');
        expect(result.right.placeholders[1].name).toBe('KIND');
        expect(result.right.placeholders[2].name).toBe('YEAR4');
      }
    });

    it('リテラルセパレーターを抽出できる', () => {
      const result = parseTemplate('{COMP}-{KIND}_{YEAR4}', {
        COMP: { type: 'enum', values: ['PCE'] },
        KIND: { type: 'enum', values: ['SPEC'] },
        YEAR4: { type: 'year', digits: 4, source: 'created_at' },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // リテラル: "", "-", "_", ""
        expect(result.right.literalSegments).toEqual(['', '-', '_', '']);
      }
    });
  });

  describe('正常系: 正規表現パターン生成', () => {
    it('enumから選択肢の正規表現を生成できる', () => {
      const result = parseTemplate('{COMP}', {
        COMP: { type: 'enum', values: ['PCE', 'BACK', 'GW'] },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.pattern.test('PCE')).toBe(true);
        expect(result.right.pattern.test('BACK')).toBe(true);
        expect(result.right.pattern.test('INVALID')).toBe(false);
      }
    });

    it('yearから桁数の正規表現を生成できる', () => {
      const result = parseTemplate('{YEAR4}', {
        YEAR4: { type: 'year', digits: 4, source: 'created_at' },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.pattern.test('2025')).toBe(true);
        expect(result.right.pattern.test('999')).toBe(false);
        expect(result.right.pattern.test('20255')).toBe(false);
      }
    });

    it('serialから桁数の正規表現を生成できる', () => {
      const result = parseTemplate('{SER4}', {
        SER4: { type: 'serial', digits: 4, scope: [] },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.pattern.test('0001')).toBe(true);
        expect(result.right.pattern.test('9999')).toBe(true);
        expect(result.right.pattern.test('001')).toBe(false);
      }
    });

    it('checksumから1文字A-Zの正規表現を生成できる', () => {
      const result = parseTemplate('{CHK1}', {
        CHK1: { type: 'checksum', algo: 'mod26AZ', of: ['COMP'] },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.pattern.test('A')).toBe(true);
        expect(result.right.pattern.test('Z')).toBe(true);
        expect(result.right.pattern.test('a')).toBe(false);
        expect(result.right.pattern.test('1')).toBe(false);
      }
    });

    it('完全なID形式の正規表現を生成できる', () => {
      const result = parseTemplate('{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}', {
        COMP: { type: 'enum', values: ['PCE', 'BACK'] },
        KIND: { type: 'enum', values: ['SPEC', 'DES'] },
        YEAR4: { type: 'year', digits: 4, source: 'created_at' },
        SER4: { type: 'serial', digits: 4, scope: ['COMP', 'KIND', 'YEAR4'] },
        CHK1: { type: 'checksum', algo: 'mod26AZ', of: ['COMP', 'KIND', 'YEAR4', 'SER4'] },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.pattern.test('PCE-SPEC-2025-0001-G')).toBe(true);
        expect(result.right.pattern.test('BACK-DES-2024-0123-Z')).toBe(true);
        expect(result.right.pattern.test('INVALID')).toBe(false);
        expect(result.right.pattern.test('PCE-SPEC-2025-0001')).toBe(false); // チェックサムなし
      }
    });
  });

  describe('正常系: キャプチャグループによる値抽出', () => {
    it('各プレースホルダーの値を抽出できる', () => {
      const result = parseTemplate('{COMP}-{KIND}-{YEAR4}', {
        COMP: { type: 'enum', values: ['PCE'] },
        KIND: { type: 'enum', values: ['SPEC'] },
        YEAR4: { type: 'year', digits: 4, source: 'created_at' },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        const match = result.right.pattern.exec('PCE-SPEC-2025');
        expect(match).not.toBeNull();
        if (match) {
          expect(match[1]).toBe('PCE');
          expect(match[2]).toBe('SPEC');
          expect(match[3]).toBe('2025');
        }
      }
    });
  });

  describe('正常系: enum_from_doc_type', () => {
    it('mapping値から正規表現を生成できる', () => {
      const result = parseTemplate('{KIND}', {
        KIND: {
          type: 'enum_from_doc_type',
          mapping: { spec: 'SPEC', design: 'DES', memo: 'MEMO' },
        },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.pattern.test('SPEC')).toBe(true);
        expect(result.right.pattern.test('DES')).toBe(true);
        expect(result.right.pattern.test('MEMO')).toBe(true);
        expect(result.right.pattern.test('INVALID')).toBe(false);
      }
    });
  });

  describe('異常系: 不正なテンプレート', () => {
    it('空のテンプレートでエラーを返す', () => {
      const result = parseTemplate('', {});

      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('INVALID_TEMPLATE');
      }
    });

    it('プレースホルダーのないテンプレートでエラーを返す', () => {
      const result = parseTemplate('STATIC-ID', {});

      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('INVALID_TEMPLATE');
      }
    });

    it('閉じていないブレースでエラーを返す', () => {
      const result = parseTemplate('{COMP', {
        COMP: { type: 'enum', values: ['PCE'] },
      });

      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('INVALID_TEMPLATE');
      }
    });

    it('未定義のdimensionでエラーを返す', () => {
      const result = parseTemplate('{COMP}-{UNDEFINED}', {
        COMP: { type: 'enum', values: ['PCE'] },
        // UNDEFINEDは未定義
      });

      expect(isLeft(result)).toBe(true);
      if (isLeft(result)) {
        expect(result.left.code).toBe('UNDEFINED_DIMENSION');
      }
    });
  });

  describe('エッジケース', () => {
    it('特殊文字を含むリテラルをエスケープする', () => {
      const result = parseTemplate('{COMP}.{KIND}', {
        COMP: { type: 'enum', values: ['PCE'] },
        KIND: { type: 'enum', values: ['SPEC'] },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        // "." は正規表現でエスケープされるべき
        expect(result.right.pattern.test('PCE.SPEC')).toBe(true);
        expect(result.right.pattern.test('PCExSPEC')).toBe(false); // "."が任意文字にマッチしない
      }
    });

    it('連続するプレースホルダーを処理できる', () => {
      const result = parseTemplate('{COMP}{KIND}', {
        COMP: { type: 'enum', values: ['PCE'] },
        KIND: { type: 'enum', values: ['SPEC'] },
      });

      expect(isRight(result)).toBe(true);
      if (isRight(result)) {
        expect(result.right.pattern.test('PCESPEC')).toBe(true);
      }
    });
  });
});
