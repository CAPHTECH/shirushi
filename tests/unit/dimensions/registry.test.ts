/**
 * Dimension Registry Unit Tests
 *
 * dimensionハンドラのレジストリ機能のテスト。
 */

import { describe, it, expect } from 'vitest';

import {
  DimensionRegistry,
  getDimensionRegistry,
  dimensionToPattern,
  EnumHandler,
  YearHandler,
  SerialHandler,
  ChecksumHandler,
  EnumFromDocTypeHandler,
} from '@/dimensions';

describe('DimensionRegistry', () => {
  describe('constructor', () => {
    it('デフォルトハンドラを登録する', () => {
      const registry = new DimensionRegistry();

      expect(registry.has('enum')).toBe(true);
      expect(registry.has('enum_from_doc_type')).toBe(true);
      expect(registry.has('year')).toBe(true);
      expect(registry.has('serial')).toBe(true);
      expect(registry.has('checksum')).toBe(true);
    });
  });

  describe('get', () => {
    it('登録されたハンドラを取得する', () => {
      const registry = new DimensionRegistry();

      expect(registry.get('enum')).toBeInstanceOf(EnumHandler);
      expect(registry.get('year')).toBeInstanceOf(YearHandler);
      expect(registry.get('serial')).toBeInstanceOf(SerialHandler);
      expect(registry.get('checksum')).toBeInstanceOf(ChecksumHandler);
      expect(registry.get('enum_from_doc_type')).toBeInstanceOf(EnumFromDocTypeHandler);
    });

    it('未登録のtypeでエラーを投げる', () => {
      const registry = new DimensionRegistry();

      expect(() => {
        // @ts-expect-error - intentionally testing invalid type
        registry.get('unknown');
      }).toThrow('No handler registered for dimension type: unknown');
    });
  });

  describe('has', () => {
    it('登録済みtypeはtrueを返す', () => {
      const registry = new DimensionRegistry();

      expect(registry.has('enum')).toBe(true);
    });

    it('未登録typeはfalseを返す', () => {
      const registry = new DimensionRegistry();

      // @ts-expect-error - intentionally testing invalid type
      expect(registry.has('unknown')).toBe(false);
    });
  });

  describe('getRegisteredTypes', () => {
    it('全ての登録済みtype名を返す', () => {
      const registry = new DimensionRegistry();
      const types = registry.getRegisteredTypes();

      expect(types).toContain('enum');
      expect(types).toContain('enum_from_doc_type');
      expect(types).toContain('year');
      expect(types).toContain('serial');
      expect(types).toContain('checksum');
      expect(types).toHaveLength(5);
    });
  });

  describe('register', () => {
    it('カスタムハンドラを登録できる', () => {
      const registry = new DimensionRegistry();
      const customHandler = new EnumHandler();

      // 既存のenumハンドラを上書き
      registry.register('enum', customHandler);

      expect(registry.get('enum')).toBe(customHandler);
    });
  });
});

describe('getDimensionRegistry', () => {
  it('シングルトンインスタンスを返す', () => {
    const registry1 = getDimensionRegistry();
    const registry2 = getDimensionRegistry();

    expect(registry1).toBe(registry2);
  });

  it('全てのデフォルトハンドラが登録されている', () => {
    const registry = getDimensionRegistry();

    expect(registry.has('enum')).toBe(true);
    expect(registry.has('year')).toBe(true);
  });
});

describe('dimensionToPattern', () => {
  it('enum dimensionからパターンを生成する', () => {
    const pattern = dimensionToPattern({
      type: 'enum',
      values: ['PCE', 'KKS', 'EDGE'],
    });

    expect(pattern).toBe('(PCE|KKS|EDGE)');
  });

  it('year dimensionからパターンを生成する', () => {
    const pattern = dimensionToPattern({
      type: 'year',
      digits: 4,
      source: 'created_at',
    });

    expect(pattern).toBe('(\\d{4})');
  });

  it('serial dimensionからパターンを生成する', () => {
    const pattern = dimensionToPattern({
      type: 'serial',
      digits: 4,
      scope: ['COMP'],
    });

    expect(pattern).toBe('(\\d{4})');
  });

  it('checksum dimensionからパターンを生成する', () => {
    const pattern = dimensionToPattern({
      type: 'checksum',
      algo: 'mod26AZ',
      of: ['COMP'],
    });

    expect(pattern).toBe('([A-Z])');
  });

  it('enum_from_doc_type dimensionからパターンを生成する', () => {
    const pattern = dimensionToPattern({
      type: 'enum_from_doc_type',
      mapping: { spec: 'SPEC', design: 'DES' },
    });

    expect(pattern).toBe('(SPEC|DES)');
  });
});
