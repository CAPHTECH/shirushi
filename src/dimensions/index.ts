/**
 * Dimension Handler Registry
 *
 * 各dimension type (enum, year, serial, checksum等) のハンドラを
 * 一元管理するレジストリ。
 *
 * 新しいdimension typeを追加する場合:
 * 1. handlers/に新しいハンドラを実装
 * 2. このファイルのregisterDefaultHandlers()に登録
 */

import { ChecksumHandler } from './handlers/checksum';
import { EnumHandler } from './handlers/enum';
import { EnumFromDocTypeHandler } from './handlers/enum-from-doc-type';
import { SerialHandler } from './handlers/serial';
import { YearHandler } from './handlers/year';

import type { DimensionHandler } from './handlers/base';
import type { DimensionDefinition } from '@/config/schema';


// Dimension型
type Dimension = DimensionDefinition;

/**
 * Dimension type名（discriminated unionのtype値）
 */
export type DimensionType = Dimension['type'];

/**
 * Dimension Handler Registry
 *
 * dimension type名からハンドラインスタンスを取得する。
 * シングルトンパターンでアプリケーション全体で共有。
 */
export class DimensionRegistry {
  private handlers = new Map<DimensionType, DimensionHandler>();

  constructor() {
    this.registerDefaultHandlers();
  }

  /**
   * デフォルトハンドラを登録
   */
  private registerDefaultHandlers(): void {
    this.register('enum', new EnumHandler());
    this.register('enum_from_doc_type', new EnumFromDocTypeHandler());
    this.register('year', new YearHandler());
    this.register('serial', new SerialHandler());
    this.register('checksum', new ChecksumHandler());
  }

  /**
   * ハンドラを登録
   *
   * @param type - dimension type名
   * @param handler - ハンドラインスタンス
   */
  register(type: DimensionType, handler: DimensionHandler): void {
    this.handlers.set(type, handler);
  }

  /**
   * ハンドラを取得
   *
   * @param type - dimension type名
   * @returns ハンドラインスタンス
   * @throws 未登録のtypeの場合
   */
  get(type: DimensionType): DimensionHandler {
    const handler = this.handlers.get(type);
    if (!handler) {
      throw new Error(`No handler registered for dimension type: ${type}`);
    }
    return handler;
  }

  /**
   * ハンドラが登録されているか確認
   *
   * @param type - dimension type名
   * @returns 登録されていればtrue
   */
  has(type: DimensionType): boolean {
    return this.handlers.has(type);
  }

  /**
   * 登録されている全てのtype名を取得
   */
  getRegisteredTypes(): DimensionType[] {
    return Array.from(this.handlers.keys());
  }
}

/**
 * デフォルトのレジストリインスタンス（シングルトン）
 */
let defaultRegistry: DimensionRegistry | null = null;

/**
 * デフォルトレジストリを取得
 *
 * @returns DimensionRegistryのシングルトンインスタンス
 */
export function getDimensionRegistry(): DimensionRegistry {
  if (!defaultRegistry) {
    defaultRegistry = new DimensionRegistry();
  }
  return defaultRegistry;
}

/**
 * dimension定義から正規表現パターンを生成
 *
 * @param dimension - dimension定義
 * @returns 正規表現パターン文字列
 */
export function dimensionToPattern(dimension: Dimension): string {
  const registry = getDimensionRegistry();
  const handler = registry.get(dimension.type);
  return handler.toPattern(dimension);
}

// Re-export handlers for direct access
export { EnumHandler } from './handlers/enum';
export { EnumFromDocTypeHandler } from './handlers/enum-from-doc-type';
export { YearHandler } from './handlers/year';
export { SerialHandler } from './handlers/serial';
export { ChecksumHandler, mod26AZ } from './handlers/checksum';

// Re-export types
export type {
  DimensionHandler,
  ValidationContext,
  GenerationContext,
  ValidationError,
  GenerationError,
} from './handlers/base';
