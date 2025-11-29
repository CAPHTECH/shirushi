/**
 * Enum Dimension Handler
 *
 * 固定された候補集合から値をとるdimensionのハンドラ。
 * 例: COMP（コンポーネント名）など。
 *
 * 仕様:
 * - values: 取りうる文字列の列挙
 * - select.by_path: パスパターンによる値の自動選択（オプション）
 */

import { type Either, left, right } from 'fp-ts/Either';
import { minimatch } from 'minimatch';

import { escapeRegex } from '@/utils/regex';

import type {
  DimensionHandler,
  ValidationContext,
  GenerationContext,
  ValidationError,
  GenerationError,
} from './base';
import type { EnumDimensionSchema } from '@/config/schema';
import type { z } from 'zod';

// EnumDimension型
export type EnumDimension = z.infer<typeof EnumDimensionSchema>;

/**
 * Enum Dimension Handler
 */
export class EnumHandler implements DimensionHandler<EnumDimension> {
  /**
   * enum値を検証
   *
   * 検証項目:
   * 1. 値がvaluesに含まれているか
   * 2. select.by_pathがある場合、パスマッチした値と一致するか
   */
  validate(
    value: string,
    dimension: EnumDimension,
    context: ValidationContext
  ): Either<ValidationError, true> {
    // 1. values内に存在するか
    if (!dimension.values.includes(value)) {
      return left({
        code: 'INVALID_DIMENSION_VALUE',
        message: `Value "${value}" is not in allowed values: [${dimension.values.join(', ')}]`,
        dimensionName: context.dimensionName,
        value,
        expected: dimension.values.join(' | '),
      });
    }

    // 2. select.by_pathがある場合、パスマッチを検証
    if (dimension.select?.by_path) {
      for (const rule of dimension.select.by_path) {
        // グロブパターンでマッチ
        if (minimatch(context.documentPath, rule.pattern)) {
          if (rule.value !== value) {
            return left({
              code: 'DIMENSION_MISMATCH',
              message: `Path "${context.documentPath}" requires value "${rule.value}", but got "${value}"`,
              dimensionName: context.dimensionName,
              value,
              expected: rule.value,
              context: { path: context.documentPath, pattern: rule.pattern },
            });
          }
          // マッチして値も一致 → OK
          break;
        }
      }
    }

    return right(true);
  }

  /**
   * enum値を生成
   *
   * 生成ロジック:
   * 1. select.by_pathがある場合、パスマッチした値を返す
   * 2. なければ最初のvalueを返す
   */
  generate(
    dimension: EnumDimension,
    context: GenerationContext
  ): Either<GenerationError, string> {
    // select.by_pathがある場合、パスマッチを試みる
    if (dimension.select?.by_path) {
      for (const rule of dimension.select.by_path) {
        if (minimatch(context.documentPath, rule.pattern)) {
          return right(rule.value);
        }
      }
    }

    // デフォルト: 最初のvalueを返す
    if (dimension.values.length > 0) {
      const firstValue = dimension.values[0];
      if (firstValue !== undefined) {
        return right(firstValue);
      }
    }

    return left({
      code: 'INVALID_DIMENSION_VALUE',
      message: 'No values defined for enum dimension',
      dimensionName: context.dimensionName,
    });
  }

  /**
   * 正規表現パターンを生成
   *
   * @returns (value1|value2|...) 形式のパターン
   */
  toPattern(dimension: EnumDimension): string {
    const escaped = dimension.values.map(escapeRegex);
    return `(${escaped.join('|')})`;
  }
}
