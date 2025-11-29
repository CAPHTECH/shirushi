/**
 * Year Dimension Handler
 *
 * 年を表すdimensionのハンドラ。
 * 例: YEAR4（4桁の年）
 *
 * 仕様:
 * - digits: 年を表す桁数（通常4）
 * - source: "created_at" または "now"
 */

import { type Either, left, right } from 'fp-ts/Either';

import type {
  DimensionHandler,
  ValidationContext,
  GenerationContext,
  ValidationError,
  GenerationError,
} from './base';
import type { YearDimensionSchema } from '@/config/schema';
import type { z } from 'zod';

// YearDimension型
export type YearDimension = z.infer<typeof YearDimensionSchema>;

// source type for year dimension
type YearSource = 'created_at' | 'now';

/**
 * Year Dimension Handler
 */
export class YearHandler implements DimensionHandler<YearDimension> {
  /**
   * year値を検証
   *
   * 検証項目:
   * 1. 指定桁数の数字であるか
   * 2. 有効な年の範囲内か（1000-9999 for 4桁）
   */
  validate(
    value: string,
    dimension: YearDimension,
    context: ValidationContext
  ): Either<ValidationError, true> {
    // 1. 桁数チェック
    const digitPattern = new RegExp(`^\\d{${dimension.digits}}$`);
    if (!digitPattern.test(value)) {
      return left({
        code: 'INVALID_YEAR_VALUE',
        message: `Year value "${value}" must be ${dimension.digits} digits`,
        dimensionName: context.dimensionName,
        value,
        expected: `${dimension.digits} digit number`,
      });
    }

    // 2. 有効な年の範囲（オプション: 厳密な検証）
    const yearNum = parseInt(value, 10);
    const minYear = Math.pow(10, dimension.digits - 1); // 4桁なら1000
    const maxYear = Math.pow(10, dimension.digits) - 1; // 4桁なら9999

    if (yearNum < minYear || yearNum > maxYear) {
      return left({
        code: 'INVALID_YEAR_VALUE',
        message: `Year value "${value}" is out of valid range (${minYear}-${maxYear})`,
        dimensionName: context.dimensionName,
        value,
        expected: `${minYear}-${maxYear}`,
      });
    }

    return right(true);
  }

  /**
   * year値を生成
   *
   * 生成ロジック:
   * 1. source: "created_at" → メタデータから取得
   * 2. source: "now" → 現在年を使用
   */
  generate(
    dimension: YearDimension,
    context: GenerationContext
  ): Either<GenerationError, string> {
    // 現在時刻を一度だけ取得（年境界でのレースコンディション防止）
    const now = new Date();
    let year: number;

    const source = dimension.source as YearSource;
    if (source === 'created_at') {
      // メタデータから取得を試みる
      const createdAt = context.documentMeta['created_at'];
      if (createdAt && typeof createdAt === 'string') {
        const date = new Date(createdAt);
        if (!isNaN(date.getTime())) {
          year = date.getFullYear();
        } else {
          // パースできない場合は現在年にフォールバック
          year = now.getFullYear();
        }
      } else {
        // メタデータがない場合は現在年にフォールバック
        year = now.getFullYear();
      }
    } else {
      // source: "now" または未指定
      year = now.getFullYear();
    }

    // 指定桁数にパディング
    const yearStr = String(year).padStart(dimension.digits, '0');

    // 桁数を超える場合は下位桁を使用
    if (yearStr.length > dimension.digits) {
      return right(yearStr.slice(-dimension.digits));
    }

    return right(yearStr);
  }

  /**
   * 正規表現パターンを生成
   *
   * @returns (\d{digits}) 形式のパターン
   */
  toPattern(dimension: YearDimension): string {
    return `(\\d{${dimension.digits}})`;
  }
}
