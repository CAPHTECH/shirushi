/**
 * Serial Dimension Handler
 *
 * 連番を表すdimensionのハンドラ。
 * 例: SER4（4桁の連番）
 *
 * 仕様:
 * - digits: シリアル値の桁数（ゼロパディング）
 * - scope: 連番のカウンタを分ける単位となる他部品のリスト
 *
 * Note: v0.1では桁数検証のみ。scope検証はindex参照が必要なためv0.2以降。
 */

import { type Either, left, right } from 'fp-ts/Either';

import type {
  DimensionHandler,
  ValidationContext,
  GenerationContext,
  ValidationError,
  GenerationError,
} from './base';
import type { SerialDimensionSchema } from '@/config/schema';
import type { z } from 'zod';

// SerialDimension型
export type SerialDimension = z.infer<typeof SerialDimensionSchema>;

/**
 * Serial Dimension Handler
 */
export class SerialHandler implements DimensionHandler<SerialDimension> {
  /**
   * serial値を検証
   *
   * 検証項目:
   * 1. 指定桁数の数字であるか
   * 2. 0より大きいか（0000は無効）
   *
   * Note: scope内での一意性検証はindex参照が必要なため、
   *       core/validator.tsで別途実施
   */
  validate(
    value: string,
    dimension: SerialDimension,
    context: ValidationContext
  ): Either<ValidationError, true> {
    // 1. 桁数チェック
    const digitPattern = new RegExp(`^\\d{${dimension.digits}}$`);
    if (!digitPattern.test(value)) {
      return left({
        code: 'INVALID_SERIAL_VALUE',
        message: `Serial value "${value}" must be ${dimension.digits} digits`,
        dimensionName: context.dimensionName,
        value,
        expected: `${dimension.digits} digit number`,
      });
    }

    // 2. 0より大きいかチェック（0000は無効）
    const serialNum = parseInt(value, 10);
    if (serialNum <= 0) {
      return left({
        code: 'INVALID_SERIAL_VALUE',
        message: `Serial value "${value}" must be greater than 0`,
        dimensionName: context.dimensionName,
        value,
        expected: 'positive number',
      });
    }

    // 3. 最大値チェック
    const maxValue = Math.pow(10, dimension.digits) - 1;
    if (serialNum > maxValue) {
      return left({
        code: 'INVALID_SERIAL_VALUE',
        message: `Serial value "${value}" exceeds maximum (${maxValue})`,
        dimensionName: context.dimensionName,
        value,
        expected: `1-${maxValue}`,
      });
    }

    return right(true);
  }

  /**
   * serial値を生成
   *
   * Note: 実際の採番はindex参照が必要。
   *       ここでは暫定的に0001を返す。
   *       v0.2のassignコマンドで実装予定。
   */
  generate(
    dimension: SerialDimension,
    _context: GenerationContext
  ): Either<GenerationError, string> {
    // TODO: v0.2でindex参照による採番を実装
    // 暫定的に0001を返す
    const serial = '1'.padStart(dimension.digits, '0');
    return right(serial);
  }

  /**
   * 正規表現パターンを生成
   *
   * @returns (\d{digits}) 形式のパターン
   */
  toPattern(dimension: SerialDimension): string {
    return `(\\d{${dimension.digits}})`;
  }
}
