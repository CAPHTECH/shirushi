/**
 * Checksum Dimension Handler
 *
 * 他の複数部品の値から計算されたチェックサム文字のハンドラ。
 * 例: CHK1
 *
 * 仕様:
 * - algo: チェックサムアルゴリズム（現在は "mod26AZ" のみ）
 * - of: チェックサム計算の対象となる部品名の配列
 */

import { type Either, left, right } from 'fp-ts/Either';

import type {
  DimensionHandler,
  ValidationContext,
  GenerationContext,
  ValidationError,
  GenerationError,
} from './base';
import type { ChecksumDimensionSchema } from '@/config/schema';
import type { z } from 'zod';

// ChecksumDimension型
export type ChecksumDimension = z.infer<typeof ChecksumDimensionSchema>;

/**
 * mod26AZ チェックサムアルゴリズム
 *
 * 仕様書5.5より:
 * 対象文字列の各文字のASCII値を合計し、26で割った余りを
 * A-Z（65-90）に対応させる。
 *
 * @param input - チェックサム計算対象の文字列
 * @returns A-Zの1文字
 */
export function mod26AZ(input: string): string {
  const sum = input.split('').reduce((acc, char) => acc + char.charCodeAt(0), 0);
  return String.fromCharCode(65 + (sum % 26));
}

/**
 * Checksum Dimension Handler
 */
export class ChecksumHandler implements DimensionHandler<ChecksumDimension> {
  /**
   * checksum値を検証
   *
   * 検証項目:
   * 1. 値がA-Zの1文字であるか
   * 2. of部品を連結して計算したchecksumと一致するか
   */
  validate(
    value: string,
    dimension: ChecksumDimension,
    context: ValidationContext
  ): Either<ValidationError, true> {
    // 1. A-Zの1文字であるか
    if (!/^[A-Z]$/.test(value)) {
      return left({
        code: 'INVALID_ID_CHECKSUM',
        message: `Checksum value "${value}" must be a single uppercase letter A-Z`,
        dimensionName: context.dimensionName,
        value,
        expected: 'A-Z',
      });
    }

    // 2. of部品を連結してチェックサムを計算
    const parts: string[] = [];
    for (const partName of dimension.of) {
      const partValue = context.parsedParts[partName];
      if (partValue === undefined) {
        return left({
          code: 'INVALID_ID_CHECKSUM',
          message: `Cannot compute checksum: missing part "${partName}"`,
          dimensionName: context.dimensionName,
          value,
          context: { missingPart: partName, availableParts: Object.keys(context.parsedParts) },
        });
      }
      parts.push(partValue);
    }

    // 対象文字列を連結（セパレーターなし）
    const input = parts.join('');

    // アルゴリズムに基づいて計算
    let expected: string;
    switch (dimension.algo) {
      case 'mod26AZ':
        expected = mod26AZ(input);
        break;
      default: {
        // 将来の拡張用: 不明なアルゴリズム
        const unknownAlgo: string = dimension.algo;
        return left({
          code: 'INVALID_ID_CHECKSUM',
          message: `Unknown checksum algorithm: "${unknownAlgo}"`,
          dimensionName: context.dimensionName,
          value,
          context: { algo: unknownAlgo },
        });
      }
    }

    // 3. 計算結果と一致するか
    if (value !== expected) {
      return left({
        code: 'INVALID_ID_CHECKSUM',
        message: `Checksum mismatch: expected "${expected}", got "${value}"`,
        dimensionName: context.dimensionName,
        value,
        expected,
        context: { input, parts },
      });
    }

    return right(true);
  }

  /**
   * checksum値を生成
   *
   * 生成ロジック:
   * 1. of部品をotherPartsから取得して連結
   * 2. algoに基づいてチェックサムを計算
   */
  generate(
    dimension: ChecksumDimension,
    context: GenerationContext
  ): Either<GenerationError, string> {
    // of部品を連結
    const parts: string[] = [];
    for (const partName of dimension.of) {
      const partValue = context.otherParts[partName];
      if (partValue === undefined) {
        return left({
          code: 'INVALID_ID_CHECKSUM',
          message: `Cannot compute checksum: missing part "${partName}"`,
          dimensionName: context.dimensionName,
          context: { missingPart: partName, availableParts: Object.keys(context.otherParts) },
        });
      }
      parts.push(partValue);
    }

    const input = parts.join('');

    // アルゴリズムに基づいて計算
    switch (dimension.algo) {
      case 'mod26AZ':
        return right(mod26AZ(input));
      default: {
        const unknownAlgo: string = dimension.algo;
        return left({
          code: 'INVALID_ID_CHECKSUM',
          message: `Unknown checksum algorithm: "${unknownAlgo}"`,
          dimensionName: context.dimensionName,
          context: { algo: unknownAlgo },
        });
      }
    }
  }

  /**
   * 正規表現パターンを生成
   *
   * @returns ([A-Z]) パターン（mod26AZは常に1文字A-Z）
   */
  toPattern(_dimension: ChecksumDimension): string {
    // mod26AZは常にA-Zの1文字
    return '([A-Z])';
  }
}
