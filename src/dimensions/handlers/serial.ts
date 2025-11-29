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
 * v0.2: index参照による採番を実装
 *       スコープ内の最大シリアル + 1 を返す
 */

import { type Either, isLeft, left, right } from 'fp-ts/Either';

import { extractDimensionValues } from '@/parsers/template';

import type {
  DimensionHandler,
  ValidationContext,
  GenerationContext,
  ValidationError,
  GenerationError,
} from './base';
import type { SerialDimensionSchema } from '@/config/schema';
import type { IndexEntry } from '@/core/index-manager';
import type { TemplateParseResult } from '@/parsers/template';
import type { z } from 'zod';

// SerialDimension型
export type SerialDimension = z.infer<typeof SerialDimensionSchema>;

/**
 * スコープキーを構築
 *
 * scope で指定された dimension 名の値を otherParts から取得し、
 * ハイフンで連結してスコープキーを生成する。
 *
 * @param scope - スコープを構成するdimension名の配列
 * @param otherParts - 他のdimension値
 * @returns スコープキー、またはエラー
 */
function buildScopeKey(
  scope: string[],
  otherParts: Record<string, string>
): Either<GenerationError, string> {
  const parts: string[] = [];
  for (const dimName of scope) {
    const value = otherParts[dimName];
    if (value === undefined) {
      return left({
        code: 'MISSING_SCOPE_DIMENSION',
        message: `Missing scope dimension: ${dimName}`,
        dimensionName: dimName,
        context: { scope, availableParts: Object.keys(otherParts) },
      });
    }
    parts.push(value);
  }
  return right(parts.join('-'));
}

/**
 * スコープ内の既存シリアル番号を抽出
 *
 * インデックス内の各doc_idをテンプレートでパースし、
 * 対象スコープに属するエントリからシリアル番号を抽出する。
 *
 * @param indexEntries - インデックスエントリの配列
 * @param templateResult - テンプレート解析結果
 * @param scope - スコープを構成するdimension名の配列
 * @param targetScopeKey - 対象のスコープキー
 * @param serialDimensionName - シリアルdimensionの名前
 * @returns スコープ内のシリアル番号の配列
 */
function extractSerialsFromIndex(
  indexEntries: IndexEntry[],
  templateResult: TemplateParseResult,
  scope: string[],
  targetScopeKey: string,
  serialDimensionName: string
): number[] {
  const serials: number[] = [];

  for (const entry of indexEntries) {
    // doc_id をテンプレートでパース
    const values = extractDimensionValues(entry.doc_id, templateResult);
    if (!values) continue;

    // スコープキーを構築して比較
    const entryScopeKey = scope
      .map((dim) => values[dim])
      .filter((v): v is string => v !== undefined)
      .join('-');

    if (entryScopeKey !== targetScopeKey) continue;

    // シリアル値を抽出
    const serialStr = values[serialDimensionName];
    if (serialStr) {
      const num = parseInt(serialStr, 10);
      if (!isNaN(num) && num > 0) {
        serials.push(num);
      }
    }
  }

  return serials;
}

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
   * インデックスを参照してスコープ内の最大シリアル + 1 を返す。
   * インデックスが提供されていない場合は 0001 を返す。
   *
   * アルゴリズム:
   * 1. スコープキーを構築（scope dimensionの値を連結）
   * 2. インデックス内のdoc_idをパースしてスコープ内シリアルを抽出
   * 3. max + 1 を計算
   * 4. オーバーフローチェック
   * 5. ゼロパディングして返す
   */
  generate(
    dimension: SerialDimension,
    context: GenerationContext
  ): Either<GenerationError, string> {
    // 1. スコープキーを構築
    const scopeKeyResult = buildScopeKey(dimension.scope, context.otherParts);
    if (isLeft(scopeKeyResult)) {
      return scopeKeyResult;
    }
    const scopeKey = scopeKeyResult.right;

    // 2. インデックスまたはテンプレートがない場合は 0001 を返す
    if (!context.indexEntries || !context.templateResult) {
      return right('1'.padStart(dimension.digits, '0'));
    }

    // 3. スコープ内の既存シリアル番号を抽出
    const existingSerials = extractSerialsFromIndex(
      context.indexEntries,
      context.templateResult,
      dimension.scope,
      scopeKey,
      context.dimensionName
    );

    // 4. 次のシリアルを計算 (max + 1)
    // Note: Math.max(...[]) は -Infinity を返すため、length > 0 のガードが必須
    const maxSerial =
      existingSerials.length > 0 ? Math.max(...existingSerials) : 0;
    const nextSerial = maxSerial + 1;

    // 5. オーバーフローチェック
    const maxValue = Math.pow(10, dimension.digits) - 1;
    if (nextSerial > maxValue) {
      return left({
        code: 'SERIAL_OVERFLOW',
        message: `Serial overflow: ${nextSerial} exceeds max ${maxValue}`,
        dimensionName: context.dimensionName,
        context: { maxSerial, nextSerial, maxValue, scopeKey },
      });
    }

    // 6. ゼロパディングして返す
    return right(String(nextSerial).padStart(dimension.digits, '0'));
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
