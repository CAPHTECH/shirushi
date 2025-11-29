/**
 * EnumFromDocType Dimension Handler
 *
 * ドキュメントのdoc_typeフィールドから派生するenum dimensionのハンドラ。
 * 例: KIND（ドキュメント種別コード）
 *
 * 仕様:
 * - mapping: doc_type → コード へのマッピング
 */

import { type Either, left, right } from 'fp-ts/Either';

import { escapeRegex } from '@/utils/regex';

import type {
  DimensionHandler,
  ValidationContext,
  GenerationContext,
  ValidationError,
  GenerationError,
} from './base';
import type { EnumFromDocTypeDimensionSchema } from '@/config/schema';
import type { z } from 'zod';

// EnumFromDocTypeDimension型
export type EnumFromDocTypeDimension = z.infer<typeof EnumFromDocTypeDimensionSchema>;

/**
 * EnumFromDocType Dimension Handler
 */
export class EnumFromDocTypeHandler
  implements DimensionHandler<EnumFromDocTypeDimension>
{
  /**
   * enum_from_doc_type値を検証
   *
   * 検証項目:
   * 1. 値がmappingの値に含まれているか
   * 2. ドキュメントのdoc_typeが存在するか
   * 3. mapping[doc_type]と値が一致するか
   */
  validate(
    value: string,
    dimension: EnumFromDocTypeDimension,
    context: ValidationContext
  ): Either<ValidationError, true> {
    // 1. mapping値に含まれているか
    const allowedValues = Object.values(dimension.mapping);
    if (!allowedValues.includes(value)) {
      return left({
        code: 'INVALID_DIMENSION_VALUE',
        message: `Value "${value}" is not in mapping values: [${allowedValues.join(', ')}]`,
        dimensionName: context.dimensionName,
        value,
        expected: allowedValues.join(' | '),
      });
    }

    // 2. doc_typeの存在チェック
    const docType = context.documentMeta.doc_type;
    if (!docType) {
      return left({
        code: 'MISSING_DOC_TYPE',
        message: 'doc_type is required in document metadata for enum_from_doc_type dimension',
        dimensionName: context.dimensionName,
        value,
        context: { availableMapping: dimension.mapping },
      });
    }

    // 3. doc_typeがmappingに存在するか
    const expectedValue = dimension.mapping[docType];
    if (expectedValue === undefined) {
      return left({
        code: 'UNKNOWN_DOC_TYPE',
        message: `doc_type "${docType}" is not defined in mapping`,
        dimensionName: context.dimensionName,
        value,
        context: { docType, availableDocTypes: Object.keys(dimension.mapping) },
      });
    }

    // 4. 期待値と一致するか
    if (expectedValue !== value) {
      return left({
        code: 'DIMENSION_MISMATCH',
        message: `doc_type "${docType}" maps to "${expectedValue}", but got "${value}"`,
        dimensionName: context.dimensionName,
        value,
        expected: expectedValue,
        context: { docType },
      });
    }

    return right(true);
  }

  /**
   * enum_from_doc_type値を生成
   *
   * 生成ロジック:
   * 1. メタデータのdoc_typeからmappingを参照
   */
  generate(
    dimension: EnumFromDocTypeDimension,
    context: GenerationContext
  ): Either<GenerationError, string> {
    const docType = context.documentMeta.doc_type;

    if (!docType) {
      return left({
        code: 'MISSING_DOC_TYPE',
        message: 'doc_type is required to generate enum_from_doc_type value',
        dimensionName: context.dimensionName,
        context: { availableMapping: dimension.mapping },
      });
    }

    const value = dimension.mapping[docType];
    if (value === undefined) {
      return left({
        code: 'UNKNOWN_DOC_TYPE',
        message: `doc_type "${docType}" is not defined in mapping`,
        dimensionName: context.dimensionName,
        context: { docType, availableDocTypes: Object.keys(dimension.mapping) },
      });
    }

    return right(value);
  }

  /**
   * 正規表現パターンを生成
   *
   * @returns (value1|value2|...) 形式のパターン（mapping値から生成）
   */
  toPattern(dimension: EnumFromDocTypeDimension): string {
    const values = Object.values(dimension.mapping);
    const escaped = values.map((v) => escapeRegex(v));
    return `(${escaped.join('|')})`;
  }
}
