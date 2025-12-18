/**
 * ID Generator
 *
 * 各dimensionハンドラのgenerate()メソッドを統合し、
 * テンプレートに基づいて完全なdoc_idを生成する。
 *
 * アルゴリズム:
 * 1. テンプレートを解析してプレースホルダーを抽出
 * 2. checksum以外のdimensionを順番に生成
 * 3. checksumを最後に計算（他の部品値が必要なため）
 * 4. テンプレートに値を埋め込んでIDを構築
 */

import { type Either, isLeft, left, right } from 'fp-ts/Either';

import { getDimensionRegistry } from '@/dimensions';
import { parseTemplate, type TemplateParseResult } from '@/parsers/template';

import type { ShirushiConfig } from '@/config/schema';
import type { IndexEntry } from '@/core/index-manager';
import type { GenerationContext, GenerationError } from '@/dimensions/handlers/base';

/**
 * ID生成の入力
 */
export interface GenerateIdInput {
  /** ドキュメントのパス */
  documentPath: string;
  /** ドキュメントのメタデータ（doc_typeなど） */
  documentMeta: Record<string, unknown>;
  /** 設定 */
  config: ShirushiConfig;
  /** インデックスエントリ（serial採番用） */
  indexEntries: IndexEntry[];
}

/**
 * ID生成の結果
 */
export interface GenerateIdResult {
  /** 生成されたdoc_id */
  docId: string;
  /** 各dimensionの値 */
  parts: Record<string, string>;
}

/**
 * doc_idを生成
 *
 * @param input - 生成入力
 * @returns 生成結果またはエラー配列
 *
 * @example
 * ```typescript
 * const result = generateDocId({
 *   documentPath: 'docs/spec.md',
 *   documentMeta: { doc_type: 'spec', title: 'Spec' },
 *   config,
 *   indexEntries,
 * });
 *
 * if (isRight(result)) {
 *   console.log(result.right.docId); // 'PCE-SPEC-2025-0001-G'
 * }
 * ```
 */
export function generateDocId(
  input: GenerateIdInput
): Either<GenerationError[], GenerateIdResult> {
  const { documentPath, documentMeta, config, indexEntries } = input;

  // 1. テンプレートを解析
  const templateResult = parseTemplate(config.id_format, config.dimensions);
  if (isLeft(templateResult)) {
    return left([
      {
        code: 'INVALID_TEMPLATE',
        message: templateResult.left.message,
        dimensionName: '',
      },
    ]);
  }
  const template = templateResult.right;

  // 2. 各dimensionの値を生成
  const partsResult = generateParts(
    template,
    config,
    documentPath,
    documentMeta,
    indexEntries
  );
  if (isLeft(partsResult)) {
    return partsResult;
  }
  const parts = partsResult.right;

  // 3. ID文字列を組み立て
  const docId = assembleDocId(config.id_format, parts);

  return right({ docId, parts });
}

/**
 * 各dimensionの値を生成
 *
 * checksum以外を先に生成し、その後checksumを計算する。
 */
function generateParts(
  template: TemplateParseResult,
  config: ShirushiConfig,
  documentPath: string,
  documentMeta: Record<string, unknown>,
  indexEntries: IndexEntry[]
): Either<GenerationError[], Record<string, string>> {
  const parts: Record<string, string> = {};
  const errors: GenerationError[] = [];
  const registry = getDimensionRegistry();
  const idField = config.id_field ?? 'doc_id';

  // checksumは後回しにするため、分離
  const checksumDimensions: string[] = [];
  const nonChecksumPlaceholders = template.placeholders.filter((p) => {
    const dim = config.dimensions[p.name];
    if (dim?.type === 'checksum') {
      checksumDimensions.push(p.name);
      return false;
    }
    return true;
  });

  // checksum以外のdimensionを生成
  for (const placeholder of nonChecksumPlaceholders) {
    const dimension = config.dimensions[placeholder.name];
    if (!dimension) {
      errors.push({
        code: 'UNDEFINED_DIMENSION',
        message: `Dimension "${placeholder.name}" is not defined`,
        dimensionName: placeholder.name,
      });
      continue;
    }

    const handler = registry.get(dimension.type);
    const context: GenerationContext = {
      documentPath,
      documentMeta,
      otherParts: parts,
      dimensionName: placeholder.name,
      indexEntries,
      templateResult: template,
      idField,
    };

    try {
      const result = handler.generate(dimension, context);
      if (isLeft(result)) {
        errors.push(result.left);
      } else {
        parts[placeholder.name] = result.right;
      }
    } catch (e) {
      errors.push({
        code: 'DIMENSION_HANDLER_CRASH',
        message: `Handler for "${placeholder.name}" threw: ${e instanceof Error ? e.message : String(e)}`,
        dimensionName: placeholder.name,
      });
    }
  }

  // エラーがあれば早期リターン
  if (errors.length > 0) {
    return left(errors);
  }

  // checksumを生成（他のdimension値が揃った後）
  for (const name of checksumDimensions) {
    const dimension = config.dimensions[name];
    if (!dimension) continue;

    const handler = registry.get(dimension.type);
    const context: GenerationContext = {
      documentPath,
      documentMeta,
      otherParts: parts,
      dimensionName: name,
    };

    try {
      const result = handler.generate(dimension, context);
      if (isLeft(result)) {
        errors.push(result.left);
      } else {
        parts[name] = result.right;
      }
    } catch (e) {
      errors.push({
        code: 'DIMENSION_HANDLER_CRASH',
        message: `Handler for "${name}" threw: ${e instanceof Error ? e.message : String(e)}`,
        dimensionName: name,
      });
    }
  }

  if (errors.length > 0) {
    return left(errors);
  }

  return right(parts);
}

/**
 * テンプレートに値を埋め込んでID文字列を組み立て
 *
 * @param template - id_formatテンプレート
 * @param parts - dimension名 → 値のマップ
 * @returns 組み立てられたdoc_id
 */
function assembleDocId(
  template: string,
  parts: Record<string, string>
): string {
  let result = template;
  for (const [name, value] of Object.entries(parts)) {
    result = result.replace(`{${name}}`, value);
  }
  return result;
}
