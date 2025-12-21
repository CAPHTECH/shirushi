/**
 * Checksum Validator
 *
 * ADR-0009: チェックサムをdoc_idから分離して別フィールドに
 * 新形式のチェックサム（doc_idとは別フィールド）を検証する。
 *
 * @see SHI-ADR-2025-0009-N
 */

import { type Either, left, right, isLeft } from 'fp-ts/Either';

import { mod26AZ } from '@/dimensions/handlers/checksum';
import { parseTemplate, extractDimensionValues } from '@/parsers/template';

import type { ShirushiConfig, ChecksumConfig } from '@/config/schema';
import type { ShirushiErrorCode } from '@/errors/definitions';
import type { DocumentMetadata } from '@/types/document';

/**
 * チェックサム検証エラー
 */
export interface ChecksumValidationError {
  code: ShirushiErrorCode;
  message: string;
  expected?: string;
  actual?: string;
  context?: Record<string, unknown>;
}

/**
 * チェックサム検証結果
 */
export interface ChecksumValidationResult {
  valid: boolean;
  error?: ChecksumValidationError;
}

/**
 * チェックサムを計算
 *
 * @param docId - ドキュメントID
 * @param config - Shirushi設定
 * @param checksumConfig - チェックサム設定
 * @returns 計算されたチェックサム値またはエラー
 */
export function computeChecksum(
  docId: string,
  config: ShirushiConfig,
  checksumConfig: ChecksumConfig
): Either<ChecksumValidationError, string> {
  // doc_idからdimension値を抽出
  const templateResult = parseTemplate(config.id_format, config.dimensions);
  if (isLeft(templateResult)) {
    return left({
      code: 'INVALID_ID_FORMAT',
      message: `Failed to parse id_format: ${templateResult.left.message}`,
    });
  }

  const parsedParts = extractDimensionValues(docId, templateResult.right);
  if (!parsedParts) {
    return left({
      code: 'MALFORMED_ID',
      message: `doc_id "${docId}" does not match id_format pattern`,
    });
  }

  // checksumConfig.ofで指定されたdimensionの値を連結
  const parts: string[] = [];
  for (const dimName of checksumConfig.of) {
    const value = parsedParts[dimName];
    if (value === undefined) {
      return left({
        code: 'INVALID_ID_CHECKSUM',
        message: `Cannot compute checksum: missing dimension "${dimName}"`,
        context: { missingDimension: dimName, availableParts: Object.keys(parsedParts) },
      });
    }
    parts.push(value);
  }

  const input = parts.join('');

  // アルゴリズムに基づいて計算
  switch (checksumConfig.algo) {
    case 'mod26AZ':
      return right(mod26AZ(input));
    default: {
      const unknownAlgo: string = checksumConfig.algo;
      return left({
        code: 'INVALID_ID_CHECKSUM',
        message: `Unknown checksum algorithm: "${unknownAlgo}"`,
        context: { algo: unknownAlgo },
      });
    }
  }
}

/**
 * 新形式チェックサムを検証
 *
 * @param docId - ドキュメントID
 * @param metadata - ドキュメントメタデータ
 * @param config - Shirushi設定
 * @returns 検証結果
 */
export function validateSeparateChecksum(
  docId: string,
  metadata: DocumentMetadata,
  config: ShirushiConfig
): ChecksumValidationResult {
  const checksumConfig = config.checksum;
  if (!checksumConfig) {
    // 新形式checksum設定がない場合は検証スキップ（旧形式で検証される）
    return { valid: true };
  }

  const checksumField = checksumConfig.field;
  const actualChecksum = metadata[checksumField];

  // checksumフィールドが存在しない場合
  if (actualChecksum === undefined) {
    return {
      valid: false,
      error: {
        code: 'MISSING_CHECKSUM',
        message: `Missing checksum field "${checksumField}" in document metadata`,
        context: { field: checksumField },
      },
    };
  }

  // checksumフィールドが文字列でない場合
  if (typeof actualChecksum !== 'string') {
    return {
      valid: false,
      error: {
        code: 'INVALID_ID_CHECKSUM',
        message: `Checksum field "${checksumField}" must be a string`,
        context: { field: checksumField, type: typeof actualChecksum },
      },
    };
  }

  // チェックサムを計算
  const computeResult = computeChecksum(docId, config, checksumConfig);
  if (isLeft(computeResult)) {
    return {
      valid: false,
      error: computeResult.left,
    };
  }

  const expectedChecksum = computeResult.right;

  // 検証
  if (actualChecksum !== expectedChecksum) {
    return {
      valid: false,
      error: {
        code: 'INVALID_CHECKSUM',
        message: `Checksum mismatch: expected "${expectedChecksum}", got "${actualChecksum}"`,
        expected: expectedChecksum,
        actual: actualChecksum,
        context: { field: checksumField },
      },
    };
  }

  return { valid: true };
}

/**
 * 設定が新形式チェックサムを使用しているかどうか
 *
 * @param config - Shirushi設定
 * @returns 新形式の場合true
 */
export function usesSeparateChecksum(config: ShirushiConfig): boolean {
  return config.checksum !== undefined;
}

/**
 * 設定が旧形式チェックサム（id_format内）を使用しているかどうか
 *
 * @param config - Shirushi設定
 * @returns 旧形式の場合true
 */
export function usesLegacyChecksum(config: ShirushiConfig): boolean {
  return Object.values(config.dimensions).some((dim) => dim.type === 'checksum');
}

/**
 * doc_idからチェックサム部分を除外（旧形式用）
 *
 * 旧形式のdoc_id（チェックサムがIDの一部）から、
 * forbid_id_change比較用にチェックサム部分を除外する。
 *
 * ADR-0009: forbid_id_changeの比較対象からチェックサムを除外
 *
 * @param docId - 完全なdoc_id（チェックサム含む）
 * @param config - Shirushi設定
 * @returns チェックサムを除外したdoc_id（または元のdoc_id）
 */
export function stripChecksumFromDocId(
  docId: string | null,
  config: ShirushiConfig
): string | null {
  if (docId === null) {
    return null;
  }

  // 新形式の場合はdoc_idにチェックサムが含まれないので何もしない
  if (usesSeparateChecksum(config)) {
    return docId;
  }

  // 旧形式でない（チェックサムdimensionがない）場合もそのまま
  if (!usesLegacyChecksum(config)) {
    return docId;
  }

  // id_formatをパースしてチェックサムプレースホルダーの位置を特定
  const templateResult = parseTemplate(config.id_format, config.dimensions);
  if (isLeft(templateResult)) {
    // パース失敗時はそのまま返す
    return docId;
  }

  const template = templateResult.right;
  const parsedParts = extractDimensionValues(docId, template);
  if (!parsedParts) {
    // マッチしない場合はそのまま返す
    return docId;
  }

  // チェックサムdimensionを除外した値を再構築
  // id_formatからチェックサムプレースホルダーを除外してパターンを再生成
  const checksumDimNames = Object.entries(config.dimensions)
    .filter(([, dim]) => dim.type === 'checksum')
    .map(([name]) => name);

  if (checksumDimNames.length === 0) {
    return docId;
  }

  // シンプルなアプローチ: id_formatから{CHK*}パターンと前後の区切り文字を除去
  let strippedFormat = config.id_format;
  for (const chkName of checksumDimNames) {
    // {CHK1} のようなパターンと、その前の区切り文字を除去
    // 例: "{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}" -> "{COMP}-{KIND}-{YEAR4}-{SER4}"
    strippedFormat = strippedFormat.replace(new RegExp(`-?\\{${chkName}\\}-?`, 'g'), '');
  }

  // 末尾の区切り文字を削除
  strippedFormat = strippedFormat.replace(/-$/, '');

  // チェックサム以外の部分を連結してdoc_idを再構築
  const parts: string[] = [];
  const placeholderRegex = /\{([A-Za-z0-9_]+)\}/g;
  let lastIndex = 0;
  let match;

  while ((match = placeholderRegex.exec(strippedFormat)) !== null) {
    // リテラル部分を追加
    if (match.index > lastIndex) {
      parts.push(strippedFormat.slice(lastIndex, match.index));
    }
    // プレースホルダーの値を追加
    const dimName = match[1];
    if (dimName && parsedParts[dimName] !== undefined) {
      parts.push(parsedParts[dimName]);
    }
    lastIndex = match.index + match[0].length;
  }

  // 残りのリテラル部分を追加
  if (lastIndex < strippedFormat.length) {
    parts.push(strippedFormat.slice(lastIndex));
  }

  return parts.join('');
}
