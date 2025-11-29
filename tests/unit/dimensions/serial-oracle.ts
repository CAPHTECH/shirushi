/**
 * Serial Number Generation Oracle
 *
 * TLA+仕様を忠実に反映したリファレンス実装。
 * プロパティベーステストでの実装検証に使用する。
 *
 * このオラクルは serial_generation.tla の NextSerial 操作を
 * TypeScript で直接実装したもの。
 */

import { type Either, left, right } from 'fp-ts/Either';

import { extractDimensionValues } from '@/parsers/template';

import type { TemplateParseResult } from '@/parsers/template';

/**
 * オーバーフローエラー型
 */
export type SerialOverflow = 'OVERFLOW';

/**
 * スコープ内のシリアル番号を抽出
 *
 * TLA+ SerialsInScope(scopeKey) に対応
 *
 * @param indexDocIds - インデックス内の全doc_id
 * @param templateResult - テンプレート解析結果
 * @param scope - スコープを構成するdimension名の配列
 * @param targetScopeKey - 対象のスコープキー
 * @param serialDimensionName - シリアルdimensionの名前
 * @returns スコープ内のシリアル番号の配列
 */
export function extractSerialsInScope(
  indexDocIds: string[],
  templateResult: TemplateParseResult,
  scope: string[],
  targetScopeKey: string,
  serialDimensionName: string
): number[] {
  return indexDocIds
    .map((docId) => extractDimensionValues(docId, templateResult))
    .filter((values): values is Record<string, string> => values !== null)
    .filter((values) => {
      // スコープキーを構築して比較
      const entryScopeKey = scope
        .map((dim) => values[dim])
        .filter((v): v is string => v !== undefined)
        .join('-');
      return entryScopeKey === targetScopeKey;
    })
    .map((values) => {
      const serialStr = values[serialDimensionName];
      return serialStr ? parseInt(serialStr, 10) : NaN;
    })
    .filter((n) => !isNaN(n) && n > 0);
}

/**
 * スコープ内の最大シリアル番号を取得
 *
 * TLA+ MaxInScope(scopeKey) に対応
 *
 * @param serials - シリアル番号の配列
 * @returns 最大値（空の場合は0）
 */
export function maxInScope(serials: number[]): number {
  return serials.length === 0 ? 0 : Math.max(...serials);
}

/**
 * 次のシリアル番号を計算（オラクル実装）
 *
 * TLA+ NextSerial(scopeKey, digits) に対応
 *
 * @param scopeKey - スコープキー
 * @param indexDocIds - インデックス内の全doc_id
 * @param templateResult - テンプレート解析結果
 * @param scope - スコープを構成するdimension名の配列
 * @param serialDimensionName - シリアルdimensionの名前
 * @param digits - シリアルの桁数
 * @returns 次のシリアル番号、またはオーバーフローエラー
 */
export function oracleNextSerial(
  scopeKey: string,
  indexDocIds: string[],
  templateResult: TemplateParseResult,
  scope: string[],
  serialDimensionName: string,
  digits: number
): Either<SerialOverflow, number> {
  // 1. スコープ内のシリアルを抽出
  const serials = extractSerialsInScope(
    indexDocIds,
    templateResult,
    scope,
    scopeKey,
    serialDimensionName
  );

  // 2. 最大値を計算
  const maxSerial = maxInScope(serials);

  // 3. 次のシリアルを計算
  const nextVal = maxSerial + 1;

  // 4. オーバーフローチェック
  const maxPossible = Math.pow(10, digits) - 1;

  return nextVal > maxPossible ? left('OVERFLOW') : right(nextVal);
}

/**
 * スコープキーを構築
 *
 * @param scope - スコープを構成するdimension名の配列
 * @param otherParts - 他のdimension値
 * @returns スコープキー、または不足しているdimension名
 */
export function buildScopeKeyOracle(
  scope: string[],
  otherParts: Record<string, string>
): Either<string, string> {
  const parts: string[] = [];
  for (const dimName of scope) {
    const value = otherParts[dimName];
    if (value === undefined) {
      return left(dimName); // 不足しているdimension名を返す
    }
    parts.push(value);
  }
  return right(parts.join('-'));
}
