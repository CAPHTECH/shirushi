/**
 * Reference Validator
 *
 * doc_id変更時の参照整合性を検証する。
 *
 * Issue #15: doc_id変更時の文書間参照整合性チェック機能
 *
 * 検証フロー:
 * 1. changedDocIds（変更されたdoc_idのマップ）を取得
 * 2. 全ドキュメントの参照をスキャン
 * 3. 参照先が変更されたdoc_idの場合、StaleReferenceとして報告
 */

import type { DocumentReference, StaleReference, ReferenceValidationResult } from '@/types/reference';

/**
 * doc_id変更情報
 *
 * 変更前のdoc_idをキー、変更後の情報を値とするマップ。
 * newDocIdがnullの場合は削除を意味する。
 */
export interface DocIdChange {
  /** 変更後のdoc_id（削除の場合はnull） */
  newDocId: string | null;
  /** 変更が発生したドキュメントのパス */
  changedDocPath: string;
}

/**
 * 参照検証のコンテキスト
 */
export interface ReferenceValidationContext {
  /** 変更されたdoc_idのマップ（旧doc_id → 変更情報） */
  changedDocIds: Map<string, DocIdChange>;
}

/**
 * 参照の整合性を検証
 *
 * スキャンされた参照の中から、変更されたdoc_idを参照しているものを
 * StaleReferenceとして検出する。
 *
 * 法則（Invariants）:
 * - 参照先のdoc_idがchangedDocIdsに存在する場合、その参照は古い
 * - 参照元と参照先が同じドキュメントの場合も検出対象（自己参照の整合性）
 *
 * @param references - スキャンされた参照の配列
 * @param context - 検証コンテキスト（変更されたdoc_id情報を含む）
 * @returns 検証結果（古い参照の一覧）
 */
export function validateReferences(
  references: DocumentReference[],
  context: ReferenceValidationContext
): ReferenceValidationResult {
  const staleReferences: StaleReference[] = [];

  for (const ref of references) {
    const change = context.changedDocIds.get(ref.targetDocId);

    if (change) {
      // 参照先のdoc_idが変更されている → 古い参照
      const staleRef: StaleReference = {
        sourcePath: ref.sourcePath,
        oldDocId: ref.targetDocId,
        newDocId: change.newDocId,
        changedDocPath: change.changedDocPath,
        kind: ref.kind,
      };

      // オプショナルプロパティは定義されている場合のみ追加
      if (ref.lineNumber !== undefined) {
        staleRef.lineNumber = ref.lineNumber;
      }
      if (ref.fieldName !== undefined) {
        staleRef.fieldName = ref.fieldName;
      }
      if (ref.patternName !== undefined) {
        staleRef.patternName = ref.patternName;
      }

      staleReferences.push(staleRef);
    }
  }

  return { staleReferences };
}

/**
 * doc_id変更マップを構築
 *
 * ベースrefと現在の状態を比較して、変更されたdoc_idのマップを作成する。
 *
 * @param baseDocIds - ベースref時点でのdoc_idマップ（パス → doc_id）
 * @param currentDocIds - 現在のdoc_idマップ（パス → doc_id）
 * @returns 変更されたdoc_idのマップ
 */
export function buildChangedDocIdsMap(
  baseDocIds: Map<string, string>,
  currentDocIds: Map<string, string>
): Map<string, DocIdChange> {
  const changedDocIds = new Map<string, DocIdChange>();

  // ベースに存在するdoc_idをチェック
  for (const [path, oldDocId] of baseDocIds) {
    const newDocId = currentDocIds.get(path);

    if (newDocId === undefined) {
      // ファイルが削除された場合
      // この場合は参照整合性チェックの対象外
      // （削除されたファイルへの参照は別のエラーで検出される）
      continue;
    }

    if (newDocId !== oldDocId) {
      // doc_idが変更された
      changedDocIds.set(oldDocId, {
        newDocId,
        changedDocPath: path,
      });
    }
  }

  return changedDocIds;
}

/**
 * 自己参照を除外したStaleReferenceを取得
 *
 * 同じドキュメント内での自己参照は、doc_id変更時に自動的に
 * 更新されることを前提として除外するオプション用。
 *
 * @param staleReferences - 全ての古い参照
 * @returns 自己参照を除外した古い参照
 */
export function excludeSelfReferences(staleReferences: StaleReference[]): StaleReference[] {
  return staleReferences.filter((ref) => ref.sourcePath !== ref.changedDocPath);
}
