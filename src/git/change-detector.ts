/**
 * Doc ID Change Detector
 *
 * Git参照間でのdoc_id変更を検出する。
 * ベースrefと現在のHEADを比較して、doc_idの変更を特定する。
 *
 * LDE準拠: Either型で成功/失敗を表現
 */

import { isLeft, right, type Either } from 'fp-ts/Either';

import { parseMarkdownContent } from '@/parsers/markdown';
import { parseYamlContent } from '@/parsers/yaml';

import type {
  ChangeDetectionResult,
  DetectionTarget,
  GitError,
  GitOperations,
} from './types';

/**
 * 単一ファイルの変更検出結果（内部用）
 */
interface SingleFileChange {
  /** 新規ファイル（ベースrefに存在しない） */
  isNew: boolean;
  /** 削除ファイル（現在存在しない） */
  isDeleted: boolean;
  /** doc_idが変更された */
  docIdChanged: boolean;
  /** ベースrefでのdoc_id */
  oldDocId: string | null;
  /** 現在のdoc_id */
  newDocId: string | null;
}

/**
 * Change Detector
 *
 * GitOperationsを使用してdoc_id変更を検出する。
 * 依存性注入により、テスト時にモック実装を注入可能。
 */
export class ChangeDetector {
  constructor(private gitOps: GitOperations) {}

  /**
   * 指定されたファイル群のdoc_id変更を検出
   *
   * @param baseRef - 比較対象のGit参照
   * @param targets - 検出対象のファイル配列（リネーム情報を含む）
   * @returns 変更検出結果
   */
  async detectDocIdChanges(
    baseRef: string,
    targets: DetectionTarget[]
  ): Promise<Either<GitError, ChangeDetectionResult>> {
    const result: ChangeDetectionResult = {
      changedDocIds: [],
      newFiles: [],
      deletedFiles: [],
      errors: [],
    };

    for (const target of targets) {
      const detection = await this.detectSingleFileChange(baseRef, target);

      if (isLeft(detection)) {
        // 個別ファイルのエラーは収集して処理を継続
        result.errors.push(detection.left);
        continue;
      }

      const change = detection.right;
      if (change.isNew) {
        result.newFiles.push(target.path);
      } else if (change.isDeleted) {
        result.deletedFiles.push(target.path);
      } else if (change.docIdChanged) {
        result.changedDocIds.push({
          path: target.path,
          oldDocId: change.oldDocId,
          newDocId: change.newDocId,
          changeType: 'modified',
        });
      }
    }

    return right(result);
  }

  /**
   * 単一ファイルのdoc_id変更を検出
   *
   * リネームされたファイルの場合、oldPathを使用してベースrefの内容を取得する。
   * これにより、ファイル名変更と同時にdoc_idが変更された場合も検出できる。
   */
  private async detectSingleFileChange(
    baseRef: string,
    target: DetectionTarget
  ): Promise<Either<GitError, SingleFileChange>> {
    const { path: filePath, oldPath } = target;

    // ベースrefでのコンテンツを取得
    // リネームの場合はoldPathから取得する（重要: これがないとリネーム+doc_id変更を検出できない）
    const basePathToUse = oldPath ?? filePath;
    const baseContentResult = await this.gitOps.getFileContent(basePathToUse, baseRef);
    if (isLeft(baseContentResult)) {
      return baseContentResult;
    }

    // 現在のコンテンツを取得
    const currentContentResult = await this.gitOps.getFileContent(filePath);
    if (isLeft(currentContentResult)) {
      return currentContentResult;
    }

    const baseContent = baseContentResult.right;
    const currentContent = currentContentResult.right;

    // doc_idを抽出（拡張子判定用にそれぞれのパスを使用）
    const baseDocId = baseContent
      ? this.extractDocId(baseContent, basePathToUse)
      : null;
    const currentDocId = currentContent
      ? this.extractDocId(currentContent, filePath)
      : null;

    return right({
      isNew: baseContent === null && currentContent !== null,
      isDeleted: baseContent !== null && currentContent === null,
      docIdChanged:
        baseDocId !== currentDocId &&
        baseContent !== null &&
        currentContent !== null,
      oldDocId: baseDocId,
      newDocId: currentDocId,
    });
  }

  /**
   * コンテンツからdoc_idを抽出
   *
   * @param content - ファイル内容
   * @param filePath - ファイルパス（拡張子判定用）
   * @returns doc_id（存在しない場合はnull）
   */
  private extractDocId(content: string, filePath: string): string | null {
    const ext = filePath.toLowerCase();

    if (ext.endsWith('.md')) {
      const result = parseMarkdownContent(filePath, content);
      return result.docId ?? null;
    }

    if (ext.endsWith('.yaml') || ext.endsWith('.yml')) {
      const result = parseYamlContent(filePath, content);
      return result.docId ?? null;
    }

    // サポートされていないファイル形式
    return null;
  }
}

/**
 * ChangeDetectorファクトリ関数
 *
 * @param gitOps - GitOperations実装
 * @returns ChangeDetector
 */
export function createChangeDetector(gitOps: GitOperations): ChangeDetector {
  return new ChangeDetector(gitOps);
}
