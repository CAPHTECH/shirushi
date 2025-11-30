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
   * @param targetPaths - 検出対象のファイルパス配列
   * @returns 変更検出結果
   */
  async detectDocIdChanges(
    baseRef: string,
    targetPaths: string[]
  ): Promise<Either<GitError, ChangeDetectionResult>> {
    const result: ChangeDetectionResult = {
      changedDocIds: [],
      newFiles: [],
      deletedFiles: [],
      errors: [],
    };

    for (const filePath of targetPaths) {
      const detection = await this.detectSingleFileChange(baseRef, filePath);

      if (isLeft(detection)) {
        // 個別ファイルのエラーは収集して処理を継続
        result.errors.push(detection.left);
        continue;
      }

      const change = detection.right;
      if (change.isNew) {
        result.newFiles.push(filePath);
      } else if (change.isDeleted) {
        result.deletedFiles.push(filePath);
      } else if (change.docIdChanged) {
        result.changedDocIds.push({
          path: filePath,
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
   */
  private async detectSingleFileChange(
    baseRef: string,
    filePath: string
  ): Promise<Either<GitError, SingleFileChange>> {
    // ベースrefでのコンテンツを取得
    const baseContentResult = await this.gitOps.getFileContent(filePath, baseRef);
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

    // doc_idを抽出
    const baseDocId = baseContent
      ? this.extractDocId(baseContent, filePath)
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
