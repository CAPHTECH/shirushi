/**
 * Index Writer
 *
 * インデックスファイル（doc_index.yaml）への書き込み機能を提供。
 * assignコマンドで生成したdoc_idをインデックスに追記する。
 */

import { existsSync } from 'node:fs';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';

import { type Either, left, right } from 'fp-ts/Either';
import yaml, { JSON_SCHEMA } from 'js-yaml';

import { normalizePath } from '@/utils/path';

import type { IndexEntry, IndexFile } from '@/core/index-manager';

/**
 * インデックス書き込みエラー
 */
export interface IndexWriteError {
  code: string;
  message: string;
  path: string;
}

const YAML_OPTIONS = { schema: JSON_SCHEMA, json: true } as const;

/**
 * 新しいエントリ情報
 */
export interface NewIndexEntry {
  docId: string;
  path: string;
  title?: string;
  docType?: string;
  contentHash?: string; // SHA-256 hash of document content
}

/**
 * インデックスファイルにエントリを追記
 *
 * @param indexPath - インデックスファイルの相対パス
 * @param entries - 追加するエントリ
 * @param cwd - ベースディレクトリ
 * @param idField - IDフィールド名（デフォルト: 'doc_id'）
 * @returns 成功またはエラー
 */
export async function appendToIndex(
  indexPath: string,
  entries: NewIndexEntry[],
  cwd: string = process.cwd(),
  idField: string = 'doc_id'
): Promise<Either<IndexWriteError, void>> {
  const absolutePath = path.isAbsolute(indexPath)
    ? indexPath
    : path.join(cwd, indexPath);

  try {
    // 既存のインデックスを読み込み
    let indexFile: IndexFile = { documents: [] };

    if (existsSync(absolutePath)) {
      const content = await readFile(absolutePath, 'utf8');
      const parsed = yaml.load(content, YAML_OPTIONS) as IndexFile | null;
      if (parsed?.documents) {
        indexFile = parsed;
      }
    } else {
      // ディレクトリが存在しない場合は作成
      const dir = path.dirname(absolutePath);
      if (!existsSync(dir)) {
        await mkdir(dir, { recursive: true });
      }
    }

    // 新しいエントリを追加
    for (const entry of entries) {
      const newEntry: IndexEntry = {
        [idField]: entry.docId,
        path: normalizePath(entry.path), // Windows互換性のため正規化
        ...(entry.title ? { title: entry.title } : {}),
        ...(entry.docType ? { doc_type: entry.docType } : {}),
        ...(entry.contentHash ? { content_hash: entry.contentHash } : {}),
      };
      indexFile.documents.push(newEntry);
    }

    // ファイルに書き込み
    const content = yaml.dump(indexFile, { indent: 2, lineWidth: -1 });
    await writeFile(absolutePath, content, 'utf8');

    return right(undefined);
  } catch (error) {
    return left({
      code: 'ASSIGN_INDEX_UPDATE_FAILED',
      message: error instanceof Error ? error.message : 'Unknown index write error',
      path: absolutePath,
    });
  }
}

/**
 * インデックスファイルの内容を読み取り（ロールバック用）
 *
 * @param indexPath - インデックスファイルの相対パス
 * @param cwd - ベースディレクトリ
 * @returns ファイル内容またはnull（ファイルが存在しない場合）
 */
export async function readIndexContent(
  indexPath: string,
  cwd: string = process.cwd()
): Promise<Either<IndexWriteError, string | null>> {
  const absolutePath = path.isAbsolute(indexPath)
    ? indexPath
    : path.join(cwd, indexPath);

  try {
    if (!existsSync(absolutePath)) {
      return right(null);
    }
    const content = await readFile(absolutePath, 'utf8');
    return right(content);
  } catch (error) {
    return left({
      code: 'READ_FAILED',
      message: error instanceof Error ? error.message : 'Unknown read error',
      path: absolutePath,
    });
  }
}

/**
 * インデックスファイルに内容を書き込み（ロールバック用）
 *
 * @param indexPath - インデックスファイルの相対パス
 * @param content - 書き込む内容（nullの場合は何もしない）
 * @param cwd - ベースディレクトリ
 * @returns 成功またはエラー
 */
export async function writeIndexContent(
  indexPath: string,
  content: string | null,
  cwd: string = process.cwd()
): Promise<Either<IndexWriteError, void>> {
  if (content === null) {
    // 元々ファイルが存在しなかった場合は何もしない
    // （削除は危険なので行わない）
    return right(undefined);
  }

  const absolutePath = path.isAbsolute(indexPath)
    ? indexPath
    : path.join(cwd, indexPath);

  try {
    await writeFile(absolutePath, content, 'utf8');
    return right(undefined);
  } catch (error) {
    return left({
      code: 'ASSIGN_INDEX_UPDATE_FAILED',
      message: error instanceof Error ? error.message : 'Unknown write error',
      path: absolutePath,
    });
  }
}
