/**
 * Document Writer
 *
 * Markdown/YAMLファイルにdoc_idを書き込む。
 * 既存のfront matter/YAMLを保持しながらdoc_idのみを追加・更新する。
 *
 * 書き込み方式:
 * - Markdown: gray-matterを使用してfront matterを更新
 * - YAML: js-yamlでパースし、idFieldを先頭に配置して再シリアライズ
 */

import { readFile, writeFile } from 'node:fs/promises';

import { type Either, left, right } from 'fp-ts/Either';
import matter from 'gray-matter';
import yaml, { JSON_SCHEMA } from 'js-yaml';


import type { DocumentKind } from '@/types/document';

/**
 * 書き込みエラー
 */
export interface WriteError {
  code: string;
  message: string;
  path: string;
}

/**
 * 書き込み結果
 */
export interface WriteResult {
  path: string;
  docId: string;
}

const YAML_OPTIONS = { schema: JSON_SCHEMA, json: true } as const;

/**
 * ドキュメントにdoc_idを書き込み
 *
 * @param filePath - ファイルの絶対パス
 * @param docId - 書き込むdoc_id
 * @param kind - ドキュメント種別（markdown/yaml）
 * @param idField - IDフィールド名（デフォルト: 'doc_id'）
 * @returns 書き込み結果またはエラー
 */
export async function writeDocIdToDocument(
  filePath: string,
  docId: string,
  kind: DocumentKind,
  idField: string = 'doc_id'
): Promise<Either<WriteError, WriteResult>> {
  try {
    const content = await readFile(filePath, 'utf8');

    if (kind === 'markdown') {
      const newContent = writeDocIdToMarkdown(content, docId, idField);
      await writeFile(filePath, newContent, 'utf8');
    } else {
      const newContent = writeDocIdToYaml(content, docId, idField);
      await writeFile(filePath, newContent, 'utf8');
    }

    return right({ path: filePath, docId });
  } catch (error) {
    return left({
      code: 'ASSIGN_WRITE_FAILED',
      message: error instanceof Error ? error.message : 'Unknown write error',
      path: filePath,
    });
  }
}

/**
 * Markdownファイルのfront matterにdoc_idを追加
 *
 * gray-matterのstringify()を使用して、既存のfront matterを保持しながら
 * doc_idを追加する。
 *
 * @param content - 元のファイル内容
 * @param docId - 書き込むdoc_id
 * @param idField - IDフィールド名
 * @returns 更新されたファイル内容
 */
function writeDocIdToMarkdown(
  content: string,
  docId: string,
  idField: string
): string {
  const parsed = matter(content);

  // idFieldを先頭に配置（既存のidFieldは除外してspreadで再構築）
   
  const { [idField]: _, ...restData } = parsed.data;
  const orderedData = { [idField]: docId, ...restData };

  return matter.stringify(parsed.content, orderedData);
}

/**
 * YAMLファイルにdoc_idを追加
 *
 * js-yamlでパースし、idFieldを先頭に配置して再シリアライズする。
 *
 * @param content - 元のファイル内容
 * @param docId - 書き込むdoc_id
 * @param idField - IDフィールド名
 * @returns 更新されたファイル内容
 */
function writeDocIdToYaml(
  content: string,
  docId: string,
  idField: string
): string {
  const parsed = yaml.load(content, YAML_OPTIONS) as Record<string, unknown> | null;
  const data = parsed ?? {};

  // idFieldを先頭に配置
  const orderedData: Record<string, unknown> = { [idField]: docId };
  for (const [key, value] of Object.entries(data)) {
    if (key !== idField) {
      orderedData[key] = value;
    }
  }

  return yaml.dump(orderedData, { indent: 2, lineWidth: -1 });
}

/**
 * ファイルの元内容を読み取り（ロールバック用）
 *
 * @param filePath - ファイルパス
 * @returns ファイル内容またはエラー
 */
export async function readFileContent(
  filePath: string
): Promise<Either<WriteError, string>> {
  try {
    const content = await readFile(filePath, 'utf8');
    return right(content);
  } catch (error) {
    return left({
      code: 'READ_FAILED',
      message: error instanceof Error ? error.message : 'Unknown read error',
      path: filePath,
    });
  }
}

/**
 * ファイルに内容を書き込み（ロールバック用）
 *
 * @param filePath - ファイルパス
 * @param content - 書き込む内容
 * @returns 成功またはエラー
 */
export async function writeFileContent(
  filePath: string,
  content: string
): Promise<Either<WriteError, void>> {
  try {
    await writeFile(filePath, content, 'utf8');
    return right(undefined);
  } catch (error) {
    return left({
      code: 'ASSIGN_WRITE_FAILED',
      message: error instanceof Error ? error.message : 'Unknown write error',
      path: filePath,
    });
  }
}
