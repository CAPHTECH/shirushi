/**
 * Reference Scanner
 *
 * ドキュメント内のdoc_id参照を検出する。
 *
 * Issue #15: doc_id変更時の文書間参照整合性チェック機能
 *
 * 検出対象:
 * 1. Markdownリンク: [テキスト](doc_id)
 * 2. YAMLフィールド: superseded_by等の設定されたフィールド
 * 3. カスタムパターン: reference_patternsで定義されたパターン
 *
 * 除外対象:
 * - コードブロック内（```で囲まれた部分）
 */

import { readFile } from 'fs/promises';
import * as path from 'path';

import type { ShirushiConfig, ReferencePattern } from '@/config/schema';
import type { DocumentParseResult } from '@/types/document';
import type {
  DocumentReference,
  ReferenceKind,
  ReferenceScanResult,
  ReferenceScanError,
} from '@/types/reference';

/**
 * Markdownリンクのパターン
 * [テキスト](リンク先) 形式を検出
 */
const MARKDOWN_LINK_REGEX = /\[([^\]]*)\]\(([^)]+)\)/g;

/**
 * コードブロックのパターン（削除用）
 * ```言語名\nコード内容\n``` 形式を検出
 */
const CODE_BLOCK_REGEX = /```[\s\S]*?```/g;

/**
 * インラインコードのパターン（削除用）
 * `コード` 形式を検出
 */
const INLINE_CODE_REGEX = /`[^`]+`/g;

/**
 * コードブロックとインラインコードを除去したコンテンツを返す
 *
 * @param content - 元のコンテンツ
 * @returns コードブロック・インラインコードを除去したコンテンツ
 */
export function removeCodeBlocks(content: string): string {
  // まずコードブロックを除去
  let cleaned = content.replace(CODE_BLOCK_REGEX, '');
  // 次にインラインコードを除去
  cleaned = cleaned.replace(INLINE_CODE_REGEX, '');
  return cleaned;
}

/**
 * doc_idパターンを生成する
 *
 * 設定の id_format と dimensions から doc_id にマッチする正規表現を生成する。
 * 簡略化のため、dimension の型に関係なく英数字と記号を許容するパターンを返す。
 *
 * @param config - Shirushi設定
 * @returns doc_idにマッチする正規表現
 */
export function buildDocIdPattern(config: ShirushiConfig): RegExp {
  // id_format からパターンを構築
  // プレースホルダー {NAME} を適切な正規表現に置換
  let pattern = config.id_format;

  // 正規表現のメタ文字をエスケープ（プレースホルダー以外）
  pattern = pattern.replace(/[-[\]{}()*+?.,\\^$|#\s]/g, (char) => {
    // プレースホルダーの {} は後で処理するので一旦スキップ
    if (char === '{' || char === '}') return char;
    return `\\${char}`;
  });

  // 各プレースホルダーを正規表現に置換
  const placeholderRegex = /\{([A-Za-z0-9_]+)\}/g;
  pattern = pattern.replace(placeholderRegex, (_match, name: string) => {
    const dimension = config.dimensions[name];
    if (!dimension) {
      // 未定義のdimensionは任意の文字列にマッチ
      return '[A-Za-z0-9_]+';
    }

    switch (dimension.type) {
      case 'enum':
        // enum値のいずれかにマッチ
        return `(?:${dimension.values.map(escapeRegex).join('|')})`;
      case 'enum_from_doc_type':
        // mapping値のいずれかにマッチ
        return `(?:${Object.values(dimension.mapping).map(escapeRegex).join('|')})`;
      case 'year':
        // 指定桁数の数字
        return `\\d{${dimension.digits}}`;
      case 'serial':
        // 指定桁数の数字
        return `\\d{${dimension.digits}}`;
      case 'checksum':
        // A-Zの1文字（mod26AZの場合）
        return '[A-Z]';
      default:
        return '[A-Za-z0-9_]+';
    }
  });

  return new RegExp(pattern, 'g');
}

/**
 * 正規表現のメタ文字をエスケープする
 */
function escapeRegex(str: string): string {
  return str.replace(/[-[\]{}()*+?.,\\^$|#\s]/g, '\\$&');
}

/**
 * 全ドキュメントから参照をスキャン
 *
 * @param documents - スキャン対象のドキュメント
 * @param config - Shirushi設定
 * @param cwd - 作業ディレクトリ
 * @returns スキャン結果
 */
export async function scanDocumentReferences(
  documents: DocumentParseResult[],
  config: ShirushiConfig,
  cwd: string
): Promise<ReferenceScanResult> {
  const references: DocumentReference[] = [];
  const errors: ReferenceScanError[] = [];

  // doc_idパターンを構築
  const docIdPattern = buildDocIdPattern(config);

  for (const doc of documents) {
    try {
      // ファイルコンテンツを読み込み
      const filePath = path.join(cwd, doc.path);
      const content = await readFile(filePath, 'utf-8');

      // Markdownファイルの場合のみリンクを抽出
      if (doc.kind === 'markdown') {
        const markdownRefs = extractMarkdownLinks(content, doc.path, docIdPattern);
        references.push(...markdownRefs);
      }

      // YAMLフィールドから参照を抽出
      const yamlRefs = extractYamlFieldReferences(
        doc.metadata,
        doc.path,
        config.reference_fields,
        docIdPattern
      );
      references.push(...yamlRefs);

      // カスタムパターンで参照を抽出
      const customRefs = extractCustomPatternReferences(
        content,
        doc.path,
        config.reference_patterns,
        docIdPattern
      );
      references.push(...customRefs);
    } catch (err) {
      errors.push({
        path: doc.path,
        message: err instanceof Error ? err.message : String(err),
      });
    }
  }

  return { references, errors };
}

/**
 * Markdownコンテンツからリンク参照を抽出
 *
 * コードブロック内のリンクは除外する。
 *
 * @param content - Markdownコンテンツ
 * @param sourcePath - ソースファイルパス
 * @param docIdPattern - doc_idにマッチする正規表現
 * @returns 抽出された参照
 */
export function extractMarkdownLinks(
  content: string,
  sourcePath: string,
  docIdPattern: RegExp
): DocumentReference[] {
  const references: DocumentReference[] = [];

  // コードブロックを除去
  const cleanedContent = removeCodeBlocks(content);
  const lines = cleanedContent.split('\n');

  let lineNumber = 0;
  for (const line of lines) {
    lineNumber++;
    MARKDOWN_LINK_REGEX.lastIndex = 0;
    let match: RegExpExecArray | null;

    while ((match = MARKDOWN_LINK_REGEX.exec(line)) !== null) {
      const linkTarget = match[2];
      if (linkTarget) {
        // doc_idパターンにマッチするかチェック
        docIdPattern.lastIndex = 0;
        if (docIdPattern.test(linkTarget)) {
          references.push({
            sourcePath,
            targetDocId: linkTarget,
            kind: 'markdown_link' as ReferenceKind,
            lineNumber,
          });
        }
      }
    }
  }

  return references;
}

/**
 * YAMLメタデータからフィールド参照を抽出
 *
 * @param metadata - ドキュメントのメタデータ
 * @param sourcePath - ソースファイルパス
 * @param referenceFields - 参照フィールド名の配列
 * @param docIdPattern - doc_idにマッチする正規表現
 * @returns 抽出された参照
 */
export function extractYamlFieldReferences(
  metadata: Record<string, unknown>,
  sourcePath: string,
  referenceFields: string[],
  docIdPattern: RegExp
): DocumentReference[] {
  const references: DocumentReference[] = [];

  for (const fieldName of referenceFields) {
    const value = metadata[fieldName];

    if (typeof value === 'string') {
      // 単一の参照
      docIdPattern.lastIndex = 0;
      if (docIdPattern.test(value)) {
        references.push({
          sourcePath,
          targetDocId: value,
          kind: 'yaml_field' as ReferenceKind,
          fieldName,
        });
      }
    } else if (Array.isArray(value)) {
      // 配列の参照
      for (const item of value) {
        if (typeof item === 'string') {
          docIdPattern.lastIndex = 0;
          if (docIdPattern.test(item)) {
            references.push({
              sourcePath,
              targetDocId: item,
              kind: 'yaml_field' as ReferenceKind,
              fieldName,
            });
          }
        }
      }
    }
  }

  return references;
}

/**
 * カスタムパターンで参照を抽出
 *
 * コードブロック内のマッチは除外する。
 *
 * @param content - ドキュメントコンテンツ
 * @param sourcePath - ソースファイルパス
 * @param patterns - 参照パターン定義
 * @param docIdPattern - doc_idにマッチする正規表現
 * @returns 抽出された参照
 */
export function extractCustomPatternReferences(
  content: string,
  sourcePath: string,
  patterns: ReferencePattern[],
  docIdPattern: RegExp
): DocumentReference[] {
  const references: DocumentReference[] = [];

  // コードブロックを除去
  const cleanedContent = removeCodeBlocks(content);
  const lines = cleanedContent.split('\n');

  for (const patternDef of patterns) {
    // {DOC_ID} プレースホルダーをキャプチャグループに置換
    // doc_idパターンのソースを取得（フラグを除去）
    const docIdPatternSource = docIdPattern.source;
    const expandedPattern = patternDef.pattern.replace(/\{DOC_ID\}/g, `(${docIdPatternSource})`);

    let compiledPattern: RegExp;
    try {
      compiledPattern = new RegExp(expandedPattern, 'g');
    } catch {
      // 無効なパターンはスキップ
      continue;
    }

    let lineNumber = 0;
    for (const line of lines) {
      lineNumber++;
      compiledPattern.lastIndex = 0;
      let match: RegExpExecArray | null;

      while ((match = compiledPattern.exec(line)) !== null) {
        // キャプチャグループからdoc_idを取得
        const capturedDocId = match[1];
        if (capturedDocId) {
          references.push({
            sourcePath,
            targetDocId: capturedDocId,
            kind: 'custom_pattern' as ReferenceKind,
            lineNumber,
            patternName: patternDef.name,
          });
        }
      }
    }
  }

  return references;
}
