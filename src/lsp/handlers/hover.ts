/**
 * Hover Handler
 *
 * doc_id上でドキュメントのタイトルと概要を表示する。
 *
 * @see ADR-0010: LSP Server Integration
 */

import { lookupDocument } from '@/core/lookup';
import { findDocIdAtPosition } from '@/lsp/utils/pattern-matcher';
import { logger } from '@/utils/logger';

import type { ShirushiConfig } from '@/config/schema';
import type { TextDocuments, Hover, Position } from 'vscode-languageserver';
import type { TextDocument } from 'vscode-languageserver-textdocument';

/**
 * Hover ハンドラオプション
 */
export interface HoverHandlerOptions {
  /** プロジェクトルートディレクトリ */
  cwd: string;
  /** Shirushi設定 */
  config: ShirushiConfig;
  /** ドキュメント管理 */
  documents: TextDocuments<TextDocument>;
}

/**
 * ドキュメント情報をMarkdown形式でフォーマット
 */
function formatDocumentInfo(
  docId: string,
  title: string | undefined,
  path: string,
  status: string | undefined,
  version: string | undefined,
  contentPreview: string | undefined
): string {
  const lines: string[] = [];

  // タイトル
  lines.push(`## ${title ?? docId}`);
  lines.push('');

  // メタデータ
  lines.push(`**doc_id**: \`${docId}\``);
  lines.push(`**path**: \`${path}\``);

  if (status) {
    lines.push(`**status**: ${status}`);
  }
  if (version) {
    lines.push(`**version**: ${version}`);
  }

  // コンテンツプレビュー（最初の3行程度）
  if (contentPreview) {
    lines.push('');
    lines.push('---');
    lines.push('');

    // 最初の200文字程度をプレビュー
    const preview = contentPreview.slice(0, 200);
    const truncated = contentPreview.length > 200 ? '...' : '';
    lines.push(preview + truncated);
  }

  return lines.join('\n');
}

/**
 * Hover ハンドラを作成
 *
 * @param options - ハンドラオプション
 * @returns LSP onHoverハンドラ関数
 */
export function createHoverHandler(options: HoverHandlerOptions) {
  const { cwd, config, documents } = options;

  return async (params: {
    textDocument: { uri: string };
    position: Position;
  }): Promise<Hover | null> => {
    const document = documents.get(params.textDocument.uri);
    if (!document) {
      return null;
    }

    const text = document.getText();
    const match = findDocIdAtPosition(text, params.position, config);

    if (!match) {
      return null;
    }

    logger.debug('lsp.hover', 'Found doc_id', {
      docId: match.docId,
      position: params.position,
    });

    // doc_idからドキュメント情報を取得
    const lookupResult = await lookupDocument(match.docId, config, { cwd });

    if (!lookupResult.success) {
      // ドキュメントが見つからない場合でもエラー情報を表示
      return {
        contents: {
          kind: 'markdown',
          value: `**${match.docId}**\n\n_Document not found: ${lookupResult.message}_`,
        },
        range: {
          start: { line: match.line, character: match.startCharacter },
          end: { line: match.line, character: match.endCharacter },
        },
      };
    }

    // ドキュメント情報をMarkdownでフォーマット
    const content = formatDocumentInfo(
      lookupResult.docId,
      lookupResult.metadata.title,
      lookupResult.path,
      lookupResult.metadata.status,
      lookupResult.metadata.version,
      lookupResult.content
    );

    return {
      contents: {
        kind: 'markdown',
        value: content,
      },
      range: {
        start: { line: match.line, character: match.startCharacter },
        end: { line: match.line, character: match.endCharacter },
      },
    };
  };
}
