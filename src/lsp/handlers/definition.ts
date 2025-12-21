/**
 * Go to Definition Handler
 *
 * @see docid からドキュメントファイルへのジャンプを提供する。
 *
 * @see ADR-0010: LSP Server Integration
 */

import path from 'node:path';

import { lookupDocument } from '@/core/lookup';
import { findDocIdAtPosition } from '@/lsp/utils/pattern-matcher';
import { logger } from '@/utils/logger';

import type { ShirushiConfig } from '@/config/schema';
import type { TextDocuments, Location, Position } from 'vscode-languageserver';
import type { TextDocument } from 'vscode-languageserver-textdocument';

/**
 * Go to Definition ハンドラオプション
 */
export interface DefinitionHandlerOptions {
  /** プロジェクトルートディレクトリ */
  cwd: string;
  /** Shirushi設定 */
  config: ShirushiConfig;
  /** ドキュメント管理 */
  documents: TextDocuments<TextDocument>;
}

/**
 * Go to Definition ハンドラを作成
 *
 * @param options - ハンドラオプション
 * @returns LSP onDefinitionハンドラ関数
 */
export function createDefinitionHandler(options: DefinitionHandlerOptions) {
  const { cwd, config, documents } = options;

  return async (params: {
    textDocument: { uri: string };
    position: Position;
  }): Promise<Location | null> => {
    const document = documents.get(params.textDocument.uri);
    if (!document) {
      return null;
    }

    const text = document.getText();
    const match = findDocIdAtPosition(text, params.position, config);

    if (!match) {
      logger.debug('lsp.definition', 'No doc_id at position', {
        uri: params.textDocument.uri,
        position: params.position,
      });
      return null;
    }

    logger.debug('lsp.definition', 'Found doc_id', {
      docId: match.docId,
      position: params.position,
    });

    // doc_idからドキュメント情報を取得
    const lookupResult = await lookupDocument(match.docId, config, { cwd });

    if (!lookupResult.success) {
      logger.debug('lsp.definition', 'Document not found', {
        docId: match.docId,
        error: lookupResult.message,
      });
      return null;
    }

    // ドキュメントファイルへのLocationを返す
    const documentPath = path.resolve(cwd, lookupResult.path);
    const documentUri = `file://${documentPath}`;

    return {
      uri: documentUri,
      range: {
        start: { line: 0, character: 0 },
        end: { line: 0, character: 0 },
      },
    };
  };
}
