/**
 * Find References Handler
 *
 * doc_idを参照しているソースファイル一覧を返す。
 *
 * @see ADR-0010: LSP Server Integration
 */

import { scanSourceReferences } from '@/core/source-ref-scanner';
import { findDocIdAtPosition } from '@/lsp/utils/pattern-matcher';
import { logger } from '@/utils/logger';

import type { ShirushiConfig } from '@/config/schema';
import type { TextDocuments, Location, Position } from 'vscode-languageserver';
import type { TextDocument } from 'vscode-languageserver-textdocument';

/**
 * Find References ハンドラオプション
 */
export interface ReferencesHandlerOptions {
  /** プロジェクトルートディレクトリ */
  cwd: string;
  /** Shirushi設定 */
  config: ShirushiConfig;
  /** ドキュメント管理 */
  documents: TextDocuments<TextDocument>;
}

/**
 * Find References ハンドラを作成
 *
 * @param options - ハンドラオプション
 * @returns LSP onReferencesハンドラ関数
 */
export function createReferencesHandler(options: ReferencesHandlerOptions) {
  const { cwd, config, documents } = options;

  return async (params: {
    textDocument: { uri: string };
    position: Position;
  }): Promise<Location[] | null> => {
    const document = documents.get(params.textDocument.uri);
    if (!document) {
      return null;
    }

    const text = document.getText();
    const match = findDocIdAtPosition(text, params.position, config);

    if (!match) {
      return null;
    }

    logger.debug('lsp.references', 'Finding references for doc_id', {
      docId: match.docId,
    });

    // source_referencesが設定されていない場合は空を返す
    if (
      !config.content_integrity?.source_references ||
      config.content_integrity.source_references.length === 0
    ) {
      logger.debug(
        'lsp.references',
        'No source_references configured, skipping scan'
      );
      return [];
    }

    // ソースコード参照をスキャン
    const scanResult = await scanSourceReferences(config, cwd);

    // 指定されたdoc_idを参照しているものをフィルタ
    const matchingRefs = scanResult.references.filter(
      (ref) => ref.docId === match.docId
    );

    logger.debug('lsp.references', 'Found references', {
      docId: match.docId,
      count: matchingRefs.length,
    });

    // LocationsをLSP形式に変換
    const locations: Location[] = matchingRefs.map((ref) => ({
      uri: `file://${cwd}/${ref.sourcePath}`,
      range: {
        // lineNumberは1-indexed、LSPは0-indexed
        start: { line: ref.lineNumber - 1, character: 0 },
        end: { line: ref.lineNumber - 1, character: 0 },
      },
    }));

    return locations;
  };
}
