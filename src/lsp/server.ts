/**
 * Shirushi LSP Server
 *
 * @see docid からドキュメントへのナビゲーションを提供するLSPサーバー。
 * Claude Codeおよび他のLSP対応エディタと統合可能。
 *
 * 対応メソッド:
 * - goToDefinition: doc_id → ドキュメントファイルへジャンプ
 * - hover: doc_id上でドキュメント情報を表示
 * - findReferences: doc_idを参照しているソースファイル一覧
 *
 * @see ADR-0010: LSP Server Integration
 * @see Issue #26
 */

import {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  TextDocumentSyncKind,
} from 'vscode-languageserver/node.js';
import { TextDocument } from 'vscode-languageserver-textdocument';

import { loadConfig } from '@/config/loader';
import { logger } from '@/utils/logger';

import { createDefinitionHandler } from './handlers/definition';
import { createHoverHandler } from './handlers/hover';
import { createReferencesHandler } from './handlers/references';

import type { ShirushiConfig } from '@/config/schema';
import type { InitializeParams, InitializeResult } from 'vscode-languageserver';

/**
 * LSPサーバーオプション
 */
export interface LspServerOptions {
  /** プロジェクトルートディレクトリ */
  cwd?: string;
  /** 設定ファイルパス */
  configPath?: string | undefined;
}

/**
 * LSPサーバーを起動
 *
 * LSPサーバーはstdio経由でクライアントと通信する。
 * この関数はサーバーを起動し、connection.listenを開始する。
 * 非同期初期化は内部のハンドラで行われる。
 *
 * @param options - サーバーオプション
 */
export function startLspServer(options: LspServerOptions = {}): void {
  const cwd = options.cwd ?? process.cwd();

  logger.debug('lsp.server', 'Starting Shirushi LSP server', { cwd });

  // コネクションを作成（stdio transport）
  // process.stdin/stdoutを明示的に指定してstdio transportを使用
  const connection = createConnection(
    ProposedFeatures.all,
    process.stdin,
    process.stdout
  );

  // ドキュメント管理
  const documents = new TextDocuments(TextDocument);

  // 設定キャッシュ
  let config: ShirushiConfig | null = null;

  /**
   * 設定を読み込み（キャッシュあり）
   */
  async function getConfig(): Promise<ShirushiConfig | null> {
    if (config) {
      return config;
    }

    try {
      const loaded = await loadConfig({
        cwd,
        ...(options.configPath ? { configPath: options.configPath } : {}),
      });
      config = loaded.config;
      logger.debug('lsp.server', 'Config loaded', {
        idFormat: loaded.config.id_format,
      });
      return config;
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      logger.warn('lsp.server', 'Failed to load config', { error: message });
      return null;
    }
  }

  // Initializeハンドラ
  connection.onInitialize((_params: InitializeParams): InitializeResult => {
    logger.debug('lsp.server', 'Initializing LSP server');

    return {
      capabilities: {
        textDocumentSync: TextDocumentSyncKind.Incremental,
        definitionProvider: true,
        hoverProvider: true,
        referencesProvider: true,
      },
    };
  });

  // Initializedハンドラ
  // void返却でラップしてPromise返却の警告を回避
  connection.onInitialized(() => {
    logger.debug('lsp.server', 'LSP server initialized');

    // 設定を事前読み込み（非同期だがvoid返却）
    void getConfig();
  });

  // Go to Definition
  connection.onDefinition(async (params) => {
    const cfg = await getConfig();
    if (!cfg) {
      return null;
    }

    const handler = createDefinitionHandler({
      cwd,
      config: cfg,
      documents,
    });

    return handler(params);
  });

  // Hover
  connection.onHover(async (params) => {
    const cfg = await getConfig();
    if (!cfg) {
      return null;
    }

    const handler = createHoverHandler({
      cwd,
      config: cfg,
      documents,
    });

    return handler(params);
  });

  // Find References
  connection.onReferences(async (params) => {
    const cfg = await getConfig();
    if (!cfg) {
      return null;
    }

    const handler = createReferencesHandler({
      cwd,
      config: cfg,
      documents,
    });

    return handler(params);
  });

  // ドキュメント変更時に設定をリセット（設定ファイルが変更された場合に対応）
  documents.onDidChangeContent((change) => {
    // .shirushi.yml が変更された場合は設定をリセット
    if (change.document.uri.endsWith('.shirushi.yml') ||
        change.document.uri.endsWith('.shirushi.yaml')) {
      config = null;
      logger.debug('lsp.server', 'Config cache invalidated');
    }
  });

  // ドキュメントリスナーを接続
  documents.listen(connection);

  // コネクションをリッスン
  connection.listen();

  logger.debug('lsp.server', 'LSP server listening');
}
