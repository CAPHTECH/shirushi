/**
 * LSP Command
 *
 * ShirushiをLSPサーバーとして起動する。
 * Claude CodeやVSCode等のLSP対応エディタと統合可能。
 *
 * 使用例:
 * ```bash
 * shirushi lsp
 * ```
 *
 * @see ADR-0010: LSP Server Integration
 * @see Issue #26
 */

import { startLspServer } from '@/lsp/server';
import { logger } from '@/utils/logger';

import type { Command } from 'commander';

/**
 * LSPコマンドオプション
 */
export interface LspOptions {
  /** 設定ファイルパス */
  config?: string;
  /** ベースディレクトリ（テスト用） */
  cwd?: string;
}

/**
 * Commander.jsアクションハンドラ用の型定義
 */
interface LspCliOptions {
  config?: string;
}

/**
 * LSPコマンドを実行
 *
 * LSPサーバーを起動する。サーバーはstdioを介してLSPクライアントと通信する。
 *
 * @param options - コマンドオプション
 */
export function executeLsp(options: LspOptions): void {
  const cwd = options.cwd ?? process.cwd();

  logger.debug('lsp.command', 'Starting LSP server', { options });

  startLspServer({
    cwd,
    ...(options.config ? { configPath: options.config } : {}),
  });
}

/**
 * Commanderにlspコマンドを登録
 */
export function registerLspCommand(program: Command): void {
  program
    .command('lsp')
    .description('Start Shirushi LSP server for @see docid navigation')
    .option('-c, --config <path>', 'Path to config file')
    .action((opts: LspCliOptions) => {
      executeLsp(opts.config ? { config: opts.config } : {});
    });
}
