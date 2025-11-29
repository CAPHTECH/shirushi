/**
 * Scan Command
 *
 * ドキュメントをスキャンし、doc_idとメタ情報の一覧を出力する。
 *
 * オプション:
 * - --format <table|json|yaml>: 出力フォーマット
 */

import {
  toScanOutput,
  formatScanResult,
} from '@/cli/output/formatters';
import { loadConfig } from '@/config/loader';
import { scanDocuments } from '@/core/scanner';
import { logger } from '@/utils/logger';

import type { OutputFormat } from '@/cli/output/formatters';
import type { Command } from 'commander';

/**
 * scanコマンドオプション
 */
export interface ScanOptions {
  config?: string;
  format?: OutputFormat;
}

/**
 * Commander.jsアクションハンドラ用の型定義
 */
interface ScanCliOptions {
  config?: string;
  format?: string;
}

/**
 * scanコマンドを実行
 */
export async function executeScan(options: ScanOptions): Promise<number> {
  const cwd = process.cwd();
  const format = options.format ?? 'table';

  logger.debug('scan.start', 'Starting scan command', { options });

  // 1. 設定を読み込み
  let config;
  try {
    const loaded = await loadConfig({
      cwd,
      ...(options.config ? { configPath: options.config } : {}),
    });
    config = loaded.config;
    logger.debug('scan.config', 'Config loaded', { path: loaded.path });
  } catch (error) {
    const message =
      error instanceof Error ? error.message : 'Unknown config error';
    console.error(`Error loading config: ${message}`);
    return 1;
  }

  // 2. ドキュメントをスキャン
  const scanResult = await scanDocuments(config, { cwd });
  logger.debug('scan.complete', 'Documents scanned', {
    count: scanResult.documents.length,
  });

  // 3. 出力形式に変換
  const output = toScanOutput(scanResult.documents, scanResult.summary);

  // 4. 出力
  console.log(formatScanResult(output, format));

  return 0;
}

/**
 * Commanderにscanコマンドを登録
 */
export function registerScanCommand(program: Command): void {
  program
    .command('scan')
    .description('Scan documents and list doc_id with metadata')
    .option('-c, --config <path>', 'Path to config file')
    .option(
      '-f, --format <format>',
      'Output format (table, json, yaml)',
      'table'
    )
    .action(async (opts: ScanCliOptions) => {
      const exitCode = await executeScan({
        ...(opts.config ? { config: opts.config } : {}),
        ...(opts.format ? { format: opts.format as OutputFormat } : {}),
      });
      process.exit(exitCode);
    });
}
