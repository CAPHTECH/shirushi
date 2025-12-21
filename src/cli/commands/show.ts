/**
 * Show Command
 *
 * doc_idからドキュメント情報を取得して表示する。
 * MCP統合（#25）やLSP統合（#26）の基盤となるコア機能。
 *
 * @see Issue #27: shirushi show コマンド
 *
 * オプション:
 * - --path-only, -p: パスのみ出力（シェル連携用）
 * - --meta-only, -m: メタデータのみ（本文なし）
 * - --format, -f: 出力形式（table, json, yaml）
 * - --json: JSON形式で出力（--format json のエイリアス）
 * - --yaml: YAML形式で出力（--format yaml のエイリアス）
 */

import { loadConfigForCommand } from '@/cli/helpers/config';
import {
  formatShowResult,
  type ShowOutputMode,
} from '@/cli/output/formatters';
import { lookupDocument } from '@/core/lookup';
import { logger } from '@/utils/logger';

import type { OutputFormat } from '@/cli/output/formatters';
import type { Command } from 'commander';

/**
 * showコマンドオプション
 */
export interface ShowOptions {
  config?: string;
  format?: OutputFormat;
  /** パスのみ出力 */
  pathOnly?: boolean;
  /** メタデータのみ（本文なし） */
  metaOnly?: boolean;
  /** ベースディレクトリ（テスト用） */
  cwd?: string;
}

/**
 * Commander.jsアクションハンドラ用の型定義
 */
interface ShowCliOptions {
  config?: string;
  format?: string;
  /** --jsonエイリアス */
  json?: boolean;
  /** --yamlエイリアス */
  yaml?: boolean;
  pathOnly?: boolean;
  metaOnly?: boolean;
}

/**
 * showコマンドを実行
 *
 * @param docId - 検索するdoc_id
 * @param options - コマンドオプション
 * @returns 終了コード（0: 成功、1: エラー）
 */
export async function executeShow(
  docId: string,
  options: ShowOptions
): Promise<number> {
  const cwd = options.cwd ?? process.cwd();

  logger.debug('show.start', 'Starting show command', { docId, options });

  // 1. 設定を読み込み
  const loaded = await loadConfigForCommand(options.config, cwd, 'show');
  if (!loaded) {
    return 1;
  }
  const { config } = loaded;

  // 2. ドキュメントをLookup
  const result = await lookupDocument(docId, config, { cwd });

  if (!result.success) {
    console.error(`Error: ${result.message}`);
    logger.error('show.lookup_failed', result.message, { code: result.code });
    return 1;
  }

  // 3. 出力モードを決定
  let outputMode: ShowOutputMode = 'full';
  if (options.pathOnly) {
    outputMode = 'path-only';
  } else if (options.metaOnly) {
    outputMode = 'meta-only';
  }

  // 4. フォーマットを決定
  const format = options.format ?? 'table';

  // 5. 出力
  const output = formatShowResult(result, format, outputMode);
  console.log(output);

  logger.debug('show.complete', 'Show command completed', { docId });

  return 0;
}

/**
 * Commanderにshowコマンドを登録
 */
export function registerShowCommand(program: Command): void {
  program
    .command('show <doc_id>')
    .description('Show document information by doc_id')
    .option('-c, --config <path>', 'Path to config file')
    .option(
      '-f, --format <format>',
      'Output format (table, json, yaml)',
      'table'
    )
    .option('--json', 'Output as JSON (alias for --format json)')
    .option('--yaml', 'Output as YAML (alias for --format yaml)')
    .option('-p, --path-only', 'Output path only (for shell integration)')
    .option('-m, --meta-only', 'Output metadata only (no content)')
    .action(async (docId: string, opts: ShowCliOptions) => {
      // --json/--yamlエイリアスを--formatに変換
      let format: OutputFormat | undefined;
      if (opts.json) {
        format = 'json';
      } else if (opts.yaml) {
        format = 'yaml';
      } else if (opts.format) {
        format = opts.format as OutputFormat;
      }

      const exitCode = await executeShow(docId, {
        ...(opts.config ? { config: opts.config } : {}),
        ...(format ? { format } : {}),
        ...(opts.pathOnly ? { pathOnly: opts.pathOnly } : {}),
        ...(opts.metaOnly ? { metaOnly: opts.metaOnly } : {}),
      });
      process.exit(exitCode);
    });
}
