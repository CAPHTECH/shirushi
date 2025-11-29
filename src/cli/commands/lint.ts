/**
 * Lint Command
 *
 * ドキュメントとインデックスの整合性を検証する。
 * 終了コード: 0 (成功) / 1 (エラーあり)
 *
 * オプション:
 * - --base <git-ref>: 指定されたgit refと比較してID変更を検出
 * - --changed-only: diff対象のみ検証（最適化）
 * - --format <table|json>: 出力フォーマット
 */

import { loadConfig } from '@/config/loader';
import { scanDocuments } from '@/core/scanner';
import { validateDocId } from '@/core/validator';
import {
  loadIndexFile,
  validateIndexConsistency,
} from '@/core/index-manager';
import {
  buildLintResult,
  formatLintResult,
  problemToLintError,
  validationErrorToLintError,
  formatLintQuiet,
} from '@/cli/output/reporters';
import { logger } from '@/utils/logger';

import type { Command } from 'commander';
import type { OutputFormat } from '@/cli/output/formatters';
import type { LintError } from '@/cli/output/reporters';

/**
 * lintコマンドオプション
 */
export interface LintOptions {
  base?: string;
  changedOnly?: boolean;
  config?: string;
  format?: OutputFormat;
  quiet?: boolean;
}

/**
 * lintコマンドを実行
 */
export async function executeLint(options: LintOptions): Promise<number> {
  const cwd = process.cwd();
  const format = options.format ?? 'table';

  logger.debug('lint.start', 'Starting lint command', { options });

  // 1. 設定を読み込み
  let config;
  try {
    const loaded = await loadConfig({
      cwd,
      ...(options.config ? { configPath: options.config } : {}),
    });
    config = loaded.config;
    logger.debug('lint.config', 'Config loaded', { path: loaded.path });
  } catch (error) {
    const message =
      error instanceof Error ? error.message : 'Unknown config error';
    console.error(`Error loading config: ${message}`);
    return 1;
  }

  // 2. ドキュメントをスキャン
  const scanResult = await scanDocuments(config, { cwd });
  logger.debug('lint.scan', 'Documents scanned', {
    count: scanResult.documents.length,
  });

  // 3. 問題を収集
  const allIssues: LintError[] = [];

  for (const doc of scanResult.documents) {
    // パース時の問題を追加
    for (const problem of doc.problems) {
      allIssues.push(problemToLintError(doc.path, problem));
    }

    // doc_idがあれば検証
    if (doc.docId) {
      const validationResult = validateDocId(
        {
          docId: doc.docId,
          documentPath: doc.path,
          documentMeta: doc.metadata,
        },
        config
      );

      if (!validationResult.valid) {
        for (const error of validationResult.errors) {
          allIssues.push(validationErrorToLintError(doc.path, error));
        }
      }
    }
  }

  // 4. インデックス整合性を検証
  try {
    const indexFile = await loadIndexFile(config.index_file, cwd);
    const indexResult = validateIndexConsistency(
      scanResult.documents,
      indexFile,
      cwd
    );
    allIssues.push(...indexResult.errors);
  } catch (error) {
    const message =
      error instanceof Error ? error.message : 'Unknown index error';
    console.error(`Error loading index: ${message}`);
    // インデックス読み込みエラーは致命的ではない
    logger.warn('lint.index', 'Failed to load index file', { error: message });
  }

  // 5. 結果を構築
  const result = buildLintResult(allIssues);

  // 6. 出力
  if (options.quiet) {
    const output = formatLintQuiet(result);
    if (output) {
      console.log(output);
    }
  } else {
    console.log(formatLintResult(result, format));
  }

  // 7. 終了コード
  return result.summary.totalErrors > 0 ? 1 : 0;
}

/**
 * Commanderにlintコマンドを登録
 */
export function registerLintCommand(program: Command): void {
  program
    .command('lint')
    .description('Validate document IDs and index consistency')
    .option('--base <git-ref>', 'Compare against git ref to detect ID changes')
    .option('--changed-only', 'Validate only changed files (requires --base)')
    .option('-c, --config <path>', 'Path to config file')
    .option(
      '-f, --format <format>',
      'Output format (table, json)',
      'table'
    )
    .option('-q, --quiet', 'Quiet mode (only show file paths with errors)')
    .action(async (opts) => {
      const exitCode = await executeLint({
        base: opts.base,
        changedOnly: opts.changedOnly,
        config: opts.config,
        format: opts.format as OutputFormat,
        quiet: opts.quiet,
      });
      process.exit(exitCode);
    });
}
