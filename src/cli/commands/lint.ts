/**
 * Lint Command
 *
 * ドキュメントとインデックスの整合性を検証する。
 * 終了コード: 0 (成功) / 1 (エラーあり)
 *
 * オプション:
 * - --format <table|json>: 出力フォーマット
 * - --quiet: エラーパスのみ出力
 *
 * 注: --base, --changed-only オプションは v0.2 で実装予定
 */

import { loadConfigForCommand } from '@/cli/helpers/config';
import {
  buildLintResult,
  formatLintResult,
  problemToLintError,
  validationErrorToLintError,
  formatLintQuiet,
} from '@/cli/output/reporters';
import {
  loadIndexFile,
  validateIndexConsistency,
} from '@/core/index-manager';
import { scanDocuments } from '@/core/scanner';
import { validateDocId } from '@/core/validator';
import { logger } from '@/utils/logger';

import type { OutputFormat } from '@/cli/output/formatters';
import type { LintError } from '@/cli/output/reporters';
import type { ShirushiConfig } from '@/config/schema';
import type { ScanResult } from '@/core/scanner';
import type { Command } from 'commander';

/**
 * lintコマンドオプション
 */
export interface LintOptions {
  config?: string;
  format?: OutputFormat;
  quiet?: boolean;
}

/**
 * Commander.jsアクションハンドラ用の型定義
 */
interface LintCliOptions {
  config?: string;
  format?: string;
  quiet?: boolean;
}

/**
 * ドキュメントの問題を収集する
 */
function collectDocumentIssues(
  scanResult: ScanResult,
  config: ShirushiConfig
): LintError[] {
  const issues: LintError[] = [];

  for (const doc of scanResult.documents) {
    // パース時の問題を追加
    for (const problem of doc.problems) {
      issues.push(problemToLintError(doc.path, problem));
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
          issues.push(validationErrorToLintError(doc.path, error));
        }
      }
    }
  }

  return issues;
}

/**
 * インデックス整合性を検証する
 */
async function validateIndex(
  scanResult: ScanResult,
  indexFilePath: string,
  cwd: string
): Promise<LintError[]> {
  try {
    const indexFile = await loadIndexFile(indexFilePath, cwd);
    const indexResult = validateIndexConsistency(
      scanResult.documents,
      indexFile,
      cwd
    );
    return indexResult.errors;
  } catch (error) {
    const message =
      error instanceof Error ? error.message : 'Unknown index error';
    console.error(`Error loading index: ${message}`);
    logger.warn('lint.index', 'Failed to load index file', { error: message });
    return [];
  }
}

/**
 * lintコマンドを実行
 */
export async function executeLint(options: LintOptions): Promise<number> {
  const cwd = process.cwd();
  const format = options.format ?? 'table';

  logger.debug('lint.start', 'Starting lint command', { options });

  // 1. 設定を読み込み
  const loaded = await loadConfigForCommand(options.config, cwd, 'lint');
  if (!loaded) {
    return 1;
  }
  const { config } = loaded;

  // 2. ドキュメントをスキャン
  const scanResult = await scanDocuments(config, { cwd });
  logger.debug('lint.scan', 'Documents scanned', {
    count: scanResult.documents.length,
  });

  // 3. 問題を収集
  const documentIssues = collectDocumentIssues(scanResult, config);

  // 4. インデックス整合性を検証
  const indexIssues = await validateIndex(scanResult, config.index_file, cwd);

  // 5. 結果を構築
  const allIssues = [...documentIssues, ...indexIssues];
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
    .option('-c, --config <path>', 'Path to config file')
    .option(
      '-f, --format <format>',
      'Output format (table, json)',
      'table'
    )
    .option('-q, --quiet', 'Quiet mode (only show file paths with errors)')
    .action(async (opts: LintCliOptions) => {
      const exitCode = await executeLint({
        ...(opts.config ? { config: opts.config } : {}),
        ...(opts.format ? { format: opts.format as OutputFormat } : {}),
        ...(opts.quiet ? { quiet: opts.quiet } : {}),
      });
      process.exit(exitCode);
    });
}
