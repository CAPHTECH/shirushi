/**
 * Assign Command
 *
 * doc_id未設定のドキュメントにIDを自動生成・埋め込み。
 * 終了コード: 0 (成功) / 1 (エラーあり)
 *
 * オプション:
 * - --format <table|json>: 出力フォーマット
 * - --dry-run: 変更を加えずにプレビュー
 */

import path from 'node:path';

import { isLeft } from 'fp-ts/Either';

import { loadConfigForCommand } from '@/cli/helpers/config';
import {
  createTransactionContext,
  prepareChange,
  prepareIndexBackup,
  applyChanges,
  applyIndexUpdate,
} from '@/core/assign-transaction';
import { generateDocId } from '@/core/generator';
import { loadIndexFile } from '@/core/index-manager';
import { scanDocuments } from '@/core/scanner';
import { validateDocId } from '@/core/validator';
import { ShirushiErrors } from '@/errors/definitions';
import { logger } from '@/utils/logger';

import type { OutputFormat } from '@/cli/output/formatters';
import type { IndexEntry } from '@/core/index-manager';
import type { NewIndexEntry } from '@/core/index-writer';
import type { Command } from 'commander';

/**
 * assignコマンドオプション
 */
export interface AssignOptions {
  config?: string;
  format?: OutputFormat;
  /** ベースディレクトリ（テスト用、デフォルト: process.cwd()） */
  cwd?: string;
  /** dry-runモード（ファイルを変更しない） */
  dryRun?: boolean;
}

/**
 * Commander.jsアクションハンドラ用の型定義
 */
interface AssignCliOptions {
  config?: string;
  format?: string;
  dryRun?: boolean;
}

/**
 * 割り当て結果エントリ
 */
export interface AssignEntry {
  path: string;
  generatedId: string;
  written: boolean;
}

/**
 * 割り当てエラー
 */
export interface AssignError {
  path: string;
  code: string;
  message: string;
}

/**
 * 割り当て結果
 */
export interface AssignResult {
  assigned: AssignEntry[];
  skipped: string[];
  errors: AssignError[];
  summary: {
    totalScanned: number;
    assigned: number;
    skipped: number;
    errors: number;
  };
}

/**
 * assignコマンドを実行
 */
export async function executeAssign(options: AssignOptions): Promise<number> {
  const cwd = options.cwd ?? process.cwd();
  const format = options.format ?? 'table';
  const dryRun = options.dryRun ?? false;

  logger.debug('assign.start', 'Starting assign command', { options });

  // 1. 設定を読み込み
  const loaded = await loadConfigForCommand(options.config, cwd, 'assign');
  if (!loaded) {
    return 1;
  }
  const { config } = loaded;

  // 2. インデックスを読み込み
  const idField = config.id_field ?? 'doc_id';
  const indexFile = await loadIndexFile(config.index_file, cwd, idField);
  const indexEntries = indexFile?.documents ?? [];

  // 3. ドキュメントをスキャン
  const scanResult = await scanDocuments(config, { cwd });
  logger.debug('assign.scan', 'Documents scanned', {
    count: scanResult.documents.length,
  });

  // 4. doc_id未設定のドキュメントをフィルタ
  const docsWithoutId = scanResult.documents.filter((doc) => !doc.docId);
  const docsWithId = scanResult.documents.filter((doc) => doc.docId);

  const result: AssignResult = {
    assigned: [],
    skipped: docsWithId.map((d) => d.path),
    errors: [],
    summary: {
      totalScanned: scanResult.documents.length,
      assigned: 0,
      skipped: docsWithId.length,
      errors: 0,
    },
  };

  if (docsWithoutId.length === 0) {
    console.log(formatAssignResult(result, format, dryRun));
    return 0;
  }

  // 5. トランザクションコンテキストを作成
  const txContext = createTransactionContext(config.index_file, cwd, idField);

  // 6. インデックスをバックアップ
  if (!dryRun) {
    const backupResult = await prepareIndexBackup(txContext);
    if (isLeft(backupResult)) {
      console.error(`Error: ${backupResult.left.message}`);
      return 1;
    }
  }

  // 7. 各ドキュメントに対してID生成
  const newIndexEntries: NewIndexEntry[] = [];
  // インデックスエントリのコピー（serial採番用に更新していく）
  const workingIndexEntries = [...indexEntries];

  for (const doc of docsWithoutId) {
    // ID生成
    const genResult = generateDocId({
      documentPath: doc.path,
      documentMeta: doc.metadata,
      config,
      indexEntries: workingIndexEntries,
    });

    if (isLeft(genResult)) {
      result.errors.push({
        path: doc.path,
        code: genResult.left[0]?.code ?? ShirushiErrors.ASSIGN_GENERATION_FAILED.code,
        message: genResult.left.map((e) => e.message).join('; '),
      });
      continue;
    }

    const { docId } = genResult.right;

    // 生成したIDを検証
    const validation = validateDocId(
      { docId, documentPath: doc.path, documentMeta: doc.metadata },
      config
    );
    if (!validation.valid) {
      result.errors.push({
        path: doc.path,
        code: ShirushiErrors.ASSIGN_VALIDATION_FAILED.code,
        message: validation.errors.map((e) => e.message).join('; '),
      });
      continue;
    }

    // 変更を準備（元内容をバックアップ）
    if (!dryRun) {
      const absolutePath = path.join(cwd, doc.path);
      const prepResult = await prepareChange(txContext, absolutePath, docId, doc.kind);
      if (isLeft(prepResult)) {
        result.errors.push({
          path: doc.path,
          code: prepResult.left.code,
          message: prepResult.left.message,
        });
        continue;
      }
    }

    // 結果に追加
    result.assigned.push({
      path: doc.path,
      generatedId: docId,
      written: false, // 後で更新
    });

    // インデックスエントリを追加（次のserial採番用）
    const newEntry = {
      [idField]: docId,
      path: doc.path,
    };
    workingIndexEntries.push(newEntry as IndexEntry);

    // インデックス更新用エントリを準備
    const indexEntry: NewIndexEntry = {
      docId,
      path: doc.path,
    };
    if (typeof doc.metadata.title === 'string') {
      indexEntry.title = doc.metadata.title;
    }
    if (typeof doc.metadata.doc_type === 'string') {
      indexEntry.docType = doc.metadata.doc_type;
    }
    newIndexEntries.push(indexEntry);
  }

  // 8. ファイル書き込み（dry-runでなければ）
  if (!dryRun && result.assigned.length > 0) {
    // 変更を適用
    const applyResult = await applyChanges(txContext);
    if (isLeft(applyResult)) {
      result.errors.push({
        path: applyResult.left.path,
        code: applyResult.left.code,
        message: applyResult.left.message,
      });
      // ロールバック済みなので、assigned をクリア
      result.assigned = [];
    } else {
      // 書き込み成功をマーク
      for (const entry of result.assigned) {
        entry.written = true;
      }

      // インデックスを更新
      const indexResult = await applyIndexUpdate(txContext, newIndexEntries);
      if (isLeft(indexResult)) {
        result.errors.push({
          path: config.index_file,
          code: indexResult.left.code,
          message: indexResult.left.message,
        });
        // ロールバック済みなので、assigned をクリア
        result.assigned = [];
      }
    }
  }

  // 9. サマリー更新
  result.summary.assigned = result.assigned.length;
  result.summary.errors = result.errors.length;

  // 10. 結果出力
  console.log(formatAssignResult(result, format, dryRun));

  // 11. 終了コード
  return result.errors.length > 0 ? 1 : 0;
}

/**
 * 結果をフォーマット
 */
function formatAssignResult(
  result: AssignResult,
  format: OutputFormat,
  dryRun: boolean
): string {
  if (format === 'json') {
    return JSON.stringify({ ...result, dryRun }, null, 2);
  }

  // table形式
  const lines: string[] = [];

  if (dryRun) {
    lines.push('[DRY-RUN] Preview of changes:');
    lines.push('');
  }

  // 割り当て結果
  if (result.assigned.length > 0) {
    lines.push('Assigned:');
    for (const entry of result.assigned) {
      const status = dryRun ? '' : entry.written ? ' (written)' : ' (pending)';
      lines.push(`  ${entry.path} -> ${entry.generatedId}${status}`);
    }
    lines.push('');
  }

  // スキップ
  if (result.skipped.length > 0 && result.skipped.length <= 10) {
    lines.push('Skipped (already has doc_id):');
    for (const p of result.skipped) {
      lines.push(`  ${p}`);
    }
    lines.push('');
  } else if (result.skipped.length > 10) {
    lines.push(`Skipped: ${result.skipped.length} documents (already have doc_id)`);
    lines.push('');
  }

  // エラー
  if (result.errors.length > 0) {
    lines.push('Errors:');
    for (const error of result.errors) {
      lines.push(`  [${error.code}] ${error.path}: ${error.message}`);
    }
    lines.push('');
  }

  // サマリー
  lines.push(
    `Summary: ${result.summary.assigned} assigned, ${result.summary.skipped} skipped, ${result.summary.errors} errors`
  );

  return lines.join('\n');
}

/**
 * Commanderにassignコマンドを登録
 */
export function registerAssignCommand(program: Command): void {
  program
    .command('assign')
    .description('Assign doc_id to documents without one')
    .option('-c, --config <path>', 'Path to config file')
    .option(
      '-f, --format <format>',
      'Output format (table, json)',
      'table'
    )
    .option('-n, --dry-run', 'Preview changes without writing to files')
    .action(async (opts: AssignCliOptions) => {
      const exitCode = await executeAssign({
        ...(opts.config ? { config: opts.config } : {}),
        ...(opts.format ? { format: opts.format as OutputFormat } : {}),
        ...(opts.dryRun ? { dryRun: opts.dryRun } : {}),
      });
      process.exit(exitCode);
    });
}
