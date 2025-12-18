/**
 * Rehash Command
 *
 * 全ドキュメントのcontent_hashを再計算し、インデックスを更新する。
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
  loadIndexFile,
  getDocIdFromEntry,
  type IndexFile,
  type IndexEntry,
} from '@/core/index-manager';
import { acquireLock, releaseLock } from '@/core/lock';
import { scanDocuments } from '@/core/scanner';
import { calculateContentHash } from '@/utils/content-hash';
import { logger } from '@/utils/logger';
import { normalizePath } from '@/utils/path';

import type { OutputFormat } from '@/cli/output/formatters';
import type { Command } from 'commander';

/**
 * rehashコマンドオプション
 */
export interface RehashOptions {
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
interface RehashCliOptions {
  config?: string;
  format?: string;
  dryRun?: boolean;
}

/**
 * 更新エントリ
 */
interface RehashEntry {
  path: string;
  docId: string | undefined;
  oldHash: string | undefined;
  newHash: string;
  action: 'added' | 'updated' | 'unchanged';
}

/**
 * rehash結果
 */
interface RehashResult {
  entries: RehashEntry[];
  summary: {
    totalDocuments: number;
    added: number;
    updated: number;
    unchanged: number;
    skipped: number;
  };
}

/**
 * rehashコマンドを実行
 */
export async function executeRehash(options: RehashOptions): Promise<number> {
  const cwd = options.cwd ?? process.cwd();
  const format = options.format ?? 'table';
  const dryRun = options.dryRun ?? false;

  logger.debug('rehash.start', 'Starting rehash command', { options });

  // 0. ロックを取得（dry-runでなければ）
  if (!dryRun) {
    const lockResult = acquireLock(cwd, 'rehash');
    if (isLeft(lockResult)) {
      console.error(`Error: ${lockResult.left.message}`);
      return 1;
    }
  }

  try {
    return await executeRehashInternal(options, cwd, format, dryRun);
  } finally {
    // ロックを解放（dry-runでなければ）
    if (!dryRun) {
      releaseLock(cwd);
    }
  }
}

/**
 * rehashコマンドの内部実装
 */
async function executeRehashInternal(
  options: RehashOptions,
  cwd: string,
  format: OutputFormat,
  dryRun: boolean
): Promise<number> {
  // 1. 設定を読み込み
  const loaded = await loadConfigForCommand(options.config, cwd, 'rehash');
  if (!loaded) {
    return 1;
  }
  const { config } = loaded;

  // content_integrityが無効の場合は警告
  if (!config.content_integrity?.enabled) {
    console.warn(
      'Warning: content_integrity is not enabled in config. Hashes will be calculated but feature is disabled.'
    );
  }

  // 2. インデックスを読み込み
  const idField = config.id_field ?? 'doc_id';
  let indexFile: IndexFile | null;
  try {
    indexFile = await loadIndexFile(config.index_file, cwd, idField);
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Unknown error';
    console.error(`Error loading index: ${message}`);
    return 1;
  }

  if (!indexFile) {
    console.error('Error: Index file does not exist. Run "shirushi assign" first.');
    return 1;
  }

  // パスでインデックスエントリをマップ化
  const indexByPath = new Map<string, IndexEntry>();
  for (const entry of indexFile.documents) {
    indexByPath.set(entry.path, entry);
  }

  // 3. ドキュメントをスキャン（preserveContent: true）
  const scanResult = await scanDocuments(config, { cwd, preserveContent: true });
  logger.debug('rehash.scan', 'Documents scanned', {
    count: scanResult.documents.length,
  });

  // 4. 各ドキュメントのハッシュを計算・比較
  const result: RehashResult = {
    entries: [],
    summary: {
      totalDocuments: scanResult.documents.length,
      added: 0,
      updated: 0,
      unchanged: 0,
      skipped: 0,
    },
  };

  for (const doc of scanResult.documents) {
    // contentがない場合はスキップ
    if (doc.content === undefined) {
      result.summary.skipped++;
      continue;
    }

    // ハッシュを計算
    const newHash = calculateContentHash(doc.content);
    const normalizedPath = normalizePath(doc.path);
    const indexEntry = indexByPath.get(normalizedPath);

    if (!indexEntry) {
      // インデックスにエントリがない場合はスキップ
      result.summary.skipped++;
      continue;
    }

    const oldHash = indexEntry.content_hash;
    let action: 'added' | 'updated' | 'unchanged';

    if (!oldHash) {
      action = 'added';
      result.summary.added++;
    } else if (oldHash !== newHash) {
      action = 'updated';
      result.summary.updated++;
    } else {
      action = 'unchanged';
      result.summary.unchanged++;
    }

    result.entries.push({
      path: doc.path,
      docId: getDocIdFromEntry(indexEntry, idField),
      oldHash,
      newHash,
      action,
    });

    // インデックスエントリを更新
    indexEntry.content_hash = newHash;
  }

  // 5. インデックスファイルを書き込み（dry-runでなければ）
  if (!dryRun && (result.summary.added > 0 || result.summary.updated > 0)) {
    const yaml = await import('js-yaml');
    const { writeFile } = await import('node:fs/promises');

    const indexPath = path.isAbsolute(config.index_file)
      ? config.index_file
      : path.join(cwd, config.index_file);

    const content = yaml.dump(indexFile, { indent: 2, lineWidth: -1 });
    await writeFile(indexPath, content, 'utf8');

    logger.debug('rehash.write', 'Index file updated', { path: indexPath });
  }

  // 6. 結果出力
  console.log(formatRehashResult(result, format, dryRun));

  return 0;
}

/**
 * 結果をフォーマット
 */
function formatRehashResult(
  result: RehashResult,
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

  // 変更があったエントリのみ表示
  const changedEntries = result.entries.filter((e) => e.action !== 'unchanged');

  if (changedEntries.length > 0) {
    lines.push('Changes:');
    for (const entry of changedEntries) {
      const actionLabel = entry.action === 'added' ? '[ADD]' : '[UPD]';
      const hashPreview = entry.newHash.slice(0, 8);
      lines.push(`  ${actionLabel} ${entry.path} -> ${hashPreview}...`);
    }
    lines.push('');
  }

  // サマリー
  lines.push(
    `Summary: ${result.summary.added} added, ${result.summary.updated} updated, ${result.summary.unchanged} unchanged, ${result.summary.skipped} skipped`
  );

  if (changedEntries.length === 0 && !dryRun) {
    lines.push('');
    lines.push('No changes needed.');
  }

  return lines.join('\n');
}

/**
 * Commanderにrehashコマンドを登録
 */
export function registerRehashCommand(program: Command): void {
  program
    .command('rehash')
    .description('Recalculate content hashes for all documents')
    .option('-c, --config <path>', 'Path to config file')
    .option(
      '-f, --format <format>',
      'Output format (table, json)',
      'table'
    )
    .option('-n, --dry-run', 'Preview changes without writing to files')
    .action(async (opts: RehashCliOptions) => {
      const exitCode = await executeRehash({
        ...(opts.config ? { config: opts.config } : {}),
        ...(opts.format ? { format: opts.format as OutputFormat } : {}),
        ...(opts.dryRun ? { dryRun: opts.dryRun } : {}),
      });
      process.exit(exitCode);
    });
}
