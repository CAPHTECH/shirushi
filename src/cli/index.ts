/**
 * Shirushi CLI Entry Point
 *
 * ドキュメントID管理・検証ツールのCLIエントリーポイント。
 * Commander.jsを使用してサブコマンドを提供する。
 *
 * コマンド:
 * - lint: ドキュメントとインデックスの整合性を検証
 * - scan: ドキュメントをスキャンしてメタ情報を一覧表示
 */

import { pathToFileURL } from 'node:url';

import { Command } from 'commander';

import { logger } from '../utils/logger.js';

import { registerAssignCommand } from './commands/assign.js';
import { registerLintCommand } from './commands/lint.js';
import { registerRehashCommand } from './commands/rehash.js';
import { registerScanCommand } from './commands/scan.js';

// package.jsonからバージョンを取得（ビルド時に解決される）
const VERSION = '0.1.0';

/**
 * CLIプログラムを作成
 */
function createProgram(): Command {
  const program = new Command();

  program
    .name('shirushi')
    .description(
      'Document ID management and validation system for Git repositories'
    )
    .version(VERSION);

  // サブコマンドを登録
  registerAssignCommand(program);
  registerLintCommand(program);
  registerRehashCommand(program);
  registerScanCommand(program);

  return program;
}

/**
 * CLIを実行
 */
export function run(): void {
  logger.debug('system.startup', 'Shirushi CLI initializing');

  const program = createProgram();

  // コマンドライン引数をパース
  program.parse(process.argv);

  // サブコマンドが指定されていない場合はヘルプを表示
  if (process.argv.length < 3) {
    program.help();
  }
}

// 直接実行された場合
const executedDirectly =
  pathToFileURL(process.argv[1] ?? '').href === import.meta.url;

if (executedDirectly) {
  run();
}
