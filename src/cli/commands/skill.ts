/**
 * Skill Command
 *
 * AIエージェント向けスキルファイルのインストール・管理を行う。
 * OpenSkills互換のディレクトリ構造をサポート。
 *
 * 対応ディレクトリ:
 * - .agent/skills/ (ユニバーサル、デフォルト)
 * - .claude/skills/ (Claude Code専用)
 * - ~/.agent/skills/ (グローバル、ユニバーサル)
 * - ~/.claude/skills/ (グローバル、Claude Code専用)
 * - カスタムパス (--path で指定)
 */

import { existsSync, mkdirSync, cpSync, rmSync } from 'node:fs';
import { homedir } from 'node:os';
import { join, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import chalk from 'chalk';

import { logger } from '@/utils/logger';

import type { Command } from 'commander';

/**
 * スキル名（パッケージ名と同一）
 */
const SKILL_NAME = 'shirushi';

/**
 * ターゲットプリセット
 * - agent: ユニバーサル（Cursor, Windsurf, Aider等）
 * - claude: Claude Code専用
 */
type TargetPreset = 'agent' | 'claude';

/**
 * スキルインストールオプション
 */
interface SkillInstallOptions {
  /** ターゲットプリセット（デフォルト: 'agent'） */
  target?: TargetPreset;
  /** グローバルインストール（デフォルト: false） */
  global?: boolean;
  /** カスタムインストールパス（target/globalを上書き） */
  path?: string;
  /** 既存スキルを上書き */
  force?: boolean;
}

/**
 * スキルアンインストールオプション
 */
interface SkillUninstallOptions {
  target?: TargetPreset;
  global?: boolean;
  path?: string;
}

/**
 * スキル検索パス情報
 */
interface SkillPathInfo {
  path: string;
  exists: boolean;
  priority: number;
  type: 'project' | 'global';
  preset: TargetPreset;
}

/**
 * スキルファイルのソースディレクトリを取得
 *
 * npmパッケージ内のskills/ディレクトリを参照する。
 * ESMの import.meta.url からパッケージルートを算出。
 *
 * パス構造:
 * - ビルド後: dist/cli/index.js → 2階層上がパッケージルート
 * - 開発時/テスト時: src/cli/commands/skill.ts → 3階層上がパッケージルート
 *
 * 両方のパスを試してスキルディレクトリを見つける。
 */
function getSkillSourceDir(): string {
  const currentFile = fileURLToPath(import.meta.url);

  // 複数の候補パスを試す（ビルド後と開発時で構造が異なる）
  const candidates = [
    // ビルド後: dist/cli/index.js → skills/
    join(dirname(dirname(dirname(currentFile))), 'skills', SKILL_NAME),
    // 開発時: src/cli/commands/skill.ts → skills/
    join(dirname(dirname(dirname(dirname(currentFile)))), 'skills', SKILL_NAME),
  ];

  for (const candidate of candidates) {
    if (existsSync(join(candidate, 'SKILL.md'))) {
      return candidate;
    }
  }

  // 見つからない場合は最初の候補を返す（エラーメッセージ用）
  // candidates は常に2要素あるため、undefinedにはならない
  return candidates[0] as string;
}

/**
 * インストール先パスを解決
 *
 * セキュリティ: カスタムパスはcwd配下またはhome配下のみ許可
 */
function resolveSkillPath(options: SkillInstallOptions): string {
  // カスタムパスが指定されていればそれを使用
  if (options.path) {
    const resolved = resolve(options.path);
    const cwd = process.cwd();
    const home = homedir();

    // cwd配下またはhome配下のみ許可（パストラバーサル対策）
    if (!resolved.startsWith(cwd) && !resolved.startsWith(home)) {
      throw new Error(
        `Security: Path must be under current directory or home directory: ${options.path}`
      );
    }

    return join(resolved, SKILL_NAME);
  }

  const target = options.target ?? 'agent';
  const base = options.global ? homedir() : process.cwd();
  const dirName = target === 'claude' ? '.claude' : '.agent';

  return join(base, dirName, 'skills', SKILL_NAME);
}

/**
 * 全検索パスを取得（優先順位順）
 *
 * OpenSkills互換の検索順序:
 * 1. ./.agent/skills/ (プロジェクト、ユニバーサル)
 * 2. ~/.agent/skills/ (グローバル、ユニバーサル)
 * 3. ./.claude/skills/ (プロジェクト、Claude専用)
 * 4. ~/.claude/skills/ (グローバル、Claude専用)
 */
function getAllSkillPaths(cwd: string = process.cwd()): SkillPathInfo[] {
  const paths: SkillPathInfo[] = [
    {
      path: join(cwd, '.agent', 'skills', SKILL_NAME),
      exists: false,
      priority: 1,
      type: 'project',
      preset: 'agent',
    },
    {
      path: join(homedir(), '.agent', 'skills', SKILL_NAME),
      exists: false,
      priority: 2,
      type: 'global',
      preset: 'agent',
    },
    {
      path: join(cwd, '.claude', 'skills', SKILL_NAME),
      exists: false,
      priority: 3,
      type: 'project',
      preset: 'claude',
    },
    {
      path: join(homedir(), '.claude', 'skills', SKILL_NAME),
      exists: false,
      priority: 4,
      type: 'global',
      preset: 'claude',
    },
  ];

  // 存在チェック
  for (const info of paths) {
    info.exists = existsSync(join(info.path, 'SKILL.md'));
  }

  return paths;
}

/**
 * スキルインストールを実行
 */
export function executeSkillInstall(
  options: SkillInstallOptions
): number {
  let targetDir: string;
  try {
    targetDir = resolveSkillPath(options);
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Unknown error';
    console.error(chalk.red(`Error: ${message}`));
    return 1;
  }

  const sourceDir = getSkillSourceDir();

  logger.debug('skill.install', 'Installing skill', {
    source: sourceDir,
    target: targetDir,
    options,
  });

  // ソースディレクトリの存在確認
  if (!existsSync(sourceDir)) {
    console.error(
      chalk.red(`Error: Skill source not found at ${sourceDir}`)
    );
    console.error(
      chalk.yellow(
        'This may indicate a corrupted installation. Try reinstalling shirushi.'
      )
    );
    return 1;
  }

  // 既存チェック
  const skillMdPath = join(targetDir, 'SKILL.md');
  if (existsSync(skillMdPath) && !options.force) {
    console.error(chalk.red(`Error: Skill already exists at ${targetDir}`));
    console.error(chalk.yellow('Use --force to overwrite'));
    return 1;
  }

  try {
    // ディレクトリ作成
    mkdirSync(targetDir, { recursive: true });

    // コピー
    cpSync(sourceDir, targetDir, { recursive: true });

    console.log(chalk.green(`✓ Installed shirushi skill to ${targetDir}`));

    // ヒント表示（pathが指定されていない場合のみ）
    // pathが指定された場合はtarget presetの意味がないため表示しない
    if (!options.path) {
      const target = options.target ?? 'agent';
      if (target === 'agent') {
        console.log(
          chalk.gray(
            '\nThis skill is available for Claude Code, Cursor, Windsurf, Aider, and other agents.'
          )
        );
      } else {
        console.log(
          chalk.gray('\nThis skill is available for Claude Code.')
        );
      }
    }

    return 0;
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Unknown error';
    console.error(chalk.red(`Error installing skill: ${message}`));
    logger.error('skill.install', 'Installation failed', { error: message });
    return 1;
  }
}

/**
 * スキル一覧を表示
 */
export function executeSkillList(): number {
  const paths = getAllSkillPaths();

  console.log(chalk.bold('\nSearch paths (priority order):\n'));

  for (const info of paths) {
    const status = info.exists
      ? chalk.green('✓ installed')
      : chalk.gray('-');
    const typeLabel =
      info.type === 'project'
        ? chalk.cyan('[project]')
        : chalk.magenta('[global]');
    const presetLabel =
      info.preset === 'agent'
        ? chalk.blue('[universal]')
        : chalk.yellow('[claude]');

    console.log(
      `  ${info.priority}. ${info.path}`
    );
    console.log(
      `     ${typeLabel} ${presetLabel} ${status}`
    );
  }

  // アクティブなスキルを表示
  const activeSkill = paths.find((p) => p.exists);
  if (activeSkill) {
    console.log(
      chalk.bold(`\nActive skill: `) + chalk.green(activeSkill.path)
    );
  } else {
    console.log(
      chalk.yellow('\nNo skill installed. Run `shirushi skill install` to install.')
    );
  }

  console.log('');
  return 0;
}

/**
 * スキルアンインストールを実行
 */
export function executeSkillUninstall(
  options: SkillUninstallOptions
): number {
  let targetDir: string;
  try {
    targetDir = resolveSkillPath(options);
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Unknown error';
    console.error(chalk.red(`Error: ${message}`));
    return 1;
  }

  const skillMdPath = join(targetDir, 'SKILL.md');

  logger.debug('skill.uninstall', 'Uninstalling skill', {
    target: targetDir,
    options,
  });

  // 存在チェック
  if (!existsSync(skillMdPath)) {
    console.error(chalk.red(`Error: No skill found at ${targetDir}`));
    return 1;
  }

  try {
    // ディレクトリごと削除（force: falseでエラーを検出可能に）
    rmSync(targetDir, { recursive: true });
    console.log(chalk.green(`✓ Uninstalled shirushi skill from ${targetDir}`));
    return 0;
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Unknown error';
    console.error(chalk.red(`Error uninstalling skill: ${message}`));
    logger.error('skill.uninstall', 'Uninstallation failed', { error: message });
    return 1;
  }
}

/**
 * Commander CLIオプション型
 */
interface SkillCliOptions {
  target?: string;
  global?: boolean;
  path?: string;
  force?: boolean;
}

/**
 * Commanderにskillコマンドを登録
 */
export function registerSkillCommand(program: Command): void {
  const skill = program
    .command('skill')
    .description('Manage AI agent skills (Claude Code, Cursor, Windsurf, Aider)');

  skill
    .command('install')
    .description('Install shirushi skill for AI agents')
    .option(
      '-t, --target <preset>',
      'Target preset: agent (universal, default) or claude',
      'agent'
    )
    .option(
      '-g, --global',
      'Install globally (~/.agent/skills/ or ~/.claude/skills/)'
    )
    .option('-p, --path <dir>', 'Custom installation path')
    .option('-f, --force', 'Overwrite existing skill')
    .action((opts: SkillCliOptions) => {
      const exitCode = executeSkillInstall({
        target: (opts.target as TargetPreset) ?? 'agent',
        global: opts.global ?? false,
        ...(opts.path ? { path: opts.path } : {}),
        force: opts.force ?? false,
      });
      process.exit(exitCode);
    });

  skill
    .command('list')
    .description('List installed skills and search paths')
    .action(() => {
      const exitCode = executeSkillList();
      process.exit(exitCode);
    });

  skill
    .command('uninstall')
    .description('Remove installed skill')
    .option(
      '-t, --target <preset>',
      'Target preset: agent (default) or claude',
      'agent'
    )
    .option(
      '-g, --global',
      'Uninstall from global path (~/.agent/skills/ or ~/.claude/skills/)'
    )
    .option('-p, --path <dir>', 'Custom path')
    .action((opts: SkillCliOptions) => {
      const exitCode = executeSkillUninstall({
        target: (opts.target as TargetPreset) ?? 'agent',
        global: opts.global ?? false,
        ...(opts.path ? { path: opts.path } : {}),
      });
      process.exit(exitCode);
    });
}
