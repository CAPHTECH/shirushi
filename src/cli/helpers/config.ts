/**
 * CLI Config Helper
 *
 * lint/scanコマンド共通の設定ロードヘルパー。
 * エラーハンドリングとログ出力を統一する。
 */

import { loadConfig } from '@/config/loader';
import { logger } from '@/utils/logger';

import type { ShirushiConfig } from '@/config/schema';

/**
 * 設定ロード結果
 */
export interface ConfigLoadResult {
  config: ShirushiConfig;
  path: string;
}

/**
 * CLIコマンド用に設定をロードする
 *
 * @param configPath - 設定ファイルパス（オプション）
 * @param cwd - ベースディレクトリ
 * @param commandName - コマンド名（ログ用）
 * @returns 設定ロード結果、またはnull（エラー時）
 *
 * @example
 * ```typescript
 * const loaded = await loadConfigForCommand(options.config, cwd, 'lint');
 * if (!loaded) {
 *   return 1; // エラー終了
 * }
 * const { config } = loaded;
 * ```
 */
export async function loadConfigForCommand(
  configPath: string | undefined,
  cwd: string,
  commandName: string
): Promise<ConfigLoadResult | null> {
  try {
    const loaded = await loadConfig({
      cwd,
      ...(configPath ? { configPath } : {}),
    });
    logger.debug(`${commandName}.config`, 'Config loaded', {
      path: loaded.path,
    });
    return loaded;
  } catch (error) {
    const message =
      error instanceof Error ? error.message : 'Unknown config error';
    console.error(`Error loading config: ${message}`);
    return null;
  }
}
