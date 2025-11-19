import { defineConfig } from 'vitest/config';
import path from 'path';

export default defineConfig({
  test: {
    // グローバルなテストAPI（describe, it, expectなど）を有効化
    globals: true,

    // テスト環境: Node.js
    environment: 'node',

    // カバレッジ設定
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html', 'lcov'],
      include: ['src/**/*.ts'],
      exclude: [
        'src/**/*.test.ts',
        'src/**/*.spec.ts',
        'src/types/**',
        'src/cli/index.ts', // エントリーポイントは除外
      ],
      // カバレッジ閾値（品質ゲート）
      thresholds: {
        lines: 80,
        functions: 80,
        branches: 80,
        statements: 80,
      },
      all: true,
      clean: true,
    },

    // テストファイルのパターン
    include: [
      'tests/**/*.test.ts',
      'tests/**/*.spec.ts',
      'src/**/*.test.ts',
    ],

    // テストのタイムアウト（ミリ秒）
    testTimeout: 10000,

    // セットアップファイル
    setupFiles: ['./tests/setup.ts'],

    // 並列実行の設定
    maxConcurrency: 5,

    // ウォッチモードでファイル変更を無視
    watchExclude: [
      '**/node_modules/**',
      '**/dist/**',
      '**/coverage/**',
      '**/.git/**',
    ],

    // スナップショットの設定
    resolveSnapshotPath: (testPath, snapExtension) => {
      return path.join(
        path.dirname(testPath),
        '__snapshots__',
        path.basename(testPath) + snapExtension
      );
    },
  },

  // パスエイリアス解決（tsconfig.jsonと同期）
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
      '@/cli': path.resolve(__dirname, './src/cli'),
      '@/core': path.resolve(__dirname, './src/core'),
      '@/dimensions': path.resolve(__dirname, './src/dimensions'),
      '@/parsers': path.resolve(__dirname, './src/parsers'),
      '@/config': path.resolve(__dirname, './src/config'),
      '@/git': path.resolve(__dirname, './src/git'),
      '@/errors': path.resolve(__dirname, './src/errors'),
      '@/types': path.resolve(__dirname, './src/types'),
      '@/utils': path.resolve(__dirname, './src/utils'),
    },
  },
});
