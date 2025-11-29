import { defineConfig } from 'tsup';

export default defineConfig({
  // エントリーポイント: CLI
  entry: ['src/cli/index.ts'],

  // 出力形式: ESM（Node.js 18+対応）
  format: ['esm'],

  // TypeScript型定義ファイルを生成
  dts: true,

  // ビルド前にdistディレクトリをクリーンアップ
  clean: true,

  // Node.js互換性のためのshim（__dirname, __filenameなど）
  shims: true,

  // コード分割を無効化（単一バンドル）
  splitting: false,

  // ソースマップを生成（デバッグ用）
  sourcemap: true,

  // 出力ディレクトリ（CLIは dist/cli/ に配置）
  outDir: 'dist/cli',

  // ターゲット環境: Node.js 18以上
  target: 'node18',

  // 外部依存関係（バンドルに含めない）
  external: [
    'chalk',
    'commander',
    'debug',
    'fast-glob',
    'gray-matter',
    'js-yaml',
    'simple-git',
    'zod',
  ],

  // fp-ts, minimatchはESMインポート問題があるためバンドルに含める
  noExternal: [
    'fp-ts',
    'minimatch',
  ],

  // バナー: CLIを実行可能にする
  banner: {
    js: '#!/usr/bin/env node',
  },

  // 本番ビルドでの圧縮
  minify: false, // 開発中は無効、リリース時に有効化

  // Tree-shakingを有効化
  treeshake: true,

  // tsconfig.jsonの設定を使用
  tsconfig: './tsconfig.json',
});
