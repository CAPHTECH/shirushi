// @ts-check
import eslint from '@eslint/js';
import tseslint from 'typescript-eslint';
import importPlugin from 'eslint-plugin-import';
import eslintConfigPrettier from 'eslint-config-prettier';

const sharedPlugins = {
  '@typescript-eslint': tseslint.plugin,
  import: importPlugin,
};

const sharedSettings = {
  'import/resolver': {
    typescript: {
      alwaysTryTypes: true,
      project: './tsconfig.json',
    },
  },
};

const sharedRules = {
  // TypeScript固有のルール
  '@typescript-eslint/explicit-function-return-type': 'off', // 型推論を活用
  '@typescript-eslint/explicit-module-boundary-types': 'off',
  '@typescript-eslint/no-unused-vars': [
    'error',
    {
      argsIgnorePattern: '^_',
      varsIgnorePattern: '^_',
    },
  ],
  '@typescript-eslint/no-explicit-any': 'warn', // anyの使用を警告
  '@typescript-eslint/no-non-null-assertion': 'warn',
  '@typescript-eslint/consistent-type-imports': [
    'error',
    {
      prefer: 'type-imports',
    },
  ],
  '@typescript-eslint/no-floating-promises': 'error',
  '@typescript-eslint/await-thenable': 'error',
  '@typescript-eslint/no-misused-promises': 'error',
  '@typescript-eslint/no-base-to-string': 'off',

  // Import順序の整理
  'import/order': [
    'error',
    {
      groups: ['builtin', 'external', 'internal', 'parent', 'sibling', 'index', 'type'],
      'newlines-between': 'always',
      alphabetize: {
        order: 'asc',
        caseInsensitive: true,
      },
    },
  ],
  'import/no-unresolved': 'error',
  'import/no-cycle': 'error',

  // 一般的なルール
  'no-console': [
    'warn',
    {
      allow: ['log', 'info', 'warn', 'error', 'debug'],
    },
  ],
  'no-debugger': 'error',
  'prefer-const': 'error',
  'no-var': 'error',
  'object-shorthand': 'error',
  'prefer-template': 'error',
  'prefer-arrow-callback': 'error',
  'arrow-body-style': ['error', 'as-needed'],

  // 複雑度の制限
  complexity: ['warn', 10],
  'max-depth': ['warn', 4],
  'max-nested-callbacks': ['warn', 3],
};

export default tseslint.config(
  // Base ESLint recommended rules
  eslint.configs.recommended,

  // TypeScript ESLint recommended rules
  ...tseslint.configs.recommended,

  // Global ignores
  {
    ignores: [
      'dist/**',
      'node_modules/**',
      'coverage/**',
      'eslint.config.mjs',
      'rules/**',
      '*.config.ts',
      '*.config.js',
      '*.config.cjs',
    ],
  },

  // Main configuration
  {
    files: ['src/**/*.ts', 'src/**/*.mts', 'src/**/*.cts'],
    extends: tseslint.configs.recommendedTypeChecked,

    languageOptions: {
      parser: tseslint.parser,
      parserOptions: {
        ecmaVersion: 2022,
        sourceType: 'module',
        project: './tsconfig.json',
        tsconfigRootDir: import.meta.dirname,
      },
      globals: {
        node: true,
        es2022: true,
      },
    },

    plugins: sharedPlugins,
    settings: sharedSettings,
    rules: sharedRules,
  },

  {
    files: ['tests/**/*.ts'],
    languageOptions: {
      parser: tseslint.parser,
      parserOptions: {
        ecmaVersion: 2022,
        sourceType: 'module',
        project: null,
        tsconfigRootDir: import.meta.dirname,
      },
    },
    plugins: sharedPlugins,
    settings: sharedSettings,
    rules: {
      ...sharedRules,
      '@typescript-eslint/await-thenable': 'off',
      '@typescript-eslint/no-floating-promises': 'off',
      '@typescript-eslint/no-misused-promises': 'off',
      'max-nested-callbacks': 'off',
    },
  },

  // Prettier compatibility (must be last)
  eslintConfigPrettier,
);
