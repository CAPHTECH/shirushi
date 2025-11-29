/**
 * Error Reporters
 *
 * lintコマンドのエラーレポート出力。
 * 重要度別にエラーを分類し、人間に読みやすい形式で出力。
 */

import chalk from 'chalk';

import { ErrorSeverity } from '@/errors/definitions';

import type {
  LawDomain,
  ErrorSeverity as ErrorSeverityType,
  ShirushiErrorCode,
} from '@/errors/definitions';
import type { DocumentProblem } from '@/types/document';
import type { ValidationError } from '@/dimensions';
import type { OutputFormat } from './formatters';

/**
 * lintエラー（ドキュメント単位）
 */
export interface LintError {
  path: string;
  code: ShirushiErrorCode | string;
  message: string;
  domain: LawDomain;
  severity: ErrorSeverityType;
  details?: Record<string, unknown> | undefined;
}

/**
 * lint結果
 */
export interface LintResult {
  errors: LintError[];
  warnings: LintError[];
  summary: LintSummary;
}

/**
 * lintサマリー
 */
export interface LintSummary {
  totalFiles: number;
  filesWithErrors: number;
  filesWithWarnings: number;
  totalErrors: number;
  totalWarnings: number;
}

/**
 * DocumentProblemをLintErrorに変換
 */
export function problemToLintError(
  path: string,
  problem: DocumentProblem
): LintError {
  return {
    path,
    code: problem.code,
    message: problem.message,
    domain: problem.domain,
    severity: problem.severity,
    details: problem.details,
  };
}

/**
 * ValidationErrorをLintErrorに変換
 */
export function validationErrorToLintError(
  path: string,
  error: ValidationError,
  domain: LawDomain = 'validation'
): LintError {
  return {
    path,
    code: error.code,
    message: error.message,
    domain,
    severity: 'error',
    details: error.context,
  };
}

/**
 * 重要度別にアイコンを取得
 */
function getSeverityIcon(severity: ErrorSeverityType): string {
  switch (severity) {
    case ErrorSeverity.Error:
      return chalk.red('✖');
    case ErrorSeverity.Warning:
      return chalk.yellow('⚠');
    case ErrorSeverity.Info:
      return chalk.blue('ℹ');
    default:
      return '•';
  }
}

/**
 * 重要度別に色付け（将来の拡張用に保持）
 */
export function colorBySeverity(
  text: string,
  severity: ErrorSeverityType
): string {
  switch (severity) {
    case ErrorSeverity.Error:
      return chalk.red(text);
    case ErrorSeverity.Warning:
      return chalk.yellow(text);
    case ErrorSeverity.Info:
      return chalk.blue(text);
    default:
      return text;
  }
}

/**
 * エラーをパス別にグループ化
 */
function groupByPath(errors: LintError[]): Map<string, LintError[]> {
  const grouped = new Map<string, LintError[]>();
  for (const error of errors) {
    const existing = grouped.get(error.path) ?? [];
    existing.push(error);
    grouped.set(error.path, existing);
  }
  return grouped;
}

/**
 * テーブル形式でlint結果をフォーマット
 */
export function formatLintAsTable(result: LintResult): string {
  const lines: string[] = [];

  const allIssues = [...result.errors, ...result.warnings];
  const grouped = groupByPath(allIssues);

  // パス別にエラーを表示
  for (const [filePath, issues] of grouped) {
    lines.push(chalk.underline(filePath));

    for (const issue of issues) {
      const icon = getSeverityIcon(issue.severity);
      const code = chalk.dim(`[${issue.code}]`);
      lines.push(`  ${icon} ${issue.message} ${code}`);
    }
    lines.push('');
  }

  // サマリー
  if (result.summary.totalErrors > 0 || result.summary.totalWarnings > 0) {
    const errorText =
      result.summary.totalErrors > 0
        ? chalk.red(`${result.summary.totalErrors} error(s)`)
        : '';
    const warningText =
      result.summary.totalWarnings > 0
        ? chalk.yellow(`${result.summary.totalWarnings} warning(s)`)
        : '';

    const parts = [errorText, warningText].filter(Boolean);
    lines.push(parts.join(', '));
  } else {
    lines.push(chalk.green('No issues found.'));
  }

  return lines.join('\n');
}

/**
 * JSON形式でlint結果をフォーマット
 */
export function formatLintAsJson(result: LintResult): string {
  return JSON.stringify(
    {
      errors: result.errors,
      warnings: result.warnings,
      summary: result.summary,
    },
    null,
    2
  );
}

/**
 * 指定フォーマットでlint結果をフォーマット
 */
export function formatLintResult(
  result: LintResult,
  format: OutputFormat
): string {
  switch (format) {
    case 'json':
      return formatLintAsJson(result);
    case 'yaml':
      // YAMLはJSONと同様の構造
      return formatLintAsJson(result);
    case 'table':
    default:
      return formatLintAsTable(result);
  }
}

/**
 * quietモード用の簡潔な出力
 */
export function formatLintQuiet(result: LintResult): string {
  if (result.summary.totalErrors === 0 && result.summary.totalWarnings === 0) {
    return '';
  }

  const lines: string[] = [];
  for (const error of result.errors) {
    lines.push(`${error.path}: ${error.code}`);
  }
  return lines.join('\n');
}

/**
 * lint結果を構築
 */
export function buildLintResult(allIssues: LintError[]): LintResult {
  const errors = allIssues.filter((e) => e.severity === ErrorSeverity.Error);
  const warnings = allIssues.filter(
    (e) => e.severity === ErrorSeverity.Warning
  );

  // ファイル数のカウント
  const filesWithErrors = new Set(errors.map((e) => e.path)).size;
  const filesWithWarnings = new Set(warnings.map((e) => e.path)).size;
  const totalFiles = new Set(allIssues.map((e) => e.path)).size;

  return {
    errors,
    warnings,
    summary: {
      totalFiles,
      filesWithErrors,
      filesWithWarnings,
      totalErrors: errors.length,
      totalWarnings: warnings.length,
    },
  };
}
