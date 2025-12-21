/**
 * Output Formatters
 *
 * scan/lint/showコマンドの出力フォーマッタ。
 * JSON, YAML, table形式をサポート。
 *
 * @see Issue #27: shirushi show コマンド
 */

import yaml from 'js-yaml';

import type { LookupResult } from '@/core/lookup';
import type { ScanSummary } from '@/core/scanner';
import type { DocumentParseResult } from '@/types/document';

/**
 * 出力フォーマット
 */
export type OutputFormat = 'table' | 'json' | 'yaml';

/**
 * scanコマンドの出力データ
 */
export interface ScanOutput {
  documents: ScanDocumentEntry[];
  summary: ScanSummary;
}

/**
 * ドキュメントエントリ（出力用）
 */
export interface ScanDocumentEntry {
  doc_id: string | null;
  path: string;
  title: string | null;
  doc_type: string | null;
  status: string | null;
  version: string | null;
  owner: string | null;
}

/**
 * DocumentParseResultを出力用エントリに変換
 */
export function toScanEntry(doc: DocumentParseResult): ScanDocumentEntry {
  return {
    doc_id: doc.docId ?? null,
    path: doc.path,
    title: (doc.metadata.title as string) ?? null,
    doc_type: (doc.metadata.doc_type as string) ?? null,
    status: (doc.metadata.status as string) ?? null,
    version: (doc.metadata.version as string) ?? null,
    owner: (doc.metadata.owner as string) ?? null,
  };
}

/**
 * DocumentParseResult配列を出力用データに変換
 */
export function toScanOutput(
  documents: DocumentParseResult[],
  summary: ScanSummary
): ScanOutput {
  return {
    documents: documents.map(toScanEntry),
    summary,
  };
}

/**
 * JSON形式でフォーマット
 */
export function formatAsJson(data: unknown): string {
  return JSON.stringify(data, null, 2);
}

/**
 * YAML形式でフォーマット
 */
export function formatAsYaml(data: unknown): string {
  return yaml.dump(data, { indent: 2, lineWidth: 120 });
}

/**
 * テーブル形式でフォーマット（scan用）
 */
export function formatScanAsTable(output: ScanOutput): string {
  const lines: string[] = [];

  // ヘッダー
  const header = ['doc_id', 'path', 'title', 'doc_type', 'status'];
  const colWidths = calculateColumnWidths(output.documents, header);

  // セパレーター
  const separator = header.map((_, i) => '-'.repeat(colWidths[i] ?? 0)).join('  ');

  // ヘッダー行
  lines.push(formatRow(header, colWidths));
  lines.push(separator);

  // データ行
  for (const doc of output.documents) {
    const row = [
      doc.doc_id ?? '(none)',
      doc.path,
      truncate(doc.title ?? '', 30),
      doc.doc_type ?? '',
      doc.status ?? '',
    ];
    lines.push(formatRow(row, colWidths));
  }

  // サマリー
  lines.push('');
  lines.push(`Total: ${output.summary.totalFiles} files`);
  lines.push(
    `  Markdown: ${output.summary.markdownFiles}, YAML: ${output.summary.yamlFiles}`
  );
  lines.push(
    `  With doc_id: ${output.summary.withDocId}, Without: ${output.summary.withoutDocId}`
  );

  return lines.join('\n');
}

/**
 * 列幅を計算
 */
function calculateColumnWidths(
  docs: ScanDocumentEntry[],
  headers: string[]
): number[] {
  const widths = headers.map((h) => h.length);

  for (const doc of docs) {
    const values = [
      doc.doc_id ?? '(none)',
      doc.path,
      truncate(doc.title ?? '', 30),
      doc.doc_type ?? '',
      doc.status ?? '',
    ];
    values.forEach((v, i) => {
      widths[i] = Math.max(widths[i] ?? 0, v.length);
    });
  }

  // 最大幅の制限
  return widths.map((w) => Math.min(w, 50));
}

/**
 * 行をフォーマット
 */
function formatRow(values: string[], widths: number[]): string {
  return values.map((v, i) => v.padEnd(widths[i] ?? 0)).join('  ');
}

/**
 * 文字列を切り詰め
 */
function truncate(str: string, maxLen: number): string {
  if (str.length <= maxLen) return str;
  return `${str.slice(0, maxLen - 3)  }...`;
}

/**
 * 指定フォーマットでscan結果をフォーマット
 */
export function formatScanResult(
  output: ScanOutput,
  format: OutputFormat
): string {
  switch (format) {
    case 'json':
      return formatAsJson(output);
    case 'yaml':
      return formatAsYaml(output);
    case 'table':
    default:
      return formatScanAsTable(output);
  }
}

// ===== Show Command Formatters (Issue #27) =====

/**
 * show出力モード
 */
export type ShowOutputMode = 'full' | 'path-only' | 'meta-only';

/**
 * showコマンドの出力データ（JSON/YAML用）
 */
export interface ShowOutput {
  doc_id: string;
  path: string;
  title: string | null;
  doc_type: string | null;
  status: string | null;
  version: string | null;
  owner: string | null;
  tags: string[] | null;
  content?: string;
}

/**
 * LookupResultをShowOutputに変換
 */
export function toShowOutput(result: LookupResult, includeContent: boolean = true): ShowOutput {
  return {
    doc_id: result.docId,
    path: result.path,
    title: (result.metadata.title as string) ?? null,
    doc_type: (result.metadata.doc_type as string) ?? null,
    status: (result.metadata.status as string) ?? null,
    version: (result.metadata.version as string) ?? null,
    owner: (result.metadata.owner as string) ?? null,
    tags: (result.metadata.tags as string[]) ?? null,
    ...(includeContent ? { content: result.content } : {}),
  };
}

/**
 * テーブル形式でshow結果をフォーマット
 */
export function formatShowAsTable(result: LookupResult, mode: ShowOutputMode): string {
  const lines: string[] = [];

  // メタデータ部分
  lines.push(`Path:    ${result.path}`);

  if (result.metadata.title) {
    lines.push(`Title:   ${result.metadata.title}`);
  }

  if (result.metadata.doc_type) {
    lines.push(`Type:    ${result.metadata.doc_type}`);
  }

  if (result.metadata.status) {
    lines.push(`Status:  ${result.metadata.status}`);
  }

  if (result.metadata.version) {
    lines.push(`Version: ${result.metadata.version}`);
  }

  if (result.metadata.owner) {
    lines.push(`Owner:   ${result.metadata.owner}`);
  }

  if (result.metadata.tags && Array.isArray(result.metadata.tags) && result.metadata.tags.length > 0) {
    lines.push(`Tags:    ${result.metadata.tags.join(', ')}`);
  }

  // 本文（fullモードのみ）
  if (mode === 'full' && result.content) {
    lines.push('');
    lines.push('---');
    lines.push(result.content.trim());
  }

  return lines.join('\n');
}

/**
 * 指定フォーマットでshow結果をフォーマット
 *
 * @param result - Lookup結果
 * @param format - 出力フォーマット
 * @param mode - 出力モード
 * @returns フォーマットされた文字列
 */
export function formatShowResult(
  result: LookupResult,
  format: OutputFormat,
  mode: ShowOutputMode = 'full'
): string {
  // path-onlyモードは特別処理
  if (mode === 'path-only') {
    return result.path;
  }

  const includeContent = mode === 'full';

  switch (format) {
    case 'json':
      return formatAsJson(toShowOutput(result, includeContent));
    case 'yaml':
      return formatAsYaml(toShowOutput(result, includeContent));
    case 'table':
    default:
      return formatShowAsTable(result, mode);
  }
}
