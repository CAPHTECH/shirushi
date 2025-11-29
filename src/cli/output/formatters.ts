/**
 * Output Formatters
 *
 * scan/lintコマンドの出力フォーマッタ。
 * JSON, YAML, table形式をサポート。
 */

import yaml from 'js-yaml';

import type { DocumentParseResult } from '@/types/document';
import type { ScanSummary } from '@/core/scanner';

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
  return str.slice(0, maxLen - 3) + '...';
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
