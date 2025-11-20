import { readFile } from 'node:fs/promises';

import matter from 'gray-matter';

import type { DocumentParseResult, DocumentProblem } from '../types/document.js';
import { ShirushiErrors } from '../errors/definitions.js';

type ErrorDefinition = (typeof ShirushiErrors)[keyof typeof ShirushiErrors];

const DOC_ID_PATTERN = /^doc_id\s*:/gm;

function extractFrontMatterBlock(content: string): string | null {
  const lines = content.split(/\r?\n/);
  if (lines[0]?.trim() !== '---') {
    return null;
  }

  for (let i = 1; i < lines.length; i += 1) {
    if (lines[i]?.trim() === '---') {
      return lines.slice(1, i).join('\n');
    }
  }
  return null;
}

function countDocIdOccurrences(frontMatterBlock: string | null | undefined): number {
  if (!frontMatterBlock) return 0;
  const matches = frontMatterBlock.match(DOC_ID_PATTERN);
  return matches ? matches.length : 0;
}

function normalizeMetadata(data: Record<string, unknown>): Record<string, unknown> {
  const { doc_id: _docId, ...rest } = data;
  return rest;
}

export async function parseMarkdownFile(path: string): Promise<DocumentParseResult> {
  const file = await readFile(path, 'utf8');
  return parseMarkdownContent(path, file);
}

export function parseMarkdownContent(path: string, content: string): DocumentParseResult {
  const problems: DocumentProblem[] = [];
  let docId: string | undefined;
  let metadata: Record<string, unknown> = {};

  const frontMatterBlock = extractFrontMatterBlock(content);
  const occurrences = countDocIdOccurrences(frontMatterBlock);
  if (occurrences === 0) {
    pushProblem(problems, ShirushiErrors.MISSING_ID, { path });
  } else if (occurrences > 1) {
    pushProblem(problems, ShirushiErrors.MULTIPLE_IDS_IN_DOCUMENT, { path });
  }

  try {
    const parsed = matter(content);
    const data = (parsed.data ?? {}) as Record<string, unknown>;
    metadata = normalizeMetadata(data);

    const value = data['doc_id'];
    if (typeof value === 'string') {
      docId = value;
    } else if (value !== undefined) {
      pushProblem(problems, ShirushiErrors.INVALID_DOC_ID_TYPE, { path });
    }
  } catch {
    pushProblem(problems, ShirushiErrors.INVALID_FRONT_MATTER, { path });
  }

  return {
    kind: 'markdown',
    path,
    docId,
    metadata,
    problems,
  };
}

function pushProblem(
  collection: DocumentProblem[],
  definition: ErrorDefinition,
  details?: Record<string, unknown>,
  messageOverride?: string
): void {
  collection.push({
    code: definition.code,
    message: messageOverride ?? definition.message,
    domain: definition.domain,
    severity: definition.severity,
    ...(details ? { details } : {}),
  });
}
