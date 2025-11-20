import { readFile } from 'node:fs/promises';

import matter from 'gray-matter';

import type { DocumentParseResult, DocumentProblem } from '../types/document.js';
import { ShirushiErrors } from '../errors/definitions.js';

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
    problems.push({
      code: ShirushiErrors.MISSING_ID.code,
      message: ShirushiErrors.MISSING_ID.message,
    });
  } else if (occurrences > 1) {
    problems.push({
      code: ShirushiErrors.MULTIPLE_IDS_IN_DOCUMENT.code,
      message: ShirushiErrors.MULTIPLE_IDS_IN_DOCUMENT.message,
    });
  }

  try {
    const parsed = matter(content);
    const data = (parsed.data ?? {}) as Record<string, unknown>;
    metadata = normalizeMetadata(data);

    const value = data['doc_id'];
    if (typeof value === 'string') {
      docId = value;
    } else if (value !== undefined) {
      problems.push({
        code: ShirushiErrors.INVALID_DOC_ID_TYPE.code,
        message: ShirushiErrors.INVALID_DOC_ID_TYPE.message,
      });
    }
  } catch {
    problems.push({
      code: ShirushiErrors.INVALID_FRONT_MATTER.code,
      message: ShirushiErrors.INVALID_FRONT_MATTER.message,
    });
  }

  return {
    kind: 'markdown',
    path,
    docId,
    metadata,
    problems,
  };
}
