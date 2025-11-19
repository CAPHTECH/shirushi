import { readFile } from 'node:fs/promises';
import matter from 'gray-matter';
import { DocumentParseResult, DocumentProblem } from '../types/document.js';

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
    problems.push({ code: 'MISSING_ID', message: 'doc_id is missing from front matter' });
  } else if (occurrences > 1) {
    problems.push({ code: 'MULTIPLE_IDS_IN_DOCUMENT', message: 'doc_id appears multiple times in front matter' });
  }

  try {
    const parsed = matter(content);
    metadata = normalizeMetadata(parsed.data ?? {});

    const value = parsed.data?.doc_id;
    if (typeof value === 'string') {
      docId = value;
    } else if (value !== undefined) {
      problems.push({ code: 'INVALID_DOC_ID_TYPE', message: 'doc_id must be a string' });
    }
  } catch (error) {
    problems.push({ code: 'INVALID_FRONT_MATTER', message: 'Failed to parse YAML front matter' });
  }

  return {
    kind: 'markdown',
    path,
    docId,
    metadata,
    problems,
  };
}
