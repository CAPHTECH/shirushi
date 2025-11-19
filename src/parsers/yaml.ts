import { readFile } from 'node:fs/promises';
import yaml from 'js-yaml';
import { DocumentParseResult, DocumentProblem } from '../types/document.js';

const DOC_ID_REGEX = /^doc_id\s*:/gm;

export async function parseYamlFile(path: string): Promise<DocumentParseResult> {
  const file = await readFile(path, 'utf8');
  return parseYamlContent(path, file);
}

export function parseYamlContent(path: string, content: string): DocumentParseResult {
  const problems: DocumentProblem[] = [];
  let docId: string | undefined;
  let metadata: Record<string, unknown> = {};

  const docIdOccurrences = content.match(DOC_ID_REGEX);
  if (docIdOccurrences && docIdOccurrences.length > 1) {
    problems.push({
      code: 'MULTIPLE_IDS_IN_DOCUMENT',
      message: 'doc_id appears multiple times in YAML document',
    });
  }

  try {
    const parsed = yaml.load(content);
    if (parsed && typeof parsed === 'object') {
      const { doc_id: candidate, ...rest } = parsed as Record<string, unknown>;
      metadata = rest;
      if (typeof candidate === 'string') {
        docId = candidate;
      } else if (candidate === undefined) {
        problems.push({ code: 'MISSING_ID', message: 'doc_id is missing at YAML root' });
      } else {
        problems.push({ code: 'INVALID_DOC_ID_TYPE', message: 'doc_id must be a string' });
      }
    } else {
      problems.push({ code: 'INVALID_YAML', message: 'YAML root must be an object' });
    }
  } catch (error) {
    problems.push({ code: 'INVALID_YAML', message: 'Failed to parse YAML document' });
  }

  return {
    kind: 'yaml',
    path,
    docId,
    metadata,
    problems,
  };
}
