import { readFile } from 'node:fs/promises';

import yaml from 'js-yaml';

import type { DocumentParseResult, DocumentProblem } from '../types/document.js';
import { ShirushiErrors } from '../errors/definitions.js';

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
      code: ShirushiErrors.MULTIPLE_IDS_IN_DOCUMENT.code,
      message: ShirushiErrors.MULTIPLE_IDS_IN_DOCUMENT.message,
    });
  }

  try {
    const parsed = yaml.load(content);
    if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) {
      const { doc_id: candidate, ...rest } = parsed as Record<string, unknown>;
      metadata = rest;
      if (typeof candidate === 'string') {
        docId = candidate;
      } else if (candidate === undefined) {
        problems.push({
          code: ShirushiErrors.MISSING_ID.code,
          message: ShirushiErrors.MISSING_ID.message,
        });
      } else {
        problems.push({
          code: ShirushiErrors.INVALID_DOC_ID_TYPE.code,
          message: ShirushiErrors.INVALID_DOC_ID_TYPE.message,
        });
      }
    } else {
      problems.push({
        code: ShirushiErrors.INVALID_YAML.code,
        message: 'YAML root must be an object',
      });
    }
  } catch {
    problems.push({
      code: ShirushiErrors.INVALID_YAML.code,
      message: ShirushiErrors.INVALID_YAML.message,
    });
  }

  return {
    kind: 'yaml',
    path,
    docId,
    metadata,
    problems,
  };
}
