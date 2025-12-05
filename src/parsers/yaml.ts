import { readFile } from 'node:fs/promises';

import yaml, { JSON_SCHEMA } from 'js-yaml';

import { ShirushiErrors } from '../errors/definitions.js';

import { countDocIdDirectives } from './doc-id.js';
import { assertYamlSafety, UnsafeYamlError } from './yaml-safety.js';

import type { DocumentParseResult, DocumentProblem } from '../types/document.js';

type ErrorDefinition = (typeof ShirushiErrors)[keyof typeof ShirushiErrors];

const YAML_OPTIONS = { schema: JSON_SCHEMA, json: true } as const;

export async function parseYamlFile(
  path: string,
  idField: string = 'doc_id'
): Promise<DocumentParseResult> {
  const file = await readFile(path, 'utf8');
  return parseYamlContent(path, file, idField);
}

export function parseYamlContent(
  path: string,
  content: string,
  idField: string = 'doc_id'
): DocumentParseResult {
  const problems: DocumentProblem[] = [];
  let docId: string | undefined;
  let metadata: Record<string, unknown> = {};

  const docIdOccurrences = countDocIdDirectives(content, idField);
  if (docIdOccurrences > 1) {
    pushProblem(problems, ShirushiErrors.MULTIPLE_IDS_IN_DOCUMENT, { path });
  }

  try {
    assertYamlSafety(content, path);
    const parsed = yaml.load(content, YAML_OPTIONS);
    if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) {
      const { [idField]: candidate, ...rest } = parsed as Record<string, unknown>;
      metadata = rest;
      if (typeof candidate === 'string') {
        docId = candidate;
      } else if (candidate === undefined) {
        pushProblem(problems, ShirushiErrors.MISSING_ID, { path });
      } else {
        pushProblem(problems, ShirushiErrors.INVALID_DOC_ID_TYPE, { path });
      }
    } else {
      pushProblem(
        problems,
        ShirushiErrors.INVALID_YAML,
        {
          path,
          reason: 'YAML root must be an object',
        },
        'YAML root must be an object'
      );
    }
  } catch (error) {
    if (error instanceof UnsafeYamlError) {
      pushProblem(
        problems,
        ShirushiErrors.INVALID_YAML,
        { path, reason: error.message },
        error.message
      );
    } else {
      pushProblem(problems, ShirushiErrors.INVALID_YAML, { path });
    }
  }

  return {
    kind: 'yaml',
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
