import { readFile } from 'node:fs/promises';

import matter from 'gray-matter';
import yaml, { JSON_SCHEMA } from 'js-yaml';

import type { DocumentParseResult, DocumentProblem } from '../types/document.js';
import { ShirushiErrors } from '../errors/definitions.js';
import { assertYamlSafety, UnsafeYamlError } from './yaml-safety.js';
import { countDocIdDirectives } from './doc-id.js';

type ErrorDefinition = (typeof ShirushiErrors)[keyof typeof ShirushiErrors];

const YAML_OPTIONS = { schema: JSON_SCHEMA, json: true } as const;

export async function parseMarkdownFile(path: string): Promise<DocumentParseResult> {
  const file = await readFile(path, 'utf8');
  return parseMarkdownContent(path, file);
}

export function parseMarkdownContent(path: string, content: string): DocumentParseResult {
  const sanitizedContent = normalizeFrontMatterSource(content);
  const problems: DocumentProblem[] = [];
  let docId: string | undefined;
  let metadata: Record<string, unknown> = {};

  try {
    const parsed = matter(sanitizedContent, {
      engines: {
        yaml: (str: string) => {
          assertYamlSafety(str, path);
          return yaml.load(str, YAML_OPTIONS) ?? {};
        },
      },
    });
    const data = (parsed.data ?? {}) as Record<string, unknown>;
    metadata = normalizeMetadata(data);

    const docIdOccurrences = countDocIdDirectives(parsed.matter);
    if (docIdOccurrences === 0) {
      pushProblem(problems, ShirushiErrors.MISSING_ID, { path });
    } else if (docIdOccurrences > 1) {
      pushProblem(problems, ShirushiErrors.MULTIPLE_IDS_IN_DOCUMENT, { path });
    }

    const value = data['doc_id'];
    if (typeof value === 'string') {
      docId = value;
    } else if (value !== undefined) {
      pushProblem(problems, ShirushiErrors.INVALID_DOC_ID_TYPE, { path });
    }
  } catch (error) {
    if (error instanceof UnsafeYamlError) {
      pushProblem(
        problems,
        ShirushiErrors.INVALID_FRONT_MATTER,
        { path, reason: error.message },
        error.message
      );
    } else {
      pushProblem(problems, ShirushiErrors.INVALID_FRONT_MATTER, { path });
    }
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

function normalizeFrontMatterSource(value: string): string {
  const withoutBom = stripBom(value);
  const delimiterIndex = withoutBom.indexOf('---');
  if (delimiterIndex <= 0) {
    return withoutBom;
  }

  const prefix = withoutBom.slice(0, delimiterIndex);
  if (/^\s*$/.test(prefix)) {
    return withoutBom.slice(delimiterIndex);
  }
  return withoutBom;
}

function stripBom(value: string): string {
  return value.charCodeAt(0) === 0xfeff ? value.slice(1) : value;
}

function normalizeMetadata(data: Record<string, unknown>): Record<string, unknown> {
  const { doc_id: _docId, ...rest } = data;
  return rest;
}
