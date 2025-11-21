export const MAX_YAML_CHAR_LENGTH = 50_000;
const BASE_ALIAS_BUDGET = 16;
const ALIAS_BUDGET_PER_CHARS = 4_096;
export const MAX_YAML_ALIAS_BUDGET = 128;
const ANCHOR_PATTERN = /&[A-Za-z0-9_-]+/g;
const ALIAS_PATTERN = /\*[A-Za-z0-9_-]+/g;

export class UnsafeYamlError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'UnsafeYamlError';
  }
}

export function assertYamlSafety(raw: string, context: string): void {
  if (raw.length > MAX_YAML_CHAR_LENGTH) {
    throw new UnsafeYamlError(`YAML front matter too large in ${context}`);
  }

  const anchorCount = matchCount(raw, ANCHOR_PATTERN);
  const aliasCount = matchCount(raw, ALIAS_PATTERN);
  const allowedAliasBudget = Math.min(
    MAX_YAML_ALIAS_BUDGET,
    BASE_ALIAS_BUDGET + Math.floor(raw.length / ALIAS_BUDGET_PER_CHARS)
  );
  if (anchorCount + aliasCount > allowedAliasBudget) {
    throw new UnsafeYamlError(
      `YAML contains too many anchors/aliases (${anchorCount + aliasCount}) in ${context}`
    );
  }
}

function matchCount(source: string, pattern: RegExp): number {
  pattern.lastIndex = 0;
  const matches = source.match(pattern);
  return matches ? matches.length : 0;
}
