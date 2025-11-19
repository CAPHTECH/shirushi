---
doc_id: SHI-API-2025-0002
title: Shirushi API Documentation
version: "0.1.0"
status: Draft
created_at: 2025-11-19
---

# Shirushi API Documentation

This directory contains API documentation for Shirushi's internal modules.

## Overview

Shirushi is designed as a library with a CLI wrapper. The internal APIs can be used programmatically if needed.

## Modules

### Configuration

- [`config/loader`](config-loader.md) - Load and validate `.shirushi.yml`
- [`config/schema`](config-schema.md) - Zod schemas for configuration
- [`config/validator`](config-validator.md) - Configuration validation

### Core

- [`core/validator`](core-validator.md) - Main validation orchestrator
- [`core/scanner`](core-scanner.md) - Document scanning
- [`core/generator`](core-generator.md) - ID generation (internal)
- [`core/index-manager`](core-index-manager.md) - Index file operations

### Dimensions

- [`dimensions/registry`](dimensions-registry.md) - Dimension handler registry
- [`dimensions/handlers`](dimensions-handlers.md) - Dimension handler implementations

### Parsers

- [`parsers/markdown`](parsers-markdown.md) - Markdown front matter parser
- [`parsers/yaml`](parsers-yaml.md) - YAML parser
- [`parsers/template`](parsers-template.md) - Template string parser

### Git

- [`git/operations`](git-operations.md) - Git command wrappers
- [`git/diff`](git-diff.md) - Diff detection

### Errors

- [`errors/types`](errors-types.md) - Error class hierarchy
- [`errors/codes`](errors-codes.md) - Error code constants

### Types

- [`types/config`](types-config.md) - Configuration types
- [`types/document`](types-document.md) - Document types
- [`types/dimension`](types-dimension.md) - Dimension types
- [`types/validation`](types-validation.md) - Validation result types

## Programmatic Usage

While Shirushi is primarily a CLI tool, you can use it programmatically:

```typescript
import { loadConfig } from 'shirushi/config';
import { validateDocument } from 'shirushi/core';

// Load configuration
const config = await loadConfig('.shirushi.yml');

// Scan and validate documents
const documents = await scanDocuments(config);
const results = await Promise.all(
  documents.map(doc => validateDocument(doc, config))
);

// Check results
const errors = results.flatMap(r => r.filter(e => !e.valid));
if (errors.length > 0) {
  console.error('Validation failed:', errors);
  process.exit(1);
}
```

## Generating Documentation

API documentation is generated using TypeDoc:

```bash
# Generate API documentation
pnpm run docs:api

# Output: docs/api/generated/
```

## Contributing

When adding new modules:

1. Add JSDoc comments to public APIs
2. Create a markdown file in this directory
3. Update this README with a link
4. Generate TypeDoc documentation

## See Also

- [User Guide](../user-guide.md) - For end users
- [Developer Guide](../developer-guide.md) - For contributors
- [ADRs](../adr/) - Architecture decisions
