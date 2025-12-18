---
doc_id: SHI-SPEC-2025-0003-N
---
# Plugin Development Guide

This guide explains how to create plugins for Shirushi. Plugins allow you to extend Shirushi's capabilities by implementing custom document sources, index stores, and change trackers.

## Overview

Shirushi's plugin architecture consists of three core interfaces:

| Interface | Purpose | Example Use Cases |
|-----------|---------|-------------------|
| `DocumentSource` | Document retrieval and enumeration | PostgreSQL, MongoDB, Notion API |
| `IndexStore` | Index persistence and querying | SQLite, Redis, DynamoDB |
| `ChangeTracker` | Change detection | Audit logs, timestamps, webhooks |

A plugin can implement one or more of these interfaces.

## Quick Start

### Minimal Plugin

```typescript
import type { ShirushiPlugin } from '@shirushi/core';

const myPlugin: ShirushiPlugin = {
  name: 'my-plugin',
  version: '1.0.0',
};

export default myPlugin;
```

### Plugin with DocumentSource

```typescript
import { right, left } from 'fp-ts/Either';
import type {
  ShirushiPlugin,
  DocumentSource,
  DocumentReference,
  DocumentContent,
  DocumentFilter,
  DocumentSourceError,
} from '@shirushi/core';

class MyDocumentSource implements DocumentSource {
  readonly name = 'my-document-source';

  async *listDocuments(filter?: DocumentFilter): AsyncIterable<DocumentReference> {
    // Fetch documents from your data source
    const documents = await this.fetchDocuments(filter);

    for (const doc of documents) {
      yield {
        id: doc.id,
        displayPath: doc.path,
        kind: 'markdown',
      };
    }
  }

  async getDocument(
    ref: DocumentReference
  ): Promise<Either<DocumentSourceError, DocumentContent | null>> {
    try {
      const content = await this.fetchContent(ref.id);

      if (!content) {
        return right(null);
      }

      return right({
        ref,
        docId: content.doc_id,
        metadata: {
          title: content.title,
          doc_type: content.type,
        },
        rawContent: content.body,
      });
    } catch (error) {
      return left({
        code: 'DOCUMENT_READ_ERROR',
        message: `Failed to read document: ${ref.id}`,
        context: {
          documentId: ref.id,
          originalError: String(error),
        },
      });
    }
  }

  private async fetchDocuments(filter?: DocumentFilter) {
    // Implement your data fetching logic
    return [];
  }

  private async fetchContent(id: string) {
    // Implement your content fetching logic
    return null;
  }
}

const myPlugin: ShirushiPlugin = {
  name: 'my-document-source-plugin',
  version: '1.0.0',
  documentSource: new MyDocumentSource(),
};

export default myPlugin;
```

## Core Interfaces

### DocumentSource

Abstracts document retrieval from any data source.

```typescript
interface DocumentSource {
  /** Source name for logging */
  readonly name: string;

  /** List documents matching the filter */
  listDocuments(filter?: DocumentFilter): AsyncIterable<DocumentReference>;

  /** Get document content by reference */
  getDocument(
    ref: DocumentReference
  ): Promise<Either<DocumentSourceError, DocumentContent | null>>;

  /** Update document (optional, for assign command) */
  updateDocument?(
    ref: DocumentReference,
    options: DocumentUpdateOptions
  ): Promise<Either<DocumentSourceError, void>>;

  /** Health check (optional) */
  healthCheck?(): Promise<HealthCheckResult>;
}
```

#### Key Types

```typescript
interface DocumentReference {
  readonly id: string;           // Unique identifier
  readonly displayPath: string;  // Human-readable path
  readonly kind: DocumentKind;   // 'markdown' | 'yaml'
}

interface DocumentContent {
  readonly ref: DocumentReference;
  readonly docId: string | null;           // Extracted doc_id
  readonly metadata: DocumentMetadata;     // Parsed metadata
  readonly rawContent?: string;            // Raw content for updates
}

interface DocumentFilter {
  readonly patterns?: readonly string[];   // Glob patterns
  readonly paths?: readonly string[];      // Specific paths
  readonly metadata?: Record<string, unknown>;
  readonly modifiedAfter?: Date;
}
```

### IndexStore

Abstracts index persistence and querying.

```typescript
interface IndexStore {
  readonly name: string;

  /** Get entry by doc_id */
  getByDocId(docId: string): Promise<Either<IndexStoreError, PluginIndexEntry | null>>;

  /** Get entry by path */
  getByPath(path: string): Promise<Either<IndexStoreError, PluginIndexEntry | null>>;

  /** List all entries */
  listEntries(): AsyncIterable<PluginIndexEntry>;

  /** Add or update entry */
  upsert(entry: PluginIndexEntry): Promise<Either<IndexStoreError, void>>;

  /** Delete entry */
  delete(docId: string): Promise<Either<IndexStoreError, boolean>>;

  /** Find duplicate doc_ids */
  findDuplicates(): Promise<Either<IndexStoreError, DuplicateReport>>;

  /** Find orphaned entries (optional) */
  findOrphans?(
    documentPaths: readonly string[]
  ): Promise<Either<IndexStoreError, readonly string[]>>;
}
```

#### Key Types

```typescript
interface PluginIndexEntry {
  readonly docId: string;
  readonly path: string;
  readonly title?: string;
  readonly docType?: string;
  readonly status?: string;
  readonly version?: string;
  readonly owner?: string;
  readonly tags?: readonly string[];
  readonly extra?: Record<string, unknown>;  // Plugin-specific data
}
```

### ChangeTracker

Abstracts change detection mechanisms.

```typescript
interface ChangeTracker {
  readonly name: string;

  /** Detect changes since base reference */
  detectChanges(
    baseRef: string,
    source: DocumentSource
  ): Promise<Either<ChangeTrackerError, PluginChangeDetectionResult>>;

  /** Check if tracker is available */
  isAvailable(): Promise<boolean>;

  /** Validate reference (optional) */
  isValidRef?(ref: string): Promise<boolean>;
}
```

## Error Handling

All async methods return `Either<Error, Success>` from fp-ts:

```typescript
import { right, left, isRight, isLeft } from 'fp-ts/Either';

// Success
return right(result);

// Failure
return left({
  code: 'ERROR_CODE',
  message: 'Human-readable message',
  context: {
    // Additional context for debugging
  },
});

// Handling results
const result = await source.getDocument(ref);
if (isLeft(result)) {
  console.error(`Error: ${result.left.message}`);
} else {
  console.log(`Document: ${result.right?.docId}`);
}
```

### Error Types

```typescript
interface DocumentSourceError {
  readonly code: string;
  readonly message: string;
  readonly context?: {
    readonly documentId?: string;
    readonly displayPath?: string;
    readonly originalError?: string;
  };
}

interface IndexStoreError {
  readonly code: string;
  readonly message: string;
  readonly context?: {
    readonly docId?: string;
    readonly path?: string;
    readonly originalError?: string;
  };
}

interface ChangeTrackerError {
  readonly code: string;
  readonly message: string;
  readonly context?: {
    readonly baseRef?: string;
    readonly path?: string;
    readonly originalError?: string;
  };
}
```

## Plugin Lifecycle

```typescript
interface ShirushiPlugin {
  readonly name: string;
  readonly version: string;

  readonly documentSource?: DocumentSource;
  readonly indexStore?: IndexStore;
  readonly changeTracker?: ChangeTracker;

  /** Called when plugin is loaded */
  initialize?(config: PluginConfig): Promise<void>;

  /** Called when plugin is unloaded */
  dispose?(): Promise<void>;
}
```

### Example with Lifecycle

```typescript
class PostgresPlugin implements ShirushiPlugin {
  readonly name = '@shirushi/plugin-postgres';
  readonly version = '1.0.0';

  private pool: Pool | null = null;
  documentSource?: PostgresDocumentSource;
  indexStore?: PostgresIndexStore;

  async initialize(config: PluginConfig): Promise<void> {
    this.pool = new Pool({
      connectionString: config.connectionString as string,
    });

    await this.pool.connect();

    this.documentSource = new PostgresDocumentSource(this.pool);
    this.indexStore = new PostgresIndexStore(this.pool);
  }

  async dispose(): Promise<void> {
    await this.pool?.end();
    this.pool = null;
  }
}
```

## Type Guards

Use type guards to check plugin capabilities at runtime:

```typescript
import {
  isDocumentSource,
  isIndexStore,
  isChangeTracker,
  hasDocumentSource,
  hasIndexStore,
  hasChangeTracker,
  isUpdatableDocumentSource,
  isOrphanDetectableIndexStore,
} from '@shirushi/core';

// Check if object is a DocumentSource
if (isDocumentSource(obj)) {
  // obj is DocumentSource
}

// Check if plugin provides a DocumentSource
if (hasDocumentSource(plugin)) {
  // plugin.documentSource is DocumentSource
}

// Check for optional capabilities
if (isUpdatableDocumentSource(source)) {
  // source.updateDocument is available
}
```

## Best Practices

### 1. Use Defensive Copies for Arrays

```typescript
// Bad: Reference sharing
return {
  tags: entry.tags,  // Caller can mutate
};

// Good: Defensive copy
return {
  tags: entry.tags ? [...entry.tags] : undefined,
};
```

### 2. Use AsyncIterable for Large Datasets

```typescript
// Good: Memory-efficient streaming
async *listDocuments(): AsyncIterable<DocumentReference> {
  let offset = 0;
  const batchSize = 100;

  while (true) {
    const batch = await this.fetchBatch(offset, batchSize);
    if (batch.length === 0) break;

    for (const doc of batch) {
      yield doc;
    }

    offset += batchSize;
  }
}
```

### 3. Provide Meaningful Error Context

```typescript
return left({
  code: 'CONNECTION_FAILED',
  message: 'Failed to connect to PostgreSQL',
  context: {
    host: config.host,
    port: config.port,
    originalError: error.message,
    // Don't include sensitive data like passwords!
  },
});
```

### 4. Implement Health Checks

```typescript
async healthCheck(): Promise<HealthCheckResult> {
  try {
    await this.pool.query('SELECT 1');
    return { ok: true };
  } catch (error) {
    return {
      ok: false,
      message: `Database connection failed: ${error.message}`,
    };
  }
}
```

## Known Limitations

1. **AsyncIterable Error Handling**: `listDocuments()` and `listEntries()` cannot return structured errors mid-stream. Throw exceptions for stream errors.

2. **Type Guard Limitations**: Type guards only verify property existence, not return types. Ensure your implementation returns correct types.

3. **`extra` Field**: `PluginIndexEntry.extra` is for plugin-internal use and does not persist to YAML index files.

See [ADR-0008](./adr/0008-plugin-architecture.md) for detailed design decisions and rationale.

## Examples

### PostgreSQL Document Source

See [examples/plugin-postgres/](../examples/plugin-postgres/) (coming in Phase 4)

### SQLite Index Store

See [examples/plugin-sqlite/](../examples/plugin-sqlite/) (coming in Phase 4)

## API Reference

Full TypeScript API documentation is available in the source files:

- [`src/plugins/interfaces/document-source.ts`](../src/plugins/interfaces/document-source.ts)
- [`src/plugins/interfaces/index-store.ts`](../src/plugins/interfaces/index-store.ts)
- [`src/plugins/interfaces/change-tracker.ts`](../src/plugins/interfaces/change-tracker.ts)
- [`src/plugins/types.ts`](../src/plugins/types.ts)
