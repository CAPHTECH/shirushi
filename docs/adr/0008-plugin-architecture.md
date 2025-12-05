---
doc_id: SHI-ADR-2025-0008
title: "ADR-0008: Plugin Architecture for External System Integration"
version: "0.1.0"
status: Accepted
created_at: 2025-12-05
---

# ADR-0008: Plugin Architecture for External System Integration

**Status**: Accepted

**Date**: 2025-12-05

**Deciders**: @rizumita

**Tags**: architecture, plugin, extensibility

---

## Context

Shirushi currently has hard dependencies on:

1. **File System**: `fast-glob` + `readFile` for document retrieval
2. **YAML File**: Index management fixed to `docs/doc_index.yaml`
3. **Git**: Change detection relies on `git diff`

This prevents the following use cases:

- Managing doc_ids in documents stored in PostgreSQL/MongoDB
- Integration with cloud services like Notion/Confluence
- Audit log-based change tracking (non-Git)
- Cross-microservice ID consistency validation

The specification (`docs/specifications.md`) mentions future extensibility:

> - Expose Shirushi itself as MCP for agents and IDE plugins
> - Support for other formats (JSON, TOML, AsciiDoc, etc.)

This proposal is a natural extension of that direction.

## Decision

Introduce a plugin architecture with three core interfaces:

### 1. DocumentSource Interface

Abstracts document retrieval and enumeration:

```typescript
interface DocumentSource {
  readonly name: string;
  listDocuments(filter?: DocumentFilter): AsyncIterable<DocumentReference>;
  getDocument(ref: DocumentReference): Promise<Either<DocumentSourceError, DocumentContent | null>>;
  updateDocument?(ref: DocumentReference, options: DocumentUpdateOptions): Promise<Either<DocumentSourceError, void>>;
  healthCheck?(): Promise<HealthCheckResult>;
}
```

### 2. IndexStore Interface

Abstracts index management:

```typescript
interface IndexStore {
  readonly name: string;
  getByDocId(docId: string): Promise<Either<IndexStoreError, PluginIndexEntry | null>>;
  getByPath(path: string): Promise<Either<IndexStoreError, PluginIndexEntry | null>>;
  listEntries(): AsyncIterable<PluginIndexEntry>;
  upsert(entry: PluginIndexEntry): Promise<Either<IndexStoreError, void>>;
  delete(docId: string): Promise<Either<IndexStoreError, boolean>>;
  findDuplicates(): Promise<Either<IndexStoreError, DuplicateReport>>;
  findOrphans?(documentPaths: readonly string[]): Promise<Either<IndexStoreError, readonly string[]>>;
}
```

### 3. ChangeTracker Interface

Abstracts change detection:

```typescript
interface ChangeTracker {
  readonly name: string;
  detectChanges(baseRef: string, source: DocumentSource): Promise<Either<ChangeTrackerError, PluginChangeDetectionResult>>;
  isAvailable(): Promise<boolean>;
  isValidRef?(ref: string): Promise<boolean>;
}
```

### Design Principles

1. **Either type**: All async methods return `Promise<Either<Error, Success>>` for explicit error handling
2. **AsyncIterable**: List methods return async iterables for memory efficiency with large document sets
3. **readonly modifiers**: All interface properties are readonly for immutability
4. **Optional methods**: Non-essential methods (updateDocument, healthCheck, findOrphans, isValidRef) are optional
5. **camelCase naming**: Plugin interfaces use camelCase; conversion utilities provided for snake_case compatibility

### Implementation Phases

- **Phase 1 (v0.2.0)**: Interface definitions only (this ADR)
- **Phase 2 (v0.3.0)**: Default implementations (FileSystemSource, YamlFileIndexStore, GitChangeTracker)
- **Phase 3 (v0.4.0)**: Plugin loader and configuration
- **Phase 4 (v0.5.0+)**: Reference external plugins

## Alternatives Considered

### 1. Direct Refactoring

Refactor existing code to accept abstract interfaces without a formal plugin system.

**Pros**:
- Simpler implementation
- No new concepts to learn

**Cons**:
- No clear extension points for external plugins
- Harder to maintain separation of concerns
- No plugin lifecycle management

**Rejected because**: Limits future extensibility and makes external integrations harder.

### 2. Configuration-Only DI

Use configuration to select between built-in implementations only.

**Pros**:
- Simpler for users
- No external code execution concerns

**Cons**:
- Cannot add new backends without code changes
- Limited flexibility

**Rejected because**: Doesn't address the core need for external system integration.

### 3. Monolithic Plugin Interface

Single `ShirushiPlugin` interface that must implement all functionality.

**Pros**:
- Simpler mental model

**Cons**:
- Forces plugins to implement unused functionality
- Poor separation of concerns

**Rejected because**: Most plugins only need one or two capabilities.

## Consequences

### Positive

- **Extensibility**: External systems (databases, cloud services) can be integrated
- **Testability**: Mock implementations can be easily injected
- **Maintainability**: Clear separation between core logic and I/O
- **Backward Compatibility**: Existing behavior preserved via default implementations

### Negative

- **Complexity**: Additional abstraction layer to understand
- **Type Conversion**: Need utilities for snake_case ↔ camelCase conversion
- **Performance**: Possible overhead from abstraction (minimal in practice)

### Neutral

- **File Structure**: New `src/plugins/` directory added
- **Dependencies**: No new runtime dependencies for Phase 1

## Related Decisions

- **ADR-0003**: Document is Source of Truth - plugins must respect this principle
- **ADR-0007**: Manual Index Synchronization - IndexStore.upsert() is only called via explicit sync commands
- **Issue #16**: Original RFC for this plugin architecture

## Notes

### Phase 2 Migration Path

| Current Implementation | Phase 2 Migration Target |
|------------------------|--------------------------|
| `src/core/scanner.ts` | `FileSystemSource` |
| `src/core/index-manager.ts` | `YamlFileIndexStore` |
| `src/git/change-detector.ts` | `GitChangeTracker` |

### Naming Convention

Plugin interfaces use **camelCase** (`docId`, `docType`) following TypeScript conventions.
Existing core types use **snake_case** (`doc_id`, `doc_type`) for YAML compatibility.

Conversion utilities are provided in `src/plugins/compat.ts`:

```typescript
toPluginIndexEntry(entry: IndexEntry): PluginIndexEntry
toIndexEntry(entry: PluginIndexEntry): IndexEntry
```

### Known Limitations (Phase 1)

以下はPhase 1での既知の制約であり、Phase 2以降で対応を検討する:

#### 1. AsyncIterable の Either 非対応

`listDocuments()` と `listEntries()` は `AsyncIterable<T>` を返すが、ストリーム途中のI/Oエラーを構造化された `Either` 型で表現できない。

**緩和策**: 実装側で例外をスローし、呼び出し側で `try-catch` でハンドリング。

#### 2. 型ガードのランタイム検証限界

`isDocumentSource()` 等の型ガードは、メソッドが存在することのみを確認し、戻り値の型（`AsyncIterable` や `Promise<Either>` であること）を検証しない。

**緩和策**: プラグイン開発者向けドキュメントで正しい実装を明記。Phase 2でZodスキーマによる検証を検討。

#### 3. isAvailable/isValidRef の Either 非対応

`ChangeTracker.isAvailable()` と `isValidRef()` は `Promise<boolean>` を返すため、「利用不可」と「エラー発生」を区別できない。

**緩和策**: Phase 2で `Promise<Either<ChangeTrackerError, boolean>>` への変更を検討。

#### 4. PluginIndexEntry.extra の非永続性

`PluginIndexEntry.extra` フィールドは `IndexEntry`（YAMLスキーマ）に対応するフィールドがないため、`toIndexEntry()` 変換時に失われる。

**設計意図**: `extra` はプラグイン内部の一時データ用途であり、YAML永続化は意図していない。永続化が必要な場合は別途ストレージを使用すること。

#### 5. ChangeTracker の DocumentSource 強制依存

`detectChanges()` が `DocumentSource` を引数に取るため、Gitログのみで完結する実装でも依存が必要。

**緩和策**: Phase 2でオプショナル引数化を検討。
