---
doc_id: SHI-FORMAL-2025-0005
title: Formal Specification to Implementation Mapping
version: "0.1.0"
status: Draft
created_at: 2025-11-29
---

# Formal Specification to Implementation Mapping

This document provides traceability between formal specification elements (Alloy/TLA+) and their corresponding implementation modules.

## Overview

| Specification | Purpose | Implementation Layer |
|--------------|---------|---------------------|
| `shirushi.als` | Structural invariants, domain model | Types, Core |
| `shirushi.tla` | CLI/Service behavior, state transitions | CLI, Core |
| `ShirushiSeq.tla` | Sequential validation model | Core (Validator) |
| `ShirushiPar.tla` | Parallel validation model | Core (Validator - future) |
| `ShirushiBoundary.als` | Architecture boundary comparison | Design documentation |

---

## Alloy Signatures → TypeScript Types

### Core Domain Model (`shirushi.als`)

| Alloy Signature | TypeScript Type | Implementation File | Notes |
|-----------------|-----------------|---------------------|-------|
| `Document` | `Document` | `src/types/document.ts` | Branded type with path, doc_id, metadata |
| `DocID` | `DocId` | `src/types/document.ts` | Branded string type |
| `Path` | `DocumentPath` | `src/types/document.ts` | Branded string type |
| `DocType` | `DocType` | `src/types/document.ts` | String literal union |
| `Status` | `DocumentStatus` | `src/types/document.ts` | `'Draft' \| 'Active' \| 'Deprecated' \| 'Superseded'` |
| `Metadata` | `DocumentMetadata` | `src/types/document.ts` | `Record<string, string>` |
| `IndexFile` | `DocIndex` | `src/types/index.ts` | Index file structure |
| `IndexEntry` | `IndexEntry` | `src/types/index.ts` | Single index entry |

### Dimension System (`shirushi.als`)

| Alloy Signature | TypeScript Type | Implementation File | Notes |
|-----------------|-----------------|---------------------|-------|
| `Dimension` | `Dimension` | `src/types/dimension.ts` | Discriminated union base |
| `DimensionName` | `DimensionName` | `src/types/dimension.ts` | String literal |
| `EnumDimension` | `EnumDimension` | `src/dimensions/handlers/enum.ts` | `{ type: 'enum', values: string[] }` |
| `EnumFromDocTypeDimension` | `EnumFromDocTypeDimension` | `src/dimensions/handlers/enum.ts` | `{ type: 'enum_from_doc_type', mapping: Record }` |
| `YearDimension` | `YearDimension` | `src/dimensions/handlers/year.ts` | `{ type: 'year', digits: 2 \| 4 }` |
| `SerialDimension` | `SerialDimension` | `src/dimensions/handlers/serial.ts` | `{ type: 'serial', digits: number, scope: string[] }` |
| `ChecksumDimension` | `ChecksumDimension` | `src/dimensions/handlers/checksum.ts` | `{ type: 'checksum', algorithm: 'mod26AZ' }` |

### Configuration (`shirushi.als`)

| Alloy Signature | TypeScript Type | Implementation File | Notes |
|-----------------|-----------------|---------------------|-------|
| `ShirushiConfig` | `ShirushiConfig` | `src/config/schema.ts` | Zod-inferred type |
| `IDFormat` | `IdFormat` | `src/config/schema.ts` | Template string with placeholders |
| `Bool` | `boolean` | Native | `forbid_id_change`, `allow_missing_id_in_new_files` |

### Error System (`shirushi.als`)

| Alloy Enum Value | TypeScript Constant | Implementation File | Notes |
|------------------|---------------------|---------------------|-------|
| `MISSING_ID` | `'MISSING_ID'` | `src/errors/codes.ts` | Document has no doc_id |
| `INVALID_FORMAT` | `'INVALID_ID_FORMAT'` | `src/errors/codes.ts` | ID doesn't match format |
| `INVALID_CHECKSUM` | `'INVALID_ID_CHECKSUM'` | `src/errors/codes.ts` | Checksum mismatch |
| `INDEX_MISMATCH` | `'DOC_ID_MISMATCH_WITH_INDEX'` | `src/errors/codes.ts` | Document vs index mismatch |
| `ID_CHANGED` | `'DOC_ID_CHANGED'` | `src/errors/codes.ts` | ID modified from base ref |
| `DUPLICATE_ID` | `'DUPLICATE_DOC_ID'` | `src/errors/codes.ts` | Same ID in multiple docs |

---

## TLA+ Variables → Implementation State

### Main State (`shirushi.tla`)

| TLA+ Variable | Implementation | Location | Notes |
|---------------|----------------|----------|-------|
| `docs` | Document map | `src/core/scanner.ts` | In-memory during validation |
| `index` | Index object | `src/core/index-manager.ts` | Loaded from `doc_index.yaml` |
| `gitBase` | Git snapshot | `src/git/operations.ts` | Retrieved via `git show <ref>:path` |
| `serialCounters` | Serial counter map | `src/dimensions/handlers/serial.ts` | Built during validation pass |
| `history` | N/A | N/A | Modeling artifact only |
| `patchBuffer` | Pending changes | `src/core/generator.ts` | Two-phase assign buffer |
| `serviceLog` | N/A | CLI output | Logging/reporting |
| `activeStream` | Stream state | `src/cli/output/stream.ts` | For `--json --stream` mode |
| `streamEvents` | Event sequence | `src/cli/output/stream.ts` | NDJSON events |

### Patch Buffer Fields (`shirushi.tla`)

| TLA+ Field | Implementation | Notes |
|------------|----------------|-------|
| `patchBuffer.status` | `AssignState.phase` | `'idle' \| 'pending' \| 'committed'` |
| `patchBuffer.path` | `AssignState.targetPath` | Document to assign |
| `patchBuffer.docID` | `AssignState.generatedId` | Generated ID |
| `patchBuffer.scopeKey` | `AssignState.scopeKey` | Serial scope identifier |
| `patchBuffer.dryRun` | CLI `--dry-run` flag | No actual writes |

---

## Alloy Predicates → TypeScript Functions

### Invariant Predicates (`shirushi.als`)

| Alloy Predicate | TypeScript Function | Location | Notes |
|-----------------|---------------------|----------|-------|
| `uniqueDocIDs[s]` | `validateUniqueIds()` | `src/core/validator.ts` | Returns `ValidationError[]` if violated |
| `docIndexConsistency[s]` | `validateIndexConsistency()` | `src/core/validator.ts` | Compares doc vs index |
| `validDocIDFormat[s, d]` | `validateIdFormat()` | `src/core/validator.ts` | Regex + dimension validation |
| `validChecksum[s, d]` | `validateChecksum()` | `src/dimensions/handlers/checksum.ts` | mod26AZ computation |
| `uniqueSerialsInScope[s]` | `validateSerialUniqueness()` | `src/dimensions/handlers/serial.ts` | Per-scope check |

### Error Detection Predicates (`shirushi.als`)

| Alloy Predicate | TypeScript Function | Location |
|-----------------|---------------------|----------|
| `MISSING_ID[s, d]` | `detectMissingId()` | `src/core/validator.ts` |
| `INVALID_ID_FORMAT[s, d]` | `detectInvalidFormat()` | `src/core/validator.ts` |
| `INVALID_ID_CHECKSUM[s, d]` | `detectInvalidChecksum()` | `src/core/validator.ts` |
| `DOC_ID_MISMATCH_WITH_INDEX[s, d]` | `detectIndexMismatch()` | `src/core/validator.ts` |
| `DOC_ID_CHANGED[base, current, d]` | `detectIdChange()` | `src/git/diff.ts` |

### Helper Functions (`shirushi.als`)

| Alloy Function | TypeScript Function | Location | Notes |
|----------------|---------------------|----------|-------|
| `parseDocID[id, fmt]` | `parseDocId()` | `src/parsers/template.ts` | Regex-based parsing |
| `matchPath[p, pat]` | `matchGlob()` | `src/utils/glob.ts` | Glob pattern matching |
| `checksumLetter[total]` | `mod26AZ()` | `src/dimensions/handlers/checksum.ts` | `(sum % 26) + 'A'` |

---

## TLA+ Actions → Implementation Functions

### CLI Commands (`shirushi.tla`)

| TLA+ Action | CLI Command | Implementation |
|-------------|-------------|----------------|
| `ServiceLint` | `shirushi lint` | `src/cli/commands/lint.ts` |
| `ServiceScan` | `shirushi scan` | `src/cli/commands/scan.ts` |
| `ServiceAssignPrepare` | `shirushi assign` (plan) | `src/cli/commands/assign.ts` |
| `PatchApply` | `shirushi assign` (commit) | `src/core/generator.ts` |
| `PatchDiscard` | Conflict/dry-run abort | `src/core/generator.ts` |
| `GitCheckout` | Git operations | `src/git/operations.ts` |

### Streaming Actions (`shirushi.tla`)

| TLA+ Action | Implementation | Notes |
|-------------|----------------|-------|
| `StreamEmitDoc` | `emitDocEvent()` | `src/cli/output/stream.ts` |
| `StreamEmitFinal` | `emitSummaryEvent()` | `src/cli/output/stream.ts` |

---

## Architecture Layers (`shirushi.als`)

| Alloy Component | Implementation Module | Responsibility |
|-----------------|----------------------|----------------|
| `CLICommands` | `src/cli/commands/` | Command parsing, orchestration |
| `CLIOutput` | `src/cli/output/` | Formatters (text, json, stream) |
| `CoreValidator` | `src/core/validator.ts` | Validation logic |
| `CoreScanner` | `src/core/scanner.ts` | Document discovery |
| `CoreGenerator` | `src/core/generator.ts` | ID generation (v0.2) |
| `DimensionHandlersLayer` | `src/dimensions/handlers/` | Per-type validation/generation |
| `ParserMarkdownLayer` | `src/parsers/markdown.ts` | YAML frontmatter extraction |
| `ParserYAMLLayer` | `src/parsers/yaml.ts` | YAML file parsing |
| `GitFacadeLayer` | `src/git/` | Git operations wrapper |
| `IndexManagerLayer` | `src/core/index-manager.ts` | Index file I/O |

---

## Verification Properties → Test Coverage

| Alloy/TLA+ Property | Test Category | Test File |
|---------------------|---------------|-----------|
| `noDuplicatesWhenValid` | Unit | `tests/core/validator.test.ts` |
| `documentPrecedenceDetected` | Integration | `tests/integration/index-sync.test.ts` |
| `checksumDetectsTampering` | Unit | `tests/dimensions/checksum.test.ts` |
| `serialScopeIsolation` | Unit | `tests/dimensions/serial.test.ts` |
| `idImmutabilityEnforced` | Integration | `tests/git/diff.test.ts` |
| `TypeOK` (TLA+) | Property-based | `tests/property/` (fast-check) |
| `SystemInvariant` (TLA+) | E2E | `tests/e2e/lint.test.ts` |

---

## Assumptions and Constraints

### Explicit Assumptions (from TLA+)

| TLA+ Assumption | Implementation Constraint |
|-----------------|---------------------------|
| `MaxSerialPerScope > 0` | Config validation in Zod schema |
| `NoID \notin DocIDs` | Empty string or `undefined` represents "no ID" |
| `ForbidIDChange == TRUE` | Config `forbid_id_change` default |

### Implicit Assumptions (to be validated)

| Assumption | Validation Point |
|------------|------------------|
| File system consistency | N/A (OS responsibility) |
| Git ref validity | `git rev-parse` before operations |
| Worker count limit | Process pool configuration |

---

## References

- ADR-0001: Discriminated Unions for Dimension Types
- ADR-0002: Zod for Configuration Validation
- ADR-0003: Document is Source of Truth
- ADR-0004: mod26AZ Checksum Algorithm
- ADR-0007: Manual Index Synchronization
