# Shirushi Internal Design

## 1. Purpose
This document dives deeper than the interface specification and explains how the CLI, core logic, dimension handlers, and persistence layers cooperate at runtime. Use it when modifying internals, introducing new transports, or reviewing architecture.

## 2. Component Overview

| Layer/Component              | Responsibility                                                                   | Key Dependencies                                |
|-----------------------------|-----------------------------------------------------------------------------------|-------------------------------------------------|
| `cli/commands/*`            | Parse args, build DTOs, invoke core services                                      | Commander.js, `CoreContextBuilder`              |
| `cli/output/*`              | Render validation results (table, JSON, YAML)                                    | `ValidationResult`, reporters                   |
| `core/context.ts` (planned) | Assemble config, documents, index, git snapshot into a `CoreContext`             | Config loader, scanner, git facade              |
| `core/validator.ts`         | Orchestrate lint rules, delegate to dimension handlers                           | Dimension registry, error reporter              |
| `core/scanner.ts`           | Resolve `doc_globs`, parse doc metadata/front matter                             | Parsers (`markdown.ts`, `yaml.ts`)              |
| `core/generator.ts`         | Compose doc_ids for assign (v0.2)                                                | Dimension handlers, index manager               |
| `dimensions/handlers/*`     | Validate/derive values per dimension type                                        | Shared handler base, config                     |
| `index-manager.ts`          | Load/save `docs/doc_index.yaml`, compute diffs                                   | YAML parser, filesystem                         |
| `git/operations.ts`         | Provide `--base` snapshots, immutability comparison                              | `simple-git` wrapper                            |
| `errors/*`                  | Error codes/classes surfaced to CLI                                              | None                                           |

## 3. Core Data Structures

```ts
interface CoreContext {
  config: ShirushiConfig;
  documents: DocumentSnapshot[]; // path, docId, metadata, docType
  index: IndexFile;
  git: GitFacade; // exposes base snapshots + diff utilities
  logger: Logger;
}

interface ValidationResult {
  errors: ValidationError[];
  warnings: ValidationWarning[];
  summary: {
    checkedDocs: number;
    elapsedMs: number;
  };
}
```

## 4. Lint Flow (Detailed)

1. CLI builds `LintOptions` (`configPath`, `baseRef`, `changedOnly`).
2. `CoreContextBuilder` loads config, enumerates documents via `scanner.scan(doc_globs)`.
3. If `--base` provided, `git.diff(baseRef)` returns `{ existingDocs, newDocs }` to inform validator.
4. `validator.run(ctx, options)` executes stages:
   - **Structure**: Ensure each document has `doc_id`, parse via template.
   - **Dimension Checks**: For each placeholder, call corresponding handler (`enum`, `serial`, etc.).
   - **Checksum**: Recompute `chkDim` using handler-provided values.
   - **Index Consistency**: Compare doc vs. `index` entries.
   - **Git Immutability**: If `forbid_id_change`, compare base snapshots.
5. Results propagate back to CLI, which chooses reporter (table, JSON, YAML) and sets exit code (0=clean, 1=errors).

## 5. Assign Flow (v0.2 scope)

Usage assumptions: single user (local MCP / CI) running sequential operations. No concurrent writers.

| Step | Description |
|------|-------------|
| 1    | CLI collects documents missing `doc_id` and builds `AssignOptions` (`config`, `baseRef?`, `dryRun?`). |
| 2    | `CoreContextBuilder` prepares context; generator receives `[DocumentSnapshot]` lacking IDs. |
| 3    | Generator orchestrates dimension handlers: `enum.selectByPath`, `enum_from_doc_type`, `year`, `serial.reserve(scope, index)`, `checksum`. |
| 4    | Compose `GeneratedIdPatch { docPath, docPatch, indexPatch }`. |
| 5    | If `dryRun=false`, apply patches: update markdown front matter / YAML root + append index entries. |
| 6    | Reporter summarizes assigned IDs + files touched. |

### 5.1 Formalization Mapping

| Assign stage                     | Formal Artefact / Extension                                                   |
|----------------------------------|-------------------------------------------------------------------------------|
| Candidate detection              | Alloy scenario with `DocID = NoID`; TLA+ `Assign` precondition.               |
| Dimension derivation             | Alloy handler facts (`validateDimensionValue`); TLA+ `Assign` LET bindings.   |
| Serial reservation               | Alloy `uniqueSerialsInScope`; TLA+ `serialCounters' = serialCounters @@ {...}` |
| Checksum recomputation           | Alloy `validChecksum`; TLA+ `checksumValue`.                                  |
| Atomic doc/index patch           | TLA+ `Assign` updates `docs`/`index` in same step; Alloy `docIndexConsistency`. |
| Dry-run / write toggle           | Implementation detail; not modeled (state remains unchanged).                 |

## 6. Extension Hooks

- **API/MCP Adapter**: Expose `ShirushiService` interface around context + validator/generator.
- **Daemon Mode**: Wrap scanner + validator with file watcher; reuse reporters to push incremental diagnostics.

### 6.1 Service Layer Formalization (Planned)

Define a TLA+ adapter module (`ShirushiService`) capturing request/response contracts:

```
CONSTANTS LintReq, LintRes, ScanReq, ScanRes

LintAPI(req, res) ==
  req \in LintReq /\ res \in LintRes /\
  \* req fields optional -> defaults applied
  res.result = Validator(req.config, req.baseRef)

SpecService == InitService /\ [][NextService]_vars /\ SafeProperties
```

Key properties:
- **APIReadOnly**: `lint`/`scan` endpoints do not mutate documents/index (mirrors CLI lint property).
- **AssignWritesAtomic**: When `assign` endpoint succeeds, doc/index patches are applied in the same step (reuses CLI assign invariant).
- **ErrorCodeTotality**: Every failure path returns a defined error code (modeled as enumeration in Alloy/TLA+).

This adapter ensures MCP/REST clients inherit the same guarantees as CLI users.

## 7. Persistence and Consistency

- **Config (`.shirushi.yml`)**: Single source for dimension DSL; validated via Zod schema before use.
- **Documents**: Markdown + YAML; front matter parser extracts `doc_id` and metadata.
- **Index (`docs/doc_index.yaml`)**: Treated as derived but authoritative mirror; validator enforces doc ↔ index bijection.
- **Git Snapshot**: `git/operations.ts` caches base ref contents to ensure immutability checks don't re-read disk repeatedly.

## 8. Error Surfacing

1. Dimension handler throws typed error (`InvalidEnumValueError`, etc.).
2. Validator maps to `ValidationError` DTO with fields `{code, message, documentPath, details}`.
3. Reporter groups errors by severity and prints summary table.

## 9. Config-to-Formal Sync Plan

- Provide `shirushi formal-sync` CLI/MCP command that reads `.shirushi.yml` and emits Alloy/TLA+ constant fragments under `formal/generated/`.
- Generated files include: dimension tables, sample documents/paths, enum selections, TLA+ constants (`CompCodes`, `ScopeKeys`, etc.).
- CI pipeline should run `formal-sync` before TLC/Alloy to guarantee formal specs match repo config.
- Add validation step ensuring placeholder sets in generated constants equal `id_format` placeholders.

## 10. Assign & Streaming TODOs

- Simplify assign patching API for single-user workflow (local or CI).
- Investigate streaming output for large repositories (`lint --json` streaming chunks`).

### 10.1 Assign Flow Formalization (Proposed)

(no change; see Section 5 for mapping)

## 11. Formal Verification Traceability

| Internal Concern                        | Formal Coverage                                                           |
|-----------------------------------------|----------------------------------------------------------------------------|
| Config + dimension semantics            | Alloy `ShirushiConfig` facts, `validDocIDFormat`, `validateDimensionValue` |
| Doc/index bijection, serial scope       | Alloy `docIndexConsistency`, `uniqueSerialsInScope`                        |
| Lint immutability / read-only guarantee | TLA+ `Lint` action, `ImmutabilityInvariant`, `LintReadOnly`                |
| Assign state transition safety          | TLA+ `Assign` action + `AssignPreservesInvariants`                         |
| Missing-ID policy vs. git diff          | TLA+ `MissingIDPolicyInvariant`                                           |

> When modifying modules listed above, update the corresponding Alloy/TLA+ properties to keep the guarantees in sync.
