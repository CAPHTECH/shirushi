---
doc_id: SHI-INT-2025-0001
title: Shirushi Internal Design
version: "0.1.0"
status: Draft
created_at: 2025-11-19
---

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
| Dry-run / write toggle           | TLA+ `ServiceAssignPrepare/Apply/Discard`, `PatchAtomicityInvariant`.         |

### 5.2 Patch Buffer Implementation Notes

- Core は `PatchBuffer` を `{path, docPatch, indexPatch, scopeKey, nextSerial, prevSerial, requestId, dryRun}` で表現し、TLA+ でも同構造を使用する。
- CLI `assign.prepare` はファイルシステムを更新しない。`assign.apply` のみ doc/index/serialCounter を更新し、`history`/`serviceLog` に `assignCommit` を残す。
- `assign.discard` は `--dry-run` または競合発生時 (doc が既に ID を持つ / serial が進んだ / 同じ ID が index に存在) に呼ばれ、`serviceLog.errorCode` に `ASSIGN_DRY_RUN` もしくは `ASSIGN_CONFLICT` を設定する。
- Git immutability チェックは `PatchBuffer` に保存したスナップショットと比較し、差分検出時に discard する。

## 6. Extension Hooks

- **API/MCP Adapter**: `ShirushiService` exposes `lint`, `scan`, `assign.prepare`, `assign.apply`, `assign.discard`. Each call pushes an entry to `serviceLog`, mirroring the TLA+ `Service*` actions.
- **Daemon Mode**: `StreamEmitter` wraps validator output and produces `{requestId, phase, status}` events. It shares the same `serviceLog`/`activeStream` watermarks as the formal model.

### 6.1 Service Layer Formalization

The new TLA+ section extends the system with service-aware variables:

```
VARIABLES serviceLog, nextRequestId, activeStream

ServiceLint(req) == Lint(req.baseRef) /\ Append(serviceLog, ...)
ServiceAssignPrepare(req) == AssignPrepare(req.path, req.dryRun)
ServiceAssignCommit == ApplyPatch
ServiceAssignDiscard == DiscardPatch
```

Verified properties:
- **ServiceReadOnly**: all `lint`/`scan` log entries have `mutates = FALSE`.
- **ServiceErrorCodesTotal**: `serviceLog.errorCode` ∈ `{OK, VALIDATION_ERROR, ALLOW_MISSING_ID, ASSIGN_DRY_RUN, ASSIGN_CONFLICT, SERVER_ERROR}`.
- **PatchAtomicityInvariant**: doc/index edits occur only during `ServiceAssignCommit` and always update both artefacts together.
- **StreamFinalConsistent**: streaming summary events reuse the same `requestId`/`exitCode` as their service log counterparts.

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

- `shirushi formal-sync` (詳細: `formal/FORMAL_SYNC_SPEC.md`) は `.shirushi.yml` を Zod で検証後、CIR(JSON)→Alloy/TLA+ 断片を生成する。
- 生成物: `formal/generated/alloy-constants.als`, `formal/generated/tla-constants.tla`, `formal/generated/cir.json`。git には含めず、CI と Docker verify 実行時に毎回再生成する。
- バリデーション: placeholder 完全性、enum 値集合一致、serial scope の包含、checksum 対象次元の存在をチェック。失敗時は exit code で CI を中断。
- ワークフロー: `npm run formal:sync && docker-compose run --rm verify` を推奨コマンドにし、PR では `--check-only` で差分検出→修正を促す。

## 10. Dimension Handler Specifications

Alloy モデルに handler ごとの predicate を追加し、DSL と実装の乖離を即座に検知できるようにした。

| Handler | Formal Spec | Notes |
|---------|-------------|-------|
| `enum.selectByPath` | `firstMatchingRule(dim, path)` で最初にマッチしたルールのみ採用。PathPattern は `categories: set PathCategory` を持ち、`PatternAny` がフォールバックを提供。 | 競合するルールや未カバレッジのカテゴリがあると Alloy で反例が生成される。 |
| `enum_from_doc_type` | `parsed[dim.name] = dim.mapping[d.doc_type]` を `enumFromDocTypeSpec` で強制。 | DocType 未登録の場合はモデルが破綻する。 |
| `year` | `yearDimensionSpec` が `digits` に応じた値集合 (`Year4Strings`, `Year2Strings`) を適用。 | 4 桁/2 桁以外は `YearDimension` シグネチャで拒否。 |
| `serial` | `serialHandlerSpec` が scope での増分整合性 (`prevSerial`, `nextSerial`) と digit 長を確認。 | `ValueWeight` を整数化した ranking を用いてギャップを検出。 |
| `checksum` | 既存の `validChecksum` を handler セクションに再配置。 | `targetDims` が自分自身を参照しないことを再検証。 |

## 11. Assign & Streaming TODOs

- Assign パッチ API を SDK からも利用できるようにし、MCP で dry-run→apply を分離呼び出し可能にする。
- Streaming 出力を `lint --json --stream` 以外 (watcher/LSP) でも共通利用するため、イベントキューを抽象化する。

### 11.1 Assign Flow Formalization (Future)

継続トピック: 並列 assign (single-user 範囲外) を扱う際は `patchBuffer` をキュー化し、TLA+ の fairness 条件を追加する。

## 11. Formal Verification Traceability

| Internal Concern                        | Formal Coverage                                                           |
|-----------------------------------------|----------------------------------------------------------------------------|
| Config + dimension semantics            | Alloy `ShirushiConfig` facts, handler predicates (`enumSelectByPath`, etc.)|
| Doc/index bijection, serial scope       | Alloy `docIndexConsistency`, `uniqueSerialsInScope`, `serialHandlerSpec`   |
| Lint immutability / read-only guarantee | TLA+ `ServiceLint`, `ServiceReadOnly`, `ImmutabilityInvariant`             |
| Assign state transition safety          | TLA+ `ServiceAssign*`, `PatchAtomicityInvariant`, `AssignPreservesInvariants` |
| Missing-ID policy vs. git diff          | TLA+ `MissingIDPolicyInvariant`                                           |
| Streaming exit code consistency         | TLA+ `StreamEvents`, `StreamFinalConsistent`; Alloy `LintEvent` schema     |

> When modifying modules listed above, update the corresponding Alloy/TLA+ properties to keep the guarantees in sync.
