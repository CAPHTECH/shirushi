---
doc_id: SHI-API-2025-0001-I
title: Shirushi Interface Design
version: "0.1.0"
status: Draft
created_at: 2025-11-19
---

# Shirushi Interface Design

## 1. Overview
Shirushi exposes a compact CLI interface backed by structured configuration/metadata files. This document defines:

1. External contracts (CLI commands, configuration schema, document/index formats).
2. Interaction flows between CLI, core services, and persistence artifacts.
3. Extension points for future transports (API server, MCP integration).

```
+---------+     CLI cmds      +-----------+      Filesystem       +----------------+
|  User   | --------------->  |  CLI/SDK  |  ------------------>  | docs/, config/ |
+---------+                   +-----------+                      +----------------+
                                   |                                   /
                                   | Core services API                /
                                   v                                  /
                             +-------------------+                   /
                             | Validator/Scanner | <-----------------
                             +-------------------+
```

## 2. CLI Interfaces

| Command          | Description                               | Mandatory Flags | Optional Flags |
|------------------|-------------------------------------------|-----------------|----------------|
| `shirushi lint`  | Validate doc IDs vs. config/index         | --config        | `--base`, `--changed-only`, `--format <json|yaml>` |
| `shirushi scan`  | Emit table/JSON of doc IDs + metadata     | --config        | `--format`, `--filter <glob>` |
| `shirushi assign` (v0.2)| Auto-generate doc_id for new docs  | --config        | `--dry-run`, `--base` |

### Command Interaction Flow

1. **CLI Layer** parses flags (Commander.js) and resolves working dir / config path.
2. Issue-specific DTOs are built (e.g., `LintOptions`, `ScanOptions`).
3. DTOs are passed to `validator.runLint(options)` or `scanner.runScan(options)`.
4. The command module subscribes to error/result events and forwards them to the formatter/reporter (table, JSON, YAML).

All command handlers consume a shared `CoreContext` object:

```ts
interface CoreContext {
  config: ShirushiConfig;
  documents: DocumentSnapshot[];
  index: IndexFile;
  git: GitFacade;
  logger: Logger;
}
```

### Assign Patch Buffer Contract

- `shirushi assign` は **prepare → (commit | discard)** の 2 段階 API で実装する。CLI は prepare で doc/index patch を一旦 `patchBuffer` に置き、確定時に commit/discard を呼ぶ。
- `--dry-run` は `assign.discard` を必ず通過し、doc/index は一切変更しない。TLA+ `PatchAtomicityInvariant` で形式的に証明している。
- commit は doc/front matter・索引・serial counter を同一ステップで更新し、`serviceLog` に `{requestId, endpoint=assign, exitCode, errorCode}` を記録する。
- 失敗 (`docChanged`, `serialConflict`, `idConflict`) は discard 扱い。CLI は `errorCode` に応じたメッセージを出力し、CI は JSON で機械判定できる。

## 3. Configuration & Data Contracts

(…省略…)

## 4. Assign Patch Buffer & Dry-run Semantics

| Stage | Description |
|-------|-------------|
| `assign.prepare` | Parses candidate documents, invokes dimension handlers, and builds `{docPatch, indexPatch, scopeKey, nextSerial, prevSerial, requestId}`. No filesystem writes occur. |
| `assign.apply` | Validates that the document is still ID-less, serial counter is unchanged, and no other doc reserved the ID. Then writes both doc and index atomically and bumps the serial counter. |
| `assign.discard` | Triggered either by `--dry-run` or by a conflict (doc changed, serial drift, duplicate ID). Leaves doc/index untouched and returns `errorCode = ASSIGN_DRY_RUN | ASSIGN_CONFLICT`. |
| Service Log | Every assign action emits a service log entry, enabling CI/MCP clients to reconcile side effects. Read-only endpoints (`lint`, `scan`) always emit `mutates=false`. |

## 5. Streaming / Incremental JSON

- `lint --json --stream` emits deterministic events: **start → doc-progress* → summary**. Each event carries `requestId`, allowing consumers to correlate with `serviceLog`.
- `doc-progress` payload: `{ docPath, status (ok|warn|error), timestamp }`. `status` escalates the stream’s `worstStatus`; warnings only appear when `allow_missing_id_in_new_files=true`.
- `summary` payload: `{ exitCode, worstStatus, checkedDocs, elapsedMs }`. Exit code must equal the CLI exit status; TLA+ `StreamFinalConsistent` enforces this.
- MCP integrations consume the same stream contract via WebSocket or MCP tool streaming responses.

## 6. Config → Formal Sync Bridge

- `shirushi formal-sync` (spec: `formal/FORMAL_SYNC_SPEC.md`) generates Alloy/TLA+ constant fragments straight from `.shirushi.yml`.
- Generated artefacts (not committed):
  - `formal/generated/alloy-constants.als` – atoms for enum/year/serial universes and rule sequences.
  - `formal/generated/tla-constants.tla` – sets/functions for `CompCodes`, `EnumSelection`, `SerialFormatter`, etc.
  - `formal/generated/cir.json` – shared intermediate representation.
- CI workflow:
  1. Run `shirushi formal-sync --output formal/generated --check-only`.
  2. Execute `docker-compose run --rm verify` to run TLC + Alloy inside a hermetic container.
  3. Fail the job if generated files drift from expected values.

## 7. Formal Verification Alignment

| Interface Contract                               | Formal Artefact / Property                                                                 | Notes                                                                                     |
|--------------------------------------------------|--------------------------------------------------------------------------------------------|-------------------------------------------------------------------------------------------|
| `.shirushi.yml` dimension/DSL semantics          | Alloy `dimensions`, handler predicates (`enumSelectByPath`, etc.)                          | Sample universe mirrors config; handler-level facts catch enum/serial misconfigurations.   |
| Doc/index bijection + immutability               | Alloy `docIndexConsistency`, `indexedDocsExist`, `uniqueSerialsInScope`; TLA+ `SystemInvariant`, `ImmutabilityInvariant` | CLI lint guarantees are modeled as invariants checked per state transition.               |
| CLI lint read-only contract                      | TLA+ `ServiceLint` action + `ServiceReadOnly` property                                     | Ensures interface spec (“lint never mutates files”) is enforced temporally.               |
| `--base` and `allow_missing_id_in_new_files`     | TLA+ `MissingIDPolicyInvariant`                                                            | Interface flag semantics are reflected in TLA+ constants (`AllowMissingIDs`, `gitBase`).   |
| Assign patch buffer + dry-run semantics          | TLA+ `ServiceAssignPrepare/Apply/Discard`, `PatchAtomicityInvariant`                       | Enforces two-phase commit semantics and ensures dry-run never mutates doc/index.          |
| Streaming lint events                            | TLA+ `StreamEvents`, `StreamFinalConsistent`; Alloy `LintEvent` schema                      | Guarantees start→doc→summary ordering and exit-code consistency for streaming output.     |
| Config → formal-sync                             | `formal/FORMAL_SYNC_SPEC.md`, generated constants, Docker `verify` pre-step                | CI enforces config/formal parity before TLC/Alloy runs.                                    |
| API/MCP service error codes                      | TLA+ `serviceLog`, `ServiceErrorCodesTotal`                                                | Read-only endpoints remain pure; assign writes emit deterministic error codes.            |

> Future work: auto-generate Alloy/TLA+ constants directly from `.shirushi.yml` so that interface changes trigger formal revalidation automatically.

## 8. API / MCP Service Contract

To support non-CLI integrations, expose a gRPC/REST or MCP tool surface modeled after the CLI DTOs.

### 8.1 Service Endpoints

| Endpoint            | Request Body                                                       | Response                          | Notes |
|---------------------|--------------------------------------------------------------------|-----------------------------------|-------|
| `POST /lint`        | `{ configPath?, configInline?, baseRef?, changedOnly? }`           | `ValidationResult`                | Accepts either repo-relative path or inline config blob. |
| `POST /scan`        | `{ configPath?, format?, filter? }`                                | `ScanResult[]`                    | Format options mirror CLI. |
| `POST /assign`*     | `{ configPath?, baseRef?, dryRun? }`                               | `AssignResult[]`                  | Writes doc/front matter + index unless `dryRun`. |

\* `assign` endpoint becomes active once CLI assign graduates from ADR-0005.

### 8.2 MCP Tool Signature

```
Tool: shirushi.lint
Input schema:
  type: object
  properties:
    config: string (optional, path or inline YAML)
    baseRef: string (optional)
    changedOnly: boolean
  required: []
Output schema: ValidationResult JSON
```

同様に `shirushi.scan`/`shirushi.assign` ツールを公開する。出力 DTO は CLI JSON と互換とする。

### 8.3 Service Log & Error Codes

- すべてのエンドポイントは `serviceLog` に `{requestId, endpoint, exitCode, errorCode, mutates}` を append する。`lint`/`scan` は必ず `mutates=false` で、TLA+ `ServiceReadOnly` が担保する。
- 標準エラーコード: `OK`, `VALIDATION_ERROR`, `ALLOW_MISSING_ID`, `ASSIGN_DRY_RUN`, `ASSIGN_CONFLICT`, `SERVER_ERROR`。`serviceLog.errorCode` がこの集合外だとモデル検証で失敗する。
- MCP レスポンスは `requestId` と `serviceLogEntry` を JSON に含め、CI が streaming イベントと相互参照できるようにする。

### 8.4 Streaming / Daemon Mode

```
FileWatcher -> Scanner: changed documents
Scanner -> Validator: incremental lint
Validator -> Broker: push StreamEvents
Broker -> Clients (LSP/CI): render diagnostics / exit codes
```

- イベント schema: `{ requestId, phase (start|doc|summary), docPath?, status, exitCode, timestamp }`。
- `StreamEvents` TLA+ アクションが start→doc→summary を強制。summary.exitCode と `serviceLog.exitCode` の一致を `StreamFinalConsistent` で検証。
- `doc` イベントは `worstStatus` を逐次更新し、`summary` の exit code に反映される。`warn` は `allow_missing_id_in_new_files=true` のときだけ使用される。
## 9. Open Questions

- Given the single-user (local or CI) model, is additional locking on index updates necessary?
- How to expose partial lint results via structured JSON streaming for CI annotations?
- What minimum set of parsers must an integration implement (Markdown + YAML, or pluggable)?
