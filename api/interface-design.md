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

## 3. Configuration & Data Contracts

(…省略…)

## 7. Formal Verification Alignment

| Interface Contract                               | Formal Artefact / Property                                                                 | Notes                                                                                     |
|--------------------------------------------------|--------------------------------------------------------------------------------------------|-------------------------------------------------------------------------------------------|
| `.shirushi.yml` dimension/DSL semantics          | Alloy `dimensions` + `validDocIDFormat`/`validateDimensionValue`                           | Sample universe mirrors config to ensure enum/serial/checksum rules are exercised.        |
| Doc/index bijection + immutability               | Alloy `docIndexConsistency`, `indexedDocsExist`, `uniqueSerialsInScope`; TLA+ `SystemInvariant`, `ImmutabilityInvariant` | CLI lint guarantees are modeled as invariants checked per state transition.               |
| CLI lint read-only contract                      | TLA+ `Lint` action + `LintReadOnly` property                                               | Ensures interface spec (“lint never mutates files”) is enforced temporally.               |
| `--base` and `allow_missing_id_in_new_files`     | TLA+ `MissingIDPolicyInvariant`                                                            | Interface flag semantics are reflected in TLA+ constants (`AllowMissingIDs`, `gitBase`).   |
| Assign serial/checksum generation                | Alloy `uniqueSerialsInScope`, `validChecksum`; TLA+ `Assign` action                        | Interface commitment（ID format） matches modeled serial scope & checksum recomputation.  |
| API/MCP Service Interface contracts              | TLA+ service adapter spec (future), Alloy command model (future)                           | Need to model streaming/daemon flows; currently only CLI path is specified.               |

> Future work: auto-generate Alloy/TLA+ constants directly from `.shirushi.yml` so that interface changes trigger formal revalidation automatically.

## 8. API / MCP Service Contract (Draft)

To support non-CLI integrations, expose a gRPC/REST or MCP tool surface modeled after the CLI DTOs.

### 9.1 Service Endpoints

| Endpoint            | Request Body                                                       | Response                          | Notes |
|---------------------|--------------------------------------------------------------------|-----------------------------------|-------|
| `POST /lint`        | `{ configPath?, configInline?, baseRef?, changedOnly? }`           | `ValidationResult`                | Accepts either repo-relative path or inline config blob. |
| `POST /scan`        | `{ configPath?, format?, filter? }`                                | `ScanResult[]`                    | Format options mirror CLI. |
| `POST /assign`*     | `{ configPath?, baseRef?, dryRun? }`                               | `AssignResult[]`                  | Writes doc/front matter + index unless `dryRun`. |

\* `assign` endpoint becomes active once CLI assign graduates from ADR-0005.

### 9.2 MCP Tool Signature

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

### 8.3 Streaming / Daemon Mode (Design Sketch)

```
FileWatcher -> Scanner: changed documents
Scanner -> Validator: incremental lint
Validator -> Broker: push events
Broker -> Clients (LSP/CI): apply decorations or annotations
```

このモードでは stateless HTTP ではなく WebSocket/IPC で逐次 event を送る。前提となる `CoreContext` をホットリロード可能にする必要がある。
## 9. Open Questions

- Given the single-user (local or CI) model, is additional locking on index updates necessary?
- How to expose partial lint results via structured JSON streaming for CI annotations?
- What minimum set of parsers must an integration implement (Markdown + YAML, or pluggable)?
