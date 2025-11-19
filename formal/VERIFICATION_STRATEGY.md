---
doc_id: SHI-FORMAL-2025-0002
title: Shirushi Formal Verification Strategy
version: "0.1.0"
status: Draft
created_at: 2025-11-19
---

# Shirushi Formal Verification Strategy

## Overview

This document explains the verification approach for Shirushi, combining formal methods (Alloy/TLA+) with property-based testing to achieve comprehensive correctness guarantees.

> Self-hosting note: The documentation set (`docs/specifications.md`, `docs/api/*`, guides, etc.) is now managed by Shirushi itself via `docs/.shirushi.yml` and `docs/doc_index.yaml`. Formal sync and lint runs therefore cover these files exactly like any downstream repository, preventing "紺屋の白袴" drift between specs and tooling.

## Verification Layers

### Layer 1: Alloy - Structural Invariants

**What Alloy verifies:**
- High-level system invariants (uniqueness, consistency)
- Dimension type system correctness
- Index-document relationships
- Configuration well-formedness
- Error detection logic completeness

**What Alloy does NOT verify:**
- String parsing implementation (`id_format` → regex)
- Checksum algorithm implementation (mod26AZ)
- File I/O correctness
- Git operations

**Abstraction strategy:**
- 各 `DocID` は `dimValues` 関係を持ち、`id_format` に登場する各プレースホルダの実値を Alloy 空間上で直接保持する
- `enum`/`year`/`serial`/`checksum` の検証は有限のドメイン表（weight テーブル + アルファベット表）で具体化し、`mod26AZ` の再計算までモデル内で実行できる
- パスパターン（`select.by_path`）は `Path.category` と `PatternPCE` などのタグにより真偽を評価し、ルールの最初のマッチを取り出す
- それでも正規表現生成や任意長文字列は抽象化されているため、広い値域の検証は Layer 3 (Property-based tests) に委譲する

**Trade-off:**
- **Benefit**: Fast model checking, focus on high-level correctness
- **Cost**: Implementation bugs in parse/checksum won't be caught by Alloy
- **Mitigation**: Layer 3 (property-based tests) specifically targets these functions

### Layer 2: TLA+ - Temporal Properties

**What TLA+ verifies:**
- State transition safety (`assign` operation)
- Immutability properties across time
- Concurrent operation correctness (if applicable in future)
- Liveness properties (e.g., "assign eventually succeeds for valid input")
- Service adapter contracts (`serviceLog`, error codes, streaming exit codes)
- Assign patch buffer atomicity (prepare/apply/discard)

**Focus areas:**
- `lint` is truly read-only (no state mutation)
- `assign` preserves all invariants
- Git `--base` comparison correctly detects ID changes
- Configフラグ（`allow_missing_id_in_new_files`, `forbid_id_change`）を TLA+ の定数として表現し、ポリシーに応じた制約を常に評価
- `serviceLog` entries always use whitelisted error codes and reflect actual mutations
- `StreamEvents` start→doc→summary orderingと exit code 一貫性
- No race conditions in future concurrent implementations

### Layer 3: Property-Based Testing (fast-check)

**What property tests verify:**
- `parseDocID` implementation correctness
  - Property: Parse → unparse → parse is idempotent
  - Property: All valid IDs parse successfully
  - Property: Invalid IDs are rejected

- `computeChecksum` (mod26AZ) implementation
  - Property: Deterministic (same input → same output)
  - Property: Small input changes → different checksums (sensitivity)
  - Property: Distributes evenly across A-Z range

- Dimension validator implementations
  - Property: All enum values pass validation
  - Property: Serial numbers within digit bounds validate
  - Property: Year validators accept valid years, reject invalid

**Test strategy:**
```typescript
// Example property test
fc.assert(
  fc.property(arbitraryDocID(config), (docID) => {
    const parsed = parseDocID(docID, config.id_format);
    const reconstructed = reconstructID(parsed, config.id_format);
    expect(reconstructed).toBe(docID); // Round-trip property
  })
);
```

### Layer 4: Integration Tests

**What integration tests verify:**
- End-to-end CLI commands work correctly
- File I/O operations are correct
- Git operations integrate properly
- Error messages are user-friendly

## Coverage Map

| Component | Alloy | TLA+ | Property Tests | Integration Tests |
|-----------|-------|------|----------------|-------------------|
| ID uniqueness | ✓ | ✓ | ✓ | ✓ |
| Checksum correctness | ✓* | — | ✓✓✓ | ✓ |
| Parse correctness | ✓* | — | ✓✓✓ | ✓ |
| Immutability | ✓ | ✓✓✓ | ✓ | ✓ |
| Missing ID policy | — | ✓✓ | ✓ | ✓ |
| Index consistency | ✓✓✓ | ✓ | ✓ | ✓ |
| Dimension validation (handlers) | ✓✓ (handler predicates) | — | ✓✓✓ | ✓ |
| Assign patch buffer atomicity | — | ✓✓✓ (`ServiceAssign*`) | ✓ | ✓ |
| Service log / error codes | — | ✓✓✓ (`serviceLog`) | ✓ | ✓ |
| Streaming exit code consistency | ✓ (`LintEvent` schema) | ✓✓✓ (`StreamEvents`) | ✓ | ✓ |
| Config → formal-sync parity | ✓ (generated constants) | ✓ (generated constants) | ✓ | ✓ |
| CLI correctness | — | — | ✓ | ✓✓✓ |
| Git integration | ✓ | ✓✓ | ✓ | ✓✓✓ |

**Legend:**
- ✓ = Verified
- ✓✓✓ = Primary verification method
- — = Not applicable
- * = Alloy は有限のドメイン（`dimValues`/weight テーブル）に対してのみ検証

## Verification Workflow

0. **Config sync**: Run `shirushi formal-sync` to regenerate Alloy/TLA+ constants from `.shirushi.yml`
1. **Design phase**: Write Alloy model, check assertions
2. **Specification phase**: Write TLA+ spec, model check temporal properties
3. **Implementation phase**:
   - Implement TypeScript code
   - Write property-based tests for abstract functions
   - Ensure Alloy axioms match actual behavior
4. **Testing phase**:
   - Run property tests (100,000+ iterations)
   - Run integration tests
   - Run mutation tests on critical modules
5. **CI phase**: formal-sync → Docker `verify` (TLC + Alloy) → property/integration suites

## Known Limitations

### Alloy Limitations

**Issue**: `dimValues` や weight テーブルは有限の代表値のみを列挙
- **Impact**: 仕様上は正しいが、現実に追加される新しい `COMP`/`KIND`/`YEAR`/`SER` が Alloy の探索空間に入るとは限らず、広い値域のバグは捕捉できない
- **Mitigation**: `.shirushi.yml` から値リストを自動生成するスクリプトを追加予定。並行して property-based tests でランダム生成を継続

**Issue**: 正規表現や文字列連結は抽象化
- **Impact**: `id_format` → `id_pattern` 展開やゼロパディング実装の off-by-one を Alloy だけでは検出できない
- **Mitigation**: TypeScript 実装に対するユニットテスト／プロパティテストで網羅し、Alloy には DSL 構造の整合性チェックを集中させる

**Issue**: File I/O is not modeled
- **Impact**: Cannot verify that file reads/writes work correctly
- **Mitigation**: Integration tests with fixture files

### TLA+ Limitations

**Issue**: Git DAG structure is simplified to linear history
- **Impact**: Cannot verify behavior with complex branching/merging
- **Mitigation**: v0.1 scope only requires base-to-HEAD comparison (linear)

**Issue**: `EnumSelection`/`KindMapping`/`YearSelection`/`SerialFormatter` などの補助関数は外生定数
- **Impact**: `.shirushi.yml` の実際の設定と TLA+ 定数が乖離しても検出できない
- **Mitigation**: Apalache モデル生成ステップで設定ファイルから関数定義を自動生成する TODO を追加（下記 Next Iteration 参照）

**Issue**: Concurrent operations not modeled (v0.1)
- **Impact**: Future concurrent `assign` operations may have race conditions
- **Mitigation**: v0.2 will extend TLA+ spec before implementing concurrency

## Assertion Coverage

### Alloy Assertions (see shirushi.als)

1. `noDuplicatesWhenValid`: Invariants prevent duplicate doc_ids
2. `documentPrecedenceDetected`: Document is source of truth
3. `checksumDetectsTampering`: Invalid checksums are caught
4. `serialScopeIsolation`: Scopes correctly isolate serial numbers
5. `idImmutabilityEnforced`: Changed IDs are detected

### TLA+ Assertions (see shirushi.tla)

1. `TypeInvariant`: All state variables have correct types
2. `SystemInvariant`: All Alloy invariants hold in all reachable states
3. `LintReadOnly`: Lint never modifies state
4. `AssignPreservesInvariants`: Assign maintains uniqueness and consistency
5. `ImmutabilityNeverViolated`: Existing doc_ids never change
6. `MissingIDPolicyAlways`: `allow_missing_id_in_new_files` の条件を満たした場合のみ `doc_id` 欠落を許容

## Maintenance

- **When adding new dimension type**:
  1. Add to Alloy model
  2. Add validator to property tests
  3. Run full verification suite

- **When changing ID format**:
  1. Update Alloy `id_format` constraints
  2. Update TLA+ state machine
  3. Regenerate property test arbitraries

- **When finding bugs**:
  1. Create failing test case
  2. Fix implementation
  3. Add regression test
  4. Check if formal model needs updating

## Next Iteration Focus

1. **自動生成されたドメイン**: `.shirushi.yml` から Alloy/TLA+ の `CompCodes`・`KindCodes`・`YearCodes`・`SerialStrings` を生成し、有限集合の陳腐化リスクをなくす
2. **Config-aware Apalache**: `EnumSelection` や `YearSelection` を設定ファイルと `doc_index` から合成するスクリプトを CI に組み込み、TLA+ 定数と実装を一元化
3. **Git 分岐カバレッジ**: `gitBase` を複数の履歴スナップショットに拡張し、`AllowMissingIDs = false` のケースとマージ衝突シナリオを追加で検証
4. **Checksum fuzzing bridge**: Alloy の weight テーブルと fast-check の arbitrary を同一 YAML から生成し、形式仕様とランダムテストで同じ値空間を共有する

## References

- [Alloy Documentation](https://alloytools.org/documentation.html)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [fast-check Documentation](https://fast-check.dev/)
- [Lightweight Formal Methods](https://www.hillelwayne.com/post/fms-for-the-working-dev/)
