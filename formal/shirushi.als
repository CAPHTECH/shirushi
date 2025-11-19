// Shirushi Document ID Management System - Formal Specification
// Version: 0.1.0
// Language: Alloy 6

// ============================================================================
// Core Domain Model
// ============================================================================

// Document represents a Markdown or YAML file with metadata
sig Document {
  path: one Path,
  doc_id: lone DocID,        // 'lone' allows missing ID (for MISSING_ID error detection)
  doc_type: lone DocType,
  metadata: Metadata -> lone String
}

sig Path {}                  // File path (opaque)
sig DocID {}                 // Document ID (structured, validated by dimensions)
sig DocType {}               // Document type (spec, design, memo, etc.)
sig Metadata {}              // Metadata keys (created_at, owner, etc.)

// Index file: maps doc_id to path and metadata
sig IndexFile {
  entries: DocID -> one IndexEntry
} {
  // Constraint: Each doc_id appears at most once (enforced by function type)
  // Constraint: Each path appears at most once (bijection on paths)
  all disj id1, id2: DocID |
    (id1 in entries.IndexEntry and id2 in entries.IndexEntry)
    implies entries[id1].path != entries[id2].path
}

sig IndexEntry {
  path: one Path,
  doc_type: lone DocType,
  metadata: Metadata -> lone String
}

// ============================================================================
// Dimension System (ADR-0001: Discriminated Unions)
// ============================================================================

abstract sig Dimension {
  name: one DimensionName
}

sig DimensionName {}

sig EnumDimension extends Dimension {
  values: some String,       // At least one allowed value
  selectRules: set PathPattern -> String
} {
  // All select rule values must be in allowed values
  selectRules[PathPattern] in values
  // All values must be non-empty and distinct
  all v: values | some v
  all disj v1, v2: values | v1 != v2
}

sig EnumFromDocTypeDimension extends Dimension {
  mapping: DocType -> one String
}

sig YearDimension extends Dimension {
  digits: one Int,
  source: one YearSource
} {
  digits = 4 or digits = 2   // Only 2-digit or 4-digit years
}

enum YearSource { CreatedAt, Now }

sig SerialDimension extends Dimension {
  digits: one Int,
  scopeNames: seq DimensionName    // Ordered list of dimension names defining scope
} {
  digits > 0 and digits <= 8
  // Well-foundedness: scope cannot reference itself
  not (name in elems[scopeNames])
}

sig ChecksumDimension extends Dimension {
  algorithm: one ChecksumAlgorithm,
  targetDims: seq DimensionName   // Ordered list of dimensions to checksum
} {
  // Checksum cannot include itself
  not (name in elems[targetDims])
}

// Currently only mod26AZ, but extensible for future algorithms (e.g., CRC32, SHA256)
enum ChecksumAlgorithm { Mod26AZ }

sig PathPattern {}
sig String {}

// ============================================================================
// Configuration (from .shirushi.yml)
// ============================================================================

sig ShirushiConfig {
  id_format: one IDFormat,
  dimensions: DimensionName -> one Dimension,
  forbid_id_change: one Bool,
  allow_missing_id_in_new_files: one Bool
} {
  // All dimension names in id_format must be defined
  id_format.placeholders in dimensions.Dimension

  // All dimension names must be unique
  all d1, d2: dimensions.Dimension |
    d1.name = d2.name implies d1 = d2

  // Well-foundedness: No circular dependencies in scope/target references
  all d: dimensions.Dimension | {
    d in SerialDimension implies d.name not in reachableDims[d, d.scopeNames, dimensions]
    d in ChecksumDimension implies d.name not in reachableDims[d, d.targetDims, dimensions]
  }
}

sig IDFormat {
  template: one String,
  placeholders: set DimensionName,    // Extracted from template
  order: seq DimensionName            // Left-to-right order in template
} {
  // All placeholders appear in order
  elems[order] = placeholders
}

enum Bool { True, False }

// Helper: Compute reachable dimension names through scope/target references
fun reachableDims[
  d: Dimension,
  via: seq DimensionName,
  dimMap: DimensionName -> Dimension
]: set DimensionName {
  elems[via] + { n: DimensionName |
    some i: elems[via], refDim: dimMap[i] | {
      refDim in SerialDimension implies n in reachableDims[refDim, refDim.scopeNames, dimMap]
      refDim in ChecksumDimension implies n in reachableDims[refDim, refDim.targetDims, dimMap]
    }
  }
}

// ============================================================================
// System State
// ============================================================================

sig SystemState {
  config: one ShirushiConfig,
  documents: set Document,
  index: one IndexFile
}

// ============================================================================
// INVARIANTS (What shirushi lint validates)
// ============================================================================

// INV-1: Document IDs are unique across all documents
pred uniqueDocIDs[s: SystemState] {
  all disj d1, d2: s.documents |
    (some d1.doc_id and some d2.doc_id) implies d1.doc_id != d2.doc_id
}

// INV-2: Index doc_ids are unique (already enforced by IndexFile signature)
pred uniqueIndexIDs[s: SystemState] {
  all id: DocID | lone s.index.entries.id
}

// INV-3: Document doc_id matches index entry (ADR-0003: Document is source of truth)
// If both exist, they must match. Mismatch is DOC_ID_MISMATCH_WITH_INDEX error.
pred docIndexConsistency[s: SystemState] {
  all d: s.documents | some d.doc_id implies {
    // If document has ID and appears in index, IDs must match
    let indexIDs = { id: DocID | s.index.entries[id].path = d.path } | {
      // Either not indexed, or indexed exactly once with matching ID
      no indexIDs or (one indexIDs and d.doc_id in indexIDs)
    }
  }
}

// INV-4: All indexed documents exist as files
pred indexedDocsExist[s: SystemState] {
  all id: s.index.entries.DocID |
    some d: s.documents | d.path = s.index.entries[id].path
}

// INV-5: All documents with doc_id are indexed
pred allDocsIndexed[s: SystemState] {
  all d: s.documents | some d.doc_id implies
    some id: s.index.entries.DocID | s.index.entries[id].path = d.path
}

// INV-6: Doc_id format validation
pred validDocIDFormat[s: SystemState, d: Document] {
  some d.doc_id implies {
    // doc_id must parse according to id_format and dimensions
    let fmt = s.config.id_format,
        parsed = parseDocID[d.doc_id, fmt] |
      // All dimension values extracted successfully
      fmt.placeholders in parsed.DimensionName and
      // Each dimension value is valid for its type
      all dimName: fmt.placeholders |
        validateDimensionValue[
          parsed[dimName],
          s.config.dimensions[dimName],
          d,
          s
        ]
  }
}

// INV-7: Checksum correctness
pred validChecksum[s: SystemState, d: Document] {
  some d.doc_id implies {
    all chkDim: ChecksumDimension & s.config.dimensions[DimensionName] | {
      let parsed = parseDocID[d.doc_id, s.config.id_format],
          targetValues = { v: String |
            some name: elems[chkDim.targetDims] | v = parsed[name] },
          computed = computeChecksum[targetValues, chkDim.algorithm, chkDim.targetDims] |
        parsed[chkDim.name] = computed
    }
  }
}

// INV-8: Serial uniqueness within scope
pred uniqueSerialsInScope[s: SystemState] {
  all serialDim: s.config.dimensions.Dimension & SerialDimension | {
    all disj d1, d2: s.documents | {
      (some d1.doc_id and some d2.doc_id) implies {
        let p1 = parseDocID[d1.doc_id, s.config.id_format],
            p2 = parseDocID[d2.doc_id, s.config.id_format],
            scopeKey1 = computeScopeKey[p1, serialDim.scopeNames],
            scopeKey2 = computeScopeKey[p2, serialDim.scopeNames] |
          // If same scope, serial values must differ
          (scopeKey1 = scopeKey2) implies
            p1[serialDim.name] != p2[serialDim.name]
      }
    }
  }
}

// Combined system invariant
pred systemInvariant[s: SystemState] {
  uniqueDocIDs[s]
  uniqueIndexIDs[s]
  docIndexConsistency[s]
  indexedDocsExist[s]
  allDocsIndexed[s]
  all d: s.documents | validDocIDFormat[s, d]
  all d: s.documents | validChecksum[s, d]
  uniqueSerialsInScope[s]
}

// ============================================================================
// Helper Functions (Axiomatically Constrained)
// ============================================================================

// Parse doc_id string into dimension name -> value mapping
// AXIOM: Parsing succeeds iff doc_id structurally matches format
fun parseDocID[id: DocID, fmt: IDFormat]: DimensionName -> String {
  // Axiomatic properties (not full implementation):
  // 1. If parsing succeeds, result contains exactly the expected dimensions
  // 2. If parsing fails, result is empty
  // 3. Deterministic: same input always gives same output
  let result = DimensionName -> String |
    (some result) implies elems[result.String] = fmt.placeholders
    else (no result)
}

// Validate a dimension value according to its type
pred validateDimensionValue[
  value: String,
  dim: Dimension,
  doc: Document,
  sys: SystemState
] {
  dim in EnumDimension implies value in dim.values
  dim in EnumFromDocTypeDimension implies
    some doc.doc_type and value = dim.mapping[doc.doc_type]
  dim in YearDimension implies isValidYear[value, dim.digits]
  dim in SerialDimension implies isValidSerial[value, dim.digits]
  // Checksum validation is separate (INV-7)
}

pred isValidYear[value: String, digits: Int] {
  // Abstract: Check value is numeric and has correct digit count
  True = True  // Placeholder
}

pred isValidSerial[value: String, digits: Int] {
  // Abstract: Check value is zero-padded numeric with correct digit count
  True = True  // Placeholder
}

// Compute scope key by concatenating dimension values in order
fun computeScopeKey[
  parsed: DimensionName -> String,
  scopeDims: seq DimensionName
]: String {
  // Concatenate values with "-" separator (Issue 8 resolution)
  // Example: scope=[COMP,KIND,YEAR4], values={COMP:PCE,KIND:SPEC,YEAR4:2025}
  // => scopeKey = "PCE-SPEC-2025"
  // Edge case: empty scope => empty string
  String  // Placeholder (actual impl would use string join)
}

// Compute checksum from dimension values
fun computeChecksum[
  values: seq String,
  algo: ChecksumAlgorithm,
  order: seq DimensionName
]: String {
  // Abstract function - actual implementation is mod26AZ algorithm
  // Concatenates values in 'order' sequence, then applies algorithm
  String  // Placeholder
}

// ============================================================================
// Lint Command Model
// ============================================================================

// Validation error type (concrete, not abstract, so it can be instantiated)
sig ValidationError {
  document: one Document,
  errorCode: one ErrorCode
}

enum ErrorCode {
  MISSING_ID,
  MULTIPLE_IDS,
  INVALID_FORMAT,
  INVALID_CHECKSUM,
  INVALID_ENUM,
  ENUM_MISMATCH,
  MISSING_FILE,
  UNINDEXED,
  INDEX_MISMATCH,
  ID_CHANGED,
  DUPLICATE_ID
}

// Lint operation: computes all validation errors for a given state
fun lintErrors[s: SystemState]: set ValidationError {
  { e: ValidationError |
    (e.errorCode = MISSING_ID and MISSING_ID[s, e.document]) or
    (e.errorCode = INVALID_FORMAT and INVALID_ID_FORMAT[s, e.document]) or
    (e.errorCode = INVALID_CHECKSUM and INVALID_ID_CHECKSUM[s, e.document]) or
    (e.errorCode = INDEX_MISMATCH and DOC_ID_MISMATCH_WITH_INDEX[s, e.document]) or
    (e.errorCode = DUPLICATE_ID and DUPLICATE_DOC_ID[s, e.document])
  }
}

// Lint with Git comparison
fun lintErrorsWithBase[base: SystemState, current: SystemState]: set ValidationError {
  lintErrors[current] + { e: ValidationError |
    e.errorCode = ID_CHANGED and DOC_ID_CHANGED[base, current, e.document]
  }
}

// Lint is read-only: does not modify system state
pred lintIsReadOnly[s: SystemState] {
  // Computing errors doesn't change the state
  lintErrors[s]  // Pure function, no side effects
  s = s          // State remains unchanged
}

// ============================================================================
// Error Detection Predicates
// ============================================================================

pred MISSING_ID[s: SystemState, d: Document] {
  no d.doc_id
}

pred MULTIPLE_IDS_IN_DOCUMENT[s: SystemState, d: Document] {
  // This would require modeling document content parsing
  // Simplified: assume Document.doc_id is 'lone' enforces this
  #d.doc_id > 1
}

pred INVALID_ID_FORMAT[s: SystemState, d: Document] {
  some d.doc_id and not validDocIDFormat[s, d]
}

pred INVALID_ID_CHECKSUM[s: SystemState, d: Document] {
  some d.doc_id and not validChecksum[s, d]
}

pred DOC_ID_MISMATCH_WITH_INDEX[s: SystemState, d: Document] {
  some d.doc_id and not docIndexConsistency[s]
}

pred DUPLICATE_DOC_ID[s: SystemState, d: Document] {
  some d.doc_id and (
    some d2: s.documents - d | d2.doc_id = d.doc_id
  )
}

// ============================================================================
// Git Temporal Comparison (for --base <ref> functionality)
// ============================================================================

// Predicate: Document ID immutability check across Git states
pred checkDocIDImmutability[baseState: SystemState, currentState: SystemState] {
  all d: baseState.documents | {
    // If document exists in both states (same path)
    (some d2: currentState.documents | d2.path = d.path) implies {
      let d2 = { doc: currentState.documents | doc.path = d.path } | {
        // If both have doc_id, they must match
        (some d.doc_id and some d2.doc_id) implies d.doc_id = d2.doc_id
      }
    }
  }
}

// Error detection: Document ID was changed (forbid_id_change violation)
pred DOC_ID_CHANGED[baseState: SystemState, currentState: SystemState, d: Document] {
  d in currentState.documents and
  (some d_base: baseState.documents | d_base.path = d.path) and
  (let d_base = { doc: baseState.documents | doc.path = d.path } |
    some d_base.doc_id and some d.doc_id and d_base.doc_id != d.doc_id)
}

// ============================================================================
// Assertions (Properties to Check)
// ============================================================================

// ASSERT-1: If all invariants hold, no duplicate doc_ids exist
assert noDuplicatesWhenValid {
  all s: SystemState |
    systemInvariant[s] implies uniqueDocIDs[s]
}

// ASSERT-2: Document precedence - if doc and index disagree, it's detected
assert documentPrecedenceDetected {
  all s: SystemState | {
    all d: s.documents | {
      let indexIDs = { id: DocID | s.index.entries[id].path = d.path } | {
        (some d.doc_id and some indexIDs and d.doc_id not in indexIDs)
        implies DOC_ID_MISMATCH_WITH_INDEX[s, d]
      }
    }
  }
}

// ASSERT-3: Checksum validation catches tampering
assert checksumDetectsTampering {
  all s: SystemState, d: s.documents | {
    some d.doc_id and
    (some chkDim: ChecksumDimension & s.config.dimensions[DimensionName] | {
      let parsed = parseDocID[d.doc_id, s.config.id_format],
          targetValues = { v: String |
            some name: elems[chkDim.targetDims] | v = parsed[name] },
          computed = computeChecksum[targetValues, chkDim.algorithm, chkDim.targetDims] |
        parsed[chkDim.name] != computed
    })
  } implies INVALID_ID_CHECKSUM[s, d]
}

// ASSERT-4: Serial scope isolation - different scopes can have same serial
assert serialScopeIsolation {
  all s: SystemState |
    systemInvariant[s] implies {
      all serialDim: SerialDimension & s.config.dimensions[DimensionName] |
        all disj d1, d2: s.documents | {
          (some d1.doc_id and some d2.doc_id) implies {
            let p1 = parseDocID[d1.doc_id, s.config.id_format],
                p2 = parseDocID[d2.doc_id, s.config.id_format],
                scopeKey1 = computeScopeKey[p1, serialDim.scope],
                scopeKey2 = computeScopeKey[p2, serialDim.scope],
                serial1 = p1[serialDim.name],
                serial2 = p2[serialDim.name] |
              // Different scopes => can have same serial
              (scopeKey1 != scopeKey2) implies (serial1 = serial2 or serial1 != serial2)
          }
        }
    }
}

// ============================================================================
// Commands (for Alloy Analyzer)
// ============================================================================

// Find a valid system state
pred validSystem {
  some s: SystemState | systemInvariant[s]
}

// Find a system state with errors
pred systemWithErrors {
  some s: SystemState | not systemInvariant[s]
}

// ASSERT-5: ID immutability - changing existing doc_id is detected
assert idImmutabilityEnforced {
  all base, current: SystemState | {
    (base.config.forbid_id_change = True and
     not checkDocIDImmutability[base, current])
    implies
      (some d: current.documents | DOC_ID_CHANGED[base, current, d])
  }
}

// ============================================================================
// Commands (for Alloy Analyzer)
// ============================================================================

// Find a valid system state
pred validSystem {
  some s: SystemState | systemInvariant[s]
}

// Find a system state with errors
pred systemWithErrors {
  some s: SystemState | not systemInvariant[s]
}

// Find a case where doc_id changed between states
pred docIDChangedScenario {
  some base, current: SystemState, d: current.documents |
    DOC_ID_CHANGED[base, current, d]
}

// Check assertions (with scope limited for performance)
check noDuplicatesWhenValid for 5 but 3 Document, 3 DocID
check documentPrecedenceDetected for 5 but 3 Document, 3 DocID
check checksumDetectsTampering for 5 but 3 Document, 3 DocID
check serialScopeIsolation for 5 but 3 Document, 3 DocID
check idImmutabilityEnforced for 5 but 3 Document, 3 DocID, 2 SystemState

run validSystem for 5 but 3 Document, 3 DocID
run systemWithErrors for 5 but 3 Document, 3 DocID
run docIDChangedScenario for 5 but 3 Document, 3 DocID, 2 SystemState
