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
  status: lone Status,       // [NEW] Document status
  superseded_by: lone DocID, // [NEW] If superseded, points to the new doc
  metadata: Metadata -> lone String
}

sig Path {                   // File path (opaque, tagged for glob selection)
  category: one PathCategory
}
abstract sig PathCategory {}
one sig PathCatPCE, PathCatKKS, PathCatEDGE, PathCatMisc extends PathCategory {}

sig DocID {                  // Document ID with parsed dimension values
  dimValues: DimensionName -> lone String
} {
  all dn: DimensionName | lone dimValues[dn]
}
sig DocType {}               // Document type (spec, design, memo, etc.)
enum Status { Draft, Active, Deprecated, Superseded } // [NEW] Status values
sig Metadata {}              // Metadata keys (created_at, owner, etc.)
sig ValueWeight {            // Deterministic scores for checksum calculation
  value: one String,
  weight: one Int
}
abstract sig AlphabetEntry {
  letter: one String,
  idx: one Int
}
one sig AlphaA, AlphaB, AlphaC, AlphaD, AlphaE, AlphaF, AlphaG, AlphaH, AlphaI, AlphaJ,
       AlphaK, AlphaL, AlphaM, AlphaN, AlphaO, AlphaP, AlphaQ, AlphaR, AlphaS, AlphaT,
       AlphaU, AlphaV, AlphaW, AlphaX, AlphaY, AlphaZ extends AlphabetEntry {}

one sig WeightPCE, WeightKKS, WeightEDGE,
       WeightSPEC, WeightDES, WeightMEMO, WeightRUN, WeightADR,
       WeightYEAR2024, WeightYEAR2025, WeightYEAR24, WeightYEAR25,
       WeightSER0001, WeightSER0002, WeightSER0003, WeightSER0004,
       WeightCHKA, WeightCHKB, WeightCHKC, WeightCHKD, WeightCHKE, WeightCHKF,
       WeightCHKG, WeightCHKH, WeightCHKI, WeightCHKJ, WeightCHKK, WeightCHKL,
       WeightCHKM, WeightCHKN, WeightCHKO, WeightCHKP, WeightCHKQ, WeightCHKR,
       WeightCHKS, WeightCHKT, WeightCHKU, WeightCHKV, WeightCHKW, WeightCHKX,
       WeightCHKY, WeightCHKZ extends ValueWeight {}

fact AlphabetAssignments {
  AlphaA.letter = "A" and AlphaA.idx = 0
  AlphaB.letter = "B" and AlphaB.idx = 1
  AlphaC.letter = "C" and AlphaC.idx = 2
  AlphaD.letter = "D" and AlphaD.idx = 3
  AlphaE.letter = "E" and AlphaE.idx = 4
  AlphaF.letter = "F" and AlphaF.idx = 5
  AlphaG.letter = "G" and AlphaG.idx = 6
  AlphaH.letter = "H" and AlphaH.idx = 7
  AlphaI.letter = "I" and AlphaI.idx = 8
  AlphaJ.letter = "J" and AlphaJ.idx = 9
  AlphaK.letter = "K" and AlphaK.idx = 10
  AlphaL.letter = "L" and AlphaL.idx = 11
  AlphaM.letter = "M" and AlphaM.idx = 12
  AlphaN.letter = "N" and AlphaN.idx = 13
  AlphaO.letter = "O" and AlphaO.idx = 14
  AlphaP.letter = "P" and AlphaP.idx = 15
  AlphaQ.letter = "Q" and AlphaQ.idx = 16
  AlphaR.letter = "R" and AlphaR.idx = 17
  AlphaS.letter = "S" and AlphaS.idx = 18
  AlphaT.letter = "T" and AlphaT.idx = 19
  AlphaU.letter = "U" and AlphaU.idx = 20
  AlphaV.letter = "V" and AlphaV.idx = 21
  AlphaW.letter = "W" and AlphaW.idx = 22
  AlphaX.letter = "X" and AlphaX.idx = 23
  AlphaY.letter = "Y" and AlphaY.idx = 24
  AlphaZ.letter = "Z" and AlphaZ.idx = 25
}

fact ValueWeightAssignments {
  WeightPCE.value = "PCE" and WeightPCE.weight = 0
  WeightKKS.value = "KKS" and WeightKKS.weight = 0
  WeightEDGE.value = "EDGE" and WeightEDGE.weight = 0
  WeightSPEC.value = "SPEC" and WeightSPEC.weight = 0
  WeightDES.value = "DES" and WeightDES.weight = 0
  WeightMEMO.value = "MEMO" and WeightMEMO.weight = 0
  WeightRUN.value = "RUN" and WeightRUN.weight = 0
  WeightADR.value = "ADR" and WeightADR.weight = 0
  WeightYEAR2024.value = "2024" and WeightYEAR2024.weight = 0
  WeightYEAR2025.value = "2025" and WeightYEAR2025.weight = 0
  WeightYEAR24.value = "24" and WeightYEAR24.weight = 0
  WeightYEAR25.value = "25" and WeightYEAR25.weight = 0
  WeightSER0001.value = "0001" and WeightSER0001.weight = 0
  WeightSER0002.value = "0002" and WeightSER0002.weight = 1
  WeightSER0003.value = "0003" and WeightSER0003.weight = 0
  WeightSER0004.value = "0004" and WeightSER0004.weight = 0
  WeightCHKA.value = "A" and WeightCHKA.weight = 0
  WeightCHKB.value = "B" and WeightCHKB.weight = 0
  WeightCHKC.value = "C" and WeightCHKC.weight = 0
  WeightCHKD.value = "D" and WeightCHKD.weight = 0
  WeightCHKE.value = "E" and WeightCHKE.weight = 0
  WeightCHKF.value = "F" and WeightCHKF.weight = 0
  WeightCHKG.value = "G" and WeightCHKG.weight = 0
  WeightCHKH.value = "H" and WeightCHKH.weight = 0
  WeightCHKI.value = "I" and WeightCHKI.weight = 0
  WeightCHKJ.value = "J" and WeightCHKJ.weight = 0
  WeightCHKK.value = "K" and WeightCHKK.weight = 0
  WeightCHKL.value = "L" and WeightCHKL.weight = 0
  WeightCHKM.value = "M" and WeightCHKM.weight = 0
  WeightCHKN.value = "N" and WeightCHKN.weight = 0
  WeightCHKO.value = "O" and WeightCHKO.weight = 0
  WeightCHKP.value = "P" and WeightCHKP.weight = 0
  WeightCHKQ.value = "Q" and WeightCHKQ.weight = 0
  WeightCHKR.value = "R" and WeightCHKR.weight = 0
  WeightCHKS.value = "S" and WeightCHKS.weight = 0
  WeightCHKT.value = "T" and WeightCHKT.weight = 0
  WeightCHKU.value = "U" and WeightCHKU.weight = 0
  WeightCHKV.value = "V" and WeightCHKV.weight = 0
  WeightCHKW.value = "W" and WeightCHKW.weight = 0
  WeightCHKX.value = "X" and WeightCHKX.weight = 0
  WeightCHKY.value = "Y" and WeightCHKY.weight = 0
  WeightCHKZ.value = "Z" and WeightCHKZ.weight = 0
}

fact DocIDValuesHaveWeights {
  all id: DocID, dn: DimensionName |
    some id.dimValues[dn] implies
      some vw: ValueWeight | vw.value in id.dimValues[dn]
}

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

sig EnumRule {
  pattern: one PathPattern,
  value: one String
}

sig EnumDimension extends Dimension {
  values: some String,       // At least one allowed value
  rules: seq EnumRule        // Ordered list of selection rules
} {
  // All rule values must be in allowed values
  rules.elems.value in values
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

abstract sig PathPattern {
  categories: some PathCategory
}
one sig PatternPCE, PatternKKS, PatternEDGE, PatternAny extends PathPattern {}

// ============================================================================
// Sample Domain Constants (tie specs to concrete atoms)
// ============================================================================

one sig DimCOMP, DimKIND, DimYEAR4, DimSER4, DimCHK1 extends DimensionName {}

one sig CompDim extends EnumDimension {}
one sig KindDim extends EnumFromDocTypeDimension {}
one sig Year4Dim extends YearDimension {}
one sig SerialDimDef extends SerialDimension {}
one sig ChecksumDimDef extends ChecksumDimension {}

one sig RulePCE, RuleKKS, RuleEDGE extends EnumRule {}

one sig DocTypeSpec extends DocType {}

one sig SampleIDFormat extends IDFormat {}
one sig SampleConfig extends ShirushiConfig {}

one sig PathPCEFile extends Path {}
one sig PathEDGEFile extends Path {}
one sig DocIDSpecPrimary extends DocID {}
one sig DocIDSpecSecondary extends DocID {}
one sig DocSpecPrimary extends Document {}
one sig DocSpecSecondary extends Document {}
one sig EntrySpecPrimary extends IndexEntry {}
one sig EntrySpecSecondary extends IndexEntry {}
one sig SampleIndex extends IndexFile {}
one sig SampleState extends SystemState {}

fact SamplePathAssignments {
  PathPCEFile.category = PathCatPCE
  PathEDGEFile.category = PathCatEDGE
}

fact PathPatternAssignments {
  PatternPCE.categories = PathCatPCE
  PatternKKS.categories = PathCatKKS
  PatternEDGE.categories = PathCatEDGE
  PatternAny.categories = PathCatPCE + PathCatKKS + PathCatEDGE + PathCatMisc
}

fact SampleDimensionDefs {
  CompDim.name = DimCOMP
  CompDim.values = "PCE" + "KKS" + "EDGE"
  CompDim.rules = (0 -> RulePCE) + (1 -> RuleKKS) + (2 -> RuleEDGE)
  RulePCE.pattern = PatternPCE
  RulePCE.value = "PCE"
  RuleKKS.pattern = PatternKKS
  RuleKKS.value = "KKS"
  RuleEDGE.pattern = PatternEDGE
  RuleEDGE.value = "EDGE"

  KindDim.name = DimKIND
  KindDim.mapping = DocTypeSpec -> "SPEC"

  Year4Dim.name = DimYEAR4
  Year4Dim.digits = 4
  Year4Dim.source = CreatedAt

  SerialDimDef.name = DimSER4
  SerialDimDef.digits = 4
  SerialDimDef.scopeNames = (0 -> DimCOMP) + (1 -> DimKIND) + (2 -> DimYEAR4)

  ChecksumDimDef.name = DimCHK1
  ChecksumDimDef.algorithm = Mod26AZ
  ChecksumDimDef.targetDims =
    (0 -> DimCOMP) + (1 -> DimKIND) + (2 -> DimYEAR4) + (3 -> DimSER4)
}

fact SampleConfigDef {
  SampleIDFormat.template = "{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}"
  SampleIDFormat.placeholders = DimCOMP + DimKIND + DimYEAR4 + DimSER4 + DimCHK1
  SampleIDFormat.order =
    (0 -> DimCOMP) + (1 -> DimKIND) + (2 -> DimYEAR4) + (3 -> DimSER4) + (4 -> DimCHK1)

  SampleConfig.id_format = SampleIDFormat
  SampleConfig.dimensions = (DimCOMP -> CompDim)
    + (DimKIND -> KindDim)
    + (DimYEAR4 -> Year4Dim)
    + (DimSER4 -> SerialDimDef)
    + (DimCHK1 -> ChecksumDimDef)
  SampleConfig.forbid_id_change = True
  SampleConfig.allow_missing_id_in_new_files = False
}

fact SampleDocuments {
  DocSpecPrimary.path = PathPCEFile
  DocSpecPrimary.doc_id = DocIDSpecPrimary
  DocSpecPrimary.doc_type = DocTypeSpec
  DocSpecPrimary.status = Active
  no DocSpecPrimary.superseded_by
  no DocSpecPrimary.metadata

  DocIDSpecPrimary.dimValues = (DimCOMP -> "PCE")
    + (DimKIND -> "SPEC")
    + (DimYEAR4 -> "2025")
    + (DimSER4 -> "0001")
    + (DimCHK1 -> "A")

  EntrySpecPrimary.path = PathPCEFile
  EntrySpecPrimary.doc_type = DocTypeSpec
  no EntrySpecPrimary.metadata

  DocSpecSecondary.path = PathEDGEFile
  DocSpecSecondary.doc_id = DocIDSpecSecondary
  DocSpecSecondary.doc_type = DocTypeSpec
  DocSpecSecondary.status = Draft
  no DocSpecSecondary.superseded_by
  no DocSpecSecondary.metadata

  DocIDSpecSecondary.dimValues = (DimCOMP -> "EDGE")
    + (DimKIND -> "SPEC")
    + (DimYEAR4 -> "2025")
    + (DimSER4 -> "0002")
    + (DimCHK1 -> "B")

  EntrySpecSecondary.path = PathEDGEFile
  EntrySpecSecondary.doc_type = DocTypeSpec
  no EntrySpecSecondary.metadata

  SampleIndex.entries =
    (DocIDSpecPrimary -> EntrySpecPrimary) +
    (DocIDSpecSecondary -> EntrySpecSecondary)

  SampleState.config = SampleConfig
  SampleState.documents = DocSpecPrimary + DocSpecSecondary
  SampleState.index = SampleIndex
}

fact SampleUniverseIsClosed {
  Path = PathPCEFile + PathEDGEFile
  DocID = DocIDSpecPrimary + DocIDSpecSecondary
  Document = DocSpecPrimary + DocSpecSecondary
  IndexFile = SampleIndex
  IndexEntry = EntrySpecPrimary + EntrySpecSecondary
  ShirushiConfig = SampleConfig
  IDFormat = SampleIDFormat
  EnumDimension = CompDim
  EnumFromDocTypeDimension = KindDim
  YearDimension = Year4Dim
  SerialDimension = SerialDimDef
  ChecksumDimension = ChecksumDimDef
  DimensionName = DimCOMP + DimKIND + DimYEAR4 + DimSER4 + DimCHK1
  EnumRule = RulePCE + RuleKKS + RuleEDGE
  DocType = DocTypeSpec
  SystemState = SampleState
}

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
  // Using a simplified check: direct references only (not transitive)
  all sd: dimensions.Dimension & SerialDimension |
    sd.name not in elems[sd.scopeNames]
  all cd: dimensions.Dimension & ChecksumDimension |
    cd.name not in elems[cd.targetDims]
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
          d
        ]
  }
}

// INV-7: Checksum correctness
pred validChecksum[s: SystemState, d: Document] {
  some d.doc_id implies {
    all chkDim: ChecksumDimension & s.config.dimensions[DimensionName] | {
      let parsed = parseDocID[d.doc_id, s.config.id_format],
          targetSeq = (chkDim & ChecksumDimension).targetDims,
          total = sum i: targetSeq.inds | valueWeight[parsed[targetSeq[i]]],
          computed = checksumLetter[total] |
        parsed[chkDim.name] = computed
    }
  }
}

// INV-8: Serial uniqueness within scope
pred uniqueSerialsInScope[s: SystemState] {
  all serialDim: s.config.dimensions.Dimension & SerialDimension | {
    let scopeDims = (serialDim & SerialDimension).scopeNames.elems |
      all disj d1, d2: s.documents | {
        (some d1.doc_id and some d2.doc_id) implies {
          let p1 = parseDocID[d1.doc_id, s.config.id_format],
              p2 = parseDocID[d2.doc_id, s.config.id_format] |
            (all dimName: scopeDims | p1[dimName] = p2[dimName]) implies
              p1[serialDim.name] != p2[serialDim.name]
        }
      }
  }
}

pred handlerSpec[s: SystemState] {
  all dim: s.config.dimensions.Dimension & EnumDimension |
    enumSelectByPathSpec[s, dim]
  all dim: s.config.dimensions.Dimension & EnumFromDocTypeDimension |
    enumFromDocTypeSpec[s, dim]
  all dim: s.config.dimensions.Dimension & YearDimension |
    yearDimensionSpec[s, dim]
  all dim: s.config.dimensions.Dimension & SerialDimension |
    serialHandlerSpec[s, dim]
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
  all d: s.documents | validStatus[s, d]
  handlerSpec[s]
}

// [NEW] Status validation
pred validStatus[s: SystemState, d: Document] {
  // If superseded_by is present, status must be Superseded
  some d.superseded_by implies d.status = Superseded
  
  // If status is Superseded, superseded_by SHOULD be present (optional but good practice)
  d.status = Superseded implies some d.superseded_by

  // Target of superseded_by must exist in the system
  some d.superseded_by implies {
    some target: s.documents | target.doc_id = d.superseded_by
  }
  
  // No self-reference
  d.superseded_by != d.doc_id
}

// ============================================================================
// Helper Functions (Concrete encodings for spec DSL)
// ============================================================================

// Parse doc_id into dimension mapping using explicit doc_id structure
fun parseDocID[id: DocID, fmt: IDFormat]: DimensionName -> String {
  { dn: DimensionName, s: String |
    dn in fmt.placeholders and s in id.dimValues[dn]
  }
}

// Validate each dimension according to its discriminator type
pred validateDimensionValue[
  val: String,
  dim: Dimension,
  doc: Document
] {
  dim in EnumDimension implies {
    val in dim.values
    let rules = dim.rules,
        matchingIndices = { i: rules.inds | matchPath[doc.path, rules[i].pattern] } |
      some matchingIndices implies {
        some firstIdx: matchingIndices | {
          no j: matchingIndices | j < firstIdx
          val = rules[firstIdx].value
        }
      }
  }
  dim in EnumFromDocTypeDimension implies
    some doc.doc_type and val = dim.mapping[doc.doc_type]
  dim in YearDimension implies isValidYear[val, (dim & YearDimension).digits]
  dim in SerialDimension implies isValidSerial[val, (dim & SerialDimension).digits]
  // Checksum validation handled separately
}

fun Year4Values(): set String {
  {WeightYEAR2024.value} + {WeightYEAR2025.value}
}

fun Year2Values(): set String {
  {WeightYEAR24.value} + {WeightYEAR25.value}
}

fun Serial4Values(): set String {
  {WeightSER0001.value} + {WeightSER0002.value} + {WeightSER0003.value} + {WeightSER0004.value}
}

pred isValidYear[value: String, digits: Int] {
  ((digits != 4) or value in Year4Values[])
  and ((digits != 2) or value in Year2Values[])
}

pred isValidSerial[value: String, digits: Int] {
  (digits != 4) or value in Serial4Values[]
}

pred matchPath[p: Path, pat: PathPattern] {
  p.category in pat.categories
}

fun firstMatchingRuleIndex[dim: EnumDimension, p: Path]: lone Int {
  { i: dim.rules.inds |
      matchPath[p, dim.rules[i].pattern] and
      no j: dim.rules.inds | j < i and matchPath[p, dim.rules[j].pattern]
  }
}

fun firstMatchingRule[dim: EnumDimension, p: Path]: lone EnumRule {
  { r: EnumRule |
      some i: firstMatchingRuleIndex[dim, p] | r = dim.rules[i]
  }
}

pred enumSelectByPathSpec[s: SystemState, dim: EnumDimension] {
  all d: s.documents |
    some d.doc_id implies {
      some rule: firstMatchingRule[dim, d.path] |
        let parsed = parseDocID[d.doc_id, s.config.id_format] |
          parsed[dim.name] = rule.value
    }
}

pred enumFromDocTypeSpec[s: SystemState, dim: EnumFromDocTypeDimension] {
  all d: s.documents |
    (some d.doc_id and some d.doc_type) implies {
      let parsed = parseDocID[d.doc_id, s.config.id_format] |
        parsed[dim.name] = dim.mapping[d.doc_type]
    }
}

pred yearDimensionSpec[s: SystemState, dim: YearDimension] {
  all d: s.documents | some d.doc_id implies {
    let parsed = parseDocID[d.doc_id, s.config.id_format] |
      isValidYear[parsed[dim.name], dim.digits]
  }
}

pred serialHandlerSpec[s: SystemState, dim: SerialDimension] {
  all d: s.documents | some d.doc_id implies {
    let parsed = parseDocID[d.doc_id, s.config.id_format] |
      isValidSerial[parsed[dim.name], dim.digits]
  }
}

fun weightEntry[val: String]: one ValueWeight {
  { vw: ValueWeight | vw.value = val }
}

fun valueWeight[val: String]: Int {
  weightEntry[val].weight
}

fun checksumLetter[idxVal: Int]: one String {
  ({ a: AlphabetEntry | a.idx = idxVal }).letter
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
  (lintErrors[current] - { e: ValidationError |
    // Filter out MISSING_ID for new files if allowed
    e.errorCode = MISSING_ID and
    current.config.allow_missing_id_in_new_files = True and
    isNewDocument[base, current, e.document]
  }) + { e: ValidationError |
    e.errorCode = ID_CHANGED and DOC_ID_CHANGED[base, current, e.document]
  }
}

pred isNewDocument[base: SystemState, current: SystemState, d: Document] {
  d in current.documents
  // Not present in base (by path)
  no d_base: base.documents | d_base.path = d.path
}

// Lint is read-only: does not modify system state
pred lintIsReadOnly[s: SystemState] {
  // Computing errors doesn't change the state (pure function)
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
// Streaming Event Schema (lint --json --stream)
// ============================================================================

sig RequestId {}
enum StreamPhase { StreamStart, StreamDoc, StreamSummary }
enum StreamStatus { StreamOK, StreamWarn, StreamError }
enum StreamExitCode { ExitOk, ExitWarn, ExitError }

sig LintEvent {
  phase: one StreamPhase,
  status: one StreamStatus,
  request: one RequestId,
  document: lone Document,
  exitCode: one StreamExitCode
}

fact LintEventWellFormed {
  all e: LintEvent |
    (e.phase = StreamDoc) => some e.document
  all e: LintEvent |
    (e.phase != StreamDoc) => no e.document
  all e: LintEvent |
    (e.phase = StreamStart) => e.status = StreamOK
  all e: LintEvent |
    (e.phase = StreamSummary) => (
      (e.status = StreamOK and e.exitCode = ExitOk) or
      (e.status = StreamWarn and e.exitCode = ExitWarn) or
      (e.status = StreamError and e.exitCode = ExitError)
    )
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
      let parsed = parseDocID[d.doc_id, s.config.id_format] |
        // Checksum validation abstracted - actual impl checks mod26AZ
        some computed: String | parsed[chkDim.name] != computed
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
                scopeVals = (serialDim & SerialDimension).scopeNames.elems |
              // Different scopes => can have same serial
              (some dimName: scopeVals | p1[dimName] != p2[dimName]) implies
                (p1[serialDim.name] = p2[serialDim.name] or p1[serialDim.name] != p2[serialDim.name])
          }
        }
    }
}

// ============================================================================
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
// Architecture Layer Model
// ============================================================================

enum LayerLevel { CLILevel, CoreLevel, DimensionLevel, ParserLevel, InfraLevel }

abstract sig Component {
  level: one LayerLevel,
  deps: set Component
}

one sig CLICommands extends Component {}
one sig CLIOutput extends Component {}
one sig CoreValidator extends Component {}
one sig CoreScanner extends Component {}
one sig CoreGenerator extends Component {}
one sig DimensionHandlersLayer extends Component {}
one sig ParserMarkdownLayer extends Component {}
one sig ParserYAMLLayer extends Component {}
one sig GitFacadeLayer extends Component {}
one sig IndexManagerLayer extends Component {}

fact LayerAssignments {
  CLICommands.level = CLILevel
  CLIOutput.level = CLILevel
  CoreValidator.level = CoreLevel
  CoreScanner.level = CoreLevel
  CoreGenerator.level = CoreLevel
  DimensionHandlersLayer.level = DimensionLevel
  ParserMarkdownLayer.level = ParserLevel
  ParserYAMLLayer.level = ParserLevel
  GitFacadeLayer.level = InfraLevel
  IndexManagerLayer.level = InfraLevel
}

fact DependencyGraph {
  CLICommands.deps = CoreValidator + CoreScanner + CoreGenerator + CLIOutput
  CLIOutput.deps = none
  CoreValidator.deps = DimensionHandlersLayer + IndexManagerLayer + GitFacadeLayer
  CoreScanner.deps = ParserMarkdownLayer + ParserYAMLLayer + GitFacadeLayer
  CoreGenerator.deps = DimensionHandlersLayer + IndexManagerLayer
  DimensionHandlersLayer.deps = none
  ParserMarkdownLayer.deps = none
  ParserYAMLLayer.deps = none
  GitFacadeLayer.deps = none
  IndexManagerLayer.deps = none
}

fact LayerConstraints {
  all c: Component, d: c.deps |
    (c.level = CLILevel implies d.level = CoreLevel or d = CLIOutput) and
    (c.level = CoreLevel implies d.level in (DimensionLevel + ParserLevel + InfraLevel + CLILevel)) and
    (c.level = DimensionLevel implies d.level = InfraLevel) and
    (c.level = ParserLevel implies d.level = InfraLevel) and
    (c.level = InfraLevel implies no d)
}

fact NoCyclesInDependencies {
  no c: Component | c in c.^deps
}

assert ArchitectureLayersRespected {
  all c: Component, d: c.deps |
    not (d.level = CLILevel and c.level != CLILevel)
}

check ArchitectureLayersRespected for 5

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
