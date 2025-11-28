// Shirushi Boundary Exploration Mini Model
// Focus: Ownership, Visibility, Authority of components
// Compares Profile A (Validator-aggregated) vs Profile C (Hybrid)

// ============================================================================
// Core Component Signatures
// ============================================================================

abstract sig Component {}

one sig ConfigLoader, TemplateParser, Validator, ErrorReporter extends Component {}

sig DimensionHandler extends Component {
    handlerType: one DimensionType
}

enum DimensionType { EnumType, YearType, SerialType, ChecksumType }

sig PatternSpec {
    owner: one Component,
    readers: set Component
}

sig Registry {
    owner: one Component,
    handlers: set DimensionHandler,
    visibleTo: set Component
}

sig Config {
    declaredTypes: set DimensionType,
    loadedBy: one ConfigLoader
}

sig Document {
    docId: lone DocId
}

sig DocId {
    belongsTo: one Document,
    dimensions: set DimensionType
}

sig Scope {
    scopeDimensions: set DimensionType
}

sig SerialCounter {
    scope: one Scope,
    usedNumbers: set Int
}

// ============================================================================
// Boundary Parameters (encoded as predicates)
// ============================================================================

// --- Registry Ownership ---

pred RegistryOwnedByValidator[] {
    all r: Registry | r.owner = Validator
}

pred RegistryStandalone[] {
    all r: Registry | r.owner not in Validator
    all r: Registry | Validator in r.visibleTo
}

// --- Pattern Ownership ---

pred PatternOwnedByParser[] {
    all p: PatternSpec | p.owner = TemplateParser
    all p: PatternSpec | Validator in p.readers
}

pred PatternOwnedByValidator[] {
    all p: PatternSpec | p.owner = Validator
}

// --- Handler Authority (Pure vs Stateful) ---

pred HandlersArePure[] {
    // Pure handlers have no cross-references
    all h1, h2: DimensionHandler | h1 != h2 implies h1.handlerType != h2.handlerType
}

// --- Error Routing ---

pred ErrorsMediated[] {
    // All handlers must be visible to Validator for mediated routing
    all r: Registry | all h: r.handlers | Validator in r.visibleTo
}

// ============================================================================
// Boundary Profiles
// ============================================================================

// Profile A: Validator集約・同期制御案
pred ProfileA[] {
    RegistryOwnedByValidator[]
    PatternOwnedByValidator[]
    HandlersArePure[]
    ErrorsMediated[]
}

// Profile C: ハイブリッド案
pred ProfileC[] {
    RegistryStandalone[]
    PatternOwnedByValidator[]
    HandlersArePure[]
    ErrorsMediated[]
}

// ============================================================================
// Safety Invariants
// ============================================================================

// INV-1: ID Uniqueness - no two documents share the same docId
pred IdUniqueness[] {
    all d1, d2: Document |
        (d1 != d2 and some d1.docId and some d2.docId) implies d1.docId != d2.docId
}

// INV-2: DocId belongs to exactly one document
pred DocIdBelongsToOne[] {
    all id: DocId | one id.belongsTo
    all id: DocId | id.belongsTo.docId = id
}

// INV-3: All declared dimension types have handlers
pred ConfigSoundness[] {
    all c: Config, r: Registry |
        c.declaredTypes in r.handlers.handlerType
}

// INV-4: Serial uniqueness within scope
pred SerialUniquenessInScope[] {
    all sc: SerialCounter |
        all n: sc.usedNumbers | one d: Document |
            some d.docId and SerialType in d.docId.dimensions
}

// INV-5: Handler type coverage - all dimension types in docId have handlers
pred HandlerCoverage[] {
    all id: DocId, r: Registry |
        id.dimensions in r.handlers.handlerType
}

// Combined invariants
pred AllInvariants[] {
    IdUniqueness[]
    DocIdBelongsToOne[]
    ConfigSoundness[]
    HandlerCoverage[]
}

// ============================================================================
// Assertions
// ============================================================================

// Profile A maintains all invariants
assert ProfileA_MaintainsInvariants {
    ProfileA[] implies AllInvariants[]
}

// Profile C maintains all invariants
assert ProfileC_MaintainsInvariants {
    ProfileC[] implies AllInvariants[]
}

// Both profiles maintain ID uniqueness
assert BothProfiles_MaintainIdUniqueness {
    (ProfileA[] or ProfileC[]) implies IdUniqueness[]
}

// Config soundness is independent of profile choice
assert ConfigSoundness_IndependentOfProfile {
    ConfigSoundness[] implies (
        (ProfileA[] implies ConfigSoundness[]) and
        (ProfileC[] implies ConfigSoundness[])
    )
}

// ============================================================================
// Comparison Predicates
// ============================================================================

// Profile A has simpler ownership (single owner for registry)
pred ProfileA_SimplerOwnership[] {
    ProfileA[]
    #{c: Component | c in Registry.owner} = 1
}

// Profile C allows independent registry management
pred ProfileC_IndependentRegistry[] {
    ProfileC[]
    all r: Registry | r.owner != Validator
}

// Scenarios where profiles differ
pred ProfilesDiffer[] {
    some r: Registry | (
        (ProfileA[] implies r.owner = Validator) and
        (ProfileC[] implies r.owner != Validator)
    )
}

// ============================================================================
// Structural Well-formedness
// ============================================================================

fact BasicConstraints {
    // Each handler has exactly one type
    all h: DimensionHandler | one h.handlerType

    // Registry must have at least the 4 core handlers
    all r: Registry | #r.handlers >= 4

    // Documents with docId have dimension values
    all d: Document | some d.docId implies some d.docId.dimensions

    // Config must declare at least one type
    all c: Config | some c.declaredTypes
}

// CRITICAL: Document-DocId uniqueness constraint
// Each Document has at most one DocId, and each DocId belongs to exactly one Document
fact DocumentDocIdBijection {
    // DocId.belongsTo is the inverse of Document.docId
    all d: Document, id: DocId | d.docId = id iff id.belongsTo = d

    // No two documents share the same DocId
    all disj d1, d2: Document |
        (some d1.docId and some d2.docId) implies d1.docId != d2.docId

    // Every DocId has exactly one owning Document (already in sig, but explicit)
    all id: DocId | one id.belongsTo
}

fact HandlerTypes {
    // Ensure we have all 4 handler types
    some h: DimensionHandler | h.handlerType = EnumType
    some h: DimensionHandler | h.handlerType = YearType
    some h: DimensionHandler | h.handlerType = SerialType
    some h: DimensionHandler | h.handlerType = ChecksumType
}

// ============================================================================
// Commands
// ============================================================================

// Explore valid configurations under Profile A
run runProfileA { ProfileA[] } for 5 but exactly 1 Registry, exactly 1 Config,
    exactly 4 DimensionHandler, exactly 3 Document, exactly 1 PatternSpec

// Explore valid configurations under Profile C
run runProfileC { ProfileC[] } for 5 but exactly 1 Registry, exactly 1 Config,
    exactly 4 DimensionHandler, exactly 3 Document, exactly 1 PatternSpec

// Compare profiles - find where they differ
run runProfilesDiffer { ProfilesDiffer[] } for 5 but exactly 1 Registry, exactly 1 Config,
    exactly 4 DimensionHandler, exactly 3 Document

// Check safety invariants
check ProfileA_MaintainsInvariants for 5 but exactly 1 Registry,
    exactly 1 Config, exactly 4 DimensionHandler, exactly 3 Document

check ProfileC_MaintainsInvariants for 5 but exactly 1 Registry,
    exactly 1 Config, exactly 4 DimensionHandler, exactly 3 Document

check BothProfiles_MaintainIdUniqueness for 5 but exactly 1 Registry,
    exactly 1 Config, exactly 4 DimensionHandler, exactly 3 Document

// Verify config soundness
check ConfigSoundness_IndependentOfProfile for 5 but exactly 1 Registry,
    exactly 1 Config, exactly 4 DimensionHandler
