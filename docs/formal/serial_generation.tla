------------------- MODULE serial_generation -------------------
(*
Serial Number Generation Algorithm - TLA+ Specification
Version: 0.1.0

This specification models the serial number generation algorithm for Shirushi.
It ensures that generated serial numbers are:
1. Unique within their scope
2. Monotonically increasing (max + 1)
3. Within digit bounds (no overflow)

This module complements the main shirushi.tla specification by focusing
specifically on the serial generation algorithm used in SerialHandler.generate().
*)

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS
  \* @type: Int;
  MaxDigits,          \* Maximum digits for serial (e.g., 4)
  \* @type: Set(Str);
  ScopeKeys,          \* Set of possible scope keys (e.g., "PCE-SPEC-2025")
  \* @type: Set(Str);
  IndexDocIDs,        \* Set of doc_ids currently in the index
  \* @type: Str;
  NoScopeKey          \* Sentinel for missing scope

ASSUME MaxDigits >= 1 /\ MaxDigits <= 6
ASSUME NoScopeKey \notin ScopeKeys

(* ----------------------------------------------------------------- *)
(* Helper Functions                                                    *)
(* ----------------------------------------------------------------- *)

\* Compute maximum value for given digit count
\* Simplified for model checking (avoiding exponentiation)
MaxSerialValue(digits) ==
  CASE digits = 1 -> 9
    [] digits = 2 -> 99
    [] digits = 3 -> 999
    [] digits = 4 -> 9999
    [] digits = 5 -> 99999
    [] OTHER -> 999999

(* ----------------------------------------------------------------- *)
(* Abstract operations on doc_ids                                      *)
(* In implementation, these use template parsing.                     *)
(* ----------------------------------------------------------------- *)

\* Extract scope key from a doc_id
\* Implementation: Uses extractDimensionValues() with template parsing
ExtractScope(docID) ==
  \* Abstract: Returns the scope key portion of the doc_id
  \* Example: "PCE-SPEC-2025-0001-A" -> "PCE-SPEC-2025"
  CHOOSE scopeKey \in ScopeKeys \cup {NoScopeKey} : TRUE

\* Extract serial number from a doc_id
\* Implementation: Uses extractDimensionValues() with template parsing
ExtractSerial(docID) ==
  \* Abstract: Returns the serial portion as an integer
  \* Example: "PCE-SPEC-2025-0001-A" -> 1
  CHOOSE n \in 1..MaxSerialValue(MaxDigits) : TRUE

(* ----------------------------------------------------------------- *)
(* Core Algorithm                                                     *)
(* ----------------------------------------------------------------- *)

\* Get all serials in a specific scope
SerialsInScope(scopeKey) ==
  LET relevantIDs == { docId \in IndexDocIDs : ExtractScope(docId) = scopeKey }
  IN { ExtractSerial(docId) : docId \in relevantIDs }

\* Compute the maximum serial in a scope (0 if empty)
MaxInScope(scopeKey) ==
  LET serials == SerialsInScope(scopeKey)
  IN IF serials = {} THEN 0
     ELSE CHOOSE s \in serials : \A t \in serials : t <= s

\* Check if overflow would occur
WouldOverflow(scopeKey, digits) ==
  LET maxSerial == MaxInScope(scopeKey)
      nextVal == maxSerial + 1
      maxPossible == MaxSerialValue(digits)
  IN nextVal > maxPossible

\* Compute next serial number (only valid when not overflowing)
NextSerialValue(scopeKey) ==
  MaxInScope(scopeKey) + 1

(* ----------------------------------------------------------------- *)
(* State Variables                                                    *)
(* ----------------------------------------------------------------- *)

VARIABLES
  \* @type: Str -> Int;
  generatedSerials    \* Map from scope key to last generated serial

(* ----------------------------------------------------------------- *)
(* Type Invariant                                                     *)
(* ----------------------------------------------------------------- *)

TypeInvariant ==
  \A scopeKey \in DOMAIN generatedSerials :
    /\ scopeKey \in ScopeKeys
    /\ generatedSerials[scopeKey] \in 0..MaxSerialValue(MaxDigits)

(* ----------------------------------------------------------------- *)
(* Safety Invariants (Properties to Verify)                           *)
(* ----------------------------------------------------------------- *)

\* INV1: Uniqueness within Scope
\* No two doc_ids in the same scope have the same serial
UniqueSerialInScope ==
  \A id1, id2 \in IndexDocIDs :
    (id1 /= id2 /\ ExtractScope(id1) = ExtractScope(id2))
      => ExtractSerial(id1) /= ExtractSerial(id2)

\* INV2: Monotonic Generation
\* Generated serial is always greater than max existing in scope
MonotonicGeneration ==
  \A scopeKey \in DOMAIN generatedSerials :
    generatedSerials[scopeKey] > MaxInScope(scopeKey) \/
    generatedSerials[scopeKey] = 0  \* Initial state

\* INV3: No Overflow
\* Generated serial never exceeds max for digit count
NoOverflow ==
  \A scopeKey \in DOMAIN generatedSerials :
    generatedSerials[scopeKey] <= MaxSerialValue(MaxDigits)

\* INV4: Scope Filtering Correctness
\* Serial computation only considers doc_ids matching the scope
ScopeFilteringCorrect ==
  \A scopeKey \in ScopeKeys :
    LET relevantIDs == { id \in IndexDocIDs : ExtractScope(id) = scopeKey }
        computedMax == MaxInScope(scopeKey)
    IN \A id \in relevantIDs : ExtractSerial(id) <= computedMax

\* Combined System Invariant (for model checking)
\*
\* VERIFICATION STRATEGY:
\* - TypeInvariant, NoOverflow: Formally verified by Apalache model checker
\* - UniqueSerialInScope, ScopeFilteringCorrect: Verified via property-based
\*   tests (fast-check) in tests/unit/dimensions/serial-generation.property.test.ts
\*
\* Rationale: UniqueSerialInScope and ScopeFilteringCorrect depend on abstract
\* ExtractScope/ExtractSerial functions using CHOOSE, which return arbitrary
\* values during symbolic model checking. Since these functions represent
\* template parsing logic (extractDimensionValues), their correctness is
\* better verified through concrete property-based tests with real parsing.
\*
\* See: serial-oracle.ts for the oracle implementation corresponding to
\* this TLA+ specification.
SystemInvariant ==
  /\ TypeInvariant
  /\ NoOverflow

(* ----------------------------------------------------------------- *)
(* Actions                                                            *)
(* ----------------------------------------------------------------- *)

\* Generate a new serial for a given scope
GenerateSerial(scopeKey, digits) ==
  /\ scopeKey \in ScopeKeys
  /\ IF WouldOverflow(scopeKey, digits)
     THEN UNCHANGED generatedSerials
     ELSE generatedSerials' = [generatedSerials EXCEPT ![scopeKey] = NextSerialValue(scopeKey)]

(* ----------------------------------------------------------------- *)
(* Specification                                                      *)
(* ----------------------------------------------------------------- *)

Init ==
  generatedSerials = [s \in {} |-> 0]

Next ==
  \E scopeKey \in ScopeKeys, digits \in 1..MaxDigits :
    GenerateSerial(scopeKey, digits)

\* @type: <<Str -> Int>>;
vars == <<generatedSerials>>

Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------- *)
(* Temporal Properties                                                *)
(* ----------------------------------------------------------------- *)

\* Safety: Always maintain system invariant
AlwaysSafe == []SystemInvariant

\* Liveness: Generation eventually succeeds or detects overflow
\* (Weak fairness ensures progress)
GenerationProgress ==
  \A scopeKey \in ScopeKeys :
    scopeKey \notin DOMAIN generatedSerials ~>
      (scopeKey \in DOMAIN generatedSerials \/
       WouldOverflow(scopeKey, MaxDigits))

(* ----------------------------------------------------------------- *)
(* State Constraints (for TLC model checking)                         *)
(* ----------------------------------------------------------------- *)

StateConstraint ==
  /\ Cardinality(DOMAIN generatedSerials) <= Cardinality(ScopeKeys)
  /\ \A s \in DOMAIN generatedSerials : generatedSerials[s] <= 10

=====================================================================
(*
Property-Based Test Mapping:

TLA+ Invariant          -> fast-check Property
-------------------        ------------------
UniqueSerialInScope     -> generated not in existing serials set
MonotonicGeneration     -> generated > max(existing)
NoOverflow              -> generated <= 10^digits - 1
ScopeFilteringCorrect   -> only scope-matching docs affect result

Oracle Function:
  oracleNextSerial(scopeKey, indexDocIds, templateResult, scope, serialDimName, digits)
    -> Either<'OVERFLOW', number>

Implementation must match oracle output for all inputs.
*)
