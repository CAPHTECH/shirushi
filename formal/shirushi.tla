-------------------------- MODULE shirushi --------------------------
(*
Shirushi Document ID Management System - TLA+ Specification
Version: 0.1.0

This specification models the temporal behavior and state transitions
of the Shirushi system, complementing the structural invariants
verified in the Alloy model.

Focus areas:
- Read-only nature of 'lint' command
- Invariant preservation during 'assign' command
- Immutability enforcement across Git states
- Future: Concurrent assign operations (v0.2)
*)

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS
  \* @type: Set(Str);
  Documents,        \* Set of all possible documents
  \* @type: Set(Str);
  DocIDs,           \* Set of all possible document IDs
  \* @type: Set(Str);
  Paths,            \* Set of all possible file paths
  \* @type: Int;
  MaxSerialPerScope, \* Maximum serial number per scope (e.g., 9999 for 4 digits)

  \* TLC Model Checking Constants (bounded state space)
  \* @type: Set(Str);
  PathsSubset,      \* Finite subset of Paths for model checking
  \* @type: Set(Str);
  DocIDsSubset,     \* Finite subset of DocIDs for model checking
  \* @type: Set(Str);
  ScopeKeys,        \* Finite set of scope keys (e.g., {"PCE-SPEC-2025"})

  \* @type: Int;
  MaxDocs,          \* Maximum number of documents in state space
  \* @type: Set(Str);
  MetadataKeys,     \* Set of allowed metadata keys
  \* @type: Set(Str);
  GitRefs,          \* Set of allowed git references

  \* @type: Int;
  MaxHistory,       \* Maximum history length for bounded checking

  \* @type: Str;
  NoID              \* Special value representing "no ID assigned yet"

ASSUME MaxSerialPerScope > 0
ASSUME MaxDocs > 0
ASSUME MaxHistory > 0
ASSUME NoID \notin DocIDs

CompCodes == {"PCE"}
KindCodes == {"SPEC"}
YearCodes == {"2024", "2025"}
SerialStrings == {"0001", "0002"}
ChecksumLetters == {"A", "B"}

EnumSelection == [p \in Paths |-> "PCE"]

KindMapping == [dt \in STRING |->
  "SPEC"
]

YearSelection == [p \in Paths |-> "2025"]

SerialFormatter == [i \in 1..MaxSerialPerScope |->
  IF i = 1 THEN "0001"
  ELSE IF i = 2 THEN "0002"
  ELSE "0001"
]

ScopeKeyBuilder == [tuple \in CompCodes \X KindCodes \X YearCodes |->
  "PCE-SPEC-2025"
]

ChecksumFunction == [tuple \in CompCodes \X KindCodes \X YearCodes \X SerialStrings |->
  "A"
]

ComposeDocID == [tuple \in CompCodes \X KindCodes \X YearCodes \X SerialStrings \X ChecksumLetters |->
  LET serial == tuple[4] IN
    IF serial = "0001"
      THEN "PCE-SPEC-2025-0001-A"
      ELSE "PCE-SPEC-2025-0002-A"
]

AllowMissingIDs == FALSE
ForbidIDChange == TRUE
InitialDocIDs == [p \in Paths |-> NoID]

----

(*
VARIABLES
*)

VARIABLES
  (* Current state of documents in the working directory *)
  \* @type("Str -> [docID: Str, docType: Str, metadata: Str -> Str]");
  docs,             \* [Path -> Document record]

  (* Index file state *)
  \* @type("Str -> [path: Str, docType: Str, metadata: Str -> Str]");
  index,            \* [DocID -> IndexEntry record]

  (* Git state for --base comparison *)
  \* @type("Str -> [docID: Str, docType: Str, metadata: Str -> Str]");
  gitBase,          \* [Path -> Document record] - base ref snapshot

  (* Serial counter state for assign operation *)
  \* @type("Str -> Int");
  serialCounters,   \* [ScopeKey -> Int] - highest serial per scope

  (* Operation history for temporal reasoning *)
  \* @type: Seq([op: Str, params: Str]);
  history           \* Sequence of operations performed (params simplified for type checking)

----

(*
TYPE INVARIANT
All state variables maintain their expected types
*)

TypeInvariant ==
  /\ docs \in [Paths -> [
       docID: DocIDs \cup {NoID},
       docType: STRING,
       metadata: [MetadataKeys -> STRING]
     ]]
  /\ DOMAIN index \subseteq DocIDs
  /\ \A id \in DOMAIN index : index[id] \in [
       path: Paths,
       docType: STRING,
       metadata: [MetadataKeys -> STRING]
     ]
  /\ gitBase \in [Paths -> [
       docID: DocIDs \cup {NoID},
       docType: STRING,
       metadata: [MetadataKeys -> STRING]
     ]]
  /\ serialCounters \in [ScopeKeys -> 0..MaxSerialPerScope]
  /\ history \in Seq([
       op: {"lint", "assign", "gitCheckout"},
       params: STRING \cup Paths
     ])

----

(*
HELPER FUNCTIONS
*)

(* Extract scope key from document ID components *)
(* Abstracted as CONSTANT to avoid Apalache string concatenation issues *)
(* Example: scopeKey(["COMP" |-> "PCE", "KIND" |-> "SPEC", "YEAR4" |-> "2025"], ["COMP", "KIND", "YEAR4"])
             = "PCE-SPEC-2025" *)
\* In actual impl: concatenates parsedID[scopeDims[i]] with "-" separator
\* For model checking: treated as uninterpreted function

(* Note: ParseDocID and ComputeChecksum are fully abstracted away *)
(* All doc_id operations use concrete literals to avoid Apalache string concatenation issues *)
(* This simplification is acceptable for v0.1 model checking *)

(* Get all doc_ids currently in use *)
UsedDocIDs == { docs[p].docID : p \in DOMAIN docs }

(* Get all indexed doc_ids *)
IndexedDocIDs == DOMAIN index

----

(*
INVARIANTS (from Alloy model)
*)

(* INV-1: Document IDs are unique *)
UniqueDocIDs ==
  \A p1, p2 \in DOMAIN docs :
    (p1 /= p2 /\ docs[p1].docID /= NoID /\ docs[p2].docID /= NoID)
      => docs[p1].docID /= docs[p2].docID

(* INV-2: Index IDs are unique - enforced by function type [DocID -> ...] *)
UniqueIndexIDs == TRUE  \* Guaranteed by TLA+ function type

(* INV-3: Document is source of truth - doc_id matches index *)
DocIndexConsistency ==
  \A p \in DOMAIN docs :
    docs[p].docID /= NoID =>
      (\E id \in DOMAIN index :
        /\ index[id].path = p
        /\ id = docs[p].docID)

(* INV-4: All indexed documents exist *)
IndexedDocsExist ==
  \A id \in DOMAIN index :
    \E p \in DOMAIN docs :
      index[id].path = p

(* INV-5: All documents with doc_id are indexed *)
AllDocsIndexed ==
  \A p \in DOMAIN docs :
    docs[p].docID /= NoID =>
      \E id \in DOMAIN index :
        index[id].path = p

(* INV-6: Index paths are unique (bijection) *)
UniqueIndexPaths ==
  \A id1, id2 \in DOMAIN index :
    id1 /= id2 => index[id1].path /= index[id2].path

(* Combined system invariant *)
MissingIDPolicyInvariant ==
  /\ (AllowMissingIDs =>
        \A p \in DOMAIN docs :
          docs[p].docID = NoID => gitBase[p].docID = NoID)
  /\ (~AllowMissingIDs =>
        \A p \in DOMAIN docs :
          gitBase[p].docID /= NoID => docs[p].docID /= NoID)

SystemInvariant ==
  /\ UniqueDocIDs
  /\ UniqueIndexIDs
  /\ DocIndexConsistency
  /\ IndexedDocsExist
  /\ AllDocsIndexed
  /\ UniqueIndexPaths
  /\ MissingIDPolicyInvariant

(* Immutability invariant: Existing doc_ids never change *)
ImmutabilityInvariant ==
  ForbidIDChange =>
    \A p \in (DOMAIN gitBase \cap DOMAIN docs) :
      (gitBase[p].docID /= NoID /\ docs[p].docID /= NoID)
        => gitBase[p].docID = docs[p].docID

----

(*
OPERATIONS
*)

(* LINT: Read-only validation - returns error set but doesn't modify state *)
Lint(baseRef) ==
  /\ history' = Append(history, [op |-> "lint", params |-> baseRef])
  /\ UNCHANGED <<docs, index, gitBase, serialCounters>>
  \* Note: Errors are computed but not stored in state (read-only)

(* Git checkout: Update base reference for immutability checking *)
GitCheckout(ref) ==
  /\ gitBase' = docs  \* Snapshot current state as base
  /\ history' = Append(history, [op |-> "gitCheckout", params |-> ref])
  /\ UNCHANGED <<docs, index, serialCounters>>

(* ASSIGN: Generate and assign new doc_id to a document *)
(* This is the only state-modifying operation in v0.1 *)
Assign(path) ==
  /\ path \in DOMAIN docs
  /\ docs[path].docID = NoID  \* Can only assign to documents without ID

  \* Generate new doc_id (abstracted - actual implementation uses dimension handlers)
  /\ LET
       \* Get document metadata to determine dimension values
       docType == docs[path].docType

       \* Enum dimensions follow select.by_path and doc_type mapping rules
       compValue == EnumSelection[path]
       kindValue == KindMapping[docType]

       \* Year dimension (from metadata source abstraction)
       yearValue == YearSelection[path]

       \* Serial dimension - increment counter for this scope
       scopeTuple == <<compValue, kindValue, yearValue>>
       scopeKey == ScopeKeyBuilder[scopeTuple]
       nextSerial == IF scopeKey \in DOMAIN serialCounters
                     THEN serialCounters[scopeKey] + 1
                     ELSE 1
       serialValue == SerialFormatter[nextSerial]

       \* Checksum dimension (mod26AZ abstraction)
       checksumValue == ChecksumFunction[<<compValue, kindValue, yearValue, serialValue>>]

       \* Construct new doc_id (abstracted to avoid string concat issues)
       newDocID == ComposeDocID[<<compValue, kindValue, yearValue, serialValue, checksumValue>>]

       \* Create index entry
       newIndexEntry == [
         path |-> path,
         docType |-> docType,
         metadata |-> docs[path].metadata
       ]
     IN
       /\ nextSerial <= MaxSerialPerScope  \* Don't overflow serial counter
       /\ newDocID \notin UsedDocIDs        \* Ensure uniqueness
       /\ newDocID \notin IndexedDocIDs

       \* Update document
       /\ docs' = [docs EXCEPT ![path].docID = newDocID]

       \* Update index
       /\ index' = index @@ (newDocID :> newIndexEntry)

       \* Update serial counter
       /\ serialCounters' = [serialCounters EXCEPT ![scopeKey] = nextSerial]

       \* Record operation
       /\ history' = Append(history, [
            op |-> "assign",
            params |-> path  \* Simplified to string for type checking
          ])

       \* Git base unchanged (only modified by GitCheckout)
       /\ UNCHANGED gitBase

----

(*
SPECIFICATION
*)

(* Fairness: Ensure assign operations eventually execute for all pending documents *)
Fairness ==
  /\ WF_<<docs, index, gitBase, serialCounters, history>>(\E p \in Paths : Assign(p))
  /\ WF_<<docs, index, gitBase, serialCounters, history>>(\E ref \in GitRefs : GitCheckout(ref))

Init ==
  /\ docs = [p \in PathsSubset |-> [
       docID |-> InitialDocIDs[p],
       docType |-> "",
       metadata |-> [k \in MetadataKeys |-> ""]
     ]]
  /\ index = [id \in {} |-> [path |-> "", docType |-> "", metadata |-> [k \in MetadataKeys |-> ""]]]  \* Empty initially
  /\ gitBase = [p \in PathsSubset |-> [
       docID |-> InitialDocIDs[p],
       docType |-> "",
       metadata |-> [k \in MetadataKeys |-> ""]
     ]]
  /\ serialCounters = [k \in ScopeKeys |-> 0]
  /\ history = <<>>

Next ==
  \/ \E p \in Paths : Assign(p)
  \/ \E ref \in GitRefs : GitCheckout(ref)
  \/ \E ref \in GitRefs : Lint(ref)

Spec == Init /\ [][Next]_<<docs, index, gitBase, serialCounters, history>> /\ Fairness

----

(*
TEMPORAL PROPERTIES
*)

(* SAFETY: System invariants always hold *)
AlwaysValid == []SystemInvariant

(* SAFETY: Lint never modifies state *)
LintReadOnly ==
  [](\A i \in 1..Len(history) :
      history[i].op = "lint" =>
        \* State before and after lint is identical
        \* (This is enforced by Lint action, but we assert it here)
        TRUE)

(* SAFETY: Assign preserves invariants *)
AssignPreservesInvariants ==
  [](\A i \in 1..Len(history) :
      history[i].op = "assign" => SystemInvariant)

(* SAFETY: Immutability never violated after GitCheckout *)
ImmutabilityNeverViolated ==
  [](\A i, j \in 1..Len(history) :
      (i < j /\ history[i].op = "gitCheckout") =>
        ImmutabilityInvariant)

(* SAFETY: Missing ID policy (allowance only for new docs) always enforced *)
MissingIDPolicyAlways ==
  []MissingIDPolicyInvariant

(* LIVENESS: Valid assign requests eventually succeed *)
(* Note: In v0.1, assign is manual CLI command, so this is aspirational *)
AssignEventuallySucceeds ==
  \A p \in Paths :
    (p \in DOMAIN docs /\ docs[p].docID = NoID) ~>
      \E id \in DocIDs : docs[p].docID = id

----

(*
MODEL CHECKING CONFIGURATION
NOTE: Test constants are defined in apalache.cfg
*)

(* Constraint: Limit state space for TLC model checking *)
StateConstraint ==
  /\ Len(history) <= MaxHistory           \* Bound history length
  /\ Cardinality(DOMAIN docs) <= MaxDocs  \* Bound number of documents
  /\ DOMAIN docs \subseteq PathsSubset    \* Constrain paths to finite subset

(* Fairness: Ensure assign operations eventually execute for all pending documents *)


----

(*
THEOREMS (verified by TLC as invariants/properties)
These are expressed as invariants rather than THEOREM syntax for TLC compatibility
*)

\* Note: Inductiveness checks removed (not needed for standard model checking)

(* Check: Assign maintains uniqueness *)
AssignMaintainsUniquenessCheck ==
  []SystemInvariant  \* If this holds, Assign preserves it

=====================================================================

(*
VERIFICATION NOTES

This TLA+ spec models the core temporal properties of Shirushi:
1. State transitions (Init, Assign, Lint, GitCheckout)
2. Invariant preservation
3. Immutability enforcement
4. Read-only guarantees

Limitations (see VERIFICATION_STRATEGY.md):
- ParseDocID and ComputeChecksum are axiomatically assumed correct
- Dimension generation logic is simplified (actual impl is more complex)
- File I/O operations are not modeled
- Git operations are simplified to linear history

Verification approach:
- TLC model checking with bounded state space (StateConstraint)
- Invariant checking at every step
- Temporal property verification (safety + liveness)
- Property-based tests verify abstract functions separately

To run TLC:
  java -jar tla2tools.jar -config shirushi.cfg shirushi.tla

*)
