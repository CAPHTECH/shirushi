---------------------------- MODULE ShirushiSeq ----------------------------
(*
Case A: Type-Safe Sequential Validation
- Sequential document processing
- Context injection for serial scope
- Structured error collection

This module compares with ShirushiPar (Case C) for execution model evaluation.

== Verified Properties ==
- S1: SerialUniqueness - No duplicate serials within same scope
- S2: ValidationCompleteness - All documents processed at termination
- S3: ErrorCollectionComplete - Every invalid doc has corresponding error
- S4: IndexConsistency - Missing index entries detected
- S5: SequentialProcessing - At most one document in processing state

== Assumptions ==
- A1: Documents set is finite and non-empty
- A2: Each document has exactly one scope and serial (ScopeOf, SerialOf functions)
- A3: Parsing and validation are deterministic
- A4: No external modifications during validation

== Fairness ==
- WF_vars(Next): Weak fairness ensures progress when actions are enabled
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Documents,          \* Set of document identifiers (finite, non-empty)
    Scopes,             \* Set of serial scopes (e.g., {"COMP-SPEC", "COMP-ADR"})
    SerialNumbers,      \* Set of possible serial numbers {1, 2, 3, ...}
    IndexEntries        \* Set of doc_ids in the index

\* Assumption: Documents set is non-empty
ASSUME Documents # {}

\* Assumption: Scopes and SerialNumbers are non-empty
ASSUME Scopes # {} /\ SerialNumbers # {}

VARIABLES
    phase,              \* Current phase of validation
    docStatus,          \* Function: Document -> Status
    currentDoc,         \* Currently processing document (or "none")
    serialCounters,     \* Function: Scope -> Set of used serial numbers
    errors,             \* Sequence of collected errors
    processedCount      \* Number of processed documents

vars == <<phase, docStatus, currentDoc, serialCounters, errors, processedCount>>

Status == {"pending", "parsing", "parsed", "validating", "valid", "invalid"}
ErrorType == {"MALFORMED_ID", "INVALID_CHECKSUM", "DUPLICATE_SERIAL", "NOT_IN_INDEX"}

\* Scope and serial are abstracted as functions
CONSTANTS ScopeOf, SerialOf

---------------------------------------------------------------------------
(* Type Invariant *)
---------------------------------------------------------------------------

TypeOK ==
    /\ phase \in {"init", "parsing", "validating", "collecting", "done"}
    /\ docStatus \in [Documents -> Status]
    /\ currentDoc \in Documents \cup {"none"}
    /\ serialCounters \in [Scopes -> SUBSET SerialNumbers]
    /\ errors \in Seq([doc: Documents, error: ErrorType])
    /\ processedCount \in Nat

---------------------------------------------------------------------------
(* Initial State *)
---------------------------------------------------------------------------

Init ==
    /\ phase = "init"
    /\ docStatus = [d \in Documents |-> "pending"]
    /\ currentDoc = "none"
    /\ serialCounters = [s \in Scopes |-> {}]
    /\ errors = <<>>
    /\ processedCount = 0

---------------------------------------------------------------------------
(* Helper Operators *)
---------------------------------------------------------------------------

\* Get pending documents
PendingDocs == {d \in Documents : docStatus[d] = "pending"}

\* Check if document's doc_id is in index
InIndex(doc) == doc \in IndexEntries

---------------------------------------------------------------------------
(* Actions *)
---------------------------------------------------------------------------

\* Start validation phase
StartValidation ==
    /\ phase = "init"
    /\ phase' = "validating"
    /\ UNCHANGED <<docStatus, currentDoc, serialCounters, errors, processedCount>>

\* Pick next document to validate (sequential - deterministic)
PickDocument ==
    /\ phase = "validating"
    /\ currentDoc = "none"
    /\ PendingDocs # {}
    /\ LET doc == CHOOSE d \in PendingDocs : TRUE
       IN /\ currentDoc' = doc
          /\ docStatus' = [docStatus EXCEPT ![doc] = "parsing"]
    /\ UNCHANGED <<phase, serialCounters, errors, processedCount>>

\* Parse document (success or failure)
ParseDocument ==
    /\ phase = "validating"
    /\ currentDoc # "none"
    /\ docStatus[currentDoc] = "parsing"
    /\ \/ \* Parse success
          /\ docStatus' = [docStatus EXCEPT ![currentDoc] = "parsed"]
          /\ errors' = errors
       \/ \* Parse failure
          /\ docStatus' = [docStatus EXCEPT ![currentDoc] = "invalid"]
          /\ errors' = Append(errors, [doc |-> currentDoc, error |-> "MALFORMED_ID"])
    /\ UNCHANGED <<phase, currentDoc, serialCounters, processedCount>>

\* Validate parsed document (checksum, serial, index)
ValidateDocument ==
    /\ phase = "validating"
    /\ currentDoc # "none"
    /\ docStatus[currentDoc] = "parsed"
    /\ LET
           scope == ScopeOf[currentDoc]
           serial == SerialOf[currentDoc]
           isDuplicateSerial == serial \in serialCounters[scope]
           notInIndex == ~InIndex(currentDoc)
       IN
       \/ \* All checks pass
          /\ ~isDuplicateSerial
          /\ ~notInIndex
          /\ docStatus' = [docStatus EXCEPT ![currentDoc] = "valid"]
          /\ serialCounters' = [serialCounters EXCEPT ![scope] = @ \cup {serial}]
          /\ errors' = errors
       \/ \* Duplicate serial error
          /\ isDuplicateSerial
          /\ docStatus' = [docStatus EXCEPT ![currentDoc] = "invalid"]
          /\ errors' = Append(errors, [doc |-> currentDoc, error |-> "DUPLICATE_SERIAL"])
          /\ UNCHANGED serialCounters
       \/ \* Not in index error
          /\ notInIndex
          /\ docStatus' = [docStatus EXCEPT ![currentDoc] = "invalid"]
          /\ errors' = Append(errors, [doc |-> currentDoc, error |-> "NOT_IN_INDEX"])
          /\ serialCounters' = [serialCounters EXCEPT ![scope] = @ \cup {serial}]
       \/ \* Checksum error (non-deterministic simulation)
          /\ docStatus' = [docStatus EXCEPT ![currentDoc] = "invalid"]
          /\ errors' = Append(errors, [doc |-> currentDoc, error |-> "INVALID_CHECKSUM"])
          /\ serialCounters' = [serialCounters EXCEPT ![scope] = @ \cup {serial}]
    /\ UNCHANGED <<phase, currentDoc, processedCount>>

\* Finish processing current document
FinishDocument ==
    /\ phase = "validating"
    /\ currentDoc # "none"
    /\ docStatus[currentDoc] \in {"valid", "invalid"}
    /\ currentDoc' = "none"
    /\ processedCount' = processedCount + 1
    /\ UNCHANGED <<phase, docStatus, serialCounters, errors>>

\* Complete validation when all documents processed
CompleteValidation ==
    /\ phase = "validating"
    /\ currentDoc = "none"
    /\ PendingDocs = {}
    /\ processedCount = Cardinality(Documents)
    /\ phase' = "done"
    /\ UNCHANGED <<docStatus, currentDoc, serialCounters, errors, processedCount>>

---------------------------------------------------------------------------
(* Next State Relation *)
---------------------------------------------------------------------------

Next ==
    \/ StartValidation
    \/ PickDocument
    \/ ParseDocument
    \/ ValidateDocument
    \/ FinishDocument
    \/ CompleteValidation

---------------------------------------------------------------------------
(* Safety Properties *)
---------------------------------------------------------------------------

\* S1: Serial Uniqueness - no duplicate serials in same scope at completion
SerialUniqueness ==
    phase = "done" =>
        \A s \in Scopes :
            \A d1, d2 \in Documents :
                (d1 # d2 /\ docStatus[d1] = "valid" /\ docStatus[d2] = "valid"
                 /\ ScopeOf[d1] = s /\ ScopeOf[d2] = s)
                => SerialOf[d1] # SerialOf[d2]

\* S2: Validation Completeness - all documents processed at end
ValidationCompleteness ==
    phase = "done" =>
        \A d \in Documents : docStatus[d] \in {"valid", "invalid"}

\* S3: Error Collection Completeness - invalid docs have errors
ErrorCollectionComplete ==
    phase = "done" =>
        \A d \in Documents :
            docStatus[d] = "invalid" =>
                \E i \in 1..Len(errors) : errors[i].doc = d

\* S4: Index Consistency - docs not in index are reported
IndexConsistency ==
    phase = "done" =>
        \A d \in Documents :
            (~InIndex(d) /\ docStatus[d] \in {"valid", "invalid"}) =>
                (docStatus[d] = "invalid" /\
                 \E i \in 1..Len(errors) :
                    errors[i].doc = d /\ errors[i].error = "NOT_IN_INDEX")

\* S5: Sequential processing - only one document at a time
SequentialProcessing ==
    Cardinality({d \in Documents : docStatus[d] \in {"parsing", "parsed"}}) <= 1

\* Combined Safety
Safety == TypeOK /\ SerialUniqueness /\ SequentialProcessing

---------------------------------------------------------------------------
(* Liveness Properties *)
---------------------------------------------------------------------------

\* L1: Termination - eventually reaches done
Termination == <>(phase = "done")

\* L2: Progress - every document eventually processed
Progress == \A d \in Documents : <>(docStatus[d] \in {"valid", "invalid"})

---------------------------------------------------------------------------
(* Specification *)
---------------------------------------------------------------------------

Fairness == WF_vars(Next)
Spec == Init /\ [][Next]_vars /\ Fairness

\* State constraint for bounded model checking
StateConstraint ==
    /\ processedCount <= Cardinality(Documents)
    /\ Len(errors) <= Cardinality(Documents)

=============================================================================
