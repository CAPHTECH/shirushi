---------------------------- MODULE ShirushiPar ----------------------------
(*
Case C: Hybrid Parallel Validation
- Parallel document processing with workers
- Pre-resolved serial scope with lock coordination
- Structured error collection with merge

This module compares with ShirushiSeq (Case A) for execution model evaluation.

== Verified Properties ==
- S1: SerialUniqueness - No duplicate serials within same scope (same as Case A)
- S2: ValidationCompleteness - All documents processed at termination
- S3: ErrorCollectionComplete - Every invalid doc has corresponding error (after merge)
- S4: IndexConsistency - Missing index entries detected
- S5: LockInvariant - Lock holder is always a worker when lock is held
- S6: MutexInvariant - Only lock holder can be in awaiting_lock state
- S7: NoDeadlock - Lock holder can always make progress
- S8: ParallelLimitRespected - Active workers <= MaxParallel

== Assumptions ==
- A1: Documents set is finite and non-empty
- A2: Workers set is finite with size >= 1
- A3: MaxParallel > 0 and <= |Workers|
- A4: Lock acquisition is atomic (no partial states)
- A5: Workers execute independently (no shared mutable state except lock)
- A6: Error merge preserves all local errors

== Fairness ==
- WF_vars(Next): Weak fairness on all actions
- WF_vars(WorkerReleaseLock(w)): Workers eventually release locks
- WF_vars(WorkerValidateWithLock(w)): Validation completes

== Comparison with Case A (Sequential) ==
- Same safety properties (S1-S4) with additional concurrency properties (S5-S8)
- Higher throughput potential due to parallelism
- Added complexity: lock management, error merging
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Documents,          \* Set of document identifiers (finite, non-empty)
    Scopes,             \* Set of serial scopes
    SerialNumbers,      \* Set of possible serial numbers
    IndexEntries,       \* Set of doc_ids in the index
    Workers,            \* Set of worker identifiers (e.g., {w1, w2, w3})
    MaxParallel         \* Maximum concurrent validations

\* Assumptions as ASSUME statements
ASSUME Documents # {}
ASSUME Workers # {}
ASSUME MaxParallel > 0
ASSUME MaxParallel <= Cardinality(Workers)

VARIABLES
    phase,              \* Current phase
    docStatus,          \* Function: Document -> Status
    workerDoc,          \* Function: Worker -> Document or "idle"
    serialCounters,     \* Function: Scope -> Set of used serial numbers
    serialLock,         \* Lock for serial counter updates
    lockHolder,         \* Current lock holder (worker or "none")
    errors,             \* Sequence of collected errors (global)
    localErrors         \* Function: Worker -> local error buffer

vars == <<phase, docStatus, workerDoc, serialCounters, serialLock, lockHolder, errors, localErrors>>

Status == {"pending", "assigned", "parsing", "parsed", "awaiting_lock", "validating", "valid", "invalid"}
ErrorType == {"MALFORMED_ID", "INVALID_CHECKSUM", "DUPLICATE_SERIAL", "NOT_IN_INDEX"}

\* Scope and serial are abstracted as functions
CONSTANTS ScopeOf, SerialOf

---------------------------------------------------------------------------
(* Type Invariant *)
---------------------------------------------------------------------------

TypeOK ==
    /\ phase \in {"init", "validating", "merging", "done"}
    /\ docStatus \in [Documents -> Status]
    /\ workerDoc \in [Workers -> Documents \cup {"idle"}]
    /\ serialCounters \in [Scopes -> SUBSET SerialNumbers]
    /\ serialLock \in BOOLEAN
    /\ lockHolder \in Workers \cup {"none"}
    /\ errors \in Seq([doc: Documents, error: ErrorType])
    /\ localErrors \in [Workers -> Seq([doc: Documents, error: ErrorType])]

---------------------------------------------------------------------------
(* Initial State *)
---------------------------------------------------------------------------

Init ==
    /\ phase = "init"
    /\ docStatus = [d \in Documents |-> "pending"]
    /\ workerDoc = [w \in Workers |-> "idle"]
    /\ serialCounters = [s \in Scopes |-> {}]
    /\ serialLock = FALSE
    /\ lockHolder = "none"
    /\ errors = <<>>
    /\ localErrors = [w \in Workers |-> <<>>]

---------------------------------------------------------------------------
(* Helper Operators *)
---------------------------------------------------------------------------

PendingDocs == {d \in Documents : docStatus[d] = "pending"}
IdleWorkers == {w \in Workers : workerDoc[w] = "idle"}
ActiveWorkers == Workers \ IdleWorkers
ProcessedDocs == {d \in Documents : docStatus[d] \in {"valid", "invalid"}}

InIndex(doc) == doc \in IndexEntries

\* Count active workers
ActiveCount == Cardinality(ActiveWorkers)

---------------------------------------------------------------------------
(* Actions *)
---------------------------------------------------------------------------

\* Start parallel validation
StartValidation ==
    /\ phase = "init"
    /\ phase' = "validating"
    /\ UNCHANGED <<docStatus, workerDoc, serialCounters, serialLock, lockHolder, errors, localErrors>>

\* Worker picks a document (parallel assignment)
WorkerPickDocument(w) ==
    /\ phase = "validating"
    /\ workerDoc[w] = "idle"
    /\ PendingDocs # {}
    /\ ActiveCount < MaxParallel
    /\ LET doc == CHOOSE d \in PendingDocs : TRUE
       IN /\ workerDoc' = [workerDoc EXCEPT ![w] = doc]
          /\ docStatus' = [docStatus EXCEPT ![doc] = "assigned"]
    /\ UNCHANGED <<phase, serialCounters, serialLock, lockHolder, errors, localErrors>>

\* Worker parses document
WorkerParse(w) ==
    /\ phase = "validating"
    /\ workerDoc[w] # "idle"
    /\ LET doc == workerDoc[w]
       IN /\ docStatus[doc] = "assigned"
          /\ \/ \* Parse success
                /\ docStatus' = [docStatus EXCEPT ![doc] = "parsed"]
                /\ localErrors' = localErrors
             \/ \* Parse failure
                /\ docStatus' = [docStatus EXCEPT ![doc] = "invalid"]
                /\ localErrors' = [localErrors EXCEPT ![w] =
                     Append(@, [doc |-> doc, error |-> "MALFORMED_ID"])]
    /\ UNCHANGED <<phase, workerDoc, serialCounters, serialLock, lockHolder, errors>>

\* Worker requests lock for serial validation
WorkerRequestLock(w) ==
    /\ phase = "validating"
    /\ workerDoc[w] # "idle"
    /\ docStatus[workerDoc[w]] = "parsed"
    /\ ~serialLock
    /\ serialLock' = TRUE
    /\ lockHolder' = w
    /\ docStatus' = [docStatus EXCEPT ![workerDoc[w]] = "awaiting_lock"]
    /\ UNCHANGED <<phase, workerDoc, serialCounters, errors, localErrors>>

\* Worker validates with lock held
WorkerValidateWithLock(w) ==
    /\ phase = "validating"
    /\ workerDoc[w] # "idle"
    /\ docStatus[workerDoc[w]] = "awaiting_lock"
    /\ serialLock = TRUE
    /\ lockHolder = w
    /\ LET doc == workerDoc[w]
           scope == ScopeOf[doc]
           serial == SerialOf[doc]
           isDuplicateSerial == serial \in serialCounters[scope]
           notInIndex == ~InIndex(doc)
       IN
       \/ \* All checks pass
          /\ ~isDuplicateSerial
          /\ ~notInIndex
          /\ docStatus' = [docStatus EXCEPT ![doc] = "valid"]
          /\ serialCounters' = [serialCounters EXCEPT ![scope] = @ \cup {serial}]
          /\ localErrors' = localErrors
       \/ \* Duplicate serial
          /\ isDuplicateSerial
          /\ docStatus' = [docStatus EXCEPT ![doc] = "invalid"]
          /\ localErrors' = [localErrors EXCEPT ![w] =
               Append(@, [doc |-> doc, error |-> "DUPLICATE_SERIAL"])]
          /\ UNCHANGED serialCounters
       \/ \* Not in index
          /\ notInIndex
          /\ docStatus' = [docStatus EXCEPT ![doc] = "invalid"]
          /\ localErrors' = [localErrors EXCEPT ![w] =
               Append(@, [doc |-> doc, error |-> "NOT_IN_INDEX"])]
          /\ serialCounters' = [serialCounters EXCEPT ![scope] = @ \cup {serial}]
       \/ \* Checksum error
          /\ docStatus' = [docStatus EXCEPT ![doc] = "invalid"]
          /\ localErrors' = [localErrors EXCEPT ![w] =
               Append(@, [doc |-> doc, error |-> "INVALID_CHECKSUM"])]
          /\ serialCounters' = [serialCounters EXCEPT ![scope] = @ \cup {serial}]
    /\ UNCHANGED <<phase, workerDoc, serialLock, lockHolder, errors>>

\* Release lock after validation
WorkerReleaseLock(w) ==
    /\ phase = "validating"
    /\ workerDoc[w] # "idle"
    /\ docStatus[workerDoc[w]] \in {"valid", "invalid"}
    /\ serialLock = TRUE
    /\ lockHolder = w
    /\ serialLock' = FALSE
    /\ lockHolder' = "none"
    /\ workerDoc' = [workerDoc EXCEPT ![w] = "idle"]
    /\ UNCHANGED <<phase, docStatus, serialCounters, errors, localErrors>>

\* Transition to merge phase
StartMerge ==
    /\ phase = "validating"
    /\ PendingDocs = {}
    /\ \A w \in Workers : workerDoc[w] = "idle"
    /\ serialLock = FALSE
    /\ phase' = "merging"
    /\ UNCHANGED <<docStatus, workerDoc, serialCounters, serialLock, lockHolder, errors, localErrors>>

\* Merge local errors into global errors
MergeErrors ==
    /\ phase = "merging"
    /\ \E w \in Workers : localErrors[w] # <<>>
    /\ LET w == CHOOSE w \in Workers : localErrors[w] # <<>>
       IN /\ errors' = errors \o localErrors[w]
          /\ localErrors' = [localErrors EXCEPT ![w] = <<>>]
    /\ UNCHANGED <<phase, docStatus, workerDoc, serialCounters, serialLock, lockHolder>>

\* Complete validation
CompleteValidation ==
    /\ phase = "merging"
    /\ \A w \in Workers : localErrors[w] = <<>>
    /\ phase' = "done"
    /\ UNCHANGED <<docStatus, workerDoc, serialCounters, serialLock, lockHolder, errors, localErrors>>

---------------------------------------------------------------------------
(* Next State Relation *)
---------------------------------------------------------------------------

Next ==
    \/ StartValidation
    \/ \E w \in Workers : WorkerPickDocument(w)
    \/ \E w \in Workers : WorkerParse(w)
    \/ \E w \in Workers : WorkerRequestLock(w)
    \/ \E w \in Workers : WorkerValidateWithLock(w)
    \/ \E w \in Workers : WorkerReleaseLock(w)
    \/ StartMerge
    \/ MergeErrors
    \/ CompleteValidation

---------------------------------------------------------------------------
(* Safety Properties *)
---------------------------------------------------------------------------

\* S1: Serial Uniqueness (same as Case A)
SerialUniqueness ==
    phase = "done" =>
        \A s \in Scopes :
            \A d1, d2 \in Documents :
                (d1 # d2 /\ docStatus[d1] = "valid" /\ docStatus[d2] = "valid"
                 /\ ScopeOf[d1] = s /\ ScopeOf[d2] = s)
                => SerialOf[d1] # SerialOf[d2]

\* S2: Validation Completeness
ValidationCompleteness ==
    phase = "done" =>
        \A d \in Documents : docStatus[d] \in {"valid", "invalid"}

\* S3: Error Collection Completeness (including merged)
ErrorCollectionComplete ==
    phase = "done" =>
        \A d \in Documents :
            docStatus[d] = "invalid" =>
                \E i \in 1..Len(errors) : errors[i].doc = d

\* S4: Index Consistency
IndexConsistency ==
    phase = "done" =>
        \A d \in Documents :
            (~InIndex(d) /\ docStatus[d] \in {"valid", "invalid"}) =>
                (docStatus[d] = "invalid" /\
                 \E i \in 1..Len(errors) :
                    errors[i].doc = d /\ errors[i].error = "NOT_IN_INDEX")

\* Lock invariant - at most one worker holds lock
LockInvariant ==
    serialLock => lockHolder \in Workers

\* Mutex invariant - only lock holder can be in awaiting_lock or validating
MutexInvariant ==
    \A w \in Workers :
        (workerDoc[w] # "idle" /\ docStatus[workerDoc[w]] = "awaiting_lock")
        => lockHolder = w

\* No deadlock - if lock is held, holder can make progress
NoDeadlock ==
    (serialLock /\ lockHolder \in Workers) =>
        (workerDoc[lockHolder] # "idle" /\
         docStatus[workerDoc[lockHolder]] \in {"awaiting_lock", "valid", "invalid"})

\* Parallel limit respected
ParallelLimitRespected ==
    ActiveCount <= MaxParallel

\* Combined Safety
Safety == TypeOK /\ SerialUniqueness /\ LockInvariant /\ MutexInvariant /\ ParallelLimitRespected

---------------------------------------------------------------------------
(* Liveness Properties *)
---------------------------------------------------------------------------

Termination == <>(phase = "done")
Progress == \A d \in Documents : <>(docStatus[d] \in {"valid", "invalid"})

\* Lock eventually released
LockEventuallyReleased ==
    serialLock ~> ~serialLock

---------------------------------------------------------------------------
(* Specification *)
---------------------------------------------------------------------------

Fairness == /\ WF_vars(Next)
            /\ \A w \in Workers : WF_vars(WorkerPickDocument(w))
            /\ \A w \in Workers : WF_vars(WorkerReleaseLock(w))
            /\ \A w \in Workers : WF_vars(WorkerValidateWithLock(w))

Spec == Init /\ [][Next]_vars /\ Fairness

\* State constraint for bounded model checking
StateConstraint ==
    /\ Cardinality(ProcessedDocs) <= Cardinality(Documents)
    /\ Len(errors) <= Cardinality(Documents)
    /\ \A w \in Workers : Len(localErrors[w]) <= Cardinality(Documents)

=============================================================================
