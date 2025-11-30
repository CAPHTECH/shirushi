<!-- Thank you for filing a report! Please ensure you have filled out all -->
<!-- sections, as it help us to address the problem effectively. -->

<!-- NOTE: Please try to ensure the bug can be produced on the latest release of -->
<!-- Apalache. See https://github.com/apalache-mc/apalache/releases -->

## Impact

<!-- Whether this is blocking your work or whether you are able to proceed using -->
<!-- workarounds or alternative approaches. -->

## Input specification

```
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
(* Helper Functions - Abstract operations on doc_ids                  *)
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
  CHOOSE n \in 1..(10^MaxDigits - 1) : TRUE

\* Compute maximum value for given digit count
MaxSerialValue(digits) == 10^digits - 1

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
\* Note: UniqueSerialInScope and ScopeFilteringCorrect depend on abstract
\* ExtractScope/ExtractSerial functions which can't be model-checked.
\* These are verified via property-based tests in TypeScript instead.
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
````

## The command line parameters used to run the tool

```
--config=serial_generation.cfg
```

## Expected behavior

<!-- What did you expect to see? -->

## Log files

<details>

```
2025-11-30T08:23:18,830 [main] INFO  a.f.a.t.Tool\$ - # APALACHE version: 0.51.1 | build: 48b9aca
2025-11-30T08:23:18,841 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > serial_generation.cfg: Loading TLC configuration
2025-11-30T08:23:18,875 [main] WARN  a.f.a.i.t.TlcConfigParserApalache\$ - TLC config option CHECK_DEADLOCK true will be ignored
2025-11-30T08:23:18,878 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > Using temporal predicate(s) AlwaysSafe from the TLC config
2025-11-30T08:23:18,878 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > Using inv predicate(s) TypeInvariant, SystemInvariant from the TLC config
2025-11-30T08:23:18,879 [main] INFO  a.f.a.t.t.o.CheckCmd - Tuning: search.outputTraces=false
2025-11-30T08:23:18,998 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser
2025-11-30T08:23:19,212 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser [OK]
2025-11-30T08:23:19,213 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat
2025-11-30T08:23:19,213 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Running Snowcat .::.
2025-11-30T08:23:19,506 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Your types are purrfect!
2025-11-30T08:23:19,506 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > All expressions are typed
2025-11-30T08:23:19,506 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat [OK]
2025-11-30T08:23:19,507 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass
2025-11-30T08:23:19,640 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > serial_generation.cfg: Using SPECIFICATION Spec
2025-11-30T08:23:19,641 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > serial_generation.cfg: found INVARIANTS: TypeInvariant, SystemInvariant
2025-11-30T08:23:19,641 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > serial_generation.cfg: found PROPERTIES: AlwaysSafe
2025-11-30T08:23:19,642 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the initialization predicate to Init
2025-11-30T08:23:19,642 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the transition predicate to Next
2025-11-30T08:23:19,642 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the constant initialization predicate to CInit
2025-11-30T08:23:19,642 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to TypeInvariant
2025-11-30T08:23:19,642 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to SystemInvariant
2025-11-30T08:23:19,643 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set a temporal property to AlwaysSafe
2025-11-30T08:23:19,645 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass [OK]
2025-11-30T08:23:19,645 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass
2025-11-30T08:23:19,645 [main] INFO  a.f.a.t.p.p.DesugarerPassImpl -   > Desugaring...
2025-11-30T08:23:19,656 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass [OK]
2025-11-30T08:23:19,656 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass
2025-11-30T08:23:19,657 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: AlwaysSafe, CInit, CInitPrimed, Init, InitPrimed, Next, SystemInvariant, TypeInvariant
2025-11-30T08:23:19,691 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass [OK]
2025-11-30T08:23:19,691 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass
2025-11-30T08:23:19,691 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > Rewriting temporal operators...
2025-11-30T08:23:19,693 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > Found 1 temporal properties
2025-11-30T08:23:19,693 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > Adding logic for loop finding
2025-11-30T08:23:19,707 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass [OK]
2025-11-30T08:23:19,707 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass
2025-11-30T08:23:19,708 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: AlwaysSafe, CInit, CInitPrimed, Init, InitPrimed, Next, SystemInvariant, TypeInvariant
2025-11-30T08:23:19,712 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass [OK]
2025-11-30T08:23:19,712 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass
2025-11-30T08:23:19,713 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing CInitPrimed for CInit'
2025-11-30T08:23:19,714 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing InitPrimed for Init'
2025-11-30T08:23:19,714 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass [OK]
2025-11-30T08:23:19,714 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #8: VCGen
2025-11-30T08:23:19,715 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant TypeInvariant
2025-11-30T08:23:19,716 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 2 verification condition(s)
2025-11-30T08:23:19,716 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant SystemInvariant
2025-11-30T08:23:19,717 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 3 verification condition(s)
2025-11-30T08:23:19,717 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant AlwaysSafe
2025-11-30T08:23:19,717 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2025-11-30T08:23:19,718 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #8: VCGen [OK]
2025-11-30T08:23:19,718 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass
2025-11-30T08:23:19,718 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Before preprocessing: unique renaming
2025-11-30T08:23:19,721 [main] INFO  a.f.a.t.p.p.PreproPassImpl -  > Applying standard transformations:
2025-11-30T08:23:19,721 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > PrimePropagation
2025-11-30T08:23:19,722 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Desugarer
2025-11-30T08:23:19,724 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > UniqueRenamer
2025-11-30T08:23:19,727 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Normalizer
2025-11-30T08:23:19,730 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Keramelizer
2025-11-30T08:23:19,751 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > After preprocessing: UniqueRenamer
2025-11-30T08:23:19,758 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass [OK]
2025-11-30T08:23:19,758 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass
2025-11-30T08:23:19,783 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 1 initializing transitions
2025-11-30T08:23:19,788 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 4 transitions
2025-11-30T08:23:19,788 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found constant initializer CInit
2025-11-30T08:23:19,789 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Applying unique renaming
2025-11-30T08:23:19,800 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass [OK]
2025-11-30T08:23:19,800 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass
2025-11-30T08:23:19,804 [main] INFO  a.f.a.t.p.p.OptPassImpl -  > Applying optimizations:
2025-11-30T08:23:19,804 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2025-11-30T08:23:19,811 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ExprOptimizer
2025-11-30T08:23:19,816 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > SetMembershipSimplifier
2025-11-30T08:23:19,819 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2025-11-30T08:23:19,833 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass [OK]
2025-11-30T08:23:19,833 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass
2025-11-30T08:23:19,835 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Marking skolemizable existentials and sets to be expanded...
2025-11-30T08:23:19,835 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Skolemization
2025-11-30T08:23:19,836 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Expansion
2025-11-30T08:23:19,839 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Remove unused let-in defs
2025-11-30T08:23:19,841 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Running analyzers...
2025-11-30T08:23:19,850 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Introduced expression grades
2025-11-30T08:23:19,850 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass [OK]
2025-11-30T08:23:19,850 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #13: BoundedChecker
2025-11-30T08:23:19,871 [main] DEBUG a.f.a.t.b.s.Z3SolverContext - Creating Z3 solver context 0
2025-11-30T08:23:20,399 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Initializing CONSTANTS
2025-11-30T08:23:20,424 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #0, transition #0
2025-11-30T08:23:20,424 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2025-11-30T08:23:20,434 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0. Is it enabled?
2025-11-30T08:23:20,435 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0 is enabled
2025-11-30T08:23:20,435 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: Checking 6 state invariants
2025-11-30T08:23:20,435 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 0
2025-11-30T08:23:20,437 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 0 holds.
2025-11-30T08:23:20,462 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 1
2025-11-30T08:23:20,462 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 1 holds.
2025-11-30T08:23:20,467 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 2
2025-11-30T08:23:20,469 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 2 holds.
2025-11-30T08:23:20,470 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 3
2025-11-30T08:23:20,470 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 3 holds.
2025-11-30T08:23:20,470 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 4
2025-11-30T08:23:20,470 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 4 holds.
2025-11-30T08:23:20,470 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 5
2025-11-30T08:23:20,470 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 5 holds.
2025-11-30T08:23:20,471 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 0: picking a transition out of 1 transition(s)
2025-11-30T08:23:20,471 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #0
2025-11-30T08:23:20,471 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2025-11-30T08:23:24,659 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #0. Is it enabled?
2025-11-30T08:23:32,517 [main] DEBUG a.f.a.i.p.PassChainExecutor - Adapted exception intercepted: 
at.forsyte.apalache.tla.bmcmt.SmtEncodingException: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
	at at.forsyte.apalache.tla.bmcmt.smt.Z3SolverContext.sat(Z3SolverContext.scala:557)
	at at.forsyte.apalache.tla.bmcmt.smt.Z3SolverContext.satOrTimeout(Z3SolverContext.scala:564)
	at at.forsyte.apalache.tla.bmcmt.smt.RecordingSolverContext.satOrTimeout(RecordingSolverContext.scala:205)
	at at.forsyte.apalache.tla.bmcmt.trex.TransitionExecutorImpl.sat(TransitionExecutorImpl.scala:349)
	at at.forsyte.apalache.tla.bmcmt.trex.FilteredTransitionExecutor.sat(FilteredTransitionExecutor.scala:181)
	at at.forsyte.apalache.tla.bmcmt.trex.ConstrainedTransitionExecutor.sat(ConstrainedTransitionExecutor.scala:127)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.\$anonfun\$prepareTransitionsAndCheckInvariants\$5(SeqModelChecker.scala:232)
	at scala.runtime.java8.JFunction1\$mcVI\$sp.apply(JFunction1\$mcVI\$sp.scala:18)
	at scala.collection.immutable.Range.foreach(Range.scala:256)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.prepareTransitionsAndCheckInvariants(SeqModelChecker.scala:213)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.makeStep(SeqModelChecker.scala:125)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.run(SeqModelChecker.scala:67)
	at at.forsyte.apalache.tla.bmcmt.passes.BoundedCheckerPassImpl.runIncrementalChecker(BoundedCheckerPassImpl.scala:164)
	at at.forsyte.apalache.tla.bmcmt.passes.BoundedCheckerPassImpl.execute(BoundedCheckerPassImpl.scala:116)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.exec(PassChainExecutor.scala:71)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.\$anonfun\$runPassOnModule\$3(PassChainExecutor.scala:60)
	at scala.util.Either.flatMap(Either.scala:360)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.\$anonfun\$runPassOnModule\$1(PassChainExecutor.scala:58)
	at scala.collection.LinearSeqOps.foldLeft(LinearSeq.scala:183)
	at scala.collection.LinearSeqOps.foldLeft\$(LinearSeq.scala:179)
	at scala.collection.immutable.List.foldLeft(List.scala:79)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.runOnPasses(PassChainExecutor.scala:51)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.run(PassChainExecutor.scala:42)
	at at.forsyte.apalache.tla.tooling.opt.CheckCmd.run(CheckCmd.scala:137)
	at at.forsyte.apalache.tla.Tool\$.runCommand(Tool.scala:139)
	at at.forsyte.apalache.tla.Tool\$.run(Tool.scala:119)
	at at.forsyte.apalache.tla.Tool\$.main(Tool.scala:40)
	at at.forsyte.apalache.tla.Tool.main(Tool.scala)
2025-11-30T08:23:32,521 [main] ERROR a.f.a.t.Tool\$ - <unknown>: error when rewriting to SMT: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
at.forsyte.apalache.infra.AdaptedException: <unknown>: error when rewriting to SMT: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
	at at.forsyte.apalache.infra.passes.PassChainExecutor.run(PassChainExecutor.scala:47)
	at at.forsyte.apalache.tla.tooling.opt.CheckCmd.run(CheckCmd.scala:137)
	at at.forsyte.apalache.tla.Tool\$.runCommand(Tool.scala:139)
	at at.forsyte.apalache.tla.Tool\$.run(Tool.scala:119)
	at at.forsyte.apalache.tla.Tool\$.main(Tool.scala:40)
	at at.forsyte.apalache.tla.Tool.main(Tool.scala)
```
</details>

## System information

- Apalache version: `0.51.1 build 48b9aca`
- OS: `Mac OS X`
- JDK version: `17.0.15`

## Triage checklist (for maintainers)

<!-- This section is for maintainers -->

- [ ] Reproduce the bug on the main development branch.
- [ ] Add the issue to the apalache GitHub project.
- [ ] If the bug is high impact, ensure someone available is assigned to fix it.

