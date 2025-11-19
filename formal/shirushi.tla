-------------------------- MODULE shirushi --------------------------
(*
Shirushi Document ID Management System - TLA+ Specification
Version: 0.2.0

This specification models CLI + service-layer behaviour, including
assign two-phase patching, streaming lint events, and config-driven
constants. It complements the Alloy structural model.
*)

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS
  \* @type: Set(Str);
  Documents,
  \* @type: Set(Str);
  DocIDs,
  \* @type: Set(Str);
  Paths,
  \* @type: Int;
  MaxSerialPerScope,

  \* TLC bounded subsets
  \* @type: Set(Str);
  PathsSubset,
  \* @type: Set(Str);
  DocIDsSubset,
  \* @type: Set(Str);
  ScopeKeys,

  \* @type: Int;
  MaxDocs,
  \* @type: Set(Str);
  MetadataKeys,
  \* @type: Set(Str);
  GitRefs,
  \* @type: Set(Str);
  ScanFormats,

  \* @type: Int;
  MaxHistory,
  \* @type: Str;
  NoID,
  \* @type: Str;
  NoPath,
  \* @type: Str;
  NoScopeKey,
  \* @type: Set(Str);
  ErrorCodes,
  \* @type: Set(Int);
  ExitCodes,
  \* @type: Int;
  MaxRequests,
  \* @type: Int;
  MaxServiceLog,
  \* @type: Int;
  MaxStreamEvents

ASSUME MaxSerialPerScope > 0
ASSUME MaxDocs > 0
ASSUME MaxHistory > 0
ASSUME MaxRequests > 0
ASSUME MaxServiceLog > 0
ASSUME MaxStreamEvents > 0
ASSUME NoID \notin DocIDs
ASSUME NoPath \notin Paths
ASSUME NoScopeKey \notin ScopeKeys
ASSUME 0 \in ExitCodes /\ 1 \in ExitCodes /\ 2 \in ExitCodes

(* Dimension helper constants (config-derived).
   In practice formal-sync generates these functions/sets. *)
CompCodes == {"PCE"}
KindCodes == {"SPEC"}
YearCodes == {"2024", "2025"}
SerialStrings == {"0001", "0002"}
ChecksumLetters == {"A", "B"}

EnumSelection == [p \in Paths |-> "PCE"]
KindMapping == [dt \in STRING |-> "SPEC"]
YearSelection == [p \in Paths |-> "2025"]
SerialFormatter == [i \in 1..MaxSerialPerScope |-> IF i = 1 THEN "0001" ELSE "0002"]
ScopeKeyBuilder == [tuple \in CompCodes \X KindCodes \X YearCodes |-> "PCE-SPEC-2025"]
ChecksumFunction == [tuple \in CompCodes \X KindCodes \X YearCodes \X SerialStrings |-> "A"]
ComposeDocID == [tuple \in CompCodes \X KindCodes \X YearCodes \X SerialStrings \X ChecksumLetters |->
  IF tuple[4] = "0001" THEN "PCE-SPEC-2025-0001-A" ELSE "PCE-SPEC-2025-0002-A"]

AllowMissingIDs == FALSE
ForbidIDChange == TRUE
InitialDocIDs == [p \in Paths |-> NoID]

(* ----------------------------------------------------------------- *)
VARIABLES
  docs,
  index,
  gitBase,
  serialCounters,
  history,
  patchBuffer,
  serviceLog,
  nextRequestId,
  activeStream,
  streamEvents

PatchStatus == {"idle", "pending"}
StreamStatuses == {"ok", "warn", "error"}
StreamPhases == {"start", "doc", "summary"}

PatchBufferType == [
  status: PatchStatus,
  path: Paths \cup {NoPath},
  docID: DocIDs \cup {NoID},
  indexEntry: [path: Paths \cup {NoPath}, docType: STRING, metadata: [MetadataKeys -> STRING]],
  scopeKey: ScopeKeys \cup {NoScopeKey},
  nextSerial: 0..MaxSerialPerScope,
  prevSerial: 0..MaxSerialPerScope,
  dryRun: BOOLEAN,
  requestId: 0..MaxRequests
]

ServiceEntryType == [
  id: 0..MaxRequests,
  endpoint: {"lint", "scan", "assign"},
  exitCode: ExitCodes,
  errorCode: ErrorCodes,
  mutates: BOOLEAN,
  dryRun: BOOLEAN
]

ActiveStreamType == [
  status: {"idle", "active"},
  requestId: 0..MaxRequests,
  finalExit: ExitCodes,
  worstStatus: StreamStatuses,
  emittedFinal: BOOLEAN
]

StreamEventType == [
  requestId: 0..MaxRequests,
  phase: StreamPhases,
  status: StreamStatuses,
  exitCode: ExitCodes,
  docPath: Paths \cup {NoPath}
]

PatchIdle == [
  status |-> "idle",
  path |-> NoPath,
  docID |-> NoID,
  indexEntry |-> [path |-> NoPath, docType |-> "", metadata |-> [k \in MetadataKeys |-> ""]],
  scopeKey |-> NoScopeKey,
  nextSerial |-> 0,
  prevSerial |-> 0,
  dryRun |-> TRUE,
  requestId |-> 0
]

ActiveStreamIdle == [
  status |-> "idle",
  requestId |-> 0,
  finalExit |-> 0,
  worstStatus |-> "ok",
  emittedFinal |-> TRUE
]

(* ----------------------------------------------------------------- *)
TypeInvariant ==
  /\ docs \in [PathsSubset -> [
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
  /\ gitBase \in [PathsSubset -> [
       docID: DocIDs \cup {NoID},
       docType: STRING,
       metadata: [MetadataKeys -> STRING]
     ]]
  /\ serialCounters \in [ScopeKeys -> 0..MaxSerialPerScope]
  /\ history \in Seq([
        op: {"lint", "scan", "assignPlan", "assignCommit", "assignDiscard", "gitCheckout"},
        params: STRING \cup Paths
      ])
  /\ patchBuffer \in PatchBufferType
  /\ serviceLog \in Seq(ServiceEntryType)
  /\ nextRequestId \in 0..MaxRequests
  /\ activeStream \in ActiveStreamType
  /\ streamEvents \in Seq(StreamEventType)

(* ----------------------------------------------------------------- *)
UsedDocIDs == ({ docs[p].docID : p \in DOMAIN docs }) \ {NoID}
IndexedDocIDs == DOMAIN index
SeqElems(seq) == { seq[i] : i \in DOMAIN seq }

StatusExit(status) ==
  IF status = "ok" THEN 0
  ELSE IF status = "warn" THEN 1
  ELSE 2

CombineStatus(a, b) ==
  IF a = "error" \/ b = "error" THEN "error"
  ELSE IF a = "warn" \/ b = "warn" THEN "warn"
  ELSE "ok"

LintMissingDocs == { p \in DOMAIN docs : docs[p].docID = NoID }
LintStatus ==
  IF LintMissingDocs = {} THEN "ok"
  ELSE IF AllowMissingIDs THEN "warn"
  ELSE "error"

LintErrorCode(status) ==
  IF status = "ok" THEN "OK"
  ELSE IF status = "warn" THEN "ALLOW_MISSING_ID"
  ELSE "VALIDATION_ERROR"

AssignDerived(path) ==
  LET docType == docs[path].docType
      compValue == EnumSelection[path]
      kindValue == KindMapping[docType]
      yearValue == YearSelection[path]
      scopeTuple == <<compValue, kindValue, yearValue>>
      scopeKey == ScopeKeyBuilder[scopeTuple]
      prevSerial == serialCounters[scopeKey]
      nextSerial == prevSerial + 1
      serialValue == SerialFormatter[nextSerial]
      checksumValue == ChecksumFunction[<<compValue, kindValue, yearValue, serialValue>>]
      newDocID == ComposeDocID[<<compValue, kindValue, yearValue, serialValue, checksumValue>>]
      newIndexEntry == [path |-> path, docType |-> docType, metadata |-> docs[path].metadata]
  IN [
       scopeKey |-> scopeKey,
       prevSerial |-> prevSerial,
       nextSerial |-> nextSerial,
       docID |-> newDocID,
       indexEntry |-> newIndexEntry
     ]

(* ----------------------------------------------------------------- *)
UniqueDocIDs ==
  \A p1, p2 \in DOMAIN docs :
    (p1 /= p2 /\ docs[p1].docID /= NoID /\ docs[p2].docID /= NoID)
      => docs[p1].docID /= docs[p2].docID

UniqueIndexIDs == TRUE

DocIndexConsistency ==
  \A p \in DOMAIN docs :
    docs[p].docID /= NoID =>
      (\E id \in DOMAIN index : index[id].path = p /\ id = docs[p].docID)

IndexedDocsExist ==
  \A id \in DOMAIN index : \E p \in DOMAIN docs : index[id].path = p

AllDocsIndexed ==
  \A p \in DOMAIN docs :
    docs[p].docID /= NoID =>
      \E id \in DOMAIN index : index[id].path = p

UniqueIndexPaths ==
  \A id1, id2 \in DOMAIN index : id1 /= id2 => index[id1].path /= index[id2].path

MissingIDPolicyInvariant ==
  /\ (AllowMissingIDs =>
        \A p \in DOMAIN docs :
          docs[p].docID = NoID => gitBase[p].docID = NoID)
  /\ (~AllowMissingIDs =>
        \A p \in DOMAIN docs :
          gitBase[p].docID /= NoID => docs[p].docID /= NoID)

ImmutabilityInvariant ==
  ForbidIDChange =>
    \A p \in (DOMAIN gitBase \cap DOMAIN docs) :
      (gitBase[p].docID /= NoID /\ docs[p].docID /= NoID)
        => gitBase[p].docID = docs[p].docID

PatchAtomicityInvariant ==
  patchBuffer.status = "pending" =>
    /\ docs[patchBuffer.path].docID = NoID
    /\ patchBuffer.docID \notin UsedDocIDs
    /\ patchBuffer.docID \notin IndexedDocIDs

SystemInvariant ==
  /\ UniqueDocIDs
  /\ UniqueIndexIDs
  /\ DocIndexConsistency
  /\ IndexedDocsExist
  /\ AllDocsIndexed
  /\ UniqueIndexPaths
  /\ MissingIDPolicyInvariant
  /\ ImmutabilityInvariant
  /\ PatchAtomicityInvariant

(* ----------------------------------------------------------------- *)
Lint(baseRef) ==
  /\ history' = Append(history, [op |-> "lint", params |-> baseRef])
  /\ UNCHANGED <<docs, index, gitBase, serialCounters, patchBuffer, serviceLog, nextRequestId, activeStream, streamEvents>>

Scan(format) ==
  /\ history' = Append(history, [op |-> "scan", params |-> format])
  /\ UNCHANGED <<docs, index, gitBase, serialCounters, patchBuffer, serviceLog, nextRequestId, activeStream, streamEvents>>

GitCheckout(ref) ==
  /\ gitBase' = docs
  /\ history' = Append(history, [op |-> "gitCheckout", params |-> ref])
  /\ UNCHANGED <<docs, index, serialCounters, patchBuffer, serviceLog, nextRequestId, activeStream, streamEvents>>

ServiceLint ==
  \E baseRef \in GitRefs, streaming \in BOOLEAN :
    LET currId == nextRequestId
        status == LintStatus
        exitCode == StatusExit(status)
        errCode == LintErrorCode(status)
        startEvent == [requestId |-> currId, phase |-> "start", status |-> status, exitCode |-> exitCode, docPath |-> NoPath]
    IN
      /\ nextRequestId < MaxRequests
      /\ history' = Append(history, [op |-> "lint", params |-> baseRef])
      /\ serviceLog' = Append(serviceLog, [
            id |-> currId,
            endpoint |-> "lint",
            exitCode |-> exitCode,
            errorCode |-> errCode,
            mutates |-> FALSE,
            dryRun |-> TRUE
          ])
      /\ nextRequestId' = currId + 1
      /\ IF streaming
            THEN /\ activeStream.status = "idle"
                 /\ activeStream' = [
                      status |-> "active",
                      requestId |-> currId,
                      finalExit |-> exitCode,
                      worstStatus |-> status,
                      emittedFinal |-> FALSE
                    ]
                 /\ streamEvents' = Append(streamEvents, startEvent)
          ELSE /\ activeStream' = activeStream
               /\ streamEvents' = streamEvents
      /\ UNCHANGED <<docs, index, gitBase, serialCounters, patchBuffer>>

ServiceScan ==
  \E format \in ScanFormats :
    LET currId == nextRequestId
    IN
      /\ nextRequestId < MaxRequests
      /\ history' = Append(history, [op |-> "scan", params |-> format])
      /\ serviceLog' = Append(serviceLog, [
            id |-> currId,
            endpoint |-> "scan",
            exitCode |-> 0,
            errorCode |-> "OK",
            mutates |-> FALSE,
            dryRun |-> TRUE
          ])
      /\ nextRequestId' = currId + 1
      /\ streamEvents' = streamEvents
      /\ activeStream' = activeStream
      /\ UNCHANGED <<docs, index, gitBase, serialCounters, patchBuffer>>

ServiceAssignPrepare ==
  /\ patchBuffer.status = "idle"
  /\ nextRequestId < MaxRequests
  /\ \E path \in PathsSubset, dryRun \in BOOLEAN :
        ( /\ path \in DOMAIN docs
          /\ docs[path].docID = NoID
          /\ LET derived == AssignDerived(path)
             IN (
               /\ derived.nextSerial <= MaxSerialPerScope
               /\ derived.docID \notin UsedDocIDs
               /\ derived.docID \notin IndexedDocIDs
               /\ patchBuffer' = [
                    status |-> "pending",
                    path |-> path,
                    docID |-> derived.docID,
                    indexEntry |-> derived.indexEntry,
                    scopeKey |-> derived.scopeKey,
                    nextSerial |-> derived.nextSerial,
                    prevSerial |-> derived.prevSerial,
                    dryRun |-> dryRun,
                    requestId |-> nextRequestId
                  ]
               /\ nextRequestId' = nextRequestId + 1
               /\ history' = Append(history, [op |-> "assignPlan", params |-> path])
               /\ UNCHANGED <<docs, index, gitBase, serialCounters, serviceLog, activeStream, streamEvents>>
             ))

PatchApply ==
  /\ patchBuffer.status = "pending"
  /\ ~patchBuffer.dryRun
  /\ docs[patchBuffer.path].docID = NoID
  /\ patchBuffer.docID \notin UsedDocIDs
  /\ patchBuffer.docID \notin IndexedDocIDs
  /\ serialCounters[patchBuffer.scopeKey] = patchBuffer.prevSerial
  /\ LET path == patchBuffer.path IN
       /\ docs' = [docs EXCEPT ![path].docID = patchBuffer.docID]
       /\ index' = index @@ (patchBuffer.docID :> patchBuffer.indexEntry)
       /\ serialCounters' = [serialCounters EXCEPT ![patchBuffer.scopeKey] = patchBuffer.nextSerial]
       /\ patchBuffer' = PatchIdle
       /\ serviceLog' = Append(serviceLog, [
             id |-> patchBuffer.requestId,
             endpoint |-> "assign",
             exitCode |-> 0,
             errorCode |-> "OK",
             mutates |-> TRUE,
             dryRun |-> FALSE
           ])
       /\ history' = Append(history, [op |-> "assignCommit", params |-> path])
  /\ UNCHANGED <<gitBase, nextRequestId, activeStream, streamEvents>>

DiscardNeeded ==
  patchBuffer.status = "pending" /\ (
    patchBuffer.dryRun \/
    docs[patchBuffer.path].docID /= NoID \/
    patchBuffer.docID \in UsedDocIDs \/
    patchBuffer.docID \in IndexedDocIDs \/
    serialCounters[patchBuffer.scopeKey] /= patchBuffer.prevSerial
  )

PatchDiscard ==
  /\ DiscardNeeded
  /\ LET reason == IF patchBuffer.dryRun THEN "dryRun" ELSE "conflict" IN
     /\ patchBuffer' = PatchIdle
     /\ docs' = docs
     /\ index' = index
     /\ serialCounters' = serialCounters
     /\ serviceLog' = Append(serviceLog, [
           id |-> patchBuffer.requestId,
           endpoint |-> "assign",
           exitCode |-> IF reason = "dryRun" THEN 0 ELSE 2,
           errorCode |-> IF reason = "dryRun" THEN "ASSIGN_DRY_RUN" ELSE "ASSIGN_CONFLICT",
           mutates |-> FALSE,
           dryRun |-> patchBuffer.dryRun
         ])
     /\ history' = Append(history, [op |-> "assignDiscard", params |-> patchBuffer.path])
     /\ UNCHANGED <<gitBase, nextRequestId, activeStream, streamEvents>>

StreamEmitDoc ==
  /\ activeStream.status = "active"
  /\ Len(streamEvents) < MaxStreamEvents
  /\ \E path \in DOMAIN docs, status \in StreamStatuses :
        LET newWorst == CombineStatus(activeStream.worstStatus, status)
            event == [requestId |-> activeStream.requestId, phase |-> "doc", status |-> status, exitCode |-> StatusExit(status), docPath |-> path]
        IN
          /\ streamEvents' = Append(streamEvents, event)
          /\ activeStream' = [activeStream EXCEPT !.worstStatus = newWorst]
          /\ UNCHANGED <<docs, index, gitBase, serialCounters, history, patchBuffer, serviceLog, nextRequestId>>

StreamEmitFinal ==
  /\ activeStream.status = "active"
  /\ ~activeStream.emittedFinal
  /\ activeStream.finalExit = StatusExit(activeStream.worstStatus)
  /\ Len(streamEvents) < MaxStreamEvents
  /\ LET finalEvent == [
         requestId |-> activeStream.requestId,
         phase |-> "summary",
         status |-> activeStream.worstStatus,
         exitCode |-> activeStream.finalExit,
         docPath |-> NoPath
       ]
     IN
       /\ streamEvents' = Append(streamEvents, finalEvent)
       /\ activeStream' = ActiveStreamIdle
       /\ UNCHANGED <<docs, index, gitBase, serialCounters, history, patchBuffer, serviceLog, nextRequestId>>

Next ==
  \/ ServiceLint
  \/ ServiceScan
  \/ ServiceAssignPrepare
  \/ PatchApply
  \/ PatchDiscard
  \/ StreamEmitDoc
  \/ StreamEmitFinal
  \/ \E ref \in GitRefs : GitCheckout(ref)

Init ==
  /\ docs = [p \in PathsSubset |-> [
       docID |-> InitialDocIDs[p],
       docType |-> "",
       metadata |-> [k \in MetadataKeys |-> ""]
     ]]
  /\ index = [d \in {} |-> [path |-> NoPath, docType |-> "", metadata |-> [k \in MetadataKeys |-> ""]]]
  /\ gitBase = [p \in PathsSubset |-> [
       docID |-> InitialDocIDs[p],
       docType |-> "",
       metadata |-> [k \in MetadataKeys |-> ""]
     ]]
  /\ serialCounters = [k \in ScopeKeys |-> 0]
  /\ history = <<>>
  /\ patchBuffer = PatchIdle
  /\ serviceLog = <<>>
  /\ nextRequestId = 0
  /\ activeStream = ActiveStreamIdle
  /\ streamEvents = <<>>

Spec == Init /\ [][Next]_<<docs, index, gitBase, serialCounters, history, patchBuffer, serviceLog, nextRequestId, activeStream, streamEvents>>

(* ----------------------------------------------------------------- *)
AlwaysValid == []SystemInvariant

ServiceReadOnly == \A entry \in SeqElems(serviceLog) :
  entry.endpoint \in {"lint", "scan"} => entry.mutates = FALSE

ServiceErrorCodesTotal == \A entry \in SeqElems(serviceLog) : entry.errorCode \in ErrorCodes

StreamFinalConsistent == \A event \in SeqElems(streamEvents) :
  event.phase = "summary" =>
    \E entry \in SeqElems(serviceLog) :
      entry.id = event.requestId /\ entry.exitCode = event.exitCode

AssignEventuallySucceeds ==
  \A p \in Paths :
    (p \in DOMAIN docs /\ docs[p].docID = NoID)
      ~> docs[p].docID /= NoID

StateConstraint ==
  /\ Len(history) <= MaxHistory
  /\ Len(serviceLog) <= MaxServiceLog
  /\ Len(streamEvents) <= MaxStreamEvents
  /\ nextRequestId <= MaxRequests
  /\ DOMAIN docs \subseteq PathsSubset

=====================================================================
