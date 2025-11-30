---------------------------- MODULE counterexample ----------------------------

EXTENDS serial_generation

(* Constant initialization state *)
ConstInit ==
  IndexDocIDs = { "PCE-SPEC-2025-0001-A", "PCE-SPEC-2025-0002-B" }
    /\ MaxDigits = 4
    /\ NoScopeKey = "ModelValue_NoScopeKey"
    /\ ScopeKeys = { "KKS-DES-2025", "PCE-SPEC-2025" }

(* Initial state [_transition(0)] *)
(* State0 ==
  IndexDocIDs = { "PCE-SPEC-2025-0001-A", "PCE-SPEC-2025-0002-B" }
    /\ MaxDigits = 4
    /\ NoScopeKey = "ModelValue_NoScopeKey"
    /\ ScopeKeys = { "KKS-DES-2025", "PCE-SPEC-2025" }
    /\ __AlwaysSafe_init = FALSE
    /\ __InLoop = FALSE
    /\ __saved_☐((∀scopeKey$29 ∈ DOMAIN generatedSerials: (scopeKey$29 ∈ ScopeKeys ∧ generatedSerials[scopeKey$29] ∈ (0 .. ((10 ^ 4) - 1)))) ∧ (∀id1$3 ∈ IndexDocIDs: (∀id2$3 ∈ IndexDocIDs: (((id1$3 ≠ id2$3) ∧ ((CHOOSE scopeKey$30 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = (CHOOSE scopeKey$31 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE))) ⇒ ((CHOOSE n$20 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE) ≠ (CHOOSE n$21 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE))))) ∧ (∀scopeKey$32 ∈ DOMAIN generatedSerials: (generatedSerials[scopeKey$32] ≤ ((10 ^ 4) - 1))) ∧ (∀scopeKey$33 ∈ ScopeKeys: (∀id$6 ∈ ({id$7 ∈ IndexDocIDs: ((CHOOSE scopeKey$43 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = scopeKey$33)}): ((CHOOSE n$23 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE) ≤ (IF (({CHOOSE n$29 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE : docId$38 ∈ ({docId$39 ∈ IndexDocIDs: ((CHOOSE scopeKey$44 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = scopeKey$33)})}) = {}) THEN 0 ELSE (CHOOSE s$18 ∈ ({CHOOSE n$30 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE : docId$40 ∈ ({docId$41 ∈ IndexDocIDs: ((CHOOSE scopeKey$45 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = scopeKey$33)})}) : (∀t$15 ∈ ({CHOOSE n$31 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE : docId$42 ∈ ({docId$43 ∈ IndexDocIDs: ((CHOOSE scopeKey$46 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = scopeKey$33)})}): (t$15 ≤ s$18))))))))
      = FALSE
    /\ __saved_generatedSerials = SetAsFun({})
    /\ ☐((∀scopeKey$29 ∈ DOMAIN generatedSerials: (scopeKey$29 ∈ ScopeKeys ∧ generatedSerials[scopeKey$29] ∈ (0 .. ((10 ^ 4) - 1)))) ∧ (∀id1$3 ∈ IndexDocIDs: (∀id2$3 ∈ IndexDocIDs: (((id1$3 ≠ id2$3) ∧ ((CHOOSE scopeKey$30 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = (CHOOSE scopeKey$31 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE))) ⇒ ((CHOOSE n$20 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE) ≠ (CHOOSE n$21 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE))))) ∧ (∀scopeKey$32 ∈ DOMAIN generatedSerials: (generatedSerials[scopeKey$32] ≤ ((10 ^ 4) - 1))) ∧ (∀scopeKey$33 ∈ ScopeKeys: (∀id$6 ∈ ({id$7 ∈ IndexDocIDs: ((CHOOSE scopeKey$43 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = scopeKey$33)}): ((CHOOSE n$23 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE) ≤ (IF (({CHOOSE n$29 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE : docId$38 ∈ ({docId$39 ∈ IndexDocIDs: ((CHOOSE scopeKey$44 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = scopeKey$33)})}) = {}) THEN 0 ELSE (CHOOSE s$18 ∈ ({CHOOSE n$30 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE : docId$40 ∈ ({docId$41 ∈ IndexDocIDs: ((CHOOSE scopeKey$45 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = scopeKey$33)})}) : (∀t$15 ∈ ({CHOOSE n$31 ∈ (1 .. ((10 ^ 4) - 1)) : TRUE : docId$42 ∈ ({docId$43 ∈ IndexDocIDs: ((CHOOSE scopeKey$46 ∈ (ScopeKeys ∪ {'ModelValue_NoScopeKey'}) : TRUE) = scopeKey$33)})}): (t$15 ≤ s$18))))))))
      = FALSE
    /\ __temporal_t_1_unroll = TRUE
    /\ __temporal_t_1_unroll_prev = TRUE
    /\ generatedSerials = SetAsFun({}) *)
State0 ==
  IndexDocIDs = { "PCE-SPEC-2025-0001-A", "PCE-SPEC-2025-0002-B" }
    /\ MaxDigits = 4
    /\ NoScopeKey = "ModelValue_NoScopeKey"
    /\ ScopeKeys = { "KKS-DES-2025", "PCE-SPEC-2025" }
    /\ __AlwaysSafe_init = FALSE
    /\ __InLoop = FALSE
    /\ __saved___temporal_t_1 = FALSE
    /\ __saved_generatedSerials = SetAsFun({})
    /\ __temporal_t_1 = FALSE
    /\ __temporal_t_1_unroll = TRUE
    /\ __temporal_t_1_unroll_prev = TRUE
    /\ generatedSerials = SetAsFun({})

(* The following formula holds true in the last state and violates the invariant *)
(* InvariantViolation ==
  Skolem((\E id1_10 \in IndexDocIDs:
    Skolem((\E id2_10 \in IndexDocIDs:
      (~(id1$10 = id2$10)
          /\ (CHOOSE scopeKey_93 \in ScopeKeys \union {"ModelValue_NoScopeKey"}:
            TRUE)
            = (CHOOSE scopeKey_94 \in ScopeKeys \union {"ModelValue_NoScopeKey"}:
              TRUE))
        /\ (CHOOSE n_57 \in 1 .. 9999: TRUE) = (CHOOSE n_58 \in 1 .. 9999: TRUE))))) *)
InvariantViolation ==
  Skolem((\E id1_10 \in IndexDocIDs:
    Skolem((\E id2_10 \in IndexDocIDs:
      (~(id1_10 = id2_10)
          /\ (CHOOSE scopeKey_93 \in ScopeKeys \union {"ModelValue_NoScopeKey"}:
            TRUE)
            = (CHOOSE scopeKey_94 \in ScopeKeys \union {"ModelValue_NoScopeKey"}:
              TRUE))
        /\ (CHOOSE n_57 \in 1 .. 9999: TRUE) = (CHOOSE n_58 \in 1 .. 9999: TRUE)))))

================================================================================
(* Created by Apalache on Sun Nov 30 08:22:42 JST 2025 *)
(* https://github.com/apalache-mc/apalache *)
