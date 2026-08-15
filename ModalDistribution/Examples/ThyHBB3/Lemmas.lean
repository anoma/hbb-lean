import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyHBB3.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History
import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.Semifilter
/-!
# ThyHBB3 Helper Lemmas

This file records the auxiliary lemmas used throughout Section~8 of the paper.
Each statement mirrors the corresponding labelled lemma in the text: the
interaction of the `3twined` axiom with sequential quorums, the extraction of
quorum witnesses from votes, and the behaviour of the correlation relation
$\mnta$.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB3

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open Set
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {correlationSymb : Signature.PredSymb S}

-- Unique-proposal helpers specialised to the `ThyHBB3` axioms.  These mirror the
-- `ThyHBB2` results but only rely on the echo-forward and echo-backward rules
-- that are also present in `ThyHBB3`.
namespace Unique

/-- Auxiliary: the antecedent ensures echoes exist for some witness value under
`ThyHBB3`. -/
theorem exists_witness_echo
    (value : Signature.Value S)
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M]
      (predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
      ∃ᶠ fun witness =>
        ↕ᶠ (ofEvent ⟨echoSymb, [witness]⟩) := by
  classical
  have hEchoForward : AllWorldValid M
      (echoForwardAxiom liveSymb proposeSymb echoSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  intro t ht
  have hLocal :
      ⟪t⟫ ⊨[M]
        echoForwardAxiom liveSymb proposeSymb echoSymb :=
    hEchoForward ht
  have hSpecialised :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun v =>
        (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) ⇒ᶠ
          ∃ᶠ fun witness =>
            ↕ᶠ (ofEvent ⟨echoSymb, [witness]⟩))
      (v := value) hLocal
  simpa [echoForwardAxiom]
    using hSpecialised

/-- Auxiliary: uniqueness of proposals forces witnesses produced by
`Echo!` to agree with the target value. -/
theorem witness_eq_value
    (value : Signature.Value S)
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    (hUnique : ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    □W⊨[M]
      (predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
      ∀ᶠ fun witness =>
        (↕ᶠ (ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
          (witness ≃ᶠ value) := by
  classical
  have hEchoBackward : AllWorldValid M
      (echoBackwardAxiom proposeSymb echoSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  intro t ht
  set wPred : World P (Signature.EventType S) := t with hwPredDef
  set wTop : World P (Signature.EventType S) :=
    ⟨t.place, †, M.history.val⟩ with hwTopDef
  have hUniqueGlobal :
      ⟪wTop⟫ ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) :=
    hUnique t.place
  have hGuardGlobal :
      ⟪wTop⟫ ⊨[M]
        ∃≤ᶠ1 v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) :=
    uniquePropose_guard_at_history
      (M := M) (proposeSymb := proposeSymb)
      (w := wTop) (hUnique := hUniqueGlobal)
  refine
    Sat.imp_intro (M := M) (w := wPred)
      (φ :=
        predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
      (ψ := ∀ᶠ fun witness =>
        (↕ᶠ (ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
          (witness ≃ᶠ value)) ?_
  intro hAnte
  have hConj :=
    (Sat.and (M := M) (w := wPred)
      (φ := predicate0 liveSymb)
      (ψ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))).1 hAnte
  have hDiamondValueLoc :
      ⟪wPred⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) :=
    hConj.2
  refine
    Sat.forall_intro (M := M) (w := wPred)
      (body := fun witness =>
        (↕ᶠ (ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
          (witness ≃ᶠ value)) ?_
  intro witness
  refine
    Sat.imp_intro (M := M) (w := wPred)
      (φ := ↕ᶠ (ofEvent ⟨echoSymb, [witness]⟩))
      (ψ := witness ≃ᶠ value) ?_
  intro hEcho
  obtain ⟨wEcho, hEcho_mem, _, hEchoEvent⟩ :=
    sometime_echo_event_exists (M := M)
      (w := wPred) (value := witness) hEcho
  have hDiamondWitnessLocal :
      ⟪wEcho⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩) :=
    echo_backward_diamond_from_sometime
      (M := M) (w := wEcho) (value := witness)
      (hEchoBack := hEchoBackward) hEchoEvent
  have hSubsetPred :
      wPred.time ⊆trn M.history.val := by
    simpa [wPred, hwPredDef, wTop, hwTopDef]
      using
        ModalDistribution.Logic.time_subset_trn_history
          (M := M) (t := t) ht
  have hDiamondValueGlobal :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) :=
    (sat_diamondPast_nil_event_subset (M := M)
        (w := wTop) (w' := wPred)
        (symb := proposeSymb) (args := [value])
        (hSubset := hSubsetPred) hDiamondValueLoc)
  have hBeforeEcho :
      wEcho.time ⪯ M.history.val :=
    PreHistory.happensBeforeEq_of_mem
      (P := P) (Event := Signature.EventType S)
      (hmem := by
        simpa [World.place, World.event, World.time] using hEcho_mem)
  have hSubsetEcho : wEcho.time ⊆trn M.history.val := by
    simpa using
      ModalDistribution.Logic.time_subset_trn_history
        (M := M) (t := wEcho) hBeforeEcho
  have hDiamondWitnessGlobal :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩) :=
    (sat_diamondPast_nil_event_subset (M := M)
        (w := wTop) (w' := wEcho)
        (symb := proposeSymb) (args := [witness])
        (hSubset := hSubsetEcho) hDiamondWitnessLocal)
  have hEqGlobal :
      ⟪wTop⟫ ⊨[M]
        witness ≃ᶠ value :=
    uniquePropose_guard_implies_eq
      (M := M) (proposeSymb := proposeSymb)
      (w := wTop) (value := value) (witness := witness)
      (hGuard := hGuardGlobal)
      (hDiamond_value := hDiamondValueGlobal)
      (hDiamond_witness := hDiamondWitnessGlobal)
  simpa [Sat] using hEqGlobal

/-- Unique proposals in `ThyHBB3` guarantee eventual echoes for the chosen value. -/
theorem eventually_echo
    (value : Signature.Value S)
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    (hUnique : ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    □W⊨[M]
      (predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨echoSymb, [value]⟩) := by
  refine uniquePropose_eventually_echo_core
      (M := M) (liveSymb := liveSymb)
      (proposeSymb := proposeSymb) (echoSymb := echoSymb)
      (value := value) ?_ ?_
  · exact exists_witness_echo (M := M) (liveSymb := liveSymb)
        (proposeSymb := proposeSymb) (echoSymb := echoSymb)
        (voteSymb := voteSymb) (deliverSymb := deliverSymb)
        (correlationSymb := correlationSymb) (value := value) (hTheory := hTheory)
  · exact witness_eq_value (M := M) (liveSymb := liveSymb)
        (proposeSymb := proposeSymb) (echoSymb := echoSymb)
        (voteSymb := voteSymb) (deliverSymb := deliverSymb)
        (correlationSymb := correlationSymb) (value := value)
        (hTheory := hTheory) (hUnique := hUnique)

end Unique

/-- `3twined` combines three guarded box facts
into a joint diamond witness. -/
theorem threeTwined_phi
    {l₁ l₂ l₃ : Signature.Value S}
    {φ₁ φ₂ φ₃ : Formula S} :
    ⊨[M]
      ((♢ᶠ[[l₁, l₂, l₃]] ⊤ᶠ) ⇒ᶠ
        ((□ᶠ[[l₁]] φ₁) ∧ᶠ (□ᶠ[[l₂]] φ₂) ∧ᶠ (□ᶠ[[l₃]] φ₃) ⇒ᶠ
          ♢ᶠ[] (φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃))) := by
  classical
  intro p
  set w : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  -- Unpack the implication hypotheses step by step.
  refine
    Sat.imp_intro (M := M) (w := w)
      (φ := ♢ᶠ[[l₁, l₂, l₃]] ⊤ᶠ)
      (ψ := (((□ᶠ[[l₁]] φ₁) ∧ᶠ (□ᶠ[[l₂]] φ₂)) ∧ᶠ (□ᶠ[[l₃]] φ₃)) ⇒ᶠ
        ♢ᶠ[] (φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃)) ?_
  intro hDiamond
  refine
    Sat.imp_intro (M := M) (w := w)
      (φ := ((□ᶠ[[l₁]] φ₁) ∧ᶠ (□ᶠ[[l₂]] φ₂)) ∧ᶠ (□ᶠ[[l₃]] φ₃))
      (ψ := ♢ᶠ[] (φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃)) ?_
  intro hBoxes
  -- Separate the three `□` guards.
  have hPairAnd :=
    (Sat.and (M := M) (w := w)
      (φ := (□ᶠ[[l₁]] φ₁) ∧ᶠ (□ᶠ[[l₂]] φ₂))
      (ψ := □ᶠ[[l₃]] φ₃)).1 hBoxes
  have hPair₁₂ := hPairAnd.1
  have hBox₃ : ⟪w⟫ ⊨[M]□ᶠ[[l₃]] φ₃ := hPairAnd.2
  have hPair₁₂' :=
    (Sat.and (M := M) (w := w)
      (φ := □ᶠ[[l₁]] φ₁) (ψ := □ᶠ[[l₂]] φ₂)).1 hPair₁₂
  have hBox₁ : ⟪w⟫ ⊨[M]□ᶠ[[l₁]] φ₁ := hPair₁₂'.1
  have hBox₂ : ⟪w⟫ ⊨[M]□ᶠ[[l₂]] φ₂ := hPair₁₂'.2
  -- For each learner, pick a quorum whose members satisfy the guard. (`sat_box_singleton_exists`).
  obtain ⟨O₁, hO₁, hAll₁⟩ :=
    (sat_box_singleton_exists (M := M) (w := w)
      (l := l₁) (φ := φ₁)).1 hBox₁
  obtain ⟨O₂, hO₂, hAll₂⟩ :=
    (sat_box_singleton_exists (M := M) (w := w)
      (l := l₂) (φ := φ₂)).1 hBox₂
  obtain ⟨O₃, hO₃, hAll₃⟩ :=
    (sat_box_singleton_exists (M := M) (w := w)
      (l := l₃) (φ := φ₃)).1 hBox₃
  -- Triple intersection witness supplied by `sat_diamond_three_intersection`
  -- (captures `♢ᶠ[[l₁,l₂,l₃]] ⊤ᶠ`).
  obtain ⟨p₀, hp₁, hp₂, hp₃⟩ :=
    sat_diamond_three_intersection (M := M) (w := w)
      (hDiamond := hDiamond) (hO₁ := hO₁) (hO₂ := hO₂) (hO₃ := hO₃)
  -- Each guard holds at the common participant.
  have hφ₁ : ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] φ₁ := hAll₁ _ hp₁
  have hφ₂ : ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] φ₂ := hAll₂ _ hp₂
  have hφ₃ : ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] φ₃ := hAll₃ _ hp₃
  -- Build the combined conjunction `(φ₁ ∧ φ₂ ∧ φ₃)` at the witness.
  have hφ₁₂ :
      ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] φ₁ ∧ᶠ φ₂ :=
    Sat.and_intro (M := M) (w := ⟨p₀, †, w.time⟩)
      (φ := φ₁) (ψ := φ₂) hφ₁ hφ₂
  have hφAll :
      ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] (φ₁ ∧ᶠ φ₂) ∧ᶠ φ₃ :=
    Sat.and_intro (M := M) (w := ⟨p₀, †, w.time⟩)
      (φ := φ₁ ∧ᶠ φ₂) (ψ := φ₃) hφ₁₂ hφ₃
  -- Witness the empty learner diamond via `sat_diamondEmpty_of_local`.
  have hWitness : ∃ q, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃ :=
    ⟨p₀, by simpa using hφAll⟩
  exact
    sat_diamondEmpty_of_local (M := M) (w := w)
      (φ := φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃) hWitness

/-- The `threeTwined` axiom forces triple learner quorums to intersect. -/
theorem threeTwined_hasQuorumNonempty
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    (hHistory : ∃ t : World P (Signature.EventType S), t ∈ M.history.val)
    {l₁ l₂ l₃ : Signature.Value S} :
    hasQuorumNonempty (M := M) [l₁, l₂, l₃] := by
  classical
  obtain ⟨t, ht⟩ := hHistory
  have hThreeTwinedEvent :
      AllWorldValid M (threeTwinedAxiom (S := S)) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  have hThreeTwinedLocal :
      ⟪t⟫ ⊨[M] threeTwinedAxiom (S := S) :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := threeTwinedAxiom (S := S))
      hThreeTwinedEvent ht
  have hDiamond :
      ⟪t⟫ ⊨[M] ♢ᶠ[[l₁, l₂, l₃]] ⊤ᶠ := by
    have hForall₁ :=
      Sat.forall_elim (M := M) (w := t)
        (body := fun learner₁ =>
          ∀ᶠ fun learner₂ =>
            ∀ᶠ fun learner₃ =>
              ♢ᶠ[[learner₁, learner₂, learner₃]] ⊤ᶠ)
        (v := l₁)
        hThreeTwinedLocal
    have hForall₂ :=
      Sat.forall_elim (M := M) (w := t)
        (body := fun learner₂ =>
          ∀ᶠ fun learner₃ =>
            ♢ᶠ[[l₁, learner₂, learner₃]] ⊤ᶠ)
        (v := l₂) hForall₁
    exact
      Sat.forall_elim (M := M) (w := t)
        (body := fun learner₃ =>
          ♢ᶠ[[l₁, l₂, learner₃]] ⊤ᶠ)
        (v := l₃) hForall₂
  exact
    (sat_diamond_top_iff_hasQuorumNonempty (M := M)
        (w := t) (ls := [l₁, l₂, l₃])).1 hDiamond

/-- Lift a learner-guarded past box from a local world to end-of-time. -/
theorem lift_boxPast_to_end
    {t : World P (Signature.EventType S)}
    {learner : Signature.Value S}
    {φ : Formula S}
    (hSubset : t.time ⊆ M.history.val)
    (hBox : ⟪t⟫ ⊨[M]□ᶠ↓[[learner]]φ) :
    ⊨[M]□ᶠ↓[[learner]]φ := by
  classical
  have hBoxPast_at :
      ⟪t⟫ ⊨[M]□ᶠ[[learner]](↓ᶠ φ) :=
    by simpa [Formula.boxPast] using hBox
  intro p
  have hBoxPast_top :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ[[learner]](↓ᶠ φ) :=
    sat_box_singleton_transfer (M := M)
      (w := t) (w' := ⟨p, †, M.history.val⟩)
      (l := learner)
      (φ := ↓ᶠ φ)
      (hTransfer := fun q hPast =>
        sat_past_of_subset (M := M)
          (q := q)
          (H := t.time)
          (H' := M.history.val)
          (φ := φ)
          (hSubset := hSubset) hPast)
      hBoxPast_at
  simpa [Formula.boxPast]
    using hBoxPast_top

/-- Eliminate the existential quantifier encoded by `∃ᶠ` at the satisfaction level. -/
@[simp] theorem sat_exists_iff
    (w : World P (Signature.EventType S))
    (body : Signature.Value S → Formula S) :
    (⟪w⟫ ⊨[M]∃ᶠ fun v => body v) ↔
      ∃ v, ⟪w⟫ ⊨[M]body v := by
  classical
  constructor
  · intro hExists
    -- Suppose no witness exists, derive a contradiction with the existential.
    refine Classical.byContradiction fun hNoWitness => ?_
    have hNone : ∀ v, ¬ (⟪w⟫ ⊨[M]body v) := fun v hv => hNoWitness ⟨v, hv⟩
    have hForall :
        ⟪w⟫ ⊨[M]∀ᶠ fun v => ¬ᶠ (body v) :=
      Sat.forall_intro (M := M) (w := w)
        (body := fun v => ¬ᶠ (body v))
        (fun v =>
          Sat.not_intro (M := M) (w := w)
            (φ := body v) (hNone v))
    have hContr :=
      (Sat.not (M := M) (w := w)
        (φ := ∀ᶠ fun v => ¬ᶠ (body v))).1
        (by simpa [Formula.exists_] using hExists)
      hForall
    exact hContr
  · intro hWitness
    simpa [Formula.exists_]
      using
        Sat.exists_intro (M := M) (w := w)
          (body := fun v => body v) hWitness

omit [Nonempty P] in
-- Auxiliary lemmas about zero height (not available yet, kept for future use).
theorem prehistory_height_le_zero_false
    (h : PreHistory P (Signature.EventType S))
    (hLe : PreHistory.height h ≤ 0) : False := by
  classical
  cases h with
  | mk l =>
      have hPos :
          0 < PreHistory.height (PreHistory.mk l) :=
        by simp [PreHistory.height]
      exact (Nat.not_lt.mpr hLe) hPos

/-- Inductive step for the height-based argument in
`vote_implies_echo_quorum_local`.  Assuming the result for all worlds strictly
smaller than `w`, we obtain the required echo quorum for `w`. -/
theorem vote_implies_echo_quorum_height_step
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {w : World P (Signature.EventType S)}
    (hMem : w ∈ M.history.val)
    {n : Nat}
    (hHeight : PreHistory.height w.time = n.succ)
    (IH : ∀ {w' : World P (Signature.EventType S)},
        w' ∈ M.history.val →
        PreHistory.height w'.time ≤ n →
        ∀ {learner value : Signature.Value S},
          (⟪w'⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) →
            ∃ source : Signature.Value S,
              ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩))
    {learner value : Signature.Value S}
    (hVote : ⟪w⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) :
    ∃ source : Signature.Value S,
      ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  -- Instantiate `Vote?` (the theory assumptions) from the theory assumptions.
  have hVoteAx :
      AllWorldValid M
        (voteBackwardAxiom echoSymb voteSymb correlationSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  have hVoteLocal :
      ⟪w⟫ ⊨[M]
        ∀ᶠ fun learner' =>
          ∀ᶠ fun value' =>
            ofEvent ⟨voteSymb, [learner', value']⟩ ⇒ᶠ
              ((□ᶠ↓[[learner']](ofEvent ⟨echoSymb, [value']⟩)) ∨ᶠ
                ∃ᶠ fun correlated =>
                  ofPredicate ⟨correlationSymb, [correlated, learner']⟩ ∧ᶠ
                    ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value']⟩)) := by
    have h :=
      AllWorldValid.of_mem_history
        (M := M)
        (φ := voteBackwardAxiom echoSymb voteSymb correlationSymb)
        hVoteAx hMem
    simpa [voteBackwardAxiom] using h
  -- Specialise the axiom to the concrete learner and value.
  have hImpLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner' =>
        ∀ᶠ fun value' =>
          ofEvent ⟨voteSymb, [learner', value']⟩ ⇒ᶠ
            ((□ᶠ↓[[learner']](ofEvent ⟨echoSymb, [value']⟩)) ∨ᶠ
              ∃ᶠ fun correlated =>
                ofPredicate ⟨correlationSymb, [correlated, learner']⟩ ∧ᶠ
                  ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value']⟩)))
      (v := learner) hVoteLocal
  have hImpValue :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value' =>
        ofEvent ⟨voteSymb, [learner, value']⟩ ⇒ᶠ
            ((□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value']⟩)) ∨ᶠ
            ∃ᶠ fun correlated =>
              ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value']⟩)))
      (v := value) hImpLearner
  let φLeft := □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)
  let ψRight :=
    ∃ᶠ fun correlated =>
      ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩)
  have hImpValue' := hImpValue
  have hDisj :=
    (Sat.imp (M := M) (w := w)
        (φ := ofEvent ⟨voteSymb, [learner, value]⟩)
        (ψ := φLeft ∨ᶠ ψRight)).1
      hImpValue' hVote
  -- Record that the past of `w` embeds into the global history.
  have hBefore_history :
      w.time ≺− M.history.val :=
    History.happensBefore_of_mem
      (P := P) (Event := Signature.EventType S) hMem
  have hSubset_history : w.time ⊆ M.history.val :=
    History.subset_of_happensBefore (H := M.history) hBefore_history
  -- Split the disjunction between a local echo quorum and a correlated vote chain.
  have hCases :=
    sat_or_cases (M := M) (w := w)
      (φ := φLeft) (ψ := ψRight) hDisj
  cases hCases with
  | inl hEchoBox =>
      -- Lift the local echo quorum to end-of-time (`lift_boxPast_to_end`).
      have hEchoBox' :
          ⟪w⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
        by simpa [φLeft]
      have hEchoGlobal :
          ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
        lift_boxPast_to_end (M := M) (t := w)
          (learner := learner) (φ := ofEvent ⟨echoSymb, [value]⟩)
          (hSubset := hSubset_history) (hBox := hEchoBox')
      exact ⟨learner, hEchoGlobal⟩
  | inr hExists =>
      -- Resolve the existential branch of `Vote?`.
      have hExists' :
          ⟪w⟫ ⊨[M]
            ∃ᶠ fun correlated =>
              ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩) :=
        by simpa [ψRight] using hExists
      have hWitness :=
        (sat_exists_iff (M := M) (w := w)
            (body := fun correlated =>
              ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩))).1
          hExists'
      obtain ⟨correlated, hConj⟩ := hWitness
      have hVoteDiamond :
          ⟪w⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩) :=
        sat_and_right (M := M) (w := w)
          (φ := ofPredicate ⟨correlationSymb, [correlated, learner]⟩)
          (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩))
          hConj
      have hDiamondNil :
          ⟪w⟫ ⊨[M]♢ᶠ[[]](↓ᶠ (ofEvent ⟨voteSymb, [correlated, value]⟩)) :=
        by simpa [Formula.diamondPast] using hVoteDiamond
      -- Extract a predecessor world witnessing the vote (`Sat.diamond_nil`, `Sat.past`).
      obtain ⟨q, hPastVote⟩ :=
        (Sat.diamond_nil (M := M) (w := w)
          (φ := ↓ᶠ (ofEvent ⟨voteSymb, [correlated, value]⟩))).1
          hDiamondNil
      obtain ⟨tVote, ht_mem, ht_place, hVote_at⟩ :=
        (Sat.past (M := M)
          (w := ⟨q, †, w.time⟩)
          (φ := ofEvent ⟨voteSymb, [correlated, value]⟩)).1
          hPastVote
      -- Show the predecessor lies in the global history and has smaller height.
      have ht_mem_history : tVote ∈ M.history.val :=
        hSubset_history _ ht_mem
      have hBefore_vote :
          tVote.time ≺− w.time :=
        History.happensBefore_of_mem
          (P := P) (Event := Signature.EventType S) ht_mem
      have hHeight_lt_aux :
          PreHistory.height tVote.time <
            PreHistory.height w.time :=
        PreHistory.height_lt_of_happensBefore
          (P := P) (Event := Signature.EventType S) hBefore_vote
      have hBound' : PreHistory.height tVote.time ≤ n := by
        have hLt := hHeight_lt_aux
        rw [hHeight] at hLt
        exact Nat.lt_succ_iff.mp hLt
      -- Apply the induction hypothesis to the earlier vote witness.
      obtain ⟨source, hSource⟩ :=
        IH (w' := tVote) ht_mem_history hBound'
          (learner := correlated) (value := value) hVote_at
      exact ⟨source, hSource⟩

/-- Strong induction on `PreHistory.height` used to establish
`vote_implies_echo_quorum_local`.  This lemma packages the base case and the
inductive step so they can be reused when we eventually provide the full proof. -/
theorem vote_implies_echo_quorum_height_induction
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {w : World P (Signature.EventType S)}
    (hMem : w ∈ M.history.val)
    {n : Nat}
    (hBound : PreHistory.height w.time ≤ n)
    {learner value : Signature.Value S}
    (hVote : ⟪w⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) :
    ∃ source : Signature.Value S,
      ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  have hMain : ∀ n,
      ∀ {w : World P (Signature.EventType S)}
        (hMem : w ∈ M.history.val)
        (hBound : PreHistory.height w.time ≤ n)
        {learner value : Signature.Value S},
        (⟪w⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) →
          ∃ source : Signature.Value S,
            ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
    intro n
    induction n with
    | zero =>
        intro w hMem hBound learner value hVote
        have hFalse :=
          prehistory_height_le_zero_false
            (P := P) (h := w.time) hBound
        cases hFalse
    | succ n ih =>
        intro w hMem hBound learner value hVote
        by_cases hLe : PreHistory.height w.time ≤ n
        · exact ih (w := w) hMem hLe (learner := learner) (value := value) hVote
        · have hLt : n < PreHistory.height w.time := Nat.lt_of_not_ge hLe
          have hEq : PreHistory.height w.time = Nat.succ n :=
            Nat.le_antisymm hBound (Nat.succ_le_of_lt hLt)
          have hIH :
              ∀ {w' : World P (Signature.EventType S)}
                (hMem' : w' ∈ M.history.val)
                (hBound' : PreHistory.height w'.time ≤ n)
                {learner value : Signature.Value S},
                (⟪w'⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) →
                  ∃ source : Signature.Value S,
            ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) :=
            by
              intro w' hMem' hBound' learner' value' hVote'
              exact
                ih (w := w') hMem' hBound'
                  (learner := learner') (value := value') hVote'
          exact
            vote_implies_echo_quorum_height_step
              (M := M) (liveSymb := liveSymb) (proposeSymb := proposeSymb)
              (echoSymb := echoSymb) (voteSymb := voteSymb)
              (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
              hTheory hMem hEq hIH hVote
  exact hMain n (w := w) hMem hBound (learner := learner) (value := value) hVote

/-- a realised vote yields an
`Echo` quorum for the same value. -/
theorem vote_implies_echo_quorum_local
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {t : World P (Signature.EventType S)}
    {learner value : Signature.Value S}
    (hMem : t ∈ M.history.val)
    (hVote : ⟪t⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) :
    ∃ source : Signature.Value S,
      ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  have hBound : PreHistory.height t.time ≤ PreHistory.height t.time := Nat.le_refl _
  exact
    vote_implies_echo_quorum_height_induction
      (M := M) (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      hTheory hMem (n := PreHistory.height t.time)
      hBound (learner := learner) (value := value) hVote

/-- votes witnessed in the past
produce a global echo quorum. -/
theorem vote_implies_echo_quorum_end
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {learner value : Signature.Value S}
    (hVote : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ∃ source : Signature.Value S,
      ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  -- Evaluate the past vote at an end-of-time world.
  let p : P := Classical.ofNonempty
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hVoteTop :
      ⟪wTop⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [learner, value]⟩) :=
    by simpa [wTop] using hVote p
  have hDiamondNil :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[]](↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    by simpa [Formula.diamondPast] using hVoteTop
  -- Unpack the past diamond to obtain a witness world in the history.
  obtain ⟨q, hPastVote⟩ :=
    (Sat.diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hDiamondNil
  obtain ⟨tVote, ht_mem, _, hVote_at⟩ :=
    (Sat.past (M := M)
        (w := ⟨q, †, wTop.time⟩)
        (φ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hPastVote
  -- The witness lies in the global history.
  have ht_mem_history : tVote ∈ M.history.val :=
    by simpa [wTop, World.time] using ht_mem
  -- Apply the local lemma to obtain the required echo quorum.
  exact
    vote_implies_echo_quorum_local
      (M := M) (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      hTheory ht_mem_history hVote_at

/-- Deliveries witnessed at end of time yield the backing vote quorum. -/
theorem deliver_to_vote_box_end
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {learner value : Signature.Value S}
    {p : P}
    (hDeliver :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
      □ᶠ↓[[learner]](ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hDeliverTop := hDeliver
  have hDeliverAx : AllWorldValid M (deliverBackwardAxiom voteSymb deliverSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  have hDiamondNil :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ[[]](↓ᶠ (ofEvent ⟨deliverSymb, [learner, value]⟩)) :=
    by simpa [Formula.diamondPast, wTop] using hDeliverTop
  obtain ⟨qDeliver, hPastDeliver⟩ :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (ofEvent ⟨deliverSymb, [learner, value]⟩))).1
      hDiamondNil
  obtain ⟨tDeliver, ht_mem, ht_place, hDeliver_at⟩ :=
    (Sat.past (M := M)
      (w := ⟨qDeliver, †, wTop.time⟩)
      (φ := ofEvent ⟨deliverSymb, [learner, value]⟩)).1
      hPastDeliver
  have ht_mem_history : tDeliver ∈ M.history.val :=
    by simpa [wTop, World.time] using ht_mem
  have hLocal :
      ⟪tDeliver⟫ ⊨[M] deliverBackwardAxiom voteSymb deliverSymb :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := deliverBackwardAxiom voteSymb deliverSymb)
      hDeliverAx ht_mem_history
  have hForLearner :=
    Sat.forall_elim (M := M) (w := tDeliver)
      (body := fun learner' =>
        ∀ᶠ fun value' =>
          ofEvent ⟨deliverSymb, [learner', value']⟩ ⇒ᶠ
            □ᶠ↓[[learner']](ofEvent ⟨voteSymb, [learner', value']⟩))
      (v := learner) hLocal
  have hForValue :=
    Sat.forall_elim (M := M) (w := tDeliver)
      (body := fun value' =>
        ofEvent ⟨deliverSymb, [learner, value']⟩ ⇒ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨voteSymb, [learner, value']⟩))
      (v := value) hForLearner
  have hBox_at_event :
      ⟪tDeliver⟫ ⊨[M]
        □ᶠ↓[[learner]](ofEvent ⟨voteSymb, [learner, value]⟩) :=
    (Sat.imp (M := M) (w := tDeliver)
      (φ := ofEvent ⟨deliverSymb, [learner, value]⟩)
      (ψ := □ᶠ↓[[learner]](ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hForValue hDeliver_at
  have hBefore_history : tDeliver.time ≺− M.history.val :=
    History.happensBefore_of_mem
      (P := P) (Event := Signature.EventType S) ht_mem_history
  have hSubset_history : tDeliver.time ⊆ M.history.val :=
    History.subset_of_happensBefore (H := M.history) hBefore_history
  have hLift :=
    lift_boxPast_to_end (M := M) (t := tDeliver)
      (learner := learner)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)
      (hSubset := hSubset_history) (hBox := hBox_at_event)
  simpa [wTop] using hLift p

/-- One-sided application of `VoteNE`: a vote together with a past vote from a
correlated learner forces value equality. -/
theorem voteNonEquiv_local
    (hVoteNE : AllWorldValid M (voteNonEquivAxiom voteSymb correlationSymb))
    {w : World P (Signature.EventType S)}
    (hMem : w ∈ M.history.val)
    {learner correlated : Signature.Value S}
    {valNow valPast : Signature.Value S}
    (hVote_now :
      ⟪w⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, valNow]⟩)
    (hVote_past :
      ⟪w⟫ ⊨[M]↓ᶠ (ofEvent ⟨voteSymb, [correlated, valPast]⟩))
    (hCorr :
      ⟪w⟫ ⊨[M]ofPredicate ⟨correlationSymb, [learner, correlated]⟩) :
    valNow = valPast := by
  classical
  have hVoteNE_local :
      ⟪w⟫ ⊨[M] voteNonEquivAxiom voteSymb correlationSymb :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := voteNonEquivAxiom voteSymb correlationSymb)
      hVoteNE hMem
  have hForLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner' =>
        ∀ᶠ fun value =>
          ∀ᶠ fun correlated' =>
            ∀ᶠ fun altValue =>
              ofEvent ⟨voteSymb, [learner', value]⟩ ⇒ᶠ
                (↓ᶠ (ofEvent ⟨voteSymb, [correlated', altValue]⟩)) ⇒ᶠ
                  (ofPredicate ⟨correlationSymb, [learner', correlated']⟩ ⇒ᶠ
                    (value ≃ᶠ altValue)))
      (v := learner) hVoteNE_local
  have hForValue :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value =>
        ∀ᶠ fun correlated' =>
          ∀ᶠ fun altValue =>
            ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
              (↓ᶠ (ofEvent ⟨voteSymb, [correlated', altValue]⟩)) ⇒ᶠ
                (ofPredicate ⟨correlationSymb, [learner, correlated']⟩ ⇒ᶠ
                  (value ≃ᶠ altValue)))
      (v := valNow) hForLearner
  have hForCorr :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun correlated' =>
        ∀ᶠ fun altValue =>
          ofEvent ⟨voteSymb, [learner, valNow]⟩ ⇒ᶠ
            (↓ᶠ (ofEvent ⟨voteSymb, [correlated', altValue]⟩)) ⇒ᶠ
              (ofPredicate ⟨correlationSymb, [learner, correlated']⟩ ⇒ᶠ
                (valNow ≃ᶠ altValue)))
      (v := correlated) hForValue
  have hForAlt :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun altValue =>
        ofEvent ⟨voteSymb, [learner, valNow]⟩ ⇒ᶠ
          (↓ᶠ (ofEvent ⟨voteSymb, [correlated, altValue]⟩)) ⇒ᶠ
            (ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
              (valNow ≃ᶠ altValue)))
      (v := valPast) hForCorr
  have hImp :=
    (Sat.imp (M := M) (w := w)
      (φ := ofEvent ⟨voteSymb, [learner, valNow]⟩)
      (ψ :=
        (↓ᶠ (ofEvent ⟨voteSymb, [correlated, valPast]⟩)) ⇒ᶠ
          (ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
            (valNow ≃ᶠ valPast)))).1
      hForAlt hVote_now
  have hImp' :=
    (Sat.imp (M := M) (w := w)
      (φ := ↓ᶠ (ofEvent ⟨voteSymb, [correlated, valPast]⟩))
      (ψ :=
        ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
          (valNow ≃ᶠ valPast))).1
      hImp hVote_past
  have hEqFormula :=
    (Sat.imp (M := M) (w := w)
      (φ := ofPredicate ⟨correlationSymb, [learner, correlated]⟩)
      (ψ := valNow ≃ᶠ valPast)).1
      hImp' hCorr
  have hEq :=
    (Sat.eq (M := M) (w := w)
      (v₁ := valNow) (v₂ := valPast)).1 hEqFormula
  simpa [Sat] using hEq

/-- sequential echo quorums fix the
broadcast value. -/
theorem echo_quorums_agree
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l l₁ l₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hEcho₁ : ⊨[M]□ᶠ↓[[l₁]](ofEvent ⟨echoSymb, [v₁]⟩))
    (hEcho₂ : ⊨[M]□ᶠ↓[[l₂]](ofEvent ⟨echoSymb, [v₂]⟩)) :
    v₁ = v₂ := by
  -- Any guarded echo quorum witnesses a concrete point in the global history.
  have hHistory :
      ∃ t : World P (Signature.EventType S), t ∈ M.history.val :=
    exists_history_mem_of_end_boxPast (M := M)
      (l := l₁)
      (φ := ofEvent ⟨echoSymb, [v₁]⟩)
      (hBox := hEcho₁)
  -- Intermediate sequential-collision step using sequential quorum intersection.
  have hSeqEchoDiamond :
      ⊨[M]
        ♢ᶠ[[]]
          ((Formula.seq ∧ᶠ
              ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
            ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)) := by
    classical
    have hThreeTwined :=
      threeTwined_phi (M := M)
        (l₁ := l) (l₂ := l₁) (l₃ := l₂)
        (φ₁ := Formula.seq)
        (φ₂ := ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))
        (φ₃ := ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))
    have hTripleDiamond :
        ⊨[M] ♢ᶠ[[l, l₁, l₂]] ⊤ᶠ := by
      classical
      have hNonempty :=
        threeTwined_hasQuorumNonempty
          (M := M)
          (hTheory := hTheory)
          (hHistory := hHistory)
          (l₁ := l)
          (l₂ := l₁)
          (l₃ := l₂)
      intro p
      exact
        (sat_diamond_top_iff_hasQuorumNonempty (M := M)
            (w := ⟨p, †, M.history.val⟩)
            (ls := [l, l₁, l₂])).2 hNonempty
    have hEcho₁Box :
        ⊨[M]□ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) := by
      simpa [Formula.boxPast] using hEcho₁
    have hEcho₂Box :
        ⊨[M]□ᶠ[[l₂]] (↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)) := by
      simpa [Formula.boxPast] using hEcho₂
    intro p
    set w : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
    have hThreeTwined_w := hThreeTwined p
    have hTripleDiamond_w := hTripleDiamond p
    have hSeqBox_w := hSeq p
    have hEcho₁Box_w := hEcho₁Box p
    have hEcho₂Box_w := hEcho₂Box p
    have hImpDiamond :=
      Sat.imp_elim (M := M) (w := w)
        (φ := ♢ᶠ[[l, l₁, l₂]] ⊤ᶠ)
        (ψ :=
          (((□ᶠ[[l]] Formula.seq) ∧ᶠ
                □ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))) ∧ᶠ
              □ᶠ[[l₂]] (↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))) ⇒ᶠ
            ♢ᶠ[]
              ((Formula.seq ∧ᶠ ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
        hThreeTwined_w hTripleDiamond_w
    have hBoxesPair :=
      Sat.and_intro (M := M) (w := w)
        (φ := □ᶠ[[l]] Formula.seq)
        (ψ := □ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)))
        hSeqBox_w hEcho₁Box_w
    have hBoxesAll :=
      Sat.and_intro (M := M) (w := w)
        (φ := (□ᶠ[[l]] Formula.seq) ∧ᶠ
          (□ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))))
        (ψ := □ᶠ[[l₂]] (↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
        hBoxesPair hEcho₂Box_w
    exact
      Sat.imp_elim (M := M) (w := w)
        (φ := ((□ᶠ[[l]] Formula.seq) ∧ᶠ
                (□ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)))) ∧ᶠ
              □ᶠ[[l₂]] (↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
        (ψ :=
          ♢ᶠ[]
            ((Formula.seq ∧ᶠ ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
              ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
        hImpDiamond hBoxesAll
  by_cases hEq : v₁ = v₂
  · simp [hEq]
  · have hNe : v₁ ≠ v₂ := hEq
    have hEventNe :
        (⟨echoSymb, [v₁]⟩ : Signature.EventType S) ≠
          ⟨echoSymb, [v₂]⟩ := by
      intro hEvt
      cases hEvt
      exact hNe rfl
    -- Evaluate the diamond at the global end-of-time world.
    let p₀ : P := Classical.ofNonempty
    set wTop : World P (Signature.EventType S) := ⟨p₀, †, M.history.val⟩
    have hDiamondTop :
        ⟪wTop⟫ ⊨[M]
          (♢ᶠ[[]]
            ((Formula.seq ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
              ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))) :=
      by
        have := hSeqEchoDiamond p₀
        simpa [wTop]
          using this
    let φEcho :=
      (Formula.seq ∧ᶠ
          ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
        ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)
    have hWitnessPair :=
      Iff.mp
        (Sat.diamond_nil (M := M) (w := wTop) (φ := φEcho))
        hDiamondTop
    obtain ⟨pEcho, hWitness⟩ := hWitnessPair
    set wEcho : World P (Signature.EventType S) :=
      ⟨pEcho, †, wTop.time⟩
    have hSplit :=
      (Sat.and (M := M) (w := wEcho)
        (φ := Formula.seq ∧ᶠ ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))
        (ψ := ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))).1 hWitness
    have hSeqAnd := hSplit.1
    have hEcho₂_local := hSplit.2
    have hSeqSplit :=
      (Sat.and (M := M) (w := wEcho)
        (φ := Formula.seq)
        (ψ := ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))).1 hSeqAnd
    have hSeq_local := hSeqSplit.1
    have hEcho₁_local := hSeqSplit.2
    -- Sequential order yields a collision diamond in one of the two directions.
    have hEchoCollision_local :
        ⟪wEcho⟫ ⊨[M]
          ((♢ᶠ↓[[]]
              ((ofEvent ⟨echoSymb, [v₁]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))) ∨ᶠ
            (♢ᶠ↓[[]]
              ((ofEvent ⟨echoSymb, [v₂]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)))) :=
      seq_two_quorums_events (M := M)
        (w := wEcho)
        (evt := ⟨echoSymb, [v₁]⟩)
        (evt' := ⟨echoSymb, [v₂]⟩)
        (hSeq := hSeq_local)
        (hEvt_local := hEcho₁_local)
        (hEvt'_local := hEcho₂_local)
        (hDistinct := hEventNe)
    -- `EchoNE` turns the collision diamond into equality.
    have hEchoNE : AllWorldValid M (echoNonEquivAxiom echoSymb) := by
      apply hTheory
      simp [ThyHBB3, ThyHBB3.theory]
    have hSubset : wEcho.time ⊆trn M.history.val := by
      simpa [wEcho, wTop]
        using History.transitiveSubset_refl (H := M.history)
    have hEquality : v₁ = v₂ := by
      cases
          sat_or_cases (M := M) (w := wEcho)
            (φ := ♢ᶠ↓[[]]
                ((ofEvent ⟨echoSymb, [v₁]⟩) ∧ᶠ
                  ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
            (ψ := ♢ᶠ↓[[]]
                ((ofEvent ⟨echoSymb, [v₂]⟩) ∧ᶠ
                  ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)))
            hEchoCollision_local with
      | inl hLeft =>
          exact
            echoNonEquiv_diamond (M := M)
              (echoSymb := echoSymb)
              (hEchoNE := hEchoNE)
              (w := wEcho)
              (hSubset := hSubset)
              (valNow := v₁)
              (valPast := v₂)
              hLeft
      | inr hRight =>
          have hEq :=
            echoNonEquiv_diamond (M := M)
              (echoSymb := echoSymb)
              (hEchoNE := hEchoNE)
              (w := wEcho)
              (hSubset := hSubset)
              (valNow := v₂)
              (valPast := v₁)
              hRight
          exact hEq.symm
    exact hEquality

/-- past votes also determine a unique
value once sequentiality holds. -/
theorem votes_eventually_agree
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l l₁ l₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hVote₁ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v₁]⟩))
    (hVote₂ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₂, v₂]⟩)) :
    v₁ = v₂ := by
  classical
  obtain ⟨source₁, hEcho₁⟩ :=
    vote_implies_echo_quorum_end
      (M := M)
      (hTheory := hTheory)
      (learner := l₁) (value := v₁)
      (hVote := hVote₁)
  obtain ⟨source₂, hEcho₂⟩ :=
    vote_implies_echo_quorum_end
      (M := M)
      (hTheory := hTheory)
      (learner := l₂) (value := v₂)
      (hVote := hVote₂)
  exact
    echo_quorums_agree
      (M := M)
      (hTheory := hTheory)
      (l := l) (l₁ := source₁) (l₂ := source₂)
      (v₁ := v₁) (v₂ := v₂)
      (hSeq := hSeq)
      (hEcho₁ := hEcho₁)
      (hEcho₂ := hEcho₂)

theorem always_corr_symm
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {w : World P (Signature.EventType S)}
    {l₁ l₂ : Signature.Value S} :
    (⟪w⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) →
      (⟪w⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) := by
  classical
  intro hAlways
  -- Symmetry axiom available at every world.
  have hSymmAx : AllWorldValid M (mntaSymmAxiom correlationSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  have hNoOrig :
      ¬ (⟪w⟫ ⊨[M]
          ↕ᶠ (¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))) := by
    have hAlwaysNot :
        ⟪w⟫ ⊨[M]
          ¬ᶠ (↕ᶠ (¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))) := by
      simpa [Formula.alwaysPast] using hAlways
    exact
      (Sat.not (M := M) (w := w)
        (φ := ↕ᶠ (¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)))).1
        hAlwaysNot
  have hGoal :
      (⟪w⟫ ⊨[M]
          ↕ᶠ (¬ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩))) → False := by
    intro hSomeSwapped
    let hSwapEquiv :=
      Sat.sometime (M := M) (w := w)
        (φ := ¬ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩))
    rcases hSwapEquiv.mp hSomeSwapped with
      ⟨t, ht_mem, ht_place, hNotSwapped⟩
    -- Instantiate the symmetry axiom at the witnessing world.
    have hSymmLocal :
        ⟪t⟫ ⊨[M] mntaSymmAxiom correlationSymb :=
      AllWorldValid.of_mem_history
        (M := M)
        (φ := mntaSymmAxiom correlationSymb)
        hSymmAx ht_mem
    have hImpLearner :=
      Sat.forall_elim (M := M) (w := t)
        (body := fun learner =>
          ∀ᶠ fun correlated =>
            ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
              ofPredicate ⟨correlationSymb, [correlated, learner]⟩)
        (v := l₁) hSymmLocal
    have hImpCorrelated :=
      Sat.forall_elim (M := M) (w := t)
        (body := fun correlated =>
          ofPredicate ⟨correlationSymb, [l₁, correlated]⟩ ⇒ᶠ
            ofPredicate ⟨correlationSymb, [correlated, l₁]⟩)
        (v := l₂) hImpLearner
    have hNotOrig :
        ⟪t⟫ ⊨[M] ¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) := by
      refine
        Sat.not_intro (M := M) (w := t)
          (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) ?_
      intro hCorr
      let hImpRelation :=
        Sat.imp (M := M) (w := t)
          (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)
          (ψ := ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)
      have hCorr' := (hImpRelation.mp hImpCorrelated) hCorr
      exact
        (Sat.not_elim (M := M) (w := t)
          (φ := ofPredicate ⟨correlationSymb, [l₂, l₁]⟩))
          hNotSwapped hCorr'
    let hOrigEquiv :=
      Sat.sometime (M := M) (w := w)
        (φ := ¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    have hSomeOrig :
        ⟪w⟫ ⊨[M]
          ↕ᶠ (¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :=
      hOrigEquiv.mpr ⟨t, ht_mem, ht_place, hNotOrig⟩
    exact hNoOrig hSomeOrig
  have hNotSwapped :=
    Sat.not_intro (M := M) (w := w)
      (φ := ↕ᶠ (¬ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)))
      hGoal
  simpa [Formula.alwaysPast] using hNotSwapped

/-- End-of-time correlation together with the persistence axiom yields
correlation throughout each participant’s history. -/
theorem correlation_global_allPast
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    □W⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) := by
  classical
  have hEventually :
      AllWorldValid M (mntaEventuallyAxiom correlationSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  intro t ht_le
  set p := t.place
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hCorrTop :
      ⟪wTop⟫ ⊨[M] ofPredicate ⟨correlationSymb, [l₁, l₂]⟩ := by
    simpa [wTop] using
      (EndValid.boxEmpty_guard (M := M)
        (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) hCorrelation) p
  have hEventuallyTop :
      ⟪wTop⟫ ⊨[M] mntaEventuallyAxiom correlationSymb :=
    hEventually (by simp [wTop, World.time])
  have hImpLearner :
      ⟪wTop⟫ ⊨[M]
        ∀ᶠ fun correlated =>
          ofPredicate ⟨correlationSymb, [l₁, correlated]⟩ ⇒ᶠ
            ⇓ᶠ (ofPredicate ⟨correlationSymb, [l₁, correlated]⟩) :=
    Sat.forall_elim (M := M) (w := wTop)
      (body := fun learner =>
        ∀ᶠ fun correlated =>
          ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
            ⇓ᶠ (ofPredicate ⟨correlationSymb, [learner, correlated]⟩))
      (v := l₁) hEventuallyTop
  have hImpCorrelated :
      ⟪wTop⟫ ⊨[M]
        ofPredicate ⟨correlationSymb, [l₁, l₂]⟩ ⇒ᶠ
          ⇓ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) :=
    Sat.forall_elim (M := M) (w := wTop)
      (body := fun correlated =>
        ofPredicate ⟨correlationSymb, [l₁, correlated]⟩ ⇒ᶠ
          ⇓ᶠ (ofPredicate ⟨correlationSymb, [l₁, correlated]⟩))
      (v := l₂) hImpLearner
  have hNoPast :
      ⟪wTop⟫ ⊨[M] ⇓ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) :=
    (Sat.imp (M := M) (w := wTop)
        (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)
        (ψ := ⇓ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))).1
      hImpCorrelated hCorrTop
  have hNoPast' :
      ⟪wTop⟫ ⊨[M]
        ¬ᶠ (↓ᶠ (¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))) := by
    simpa [Formula.eventuallyPast]
      using hNoPast
  refine Sat.not_intro (M := M) (w := t) ?_
  intro hSome
  obtain ⟨s, hs_mem, hs_place, hNotCorr⟩ :=
    (Sat.sometime (M := M) (w := t)
        (φ := ¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))).1
      hSome
  have hPastWitness :
      ⟪wTop⟫ ⊨[M]
        ↓ᶠ (¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :=
    (Sat.past (M := M)
        (w := wTop)
        (φ := ¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))).2
      ⟨s,
        by simpa [wTop, World.time] using hs_mem,
        by simpa [wTop, World.place] using hs_place,
        hNotCorr⟩
  exact
    (Sat.not_elim (M := M) (w := wTop)
      (φ := ↓ᶠ (¬ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))))
      hNoPast' hPastWitness

/-- Correlated learners admit a sequential intersection witness. -/
theorem correlation_seq_diamond
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]♢ᶠ[[l₁, l₂]] Formula.seq := by
  classical
  have hSeqAx :
      AllWorldValid M (mntaSeqAxiom correlationSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hSeqLocal :
      ⟪wTop⟫ ⊨[M] mntaSeqAxiom correlationSymb :=
    hSeqAx (by simp [wTop, World.time])
  have hImpLearner :
      ⟪wTop⟫ ⊨[M]
        ∀ᶠ fun correlated =>
          ofPredicate ⟨correlationSymb, [l₁, correlated]⟩ ⇒ᶠ
            ♢ᶠ[[l₁, correlated]] Formula.seq :=
    Sat.forall_elim (M := M) (w := wTop)
      (body := fun learner =>
        ∀ᶠ fun correlated =>
          ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
            ♢ᶠ[[learner, correlated]] Formula.seq)
      (v := l₁) hSeqLocal
  have hImpCorrelated :
      ⟪wTop⟫ ⊨[M]
        ofPredicate ⟨correlationSymb, [l₁, l₂]⟩ ⇒ᶠ
          ♢ᶠ[[l₁, l₂]] Formula.seq :=
    Sat.forall_elim (M := M) (w := wTop)
      (body := fun correlated =>
        ofPredicate ⟨correlationSymb, [l₁, correlated]⟩ ⇒ᶠ
          ♢ᶠ[[l₁, correlated]] Formula.seq)
      (v := l₂) hImpLearner
  have hCorrTop :
      ⟪wTop⟫ ⊨[M] ofPredicate ⟨correlationSymb, [l₁, l₂]⟩ :=
    (EndValid.boxEmpty_guard (M := M)
      (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) hCorrelation) p
  exact
    (Sat.imp (M := M) (w := wTop)
        (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)
        (ψ := ♢ᶠ[[l₁, l₂]] Formula.seq)).1
      hImpCorrelated hCorrTop

/-- Helper: Split antecedent `(live ∧ corr) ∧ ◊vote` into components -/
theorem split_live_corr_vote_antecedent
    {w : World P (Signature.EventType S)}
    {l₁ l₂ v : Signature.Value S}
    (hAnte : ⟪w⟫ ⊨[M]((predicate0 liveSymb ∧ᶠ
          ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))) :
    (⟪w⟫ ⊨[M] predicate0 liveSymb) ∧
    (⟪w⟫ ⊨[M] ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) := by
  have hAnteSplit :=
    (Sat.and (M := M) (w := w)
        (φ := predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
        (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).1
      hAnte
  have hLiveCorr :=
    (Sat.and (M := M) (w := w)
        (φ := predicate0 liveSymb)
        (ψ := ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))).1
      hAnteSplit.1
  exact ⟨hLiveCorr.1, hLiveCorr.2, hAnteSplit.2⟩

/-- Helper: Chain three forall eliminations for vote correlation axiom -/
theorem forall_elim_vote_correlated_chain
    {w : World P (Signature.EventType S)}
    {l₁ l₂ v : Signature.Value S}
    (hVoteCorrLocal : ⟪w⟫ ⊨[M]voteForwardCorrelatedAxiom liveSymb voteSymb correlationSymb) :
    ⟪w⟫ ⊨[M]
      (predicate0 liveSymb ∧ᶠ
          (⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) ⇒ᶠ
        ∃ᶠ fun witnessed =>
          ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩) := by
  have hVoteCorrFor₁ :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner =>
        ∀ᶠ fun correlated => ∀ᶠ fun value =>
          (predicate0 liveSymb ∧ᶠ
              (⇕ᶠ (ofPredicate ⟨correlationSymb, [learner, correlated]⟩)) ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩)) ⇒ᶠ
            ∃ᶠ fun witnessed =>
              ↕ᶠ (ofEvent ⟨voteSymb, [learner, witnessed]⟩))
      (v := l₂) hVoteCorrLocal
  have hVoteCorrFor₂ :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun correlated => ∀ᶠ fun value =>
        (predicate0 liveSymb ∧ᶠ
            (⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, correlated]⟩)) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩)) ⇒ᶠ
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩))
      (v := l₁) hVoteCorrFor₁
  have hVoteCorrFor₃ :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value =>
        (predicate0 liveSymb ∧ᶠ
            (⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, value]⟩)) ⇒ᶠ
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩))
      (v := v) hVoteCorrFor₂
  simpa [voteForwardCorrelatedAxiom] using hVoteCorrFor₃

/-- Helper: Chain two forall eliminations for vote forward axiom -/
theorem forall_elim_vote_forward_chain
    {w : World P (Signature.EventType S)}
    {l v : Signature.Value S}
    (hVoteLocal : ⟪w⟫ ⊨[M]voteForwardAxiom liveSymb echoSymb voteSymb) :
    ⟪w⟫ ⊨[M]
      (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
        ∃ᶠ fun witnessed =>
          ↕ᶠ (ofEvent ⟨voteSymb, [l, witnessed]⟩) := by
  have hImpLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner =>
        ∀ᶠ fun value =>
          (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
            ∃ᶠ fun witnessed =>
              ↕ᶠ (ofEvent ⟨voteSymb, [learner, witnessed]⟩))
      (v := l) hVoteLocal
  have hImpValue :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value =>
        (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]](ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l, witnessed]⟩))
      (v := v) hImpLearner
  exact hImpValue

/-- Helper: Lift local `↕vote` to global `◊↓vote` using subset reasoning -/
theorem lift_local_vote_to_global
    {t : World P (Signature.EventType S)}
    {l v : Signature.Value S}
    (ht : t.time ⪯ M.history.val)
    (hVote : ⟪t⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩)) :
    ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩) := by
  have hSubset_trn :
      t.time ⊆trn M.history.val :=
    ModalDistribution.Logic.time_subset_trn_history
      (M := M) (t := t) ht
  intro p
  simpa using
    (sat_diamondPast_nil_event_subset (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (w' := t)
      (symb := voteSymb)
      (args := [l, v])
      (hSubset := hSubset_trn)
      hVote)

/-- Helper: Unpack existential vote witness and lift to global diamond -/
theorem vote_exists_to_global_diamond
    {t : World P (Signature.EventType S)}
    {l v : Signature.Value S}
    (hVote : ⟪t⟫ ⊨[M]↕ᶠ(ofEvent ⟨voteSymb, [l, v]⟩)) :
    ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩) := by
  have hSometimeVote :=
    (Sat.sometime (M := M) (w := t)
        (φ := ofEvent ⟨voteSymb, [l, v]⟩)).1 hVote
  obtain ⟨tVote, htVote_mem, htVote_place, hVote_event⟩ := hSometimeVote
  intro p
  have hPastVote :
      ⟪⟨tVote.place, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩) := by
    refine
      (Sat.past (M := M)
          (w := ⟨tVote.place, †, M.history.val⟩)
          (φ := ofEvent ⟨voteSymb, [l, v]⟩)).2 ?_
    refine ⟨tVote, htVote_mem, rfl, hVote_event⟩
  have hDiamondTop :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ♢ᶠ[[]](↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) :=
    (Sat.diamond_nil (M := M)
        (w := ⟨p, †, M.history.val⟩)
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).2
      ⟨tVote.place, hPastVote⟩
  simpa [Formula.diamondPast] using hDiamondTop

/-- Helper: splits the compound antecedent, obtains symmetric correlation,
and rebuilds the antecedent with swapped learners. -/
theorem split_and_swap_correlation
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {t : World P (Signature.EventType S)}
    {l₁ l₂ : Signature.Value S}
    {v : Signature.Value S}
    (hAnte : ⟪t⟫ ⊨[M]((predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))) :
    ⟪t⟫ ⊨[M]
      ((predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) := by
  -- Split antecedent into live, correlation, and vote components
  have ⟨hLive, hCorr₁, hVote₁⟩ :=
    split_live_corr_vote_antecedent (M := M)
      (liveSymb := liveSymb) (correlationSymb := correlationSymb) (voteSymb := voteSymb)
      (w := t) (l₁ := l₁) (l₂ := l₂) (v := v) hAnte
  -- Get symmetric correlation
  have hCorr₂ :=
    always_corr_symm (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      (hTheory := hTheory) (w := t)
      (l₁ := l₁) (l₂ := l₂) hCorr₁
  -- Build swapped antecedent
  have hLiveCorrSym :=
    (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩))).2
      ⟨hLive, hCorr₂⟩
  exact
    (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩))
        (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).2
      ⟨hLiveCorrSym, hVote₁⟩

/-- Helper: applies the voteForwardCorrelatedAxiom via forall elimination
and extracts the witness value from the existential. -/
theorem apply_vote_corr_and_extract_witness
    {t : World P (Signature.EventType S)}
    {l₁ l₂ : Signature.Value S}
    {v : Signature.Value S}
    (hVoteCorrLocal : ⟪t⟫ ⊨[M](voteForwardCorrelatedAxiom liveSymb voteSymb correlationSymb))
    (hVoteAnte : ⟪t⟫ ⊨[M]((predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))) :
    ∃ v₂ : Signature.Value S,
      ⟪t⟫ ⊨[M] (↕ᶠ (ofEvent ⟨voteSymb, [l₂, v₂]⟩)) := by
  -- Apply vote correlation axiom via forall elimination chain
  have hVoteImp :=
    (Sat.imp (M := M) (w := t)
        (φ :=
          ((predicate0 liveSymb ∧ᶠ
                ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)))
        (ψ :=
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩))).1
      (forall_elim_vote_correlated_chain (M := M)
        (liveSymb := liveSymb) (voteSymb := voteSymb) (correlationSymb := correlationSymb)
        (w := t) (l₁ := l₁) (l₂ := l₂) (v := v) hVoteCorrLocal)
  have hVoteExists := hVoteImp hVoteAnte
  -- Extract witness value
  exact
    (sat_exists_iff (M := M) (w := t)
        (body := fun witnessed =>
          ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩))).1
      hVoteExists

/-- Helper: lifts both votes to global and applies agreement to prove
the values are equal. -/
theorem agree_on_correlated_votes
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {t : World P (Signature.EventType S)}
    (ht : t.time ⪯ M.history.val)
    {l : Signature.Value S}
    {l₁ l₂ : Signature.Value S}
    {v v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hVote₁ : ⟪t⟫ ⊨[M](♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)))
    (hVote₂ : ⟪t⟫ ⊨[M](↕ᶠ(ofEvent ⟨voteSymb, [l₂, v₂]⟩))) :
    v = v₂ := by
  -- Lift both votes to global
  have hVote₁_global :=
    lift_local_vote_to_global (M := M)
      (voteSymb := voteSymb)
      (t := t) (l := l₁) (v := v) ht hVote₁
  have hVote₂_global :=
    vote_exists_to_global_diamond (M := M)
      (voteSymb := voteSymb)
      (t := t) (l := l₂) (v := v₂) hVote₂
  -- Apply agreement lemma
  exact
    votes_eventually_agree (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb) (echoSymb := echoSymb)
      (voteSymb := voteSymb) (deliverSymb := deliverSymb)
      (correlationSymb := correlationSymb)
      (hTheory := hTheory)
      (l := l) (l₁ := l₁) (l₂ := l₂)
      (v₁ := v) (v₂ := v₂)
      (hSeq := hSeq)
      (hVote₁ := hVote₁_global) (hVote₂ := hVote₂_global)

/-- correlated live knowledge of a vote
forces eventual votes for the correlated learner. -/
theorem correlated_vote_eventually
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l : Signature.Value S}
    {l₁ l₂ : Signature.Value S}
    {v : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq) :
    □W⊨[M]
      (((predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) ⇒ᶠ
        ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩)) := by
  classical
  have hVoteCorrAx :
      AllWorldValid M
        (voteForwardCorrelatedAxiom liveSymb voteSymb correlationSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  intro t ht
  have hVoteCorrLocal := hVoteCorrAx ht
  refine
    Sat.imp_intro (M := M) (w := t)
      (φ :=
        ((predicate0 liveSymb ∧ᶠ
              ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)))
      (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩)) ?_
  intro hAnte
  -- Split antecedent and swap correlation
  have hVoteAnte := split_and_swap_correlation hTheory hAnte
  -- Extract original vote for agreement
  have hVote₁ :=
    (split_live_corr_vote_antecedent (M := M)
      (liveSymb := liveSymb) (correlationSymb := correlationSymb) (voteSymb := voteSymb)
      (w := t) (l₁ := l₁) (l₂ := l₂) (v := v) hAnte).2.2
  -- Apply axiom and extract witness
  obtain ⟨v₂, hVote₂⟩ := apply_vote_corr_and_extract_witness hVoteCorrLocal hVoteAnte
  -- Prove values agree
  have hValueEq : v = v₂ :=
    agree_on_correlated_votes hTheory ht hSeq hVote₁ hVote₂
  cases hValueEq
  simpa using hVote₂

/-- Helper: applies the voteForwardAxiom via forall elimination
and extracts the witness value from the existential. -/
theorem apply_vote_forward_and_extract_witness
    {t : World P (Signature.EventType S)}
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hVoteLocal : ⟪t⟫ ⊨[M](voteForwardAxiom liveSymb echoSymb voteSymb))
    (hLive : ⟪t⟫ ⊨[M](predicate0 liveSymb))
    (hEchoLocal : ⟪t⟫ ⊨[M](□ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))) :
    ∃ v₂ : Signature.Value S,
      ⟪t⟫ ⊨[M] (↕ᶠ (ofEvent ⟨voteSymb, [l, v₂]⟩)) := by
  -- Apply vote forward axiom via forall elimination chain
  have hVoteImp :=
    (Sat.imp (M := M) (w := t)
        (φ :=
          predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))
        (ψ :=
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l, witnessed]⟩))).1
      (forall_elim_vote_forward_chain (M := M)
        (liveSymb := liveSymb) (echoSymb := echoSymb) (voteSymb := voteSymb)
        (w := t) (l := l) (v := v) hVoteLocal)
  have hVoteAnte' :=
    (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))).2
      ⟨hLive, hEchoLocal⟩
  have hVoteExists := hVoteImp hVoteAnte'
  -- Extract witness value
  exact
    (sat_exists_iff (M := M) (w := t)
        (body := fun witnessed =>
          ↕ᶠ (ofEvent ⟨voteSymb, [l, witnessed]⟩))).1
      hVoteExists

/-- Helper: lifts vote to global, extracts echo source, applies agreement,
and returns simplified result. -/
theorem agree_on_echo_and_vote
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {t : World P (Signature.EventType S)}
    (hSubset : t.time ⊆ M.history.val)
    {l : Signature.Value S}
    {v v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hEchoLocal : ⟪t⟫ ⊨[M](□ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩)))
    (hVote₂ : ⟪t⟫ ⊨[M](↕ᶠ(ofEvent ⟨voteSymb, [l, v₂]⟩))) :
    ⟪t⟫ ⊨[M] (↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
  -- Lift echo to global
  have hEchoGlobal :=
    lift_boxPast_to_end (M := M)
      (t := t) (learner := l)
      (φ := ofEvent ⟨echoSymb, [v]⟩)
      (hSubset := hSubset) (hBox := hEchoLocal)
  -- Lift vote to global
  have hVote₂_global :=
    vote_exists_to_global_diamond (M := M)
      (voteSymb := voteSymb)
      (t := t) (l := l) (v := v₂) hVote₂
  -- Extract echo source from vote
  obtain ⟨sourceEcho, hEchoVote⟩ :=
    vote_implies_echo_quorum_end
      (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      (hTheory := hTheory)
      (learner := l) (value := v₂)
      (hVote := hVote₂_global)
  -- Apply echo agreement
  have hValueEq' : v = v₂ :=
    echo_quorums_agree (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      (hTheory := hTheory)
      (l := l) (l₁ := l) (l₂ := sourceEcho)
      (v₁ := v) (v₂ := v₂)
      (hSeq := hSeq)
      (hEcho₁ := hEchoGlobal)
      (hEcho₂ := hEchoVote)
  have hValueEq : v₂ = v := hValueEq'.symm
  simpa [hValueEq] using hVote₂

/-- a live echo quorum yields eventual
votes for the same learner. -/
theorem live_echo_eventually_vote
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq) :
    □W⊨[M]
      ((predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
        ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
  classical
  have hVoteAx : AllWorldValid M (voteForwardAxiom liveSymb echoSymb voteSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  intro t htMem
  have hVoteLocal := hVoteAx htMem
  refine
    Sat.imp_intro (M := M) (w := t)
      (φ :=
        predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))
      (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) ?_
  intro hAnte
  -- Split antecedent
  have hLiveEcho :=
    (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))).1 hAnte
  have hLive := hLiveEcho.1
  have hEchoLocal := hLiveEcho.2
  -- Compute subset for later use
  have hSubset_history_trn :
      t.time ⊆trn M.history.val :=
    ModalDistribution.Logic.time_subset_trn_history
      (M := M) (t := t) htMem
  have hSubset_history : t.time ⊆ M.history.val :=
    History.transitiveSubset_subset hSubset_history_trn
  -- Apply axiom and extract witness
  obtain ⟨v₂, hVote₂⟩ := apply_vote_forward_and_extract_witness hVoteLocal hLive hEchoLocal
  -- Prove values agree and simplify
  exact agree_on_echo_and_vote hTheory hSubset_history hSeq hEchoLocal hVote₂

/-- if someone believes `l₁` correlates
with `l₂`, then their quorums intersect. -/
theorem correlationImpliesPairwiseQuorumIntersection
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    (hHistory : ∃ t : World P (Signature.EventType S), t ∈ M.history.val)
    {l₁ l₂ : Signature.Value S}
    (_hSomeone : ⊨[M]♢ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ := by
  classical
  -- The threeTwined axiom guarantees 3-learner quorum intersection.
  -- Since any triple [l₁, l₂, l₃] has intersecting quorums,
  -- the pair [l₁, l₂] (obtained by dropping l₃) must also intersect.

  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩

  -- To use `sat_diamond_top_iff_hasQuorumNonempty`, we need to show
  -- `hasQuorumNonempty (M := M) [l₁, l₂]`.

  -- Strategy: Use threeTwinedAxiom with any third learner to get 3-quorum intersection,
  -- then show this implies 2-quorum intersection.

  have hNonempty : hasQuorumNonempty (M := M) [l₁, l₂] := by
    -- Pick any third learner (we use l₁ itself).
    intro F
    -- F is a quorum family for [l₁, l₂], we extend it to a triple family
    -- by adding any quorum from l₁.
    have hSemi₁ : (M.learner l₁).quorums.Nonempty :=
      (M.learner l₁).nonempty
    obtain ⟨O₁, hO₁⟩ := hSemi₁
    -- Build a triple quorum family [l₁, l₁, l₂] by prepending O₁ to F.
    let F' := QuorumFamily.cons (l := l₁) (ls' := [l₁, l₂]) O₁ hO₁ F
    -- Use the threeTwined axiom with the history nonemptiness we just established.
    have hTripleNonempty :=
      threeTwined_hasQuorumNonempty
        (M := M) (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        hTheory hHistory (l₁ := l₁) (l₂ := l₁) (l₃ := l₂)
    -- Apply to our extended family F'.
    have hIntersect := hTripleNonempty F'
    obtain ⟨pWitness, hpAll⟩ := hIntersect
    -- The witness must be in both quorums from F (the tail of F').
    exact ⟨pWitness, fun i => by
      have := hpAll (Fin.succ i)
      simpa [F', QuorumFamily.cons] using this⟩

  exact (sat_diamond_top_iff_hasQuorumNonempty (M := M)
    (w := wTop) (ls := [l₁, l₂])).2 hNonempty

/-- Correlation implies quorum intersection

The three-twined axiom from ThyHBB3 guarantees that any pair of learners has
intersecting quorums, by exploiting the three-way intersection property. This
establishes the quorum intersection needed for agreement properties.

See also: `correlationEveryoneImpliesIntersection`,
`correlationImpliesPairwiseQuorumIntersection`. -/
theorem correlationImpliesQuorumIntersection
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    (hHistory : ∃ t : World P (Signature.EventType S), t ∈ M.history.val)
    {l₁ l₂ : Signature.Value S} :
    ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ := by
  classical
  -- The threeTwined axiom guarantees 3-learner quorum intersection.
  -- Since any triple [l₁, l₂, l₃] has intersecting quorums,
  -- the pair [l₁, l₂] (obtained by dropping l₃) must also intersect.

  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩

  -- To use `sat_diamond_top_iff_hasQuorumNonempty`, we need to show
  -- `hasQuorumNonempty (M := M) [l₁, l₂]`.

  -- Strategy: Use threeTwinedAxiom with any third learner to get 3-quorum intersection,
  -- then show this implies 2-quorum intersection.

  have hNonempty : hasQuorumNonempty (M := M) [l₁, l₂] := by
    -- Pick any third learner (we use l₁ itself).
    intro F
    -- F is a quorum family for [l₁, l₂], we extend it to a triple family
    -- by adding any quorum from l₁.
    have hSemi₁ : (M.learner l₁).quorums.Nonempty :=
      (M.learner l₁).nonempty
    obtain ⟨O₁, hO₁⟩ := hSemi₁
    -- Build a triple quorum family [l₁, l₁, l₂] by prepending O₁ to F.
    let F' := QuorumFamily.cons (l := l₁) (ls' := [l₁, l₂]) O₁ hO₁ F
    -- Use the threeTwined axiom with the history nonemptiness we just established.
    have hTripleNonempty :=
      threeTwined_hasQuorumNonempty
        (M := M) (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        hTheory hHistory (l₁ := l₁) (l₂ := l₁) (l₃ := l₂)
    -- Apply to our extended family F'.
    have hIntersect := hTripleNonempty F'
    obtain ⟨pWitness, hpAll⟩ := hIntersect
    -- The witness must be in both quorums from F (the tail of F').
    exact ⟨pWitness, fun i => by
      have := hpAll (Fin.succ i)
      simpa [F', QuorumFamily.cons] using this⟩

  exact (sat_diamond_top_iff_hasQuorumNonempty (M := M)
    (w := wTop) (ls := [l₁, l₂])).2 hNonempty

/-- Universal correlation implies intersection

Universal correlation (□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) also guarantees
quorum intersection for learners l₁ and l₂. The universal box assumption is
actually stronger than needed - quorum intersection follows from the three-twined
axiom alone.

See also: `correlationImpliesQuorumIntersection`, `correlationImpliesPairwiseQuorumIntersection`. -/
theorem correlationEveryoneImpliesIntersection
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    (hHistory : ∃ t : World P (Signature.EventType S), t ∈ M.history.val)
    {l₁ l₂ : Signature.Value S}
    (hEveryone : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ := by
  -- The universal correlation assumption is not needed for the proof.
  -- Quorum intersection follows directly from threeTwinedAxiom via
  -- correlationImpliesQuorumIntersection, which doesn't use the correlation predicate.'
  have hSomeone : ⊨[M]♢ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) := by
    intro p
    -- hEveryone p gives us: ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ[]...
    have hBox := hEveryone p
    -- □ᶠ[] means the predicate holds for all participants
    have hAll := (Sat.boxEmpty (M := M)
    (w := ⟨p, †, M.history.val⟩)
    (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)).1 hBox
    -- Pick any participant (use p itself) to witness the diamond
    refine (Sat.diamondEmpty (M := M)
    (w := ⟨p, †, M.history.val⟩)
    (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)).2 ?_
    exact ⟨p, hAll p⟩
    -- Apply the "someone" version
  exact correlationImpliesPairwiseQuorumIntersection hTheory hHistory hSomeone

end ThyHBB3
end Examples
end ModalDistribution
