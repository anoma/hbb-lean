import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB1.Agreement
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Examples.ThyHBB1.LivenessHelpers
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties.Modalities

/-!
# ThyHBB1 Liveness Properties

This file contains the liveness one theorem for the ThyHBB1 broadcast protocol:

- **Liveness 1** (`livenessOneThyHBB1`): Under uniqueness of proposals and a live quorum,
  if a live participant knows a proposal, it will eventually be delivered.
  Liveness property 1: under uniqueness, live proposals are eventually delivered.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB1

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

section Liveness_One

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 6.5.3 (Liveness 1). Liveness One for ThyHBB1 (Liveness property 1).

Under uniqueness of proposals and a live quorum, if a live participant knows
a proposal for value v, then v will eventually be delivered. This establishes
that proposals from live participants will eventually propagate to delivery.

See also: `livenessTwoThyHBB1`, `livenessOneAtPastDownThyHBB1`. -/
theorem livenessOneThyHBB1
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M](♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
         predicate0 liveSymb ⇒ᶠ
         ↕ᶠ(ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hPropose
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLivep

  -- Abbreviations for the staged liveness argument.
  let φLivePropose :=
    predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)
  let φLiveEcho :=
    predicate0 liveSymb ∧ᶠ ofEvent ⟨echoSymb, [v]⟩
  let φLiveNestedEcho :=
    predicate0 liveSymb ∧ᶠ □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)
  let φLiveVote :=
    predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [l, v]⟩
  let φSafe := safeFormula proposeSymb l

  -- Fragments of `ThyLive` used throughout the derivation.
  have hThyLiveTheory : M ⊨ᵀ ThyLive liveSymb := by
    intro ax hAx
    exact hTheory (Or.inl hAx)

  have hLiveBox : ⊨[M]□ᶠ[id [l]] predicate0 liveSymb := by
    simpa using hLiveQuorum

  -- Step 1: lift the local knowledge into learner `l`'s quorum.
  have hPastWitness :
      ∃ qProp : P,
        ⟪⟨qProp, †, M.history.val⟩⟫ ⊨[M]
          ↓ᶠ ((predicate0 liveSymb) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) := by
    obtain ⟨qProp, hPastProp⟩ :=
      (Sat.Sat_diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ ((predicate0 liveSymb) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)))).1
        (by simpa [Formula.diamondPast] using hPropose)
    refine ⟨qProp, ?_⟩
    simpa [wTop] using hPastProp

  have hEventGlobal :
      ⊨[M]
        ♢ᶠ↓[[]]
          ((predicate0 liveSymb) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) := by
    intro q
    have hDiamond :=
      sat_diamondEmpty_of_local (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := ↓ᶠ ((predicate0 liveSymb) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)))
        hPastWitness
    simpa [Formula.diamondPast] using hDiamond

  have hStep1Global :
      ⊨[M] □ᶠ↓[[l]] φLivePropose := by
    intro q
    have hQuorumBox :=
      live_eventually_knows_event
        (M := M) (liveSymb := liveSymb)
        (l := l) (evt := ⟨proposeSymb, [v]⟩)
        (hTheory := hThyLiveTheory)
        (hLive := hLiveBox)
        (hEvent := hEventGlobal)
    simpa [φLivePropose] using hQuorumBox q

  have step1 :
      ⟪wTop⟫ ⊨[M] □ᶠ↓[[l]] φLivePropose := by
    simpa [wTop] using hStep1Global p

  -- Step 2: unique proposals imply eventual echoes.
  have hStep2Global :
      ⊨[M] □ᶠ↓[[l]] φLiveEcho := by
    have hImpEcho :
        □W⊨[M]
          (φLivePropose ⇒ᶠ ↕ᶠ (ofEvent ⟨echoSymb, [v]⟩)) :=
      uniquePropose_eventually_echo
        (M := M) (liveSymb := liveSymb)
        (proposeSymb := proposeSymb) (echoSymb := echoSymb)
        (value := v)
        (hEcho := by
          apply hTheory
          simp [theory])
        (hEchoBack := by
          apply hTheory
          simp [theory])
        (hUnique := hUnique)
    exact
      boxPast_live_of_eventual_quorum
        (M := M) (liveSymb := liveSymb)
        (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
        (ψ := ofEvent ⟨echoSymb, [v]⟩)
        (l := l)
        (hLiveTheory := hThyLiveTheory)
        (hQuorum := hStep1Global)
        (hImp := hImpEcho)

  -- Global guard: uniqueness of proposals enforces the at-most-one constraint.
  have hGuardGlobal :
      ⊨[M] ∃≤ᶠ1 w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩) := by
    intro q
    exact
      uniquePropose_guard_at_history
        (M := M) (proposeSymb := proposeSymb)
        (w := ⟨q, †, M.history.val⟩)
        (hUnique := hUnique q)

  -- Every learner is safe under the uniqueness hypothesis.
  have hSafeGlobal : ⊨[M] φSafe := by
    intro q
    have hImp :=
      atMostOnePropose_safeFormula
        (M := M) (proposeSymb := proposeSymb)
        (l := l) q
    exact
      (Sat.imp (M := M) (w := ⟨q, †, M.history.val⟩)
        (φ := ∃≤ᶠ1 w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩))
        (ψ := φSafe)).1
        hImp (hGuardGlobal q)

  have step2 :
      ⟪wTop⟫ ⊨[M] □ᶠ↓[[l]] φLiveEcho := by
    simpa [wTop] using hStep2Global p

  -- Step 3: promote echoes to nested quorum knowledge.
  have hStep3Global :
      ⊨[M] □ᶠ↓[[l]] φLiveNestedEcho :=
    _root_.ModalDistribution.Examples.live_boxPast_nests
      (M := M) (liveSymb := liveSymb)
      (l := l) (φ := ofEvent ⟨echoSymb, [v]⟩)
      (hTheory := hThyLiveTheory)
      (hQuorum := hStep2Global)

  have step3 :
      ⟪wTop⟫ ⊨[M] □ᶠ↓[[l]] φLiveNestedEcho := by
    simpa [wTop] using hStep3Global p

  -- Step 4: combine nested echoes with safety.
  have step4 :
      ⟪wTop⟫ ⊨[M]
        (□ᶠ↓[[l]] φLiveNestedEcho) ∧ᶠ ⇕ᶠ φSafe := by
    classical
    have hSafeAtTop : ⟪wTop⟫ ⊨[M] φSafe := by
      simpa [wTop] using hSafeGlobal p
    have hSubsetHistory :
        (World.time wTop) ⊆trn M.history.val := by
      simpa [wTop, World.time]
        using History.transitiveSubset_refl (H := M.history)
    have hSafeAlwaysTop :
        ⟪wTop⟫ ⊨[M] ⇕ᶠ φSafe := by
      refine
        (Sat.not_intro (M := M) (w := wTop)
          (φ := ↕ᶠ (¬ᶠ φSafe)) ?_)
      intro hSome
      obtain ⟨t, ht_mem, ht_place, hNotSafe⟩ :=
        (Sat.sometime (M := M) (w := wTop)
          (φ := ¬ᶠ φSafe)).1 hSome
      have hAcc : t ≪⁻ wTop := by
        refine ⟨?_, ?_⟩
        · simpa [wTop, World.time] using ht_mem
        · simpa [wTop, World.place] using ht_place
      have hBefore :
          t.time ⪯ wTop.time :=
        PreHistory.happensBeforeEq_of_accessible
          (P := P) (Event := Signature.EventType S) hAcc.1
      have hSafe_t : ⟪t⟫ ⊨[M] φSafe :=
        safeFormula_monotone_subset
          (M := M)
          (w := wTop) (w' := t)
          (l := l)
          (hSubset := hSubsetHistory)
          (hBefore := by
            simpa [wTop, World.time] using hBefore)
          (hPlace := by
            simpa [wTop, World.place] using hAcc.2)
          (hSafe := hSafeAtTop)
      exact
        (Sat.not_elim (M := M) (w := t) (φ := φSafe))
          hNotSafe hSafe_t
    exact
      (Sat.and (M := M) (w := wTop)
        (φ := □ᶠ↓[[l]] φLiveNestedEcho)
        (ψ := ⇕ᶠ φSafe)).2
        ⟨step3, hSafeAlwaysTop⟩

  -- Step 5: obtain votes for learner `l`.
  classical

  have hVoteForwardAx :
      AllWorldValid M
        (voteForwardAxiom liveSymb safeSymb echoSymb voteSymb) := by
    apply hTheory
    simp [theory]

  have hImpVotes :
      □W⊨[M]
        ((predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
    intro t ht_mem
    have hForward := hVoteForwardAx ht_mem
    have hLearner :=
      Sat.forall_elim (M := M) (w := t)
        (body := fun learner =>
          ∀ᶠ (fun value =>
            (⇕ᶠ (ofPredicate ⟨safeSymb, [learner]⟩)) ⇒ᶠ
              ((predicate0 liveSymb ∧ᶠ
                  □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
                ↕ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩))))
        (v := l)
        (by simpa [voteForwardAxiom] using hForward)
    have hValue :=
      Sat.forall_elim (M := M) (w := t)
        (body := fun value =>
          (⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩)) ⇒ᶠ
            ((predicate0 liveSymb ∧ᶠ
                □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
              ↕ᶠ (ofEvent ⟨voteSymb, [l, value]⟩)))
        (v := v) hLearner

    have hSafeTop :
        ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M] φSafe := by
      simpa [World.place, World.time]
        using hSafeGlobal t.place
    have hSubsetTop :
        (World.time ⟨t.place, †, M.history.val⟩) ⊆trn M.history.val := by
      simpa [World.time]
        using History.transitiveSubset_refl (H := M.history)
    have hSafeLocal : ⟪t⟫ ⊨[M] φSafe :=
      safeFormula_monotone_subset
        (M := M)
        (w := ⟨t.place, †, M.history.val⟩)
        (w' := t)
        (l := l)
        (hSubset := hSubsetTop)
        (hBefore := by
          simpa [World.time] using ht_mem)
        (hPlace := rfl)
        (hSafe := hSafeTop)

    have hSafeAlways : ⟪t⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
      refine
        Sat.not_intro (M := M) (w := t)
          (φ := ↕ᶠ (¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))) ?_
      intro hSome
      obtain ⟨s, hs_mem, hs_place, hNotSafe⟩ :=
        (Sat.sometime (M := M) (w := t)
          (φ := ¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))).1 hSome
      have hAcc_s : s ≪⁻ ⟨t.place, †, M.history.val⟩ :=
        ⟨by
            simpa [World.time]
              using hs_mem,
          by
            simpa [World.place]
              using hs_place⟩
      have hSafe_s : ⟪s⟫ ⊨[M] φSafe :=
        safeFormula_monotone_subset
          (M := M)
          (w := ⟨t.place, †, M.history.val⟩)
          (w' := s)
          (l := l)
          (hSubset := hSubsetTop)
          (hBefore :=
            by
              simpa [World.time] using
                PreHistory.happensBeforeEq_of_accessible
                  (P := P) (Event := Signature.EventType S)
                  hAcc_s.1)
          (hPlace := by
            simpa [World.place] using hAcc_s.2)
          (hSafe := hSafeTop)
      have hs_le : s.time ⪯ M.history.val :=
        PreHistory.happensBeforeEq_of_mem
          (P := P) (Event := Signature.EventType S)
          (hmem := by
            simpa [World.place, World.event, World.time] using hs_mem)
      have hSafePred_s :
          ⟪s⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩ :=
        (safe_iff_safeFormula (M := M) (hTheory := hTheory)
          (w := s) hs_le l).2 (by simpa [φSafe] using hSafe_s)
      exact
        (Sat.not_elim (M := M) (w := s)
          (φ := ofPredicate ⟨safeSymb, [l]⟩))
          hNotSafe hSafePred_s

    have hGuard :
        ⟪t⟫ ⊨[M]
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩) :=
      (Sat.imp (M := M) (w := t)
        (φ := ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩))
        (ψ := (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).1
        (by simpa [φSafe] using hValue)
        hSafeAlways

    refine
      (Sat.imp (M := M) (w := t)
        (φ := predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
        (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).2 ?_
    intro hConj
    have hConjSplit :=
      (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).1 hConj
    have hLive := hConjSplit.1
    have hLiveBox :=
      (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).2
        ⟨hLive, hConjSplit.2⟩
    exact
      (Sat.imp (M := M) (w := t)
        (φ := predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
        (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).1
        hGuard hLiveBox

  have hVotesGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩) :=
    boxPast_live_of_eventual_quorum
      (M := M) (liveSymb := liveSymb)
      (φ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
      (ψ := ofEvent ⟨voteSymb, [l, v]⟩)
      (l := l)
      (hLiveTheory := hThyLiveTheory)
      (hQuorum := hStep3Global)
      (hImp := hImpVotes)

  have step5 :
      ⟪wTop⟫ ⊨[M] □ᶠ↓[[l]] φLiveVote := by
    simpa [wTop, φLiveVote] using hVotesGlobal p

  -- Step 6 (Knowledge$\atddot{}$): a live participant eventually knows the votes.
  have step6 :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l]] (ofEvent ⟨voteSymb, [l, v]⟩)) := by
    classical
    have hKnow :=
      live_eventually_knows_box
        (M := M)
        (liveSymb := liveSymb)
        (l := l)
        (φ := ofEvent ⟨voteSymb, [l, v]⟩)
        (hTheory := hThyLiveTheory)
        (hQuorum := hVotesGlobal)
    simpa [wTop]
      using hKnow p

  -- Step 7: conclude eventual delivery.
  have step7 :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
    refine Sat.imp_intro (M := M) (w := wTop) ?_
    intro hLiveTop
    have hVotesTop :
        ⟪wTop⟫ ⊨[M]
          ↕ᶠ (□ᶠ↓[[l]] (ofEvent ⟨voteSymb, [l, v]⟩)) :=
      (Sat.imp (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (□ᶠ↓[[l]] (ofEvent ⟨voteSymb, [l, v]⟩)))).1
        step6 hLiveTop
    have hDeliverAx : AllWorldValid M
        (deliverForwardAxiom liveSymb voteSymb deliverSymb) := by
      apply hTheory
      simp [theory]
    exact
      deliver_from_vote_box
        (M := M)
        (liveSymb := liveSymb)
        (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (reporting := l) (learner := l) (value := v)
        (hThyLive := hThyLiveTheory)
        (hDeliverAx := hDeliverAx)
        (hLiveTop := hLiveTop)
        (hVotesTop := hVotesTop)

  -- Final application of the implication at participant `p`.
  exact
    Sat.imp_elim (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩))
      step7 hLivep

/-- Paper: Proposition 6.5.3, first corollary. Whenever a live learner
observes the guarded proposal diamond, every member of its quorum knows (in the
past) that the corresponding value was delivered. -/
theorem livenessOneAtPastDownThyHBB1
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M](♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
         □ᶠ↓[[l]] (ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLiveQuorum)
      (hMain :=
      livenessOneThyHBB1 (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (l := l) (v := v)
        (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum)
        (hUnique := hUnique))
/-- Paper: Proposition 6.5.3, second corollary. Witnessing the guarded
proposal diamond guarantees the delivery diamond for learner `l`. -/
theorem livenessOneAtPastThyHBB1
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M](♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLiveQuorum)
      (hMain :=
      livenessOneThyHBB1 (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (l := l) (v := v)
        (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum)
        (hUnique := hUnique))
end Liveness_One
end ThyHBB1
end Examples
end ModalDistribution
