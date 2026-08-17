import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB1.Agreement
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties.Modalities

/-!
# ThyHBB1 Liveness Properties

This file contains the liveness one theorem for the ThyHBB1 broadcast protocol:

- **Liveness 1** (`livenessOne`): Under uniqueness of proposals and a live quorum,
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

See also: `livenessTwo`, `livenessOne_boxPast`. -/
theorem livenessOne
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

  -- Fragments of `ThyLive` used throughout the derivation.
  have hThyLiveTheory : M ⊨ᵀ ThyLive liveSymb :=
    theory_thyLive (M := M) hTheory

  have hLiveBox : ⊨[M]□ᶠ[id [l]] predicate0 liveSymb := by
    simpa using hLiveQuorum

  -- Step 1: lift the local knowledge into learner `l`'s quorum.
  have hPastWitness :
      ∃ qProp : P,
        ⟪⟨qProp, †, M.history.val⟩⟫ ⊨[M]
          ↓ᶠ ((predicate0 liveSymb) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) := by
    obtain ⟨qProp, hPastProp⟩ :=
      (Sat.diamond_nil (M := M)
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

  have hStep2Global :
      ⊨[M] □ᶠ↓[[l]] φLiveEcho := by
    have hImpEcho :
        □W⊨[M]
          (φLivePropose ⇒ᶠ ↕ᶠ (ofEvent ⟨echoSymb, [v]⟩)) :=
      uniquePropose_eventually_echo
        (M := M) (liveSymb := liveSymb)
        (proposeSymb := proposeSymb) (echoSymb := echoSymb)
        (value := v)
        (hEcho := theory_echoForward (M := M) hTheory)
        (hEchoBack := theory_echoBackward (M := M) hTheory)
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

  -- Step 3: promote echoes to nested quorum knowledge.
  have hStep3Global :
      ⊨[M] □ᶠ↓[[l]] φLiveNestedEcho :=
    _root_.ModalDistribution.Examples.live_boxPast_nests
      (M := M) (liveSymb := liveSymb)
      (l := l) (φ := ofEvent ⟨echoSymb, [v]⟩)
      (hTheory := hThyLiveTheory)
      (hQuorum := hStep2Global)

  -- Lemma 6.5.2: with at most one proposal, every learner is everywhere and
  -- always safe.
  have hSafeAlwaysGlobal :
      □W⊨[M] ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
    have hSafeEnd : ⊨[M] ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
      intro q
      exact
        Sat.imp_elim (M := M) (w := ⟨q, †, M.history.val⟩)
          (φ := ∃≤ᶠ1 w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩))
          (ψ := ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩))
          (atMostOnePropose_safe (M := M)
            (hTheory := hTheory) (l := l) q)
          (hGuardGlobal q)
    intro t _
    refine (Sat.everytime (M := M) (w := t)
      (φ := ofPredicate ⟨safeSymb, [l]⟩)).2 ?_
    intro st hst hpl
    exact
      (Sat.everytime (M := M)
        (w := ⟨t.place, †, M.history.val⟩)
        (φ := ofPredicate ⟨safeSymb, [l]⟩)).1
        (by simpa using hSafeEnd t.place) st hst (by simpa using hpl)

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
      (hImp := voteForward_imp_of_everytime (M := M)
        (hTheory := hTheory)
        (hSafeAlways := hSafeAlwaysGlobal))

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
    exact
      live_sometime_consequent_at (M := M)
        (hLiveTheory := hThyLiveTheory)
        (hImp := HBB.deliverForward_imp (M := M)
          (theory_deliverForward (M := M) hTheory))
        hLiveTop hVotesTop

  -- Final application of the implication at participant `p`.
  exact
    Sat.imp_elim (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩))
      step7 hLivep

/-- Paper: Proposition 6.5.3, first corollary. Whenever a live learner
observes the guarded proposal diamond, every member of its quorum knows (in the
past) that the corresponding value was delivered. -/
theorem livenessOne_boxPast
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
      livenessOne (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (l := l) (v := v)
        (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum)
        (hUnique := hUnique))
/-- Paper: Proposition 6.5.3, second corollary. Witnessing the guarded
proposal diamond guarantees the delivery diamond for learner `l`. -/
theorem livenessOne_diamondPast
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
      livenessOne (M := M)
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
