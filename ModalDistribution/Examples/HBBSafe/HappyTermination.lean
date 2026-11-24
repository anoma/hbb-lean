import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBSafe.Agreement
import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Examples.HBBSafe.Safety
import ModalDistribution.Examples.HBBSafe.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBSafe Happy Termination

This file contains the Happy Termination theorem for the HBBSafe broadcast protocol:

- **Happy Termination** (`happyTermination`): Under uniqueness of proposals and a live quorum,
  if a live participant knows a proposal, it will eventually be delivered.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSafe

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

section HappyTermination

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 6.6.3 (Happy Termination). Happy Termination for HBBSafe.

Under uniqueness of proposals and a live quorum, if a live participant knows
a proposal for value v, then v will eventually be delivered. This establishes
that proposals from live participants will eventually propagate to delivery.

See also: `cascadeTermination`, `happyTermination_boxPast`. -/
theorem happyTermination
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

  -- Fragments of `ThyLive` used throughout the derivation.
  have hThyLiveTheory : M ⊨ᵀ ThyLive liveSymb :=
    theory_thyLive (M := M) hTheory

  -- Lemma 6.6.1, Proposition 5.2.8, (Echo?) with Lemma 4.2.2,
  -- Lemma 6.5.2(2) and Lemma 5.2.11: a live `l`-quorum knows of an
  -- `l`-quorum of echoes of `v`.
  have hStep3Global :
      ⊨[M]□ᶠ↓[[l]]
        (predicate0 liveSymb ∧ᶠ □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
    uniquePropose_live_nestedEcho_quorum (M := M)
      (hLiveTheory := hThyLiveTheory)
      (hEcho := theory_echoForward (M := M) hTheory)
      (hEchoBack := theory_echoBackward (M := M) hTheory)
      (hLiveQuorum := hLiveQuorum) (hUnique := hUnique)
      (hKnown := diamondPast_nil_valid_of_end (M := M)
        (by simpa [wTop] using hPropose))

  -- Global guard: uniqueness of proposals enforces the at-most-one constraint.
  have hGuardGlobal :
      ⊨[M] ∃≤ᶠ1 w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩) := by
    intro q
    exact
      uniquePropose_guard_at_history
        (M := M) (proposeSymb := proposeSymb)
        (w := ⟨q, †, M.history.val⟩)
        (hUnique := hUnique q)

  -- Step 4 (Lemma 6.6.2): with at most one proposal, every learner is
  -- everywhere and always safe.
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

  -- Step 5 (Lemma 6.5.2(2) with (Vote!)): the live echo quorum becomes a
  -- live vote quorum.
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

  -- Step 6 (Lemma 6.5.3, applied to (Knowledge□↓) and (Deliver!)):
  -- eventual vote knowledge becomes eventual delivery.
  have hDeliverImp :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
    have hDeliverEventually :=
      live_quorum_eventually_consequent (M := M)
        (hLiveTheory := hThyLiveTheory)
        (hQuorum := hVotesGlobal)
        (hImp := HBB.deliverForward_imp (M := M)
          (theory_deliverForward (M := M) hTheory))
    simpa [wTop] using hDeliverEventually p

  -- Final application of the implication at participant `p`.
  exact
    Sat.imp_elim (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩))
      hDeliverImp hLivep

/-- Paper: Proposition 6.6.3, first corollary. Whenever a live learner
observes the guarded proposal diamond, every member of its quorum knows (in the
past) that the corresponding value was delivered. -/
theorem happyTermination_boxPast
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
      happyTermination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (l := l) (v := v)
        (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum)
        (hUnique := hUnique))
/-- Paper: Proposition 6.6.3, second corollary. Witnessing the guarded
proposal diamond guarantees the delivery diamond for learner `l`. -/
theorem happyTermination_diamondPast
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
      happyTermination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (l := l) (v := v)
        (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum)
        (hUnique := hUnique))
end HappyTermination
end HBBSafe
end Examples
end ModalDistribution
