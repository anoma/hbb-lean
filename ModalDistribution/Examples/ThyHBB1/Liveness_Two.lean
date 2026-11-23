import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB1.Agreement
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties.Modalities

/-!
# ThyHBB1 Liveness Properties

This file contains the two liveness two theorem for the ThyHBB1 broadcast protocol:

- **Liveness 2** (`livenessTwo`): If a value is delivered to one learner and certain
  liveness/intersection conditions hold, it will eventually be delivered to another learner.
  Liveness property 2: deliveries propagate across intersecting learner quorums.
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

section Liveness_Two

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 6.4.5 (Liveness 2). Liveness property 2 specialised to `ThyHBB1`.
If a value is delivered to learner l₁' and:
- Learners l₁' and l₂' have intersecting quorums
- The safe condition holds for learner l
- All of learner l₂'s quorum members are live
Then if p is live, the value will eventually be delivered to learner l₂'. -/
theorem livenessTwo
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         predicate0 liveSymb ⇒ᶠ
         ↕ᶠ(ofEvent ⟨deliverSymb, [l₂', l, v]⟩) := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLivep

  have hThyLiveTheory : M ⊨ᵀ ThyLive liveSymb :=
    theory_thyLive (M := M) hTheory

  -- (Deliver?) with Lemma 4.2.3(2): the delivery forces an end-of-time
  -- quorum of votes at the reporting learner.
  have hVoteBoxTop :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [l, v]⟩) := by
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := theory_deliverBackward (M := M) hTheory)
          (reporting := l₁') (learner := l)
          (value := v) (p := p)
          (hDeliver := hDeliver)
  have hVoteBoxGlobal :
      ⊨[M]□ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [l, v]⟩) := fun q => by
    simpa [wTop] using hVoteBoxTop

  -- Proposition 5.2.11: the intersecting live quorum exposes a live voter.
  have hLiveVote :
      ⊨[M]♢ᶠ↓[[]]
        ((predicate0 liveSymb) ∧ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
    have h :=
      intertwined_two_quorums (M := M)
        (liveSymb := liveSymb) (l := l₁') (l₁ := l₂')
        (φ := ofEvent ⟨voteSymb, [l, v]⟩)
        (hTheory := hThyLiveTheory)
        (hIntersect := by intro q; simpa using hIntersect q)
        (hLiveQuorum := by intro q; simpa using hLive q)
        (hWitness := by intro q; simpa using hVoteBoxGlobal q)
    intro q
    simpa using h q

  -- Proposition 5.2.8: the live `l₂'`-quorum eventually knows of that vote.
  have hKnowsVoteGlobal :
      ⊨[M]□ᶠ↓[[l₂']]
        (predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩)) := by
    have hKV :=
      live_eventually_knows (P := P) (M := M) (liveSymb := liveSymb)
        (l := l₂') (evt := ⟨voteSymb, [l, v]⟩)
        (hTheory := hThyLiveTheory)
        (hLive := by intro q; simpa using hLive q)
        (hEvent := hLiveVote)
    intro q
    simpa using hKV q

  -- (Vote?) with Lemma 4.2.3(1): knowing of the vote, the quorum knows of an
  -- `l`-quorum of echoes.
  have hStep4Global :
      ⊨[M]□ᶠ↓[[l₂']]
        (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    refine boxPast_mono_of_history (M := M) (fun t ht hConj => ?_) hKnowsVoteGlobal
    have hSplit :=
      (Sat.and (M := M) (w := t) (φ := predicate0 liveSymb)
        (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩))).1 hConj
    obtain ⟨q, hPastVote⟩ :=
      (Sat.diamond_nil (M := M) (w := t)
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).1
        (by simpa [Formula.diamondPast] using hSplit.2)
    have hPastEcho :=
      Sat.past_of_imp (M := M) (w := ⟨q, †, t.time⟩)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
        (fun t' _ _ hVote =>
          (voteBackward_elim (M := M)
            (hAx := theory_voteBackward (M := M) hTheory)
            (hMem := Sat.mem_of_ofEvent (M := M) hVote)
            (hVote := hVote)).2)
        hPastVote
    have hKnowsEcho :
        ⟪t⟫ ⊨[M] ♢ᶠ↓[[]] (□ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
      simpa [Formula.diamondPast] using
        (Sat.diamond_nil (M := M) (w := t)
          (φ := ↓ᶠ (□ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)))).2 ⟨q, hPastEcho⟩
    exact
      (Sat.and (M := M) (w := t) (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).2
        ⟨hSplit.1,
          pastDiamondBoxCollapsesToPresentBox (M := M) t l _ ht hKnowsEcho⟩

  -- Lemma 6.4.2(2) with (Vote!): the safe learner's quorum eventually votes.
  -- Safety enters through `voteForward_imp`, i.e. Lemma 6.4.1.
  have hVotesGlobal :
      ⊨[M]□ᶠ↓[[l₂']]
        (predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [l, v]⟩) :=
    boxPast_live_of_eventual_quorum
      (M := M) (liveSymb := liveSymb)
      (φ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
      (ψ := ofEvent ⟨voteSymb, [l, v]⟩)
      (l := l₂')
      (hLiveTheory := hThyLiveTheory)
      (hQuorum := hStep4Global)
      (hImp := voteForward_imp (M := M)
        (hTheory := hTheory) (hSafe := hSafe))

  -- Lemma 6.4.3, applied to (Knowledge□↓) and (Deliver!): eventual vote
  -- knowledge becomes eventual delivery.
  have hDeliverEventually :
      ⊨[M](predicate0 liveSymb ⇒ᶠ
        ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', l, v]⟩)) :=
    live_eventually_consequent (M := M)
      (hLiveTheory := hThyLiveTheory)
      (φ := □ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [l, v]⟩))
      (ψ := ofEvent ⟨deliverSymb, [l₂', l, v]⟩)
      (hLive :=
        _root_.ModalDistribution.Examples.live_eventually_knows_box
          (M := M) (liveSymb := liveSymb)
          (l := l₂') (evt := ⟨voteSymb, [l, v]⟩)
          (hTheory := hThyLiveTheory)
          (hQuorum := hVotesGlobal))
      (hImp := HBB.deliverForward_imp (M := M)
        (theory_deliverForward (M := M) hTheory))
  exact
    Sat.imp_elim (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', l, v]⟩))
      (by simpa [wTop] using hDeliverEventually p) hLivep

/-- Paper: Proposition 6.4.5, first corollary. Corollary: a delivery for `(l₁', l)`
forces every `l₂'`-quorum member to know (in the past) that `(l₂', l)` was
delivered. -/
theorem livenessTwo_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂']] (ofEvent ⟨deliverSymb, [l₂', l, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      livenessTwo (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hSafe := hSafe)
        (hLive := hLive))
/-- Paper: Proposition 6.4.5, second corollary. Corollary: a delivery for `(l₁', l)`
forces a delivery for `(l₂', l)` somewhere in the past of the history. -/
theorem livenessTwo_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      livenessTwo (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hSafe := hSafe)
        (hLive := hLive))
end Liveness_Two
end ThyHBB1
end Examples
end ModalDistribution
