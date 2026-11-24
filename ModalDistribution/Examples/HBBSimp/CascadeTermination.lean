import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBSimp.Axioms
import ModalDistribution.Examples.HBBSimp.Lemmas
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Examples.HBBSafe.Safety
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBSimp Cascade Termination

This file records the Cascade Termination statement for `HBBSimp`.
Intersecting reporting quorums together with a live quorum for `l₂'` ensure
that deliveries for `(l₁', ℓ)` propagate to `(l₂', ℓ)`.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSimp

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 7.3.2 (Cascade Termination). If reporting learners `l₁'` and `l₂'`
have intersecting quorums and learner `l₂'` is live, then any delivery for
`(l₁', ℓ)` propagates to `(l₂', ℓ)`. -/
theorem cascadeTermination
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩)) ⇒ᶠ
         predicate0 liveSymb ⇒ᶠ
         ↕ᶠ(ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliverSource
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLiveHere
  have hVoteBox :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [ℓ, v]⟩) := by
    -- Use `Deliver?` to extract the votes that justify the source delivery.
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := theory_deliverBackward (M := M) hTheory)
          (reporting := l₁') (learner := ℓ)
          (value := v) (p := p)
          (hDeliver := hDeliverSource)
  have hThyLive : M ⊨ᵀ ThyLive liveSymb :=
    theory_thyLive (M := M) hTheory
  -- Proposition 5.2.10: the intersecting live quorum exposes a live voter.
  have hLiveVote :
      ⊨[M]♢ᶠ↓[[]]
        (predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [ℓ, v]⟩) := by
    have h :=
      intertwined_two_quorums (M := M)
        (liveSymb := liveSymb) (l := l₁') (l₁ := l₂')
        (φ := ofEvent ⟨voteSymb, [ℓ, v]⟩)
        (hTheory := hThyLive)
        (hIntersect := by intro q; simpa using hIntersect q)
        (hLiveQuorum := by intro q; simpa using hLive q)
        (hWitness := by intro q; simpa [wTop] using hVoteBox)
    intro q
    simpa using h q
  -- Proposition 5.2.8: the live `l₂'`-quorum eventually knows of that vote.
  have hKnowsVoteGlobal :
      ⊨[M]□ᶠ↓[[l₂']]
        (predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [ℓ, v]⟩)) := by
    have hKV :=
      live_eventually_knows (P := P) (M := M) (liveSymb := liveSymb)
        (l := l₂') (evt := ⟨voteSymb, [ℓ, v]⟩)
        (hTheory := hThyLive)
        (hLive := by intro q; simpa using hLive q)
        (hEvent := hLiveVote)
    intro q
    simpa using hKV q
  -- (Vote?) with Lemma 4.2.3(1): knowing of the vote, the quorum knows of an
  -- `ℓ`-quorum of echoes.
  have hLiveEchoBoxGlobal :
      ⊨[M]□ᶠ↓[[l₂']] (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    refine HBBSafe.boxPast_mono_of_history (M := M)
      (fun t ht hConj => ?_) hKnowsVoteGlobal
    have hSplit :=
      (Sat.and (M := M) (w := t) (φ := predicate0 liveSymb)
        (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [ℓ, v]⟩))).1 hConj
    obtain ⟨q, hPastVote⟩ :=
      (Sat.diamond_nil (M := M) (w := t)
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [ℓ, v]⟩))).1
        (by simpa [Formula.diamondPast] using hSplit.2)
    have hPastEcho :=
      Sat.past_of_imp (M := M) (w := ⟨q, †, t.time⟩)
        (ψ := □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩))
        (fun t' _ _ hVote =>
          voteBackward_elim (M := M)
            (hAx := theory_voteBackward (M := M) hTheory)
            (hMem := Sat.mem_of_ofEvent (M := M) hVote)
            (hVote := hVote))
        hPastVote
    have hKnowsEcho :
        ⟪t⟫ ⊨[M] ♢ᶠ↓[[]] (□ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)) := by
      simpa [Formula.diamondPast] using
        (Sat.diamond_nil (M := M) (w := t)
          (φ := ↓ᶠ (□ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)))).2 ⟨q, hPastEcho⟩
    exact
      (Sat.and (M := M) (w := t) (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩))).2
        ⟨hSplit.1,
          pastDiamondBoxCollapsesToPresentBox (M := M) t ℓ _ ht hKnowsEcho⟩
  -- Lemma 6.5.2(2) with (Vote!): the quorum votes.
  have hVoteBoxGlobal :
      ⊨[M]□ᶠ↓[[l₂']] (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [ℓ, v]⟩) :=
    HBBSafe.boxPast_live_of_eventual_quorum
      (M := M) (liveSymb := liveSymb)
      (φ := □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩))
      (ψ := ofEvent ⟨voteSymb, [ℓ, v]⟩)
      (l := l₂')
      (hLiveTheory := hThyLive)
      (hQuorum := hLiveEchoBoxGlobal)
      (hImp := voteForward_imp (M := M) (hTheory := hTheory))
  -- Lemma 6.5.3, applied to (Knowledge□↓) and (Deliver!): eventual vote
  -- knowledge becomes eventual delivery.
  have hDeliverEventually :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
    have hGlobal :=
      HBBSafe.live_eventually_consequent (M := M)
        (hLiveTheory := hThyLive)
        (φ := □ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [ℓ, v]⟩))
        (ψ := ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩)
        (hLive :=
          live_eventually_knows_box (M := M)
            (liveSymb := liveSymb)
            (l := l₂') (evt := ⟨voteSymb, [ℓ, v]⟩)
            (hTheory := hThyLive)
            (hQuorum := hVoteBoxGlobal))
        (hImp := HBB.deliverForward_imp (M := M)
          (theory_deliverForward (M := M) hTheory))
    simpa [wTop] using hGlobal p
  have hGoal :
      ⟪wTop⟫ ⊨[M]
        ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
    -- Combine the eventual delivery implication with the local `live` hypothesis.
    exact
      (Sat.imp (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩))).1
        hDeliverEventually hLiveHere
  simpa [wTop] using hGoal

/-- Paper: Proposition 7.3.2, first corollary. A delivery for `(l₁', ℓ)`
forces every member of `l₂'`'s quorum to know (in the past) that `(l₂', ℓ)` was
delivered. -/
theorem cascadeTermination_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂']] (ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      cascadeTermination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (l₁' := l₁') (l₂' := l₂') (ℓ := ℓ) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hLive := hLive))
/-- Paper: Proposition 7.3.2, second corollary. A delivery for `(l₁', ℓ)`
eventually yields a delivery for `(l₂', ℓ)`. -/
theorem cascadeTermination_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      cascadeTermination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (l₁' := l₁') (l₂' := l₂') (ℓ := ℓ) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hLive := hLive))
end HBBSimp
end Examples
end ModalDistribution
