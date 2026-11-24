import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBCorr.Axioms
import ModalDistribution.Examples.HBBCorr.Lemmas
import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBCorr Cascade Termination

This file states the Cascade Termination property for `HBBCorr`. When `l₁`
and `l₂` are always correlated and `l₂` has a live quorum, any delivery for
`l₁` eventually propagates to a live delivery for `l₂`.
-/

namespace ModalDistribution
namespace Examples
namespace HBBCorr

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
variable {correlationSymb : Signature.PredSymb S}

/-- Paper: Proposition 8.4.5 (Cascade Termination). If learners `l₁` and `l₂` are always
correlated and `l₂` has a live quorum, then any delivery for `l₁` eventually
forces a live delivery for `l₂`. -/
theorem cascade_termination
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hLiveQuorum : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) :
    ⊨[M]
      (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
        predicate0 liveSymb ⇒ᶠ
        ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩) := by
  classical
  have hLiveSequentialGlobal :
      ⊨[M]□ᶠ[[l₂]] Formula.seq :=
    live_quorum_seq (M := M)
      (hTheory := fun _ hAx => hTheory (Or.inl hAx))
      (hLiveQuorum := hLiveQuorum)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hThyLive : M ⊨ᵀ thyLive liveSymb :=
    fun _ hAx => hTheory (Or.inl hAx)
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliverDiamond
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLiveHere
  -- Quorum intersections supplied by the correlation hypothesis.
  have hIntersectGlobal :
      ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ :=
    correlation_implies_quorum_intersection
      (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (voteSymb := voteSymb)
      (deliverSymb := deliverSymb)
      (correlationSymb := correlationSymb)
      hTheory hCorrelation
  -- Correlation persists through every local past (available as an event-valid fact).
  have hCorrelationAlways :
      □W⊨[M] (⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) := by
    exact
      correlation_global_allPast
        (M := M)
        (liveSymb := liveSymb)
        (proposeSymb := proposeSymb)
        (echoSymb := echoSymb)
        (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (correlationSymb := correlationSymb)
        (hTheory := hTheory)
        (hCorrelation := hCorrelation)
  -- `Deliver?`: deliveries for `l₁` enforce an `l₁` vote quorum.
  have hVotesBox_l₁ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₁]] (ofEvent ⟨voteSymb, [l₁, v]⟩) :=
    deliver_to_vote_box_end (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (voteSymb := voteSymb)
      (deliverSymb := deliverSymb)
      (correlationSymb := correlationSymb)
      (hTheory := hTheory)
      (learner := l₁)
      (value := v)
      (p := p)
      (hDeliver := hDeliverDiamond)
  -- Propositions 5.2.10 and 5.2.8: the live `l₂`-quorum eventually knows of
  -- a vote of the intersecting `l₁`-quorum.
  have hLiveVoteBoxGlobal_l₂ :
      ⊨[M]
        □ᶠ↓[[l₂]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) :=
    HBB.boxPast_live_knows_of_intersecting (M := M)
      (hLiveTheory := hThyLive)
      (hIntersect := hIntersectGlobal) (hLive := hLiveQuorum)
      (hQuorum := fun q => by simpa [wTop] using hVotesBox_l₁)
  -- Lemma 6.5.2(2) with (Vote'!) as Lemma 8.4.3(3): correlated votes
  -- propagate the value to `l₂`.
  have hVotesBox_l₂ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₂, v]⟩) := by
    classical
    have hVotePropagation :
        □W⊨[M]
          ((↕ᶠ ((predicate0 liveSymb ∧ᶠ
                ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      correlated_vote_eventually
        (M := M)
        (liveSymb := liveSymb)
        (proposeSymb := proposeSymb)
        (echoSymb := echoSymb)
        (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (correlationSymb := correlationSymb)
        (hTheory := hTheory)
        (l := l₂)
        (l₁ := l₁)
        (l₂ := l₂)
        (v := v)
        (hSeq := hLiveSequentialGlobal)
    -- Fold the always-correlated fact into Lemma 8.4.3(3) to obtain the
    -- implication shape consumed by Lemma 6.5.2(2).
    have hImp :
        □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩)) := by
      intro t ht
      refine Sat.imp_intro (M := M) (w := t) ?_
      intro hSometimeAnte
      obtain ⟨s, hs, hsPlace, hAnte⟩ :=
        (Sat.sometime (M := M) (w := t)
          (φ := predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).1 hSometimeAnte
      have hSplit :=
        (Sat.and (M := M) (w := s)
          (φ := predicate0 liveSymb)
          (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).1 hAnte
      have hTriple :
          ⟪s⟫ ⊨[M] (predicate0 liveSymb ∧ᶠ
              ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩) :=
        (Sat.and (M := M) (w := s)
          (φ := predicate0 liveSymb ∧ᶠ
            ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
          (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).2
          ⟨(Sat.and (M := M) (w := s)
            (φ := predicate0 liveSymb)
            (ψ := ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))).2
            ⟨hSplit.1, hCorrelationAlways (M.time_le_of_mem hs)⟩, hSplit.2⟩
      exact
        Sat.imp_elim (M := M) (w := t)
          (hVotePropagation ht)
          (Sat.sometime_of_place_eq (M := M) hsPlace
            (Sat.sometime_of_mem (M := M) hs hTriple))
    have hGlobal :
        ⊨[M]□ᶠ↓[[l₂]]
          (predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [l₂, v]⟩) :=
      HBB.boxPast_live_of_eventual_quorum (M := M)
        (hLiveTheory := hThyLive)
        (φ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))
        (ψ := ofEvent ⟨voteSymb, [l₂, v]⟩)
        (l := l₂)
        (hQuorum := hLiveVoteBoxGlobal_l₂)
        (hImp := hImp)
    simpa [wTop] using hGlobal p
  -- Lemma 6.5.3, applied to (Knowledge□↓) and (Deliver!), concludes
  -- eventual delivery.
  exact
    Sat.imp_elim (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩))
      (by
        simpa [wTop] using
          HBB.live_quorum_eventually_consequent (M := M)
            (hLiveTheory := hThyLive)
            (hQuorum := fun q => by simpa [wTop] using hVotesBox_l₂)
            (hImp := deliver_forward_imp (M := M)
              (theory_deliver_forward (M := M) hTheory)) p)
      hLiveHere

/-- Paper: Proposition 8.4.5, first corollary. A delivery for `l₁`
forces every member of `l₂`'s quorum to know (in the past) that `l₂` delivered
the same value. -/
theorem cascade_termination_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hLiveQuorum : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂]] (ofEvent ⟨deliverSymb, [l₂, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLiveQuorum)
      (hMain :=
      cascade_termination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (l₁ := l₁) (l₂ := l₂) (v := v)
        (hTheory := hTheory)
        (hCorrelation := hCorrelation)
        (hLiveQuorum := hLiveQuorum))
/-- Paper: Proposition 8.4.5, second corollary. A delivery for `l₁`
produces a delivery for `l₂` somewhere in the past. -/
theorem cascade_termination_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hLiveQuorum : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLiveQuorum)
      (hMain :=
      cascade_termination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (l₁ := l₁) (l₂ := l₂) (v := v)
        (hTheory := hTheory)
        (hCorrelation := hCorrelation)
        (hLiveQuorum := hLiveQuorum))
end HBBCorr
end Examples
end ModalDistribution
