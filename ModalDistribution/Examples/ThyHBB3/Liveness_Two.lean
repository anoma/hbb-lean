import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB3.Axioms
import ModalDistribution.Examples.ThyHBB3.Lemmas
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Properties.Modalities

/-!
# ThyHBB3 Liveness 2

This file states the Liveness~2 property for `ThyHBB3`, following
Liveness property 2 for ThyHBB3. When `l₁` and `l₂` are always correlated
and `l₂` has a live quorum, any delivery for `l₁` eventually propagates to a
live delivery for `l₂`.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB3

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

/-- Paper: Proposition 8.4.5 (Liveness 2). If learners `l₁` and `l₂` are always
correlated and `l₂` has a live quorum, then any delivery for `l₁` eventually
forces a live delivery for `l₂`. -/
theorem livenessTwo
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
  have hThyLive : M ⊨ᵀ ThyLive liveSymb := by
    intro ax hAx
    exact hTheory (Or.inl hAx)
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliverDiamond
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLiveHere
  -- Quorum intersections supplied by the correlation hypothesis.
  have hIntersectGlobal :
      ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ :=
    correlationImpliesQuorumIntersection
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
  have hVotesBoxGlobal_l₁ :
      ⊨[M]
        □ᶠ↓[[l₁]] (ofEvent ⟨voteSymb, [l₁, v]⟩) := by
    have hBoxTop :
        ⟪wTop⟫ ⊨[M]
          □ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨voteSymb, [l₁, v]⟩)) :=
      by simpa [Formula.boxPast]
        using hVotesBox_l₁
    obtain ⟨O, hO, hAll⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₁)
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v]⟩))).1
        hBoxTop
    intro q
    have hAllGlobal :
        ∀ q' ∈ O,
          ⟪⟨q', †, M.history.val⟩⟫ ⊨[M]
            ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v]⟩) := by
      intro q' hqO
      simpa [wTop, World.time]
        using hAll q' hqO
    refine
      (sat_box_singleton_exists (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (l := l₁)
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v]⟩))).2
        ⟨O, hO, ?_⟩
    intro q' hqO
    exact hAllGlobal q' hqO
  -- The vote quorum meets a live witness.
  have hLiveVoteDiamond :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₁, v]⟩) := by
    classical
    have hLiveVoteDiamondGlobal :=
      intertwined_two_quorums (M := M)
        (liveSymb := liveSymb)
        (l := l₁)
        (l₁ := l₂)
        (φ := ofEvent ⟨voteSymb, [l₁, v]⟩)
        (hTheory := hThyLive)
        (hIntersect := hIntersectGlobal)
        (hLiveQuorum := hLiveQuorum)
        (hWitness := hVotesBoxGlobal_l₁)
    simpa [wTop]
      using hLiveVoteDiamondGlobal p
  -- Knowledge$\atddot{}$: live participants eventually learn about the `l₁` vote.
  have hLiveVoteBoxGlobal_l₂ :
      ⊨[M]
        □ᶠ↓[[l₂]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) := by
    classical
    -- Extract a concrete history point witnessing the `l₁` vote.
    have hDiamondNil :
        ⟪wTop⟫ ⊨[M]
          ♢ᶠ[[]]
            (↓ᶠ (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₁, v]⟩)) :=
      by
        simpa [Formula.diamondPast]
          using hLiveVoteDiamond
    obtain ⟨qVote, hPastLiveVote⟩ :=
      (Sat.diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₁, v]⟩))).1
        hDiamondNil
    obtain ⟨tVote, ht_mem, ht_place, hLiveVoteLocal⟩ :=
      (Sat.past (M := M)
        (w := ⟨qVote, †, wTop.time⟩)
        (φ := predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₁, v]⟩)).1
        hPastLiveVote
    have ht_mem_history : tVote ∈ M.history.val :=
      by simpa [wTop, World.time] using ht_mem
    have hLiveVoteSplit :=
      (Sat.and (M := M) (w := tVote)
        (φ := predicate0 liveSymb)
        (ψ := ofEvent ⟨voteSymb, [l₁, v]⟩)).1
        hLiveVoteLocal
    have hLive_t : ⟪tVote⟫ ⊨[M] predicate0 liveSymb := hLiveVoteSplit.1
    -- The vote event occurs at `tVote`.
    have hVote_t :
        ⟪tVote⟫ ⊨[M] ofEvent ⟨voteSymb, [l₁, v]⟩ :=
      hLiveVoteSplit.2
    -- Record the conjunction directly at `tVote`.
    have hConj_t :
        ⟪tVote⟫ ⊨[M]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₁, v]⟩) :=
      (Sat.and (M := M) (w := tVote)
        (φ := predicate0 liveSymb)
        (ψ := ofEvent ⟨voteSymb, [l₁, v]⟩)).2
        ⟨hLive_t, hVote_t⟩
    -- Promote the local witness to the end-of-time perspective.
    have hPastConjEnd :
        ⟪⟨tVote.place, †, M.history.val⟩⟫ ⊨[M]
          ↓ᶠ (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₁, v]⟩) :=
      (Sat.past (M := M)
        (w := ⟨tVote.place, †, M.history.val⟩)
        (φ := predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₁, v]⟩)).2
        ⟨tVote, ht_mem_history, rfl, hConj_t⟩
    -- Any participant can reference the witnessed vote in the global history.
    have hEventGlobal :
        ⊨[M]
          ♢ᶠ↓[[]]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₁, v]⟩) := by
      intro q
      exact
        (Sat.diamond_nil (M := M)
          (w := ⟨q, †, M.history.val⟩)
          (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₁, v]⟩))).2
          ⟨tVote.place, hPastConjEnd⟩
    -- Instantiate eventual knowledge for learner `l₂`.
    have hLiveVoteBoxGlobal :
        ⊨[M]
          □ᶠ↓[[l₂]]
            (predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) :=
      live_eventually_knows (M := M)
        (liveSymb := liveSymb)
        (l := l₂)
        (φ := ofEvent ⟨voteSymb, [l₁, v]⟩)
        (hTheory := hThyLive)
        (hLive := hLiveQuorum)
        (hEvent := hEventGlobal)
    exact hLiveVoteBoxGlobal
  -- Lemma 6.4.2(2) with (Vote'!) as Lemma 8.4.3(3): correlated votes
  -- propagate the value to `l₂`.
  have hVotesBox_l₂ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₂, v]⟩) := by
    classical
    have hVotePropagation :
        □W⊨[M]
          (((predicate0 liveSymb ∧ᶠ
                ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) ⇒ᶠ
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
    -- Fold the always-correlated fact into `Vote'!` to obtain the
    -- implication shape consumed by Lemma 6.4.2(2).
    have hImp :
        □W⊨[M]((predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩)) := by
      intro t ht
      refine Sat.imp_intro (M := M) (w := t) ?_
      intro hAnte
      have hSplit :=
        (Sat.and (M := M) (w := t)
          (φ := predicate0 liveSymb)
          (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).1 hAnte
      refine
        Sat.imp_elim (M := M) (w := t)
          (φ := (predicate0 liveSymb ∧ᶠ
              ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))
          (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩))
          (hVotePropagation ht) ?_
      exact
        (Sat.and (M := M) (w := t)
          (φ := predicate0 liveSymb ∧ᶠ
            ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
          (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).2
          ⟨(Sat.and (M := M) (w := t)
            (φ := predicate0 liveSymb)
            (ψ := ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))).2
            ⟨hSplit.1, hCorrelationAlways ht⟩, hSplit.2⟩
    have hGlobal :
        ⊨[M]□ᶠ↓[[l₂]]
          (predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [l₂, v]⟩) :=
      ThyHBB1.boxPast_live_of_eventual_quorum (M := M)
        (hLiveTheory := hThyLive)
        (φ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))
        (ψ := ofEvent ⟨voteSymb, [l₂, v]⟩)
        (l := l₂)
        (hQuorum := hLiveVoteBoxGlobal_l₂)
        (hImp := hImp)
    simpa [wTop] using hGlobal p
  -- Knowledge$\atddot{}$: persistent `l₂` votes become eventual knowledge.
  have hVotesEventuallyBox :
      ⟪wTop⟫ ⊨[M]
        (predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l₂]]
            (ofEvent ⟨voteSymb, [l₂, v]⟩))) := by
    classical
    refine Sat.imp_intro (M := M) (w := wTop) ?_
    intro hLiveTop
    -- Instantiate the knowledge axiom for `[l₂]` vote quorums.
    have hKnowledgeMem :
        knowledgeBoxAxiom (S := S)
          liveSymb [l₂]
          (ofEvent ⟨voteSymb, [l₂, v]⟩) ∈ ThyLive liveSymb := by
      dsimp [ThyLive]
      refine Or.inr ?_
      refine Or.inr ?_
      refine Or.inr ?_
      exact ⟨[l₂], ofEvent ⟨voteSymb, [l₂, v]⟩, rfl⟩
    have hKnowledgeEvent :
        AllWorldValid M
          (knowledgeBoxAxiom (S := S)
            liveSymb [l₂]
            (ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      hThyLive hKnowledgeMem
    -- Evaluate the box hypothesis at the end of time.
    have hAtEnd :
        ⟪wTop⟫ ⊨[M]
          ⤒ᶠ (□ᶠ↓[[l₂]]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      (Sat.atEnd (M := M)
        (w := wTop)
        (φ := □ᶠ↓[[l₂]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₂, v]⟩))).2
        (by simpa [wTop, World.place, World.time] using hVotesBox_l₂)
    have hImp :=
      Sat.imp_elim (M := M) (w := wTop)
        (φ := ⤒ᶠ (□ᶠ↓[[l₂]]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩)))
        (ψ := predicate0 liveSymb ⇒ᶠ
            ↕ᶠ (□ᶠ↓[[l₂]]
              (ofEvent ⟨voteSymb, [l₂, v]⟩)))
        (AllWorldValid.at_end (M := M)
          (φ := knowledgeBoxAxiom (S := S)
            liveSymb [l₂] (ofEvent ⟨voteSymb, [l₂, v]⟩))
          hKnowledgeEvent p)
        hAtEnd
    exact
      Sat.imp_elim (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (□ᶠ↓[[l₂]]
          (ofEvent ⟨voteSymb, [l₂, v]⟩)))
        hImp hLiveTop
  -- Votes for `l₂` lead to deliveries for `l₂`; see `ThyHBB3.deliverForwardAxiom`.
  have hLiveToDeliver :
      ⟪wTop⟫ ⊨[M]
        (predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩)) := by
    refine Sat.imp_intro (M := M) (w := wTop) ?_
    intro hLiveTop
    exact
      ThyHBB1.live_sometime_consequent_at (M := M)
        (hLiveTheory := hThyLive)
        (hImp := deliverForward_imp (M := M)
          (theory_deliverForward (M := M) hTheory))
        hLiveTop
        ((Sat.imp (M := M) (w := wTop)
          (φ := predicate0 liveSymb)
          (ψ := ↕ᶠ (□ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v]⟩)))).1
          hVotesEventuallyBox hLiveTop)

  -- Apply the live guard to obtain eventual `l₂` votes.
  have hVotesEventually :
      ⟪wTop⟫ ⊨[M]
        ↕ᶠ (□ᶠ↓[[l₂]]
          (ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
    (Sat.imp (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (□ᶠ↓[[l₂]]
        (ofEvent ⟨voteSymb, [l₂, v]⟩)))).1
      hVotesEventuallyBox hLiveHere

  have hDeliverEventually :
      ⟪wTop⟫ ⊨[M]
        ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩) :=
    (Sat.imp (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩))).1
      hLiveToDeliver hLiveHere

  exact hDeliverEventually

/-- Paper: Proposition 8.4.5, first corollary. A delivery for `l₁`
forces every member of `l₂`'s quorum to know (in the past) that `l₂` delivered
the same value. -/
theorem livenessTwo_boxPast
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
      livenessTwo (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (l₁ := l₁) (l₂ := l₂) (v := v)
        (hTheory := hTheory)
        (hCorrelation := hCorrelation)
        (hLiveQuorum := hLiveQuorum))
/-- Paper: Proposition 8.4.5, second corollary. A delivery for `l₁`
produces a delivery for `l₂` somewhere in the past. -/
theorem livenessTwo_diamondPast
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
      livenessTwo (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (l₁ := l₁) (l₂ := l₂) (v := v)
        (hTheory := hTheory)
        (hCorrelation := hCorrelation)
        (hLiveQuorum := hLiveQuorum))
end ThyHBB3
end Examples
end ModalDistribution
