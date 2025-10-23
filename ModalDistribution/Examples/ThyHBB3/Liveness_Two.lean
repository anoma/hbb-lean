import ModalDistribution.Examples.ThyHBB3.Axioms
import ModalDistribution.Examples.ThyHBB3.Lemmas
import ModalDistribution.Examples.ThyHBB1.LivenessHelpers
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Properties.Modalities

/-!
# ThyHBB3 Liveness 2

This file states the Liveness~2 property for `ThyHBB3`, following
Proposition~\ref{prop.3.liveness.2}. When `l₁` and `l₂` are always correlated
and `l₂` has a live quorum, any delivery for `l₁` eventually propagates to a
live delivery for `l₂`.
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
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {correlationSymb : Signature.PredSymb S}

/-- Proposition~\ref{prop.3.liveness.2}: if learners `l₁` and `l₂` are always
correlated and `l₂` has a live quorum, then any delivery for `l₁` eventually
forces a live delivery for `l₂`. -/
  lemma livenessTwoThyHBB3
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hLiveQuorum : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) :
    ⊨[M]
      (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
        predicate0 liveSymb ⇒ᶠ
        ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩) := by
  classical
  have hLiveSeqAx :
      AllWorldValid M (liveSeqAxiom liveSymb) := by
    apply hTheory
    simp [ThyHBB3, ThyHBB3.theory]
  have hLiveSequentialGlobal :
      ⊨[M]□ᶠ[[l₂]] Formula.seq := by
    intro p
    set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
    have hLiveTop :
        ⟪wTop⟫ ⊨[M]□ᶠ[[l₂]] predicate0 liveSymb :=
      by simpa [wTop] using hLiveQuorum p
    obtain ⟨O, hO, hAllLive⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₂)
        (φ := predicate0 liveSymb)).1 hLiveTop
    refine
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₂)
        (φ := Formula.seq)).2 ?_
    refine ⟨O, hO, ?_⟩
    intro q hqO
    have hLive_q :
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb :=
      hAllLive q hqO
    have hSeqImp :
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
          liveSeqAxiom liveSymb :=
      hLiveSeqAx
        (by simp [World.time])
    have hImp :=
      (Sat.imp (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := predicate0 liveSymb)
        (ψ := Formula.seq)).1
        (by simpa [liveSeqAxiom] using hSeqImp)
    exact hImp hLive_q
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hThyLive : M ⊨ᵀ ThyLive liveSymb := by
    intro ax hAx
    exact hTheory (Or.inl hAx)
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliverDiamond
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLiveHere
  -- Quorum intersections supplied by the correlation hypothesis.  We extract
  -- the history witness from the delivery diamond.
  have hHistoryNonempty :
      ∃ t : World P (Signature.EventType S), t ∈ M.history.val := by
    -- Reuse the delivery witness supplied by the initial diamond.
    have hDiamondNil :
        ⟪wTop⟫ ⊨[M]
          ♢ᶠ[[]](↓ᶠ (ofEvent ⟨deliverSymb, [l₁, v]⟩)) :=
      by simpa [Formula.diamondPast, wTop] using hDeliverDiamond
    obtain ⟨qDeliver, hPastDeliver⟩ :=
      (Sat.diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ (ofEvent ⟨deliverSymb, [l₁, v]⟩))).1
        hDiamondNil
    obtain ⟨tDeliver, ht_mem, _, _⟩ :=
      (Sat.past (M := M)
        (w := ⟨qDeliver, †, wTop.time⟩)
        (φ := ofEvent ⟨deliverSymb, [l₁, v]⟩)).1
        hPastDeliver
    exact ⟨tDeliver, by simpa [wTop, World.time] using ht_mem⟩
  have hIntersectGlobal :
      ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ :=
    correlationEveryoneImpliesIntersection
      (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (voteSymb := voteSymb)
      (deliverSymb := deliverSymb)
      (correlationSymb := correlationSymb)
      hTheory hHistoryNonempty hCorrelation
  have hQuorumIntersect :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ := by
    -- Exhibit a concrete delivery event.
    have hDiamondNil :
        ⟪wTop⟫ ⊨[M]
          ♢ᶠ[[]](↓ᶠ (ofEvent ⟨deliverSymb, [l₁, v]⟩)) :=
      by simpa [Formula.diamondPast, wTop] using hDeliverDiamond
    obtain ⟨qDeliver, hPastDeliver⟩ :=
      (Sat.diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ (ofEvent ⟨deliverSymb, [l₁, v]⟩))).1
        hDiamondNil
    -- Apply Lemma~\ref{lemm.mnta.intersections}.
    exact hIntersectGlobal p
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
  -- Proposition~\ref{prop.intertwined.two.quorums}: the vote quorum meets a live witness.
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
  have hLiveVoteBox_l₂ :
      ⟪wTop⟫ ⊨[M]
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
    -- Instatiate Proposition~\ref{prop.live.eventually.knows} for learner `l₂`.
    have hLiveVoteBoxGlobal :
        ⊨[M]
          □ᶠ↓[[l₂]]
            (predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) :=
      live_eventually_knows (M := M)
        (liveSymb := liveSymb)
        (l := l₂)
        (evt := ⟨voteSymb, [l₁, v]⟩)
        (hTheory := hThyLive)
        (hLive := hLiveQuorum)
        (hEvent := hEventGlobal)
    simpa [wTop]
      using hLiveVoteBoxGlobal p
  -- Lemma~\ref{lemm.3twined.echodup}(3): correlated votes propagate the value to `l₂`.
  have hVotesBox_l₂ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₂, v]⟩) := by
    classical
    have hLiveVoteBox :
        ⟪wTop⟫ ⊨[M]
          □ᶠ[[l₂]]
            ↓ᶠ (predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) := by
      simpa [Formula.boxPast] using hLiveVoteBox_l₂
    have hVotePropagation :
        AllWorldValid M
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
    obtain ⟨O, hO, hAllLiveDiamond⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₂)
        (φ :=
          ↓ᶠ (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)))).1
        hLiveVoteBox
    have hBoxResult :
        ⟪wTop⟫ ⊨[M]
          □ᶠ[[l₂]]
            ↓ᶠ (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩) := by
      refine
        (sat_box_singleton_exists (M := M)
          (w := wTop) (l := l₂)
          (φ :=
            ↓ᶠ (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩))).2
          ⟨O, hO, ?_⟩
      intro q hqO
      have hPastLiveDiamond :
          ⟪⟨q, †, wTop.time⟩⟫ ⊨[M]
            ↓ᶠ (predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) :=
        hAllLiveDiamond q hqO
      obtain ⟨t, ht_mem, ht_place, hLiveDiamond⟩ :=
        (Sat.past (M := M)
          (w := ⟨q, †, wTop.time⟩)
          (φ :=
            predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).1
          hPastLiveDiamond
      have hLiveDiamond_split :=
        (Sat.and (M := M) (w := t)
          (φ := predicate0 liveSymb)
          (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).1
          hLiveDiamond
      have hLive_t : ⟪t⟫ ⊨[M] predicate0 liveSymb :=
        hLiveDiamond_split.1
      have hDiamond_t :
          ⟪t⟫ ⊨[M] ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩) :=
        hLiveDiamond_split.2
      have ht_mem' : t ∈ M.history.val := by
        simpa [wTop, World.time] using ht_mem
      have hCorrelation_t :
          ⟪t⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) :=
        AllWorldValid.of_mem_history
          (M := M)
          (φ := ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
          hCorrelationAlways ht_mem'
      have hAnte :
          ⟪t⟫ ⊨[M]
            ((predicate0 liveSymb ∧ᶠ
                ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) := by
        refine
          (Sat.and (M := M) (w := t)
            (φ :=
              predicate0 liveSymb ∧ᶠ
                ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
            (ψ :=
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).2
            ?_
        refine ⟨?_, hDiamond_t⟩
        exact
          (Sat.and (M := M) (w := t)
            (φ := predicate0 liveSymb)
            (ψ := ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))).2
            ⟨hLive_t, hCorrelation_t⟩
      have hVoteImp_t :=
        AllWorldValid.of_mem_history
          (M := M)
          (φ := ((predicate0 liveSymb ∧ᶠ
              ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩))
          hVotePropagation ht_mem'
      have hSometimeVote :
          ⟪t⟫ ⊨[M]
            ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩) :=
        Sat.imp_elim (M := M) (w := t)
          (φ :=
            (predicate0 liveSymb ∧ᶠ
              ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))
          (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩))
          hVoteImp_t hAnte
      obtain ⟨tVote, htVote_mem, htVote_place, hVote_tVote⟩ :=
        (Sat.sometime (M := M)
          (w := t)
          (φ := ofEvent ⟨voteSymb, [l₂, v]⟩)).1
          hSometimeVote
      have hPlaceEq : t.place = tVote.place := by
        simpa [World.place] using htVote_place.symm
      have hLive_tVote : ⟪tVote⟫ ⊨[M] predicate0 liveSymb := by
        have hEquiv :=
          alwaysLiveEquivBackward
            (M := M)
            (liveSymb := liveSymb)
            (hTheory := hThyLive)
            (t := t) (t' := tVote)
            (ht := ht_mem') (ht' := htVote_mem)
            (hplace := hPlaceEq)
        exact (hEquiv).1 hLive_t
      have hVoteConj :
          ⟪tVote⟫ ⊨[M]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩) :=
        (Sat.and (M := M) (w := tVote)
          (φ := predicate0 liveSymb)
          (ψ := ofEvent ⟨voteSymb, [l₂, v]⟩)).2
          ⟨hLive_tVote, hVote_tVote⟩
      have hPlace_tVote : tVote.place = q :=
        htVote_place.trans ht_place
      have hPastVote :
          ⟪⟨q, †, wTop.time⟩⟫ ⊨[M]
            ↓ᶠ (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩) := by
        refine (Sat.past (M := M)
          (w := ⟨q, †, wTop.time⟩)
          (φ :=
            predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩)).2 ?_
        refine ⟨tVote, ?_, ?_, hVoteConj⟩
        · simpa [wTop, World.time] using htVote_mem
        · simpa [World.place, wTop] using hPlace_tVote
      simpa [wTop, World.time, World.place] using hPastVote
    simpa [Formula.boxPast] using hBoxResult
  -- Knowledge$\atddot{}$: persistent `l₂` votes become eventual knowledge.
  have hVotesEventuallyBox :
      ⟪wTop⟫ ⊨[M]
        (predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l₂]]
            (ofEvent ⟨voteSymb, [l₂, v]⟩))) := by
    classical
    refine Sat.imp_intro (M := M) (w := wTop) ?_
    intro hLiveTop
    obtain ⟨wPre, hw_mem, hw_place, _, hLivePre⟩ :=
      live_guard_predecessor_data (M := M)
        (hTheory := hThyLive)
        (hNonempty := hHistoryNonempty)
        (w := wTop)
        (hLive := hLiveTop)
    -- Instantiate the knowledge axiom for `[l₂]` vote quorums.
    have hKnowledgeMem :
        knowledgeDiamondEventuallyAxiom (S := S)
          liveSymb [l₂]
          (ofEvent ⟨voteSymb, [l₂, v]⟩) ∈ ThyLive liveSymb := by
      dsimp [ThyLive]
      refine Or.inr ?_
      refine Or.inr ?_
      refine Or.inr ?_
      refine Or.inr ?_
      exact ⟨[l₂], ofEvent ⟨voteSymb, [l₂, v]⟩, rfl⟩
    have hKnowledgeEvent :
        AllWorldValid M
          (knowledgeDiamondEventuallyAxiom (S := S)
            liveSymb [l₂]
            (ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      hThyLive hKnowledgeMem
    -- Evaluate the box hypothesis at the predecessor participant.
    have hQuorumPreTop :
        ⟪⟨wPre.place, †, M.history.val⟩⟫ ⊨[M]
          □ᶠ↓[[l₂]]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩) := by
      cases hw_place
      simpa [wTop, World.place, World.time] using hVotesBox_l₂
    have hAtEnd :
        ⟪wPre⟫ ⊨[M]
          ⤒ᶠ (□ᶠ↓[[l₂]]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      (Sat.atEnd (M := M)
        (w := wPre)
        (φ := □ᶠ↓[[l₂]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l₂, v]⟩))).2
        (by simpa using hQuorumPreTop)
    have hKnowledgePre :=
      AllWorldValid.of_mem_history
        (M := M)
        (φ := knowledgeDiamondEventuallyAxiom (S := S)
          liveSymb [l₂] (ofEvent ⟨voteSymb, [l₂, v]⟩))
        hKnowledgeEvent hw_mem
    have hImp :=
      Sat.imp_elim (M := M) (w := wPre)
        (φ := ⤒ᶠ (□ᶠ↓[[l₂]]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l₂, v]⟩)))
        (ψ := predicate0 liveSymb ⇒ᶠ
            ↕ᶠ (□ᶠ↓[[l₂]]
              (ofEvent ⟨voteSymb, [l₂, v]⟩)))
        hKnowledgePre hAtEnd
    have hSometimeBox :
        ⟪wPre⟫ ⊨[M]
          ↕ᶠ (□ᶠ↓[[l₂]]
            (ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      Sat.imp_elim (M := M) (w := wPre)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (□ᶠ↓[[l₂]]
          (ofEvent ⟨voteSymb, [l₂, v]⟩)))
        hImp hLivePre
    have hPastBoxPre :
        ⟪⟨wPre.place, †, M.history.val⟩⟫ ⊨[M]
          ↓ᶠ (□ᶠ↓[[l₂]]
            (ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      (Sat.atEnd (M := M)
        (w := wPre)
        (φ := ↓ᶠ (□ᶠ↓[[l₂]]
          (ofEvent ⟨voteSymb, [l₂, v]⟩)))).1
        (by
          simpa [Formula.sometime]
            using hSometimeBox)
    have hPastBoxTop :
        ⟪wTop⟫ ⊨[M]
          ↓ᶠ (□ᶠ↓[[l₂]]
            (ofEvent ⟨voteSymb, [l₂, v]⟩)) := by
      cases hw_place
      simpa [wTop, World.place, World.time]
        using hPastBoxPre
    exact
      (Sat.atEnd (M := M)
        (w := wTop)
        (φ := ↓ᶠ (□ᶠ↓[[l₂]]
          (ofEvent ⟨voteSymb, [l₂, v]⟩)))).2
        hPastBoxTop
  -- Votes for `l₂` lead to deliveries for `l₂`; see `ThyHBB3.deliverForwardAxiom`.
  have hLiveToDeliver :
      ⟪wTop⟫ ⊨[M]
        (predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩)) := by
    classical
    have hDeliverAx : AllWorldValid M
        (deliverForwardAxiom liveSymb voteSymb deliverSymb) := by
      apply hTheory
      simp [ThyHBB3, ThyHBB3.theory]
    refine Sat.imp_intro (M := M) (w := wTop) ?_
    intro hLiveTop
    -- Apply the intermediate implication to obtain a vote quorum in the past.
    have hVotesTop :
        ⟪wTop⟫ ⊨[M]
          ↕ᶠ (□ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      (Sat.imp (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (□ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v]⟩)))).1
        hVotesEventuallyBox hLiveTop
    -- Pull the sometime witness into the concrete history.
    have hPastVotes :
        ⟪wTop⟫ ⊨[M]
          ↓ᶠ (□ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      (Sat.atEnd (M := M)
        (w := wTop)
        (φ := ↓ᶠ (□ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v]⟩)))).1
        (by
          simpa [Formula.sometime]
            using hVotesTop)
    obtain ⟨t, ht_mem, ht_place, hVoteLocal⟩ :=
      (Sat.past (M := M)
        (w := wTop)
        (φ := □ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v]⟩))).1
        hPastVotes
    -- Transport the liveness hypothesis to the witnessing world.
    have hLiveEnd :
        ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb := by
      cases ht_place
      simpa [wTop, World.place, World.time] using hLiveTop
    have hLiveLocal :
        ⟪t⟫ ⊨[M] predicate0 liveSymb :=
      (alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hThyLive)
        (t := t)
        (ht := ht_mem)).mpr
        (by
          simpa [World.place, World.time]
            using hLiveEnd)
    -- Instantiate `Deliver!` at the witnessed history point.
    have hForward :=
      AllWorldValid.of_mem_history
        (M := M)
        (φ := deliverForwardAxiom liveSymb voteSymb deliverSymb)
        hDeliverAx ht_mem
    have hLearner :=
      Sat.forall_elim (M := M) (w := t)
        (body := fun learner' =>
          ∀ᶠ fun value' =>
            (predicate0 liveSymb ∧ᶠ
                □ᶠ↓[[learner']] (ofEvent ⟨voteSymb, [learner', value']⟩)) ⇒ᶠ
              ↕ᶠ (ofEvent ⟨deliverSymb, [learner', value']⟩))
        (v := l₂) hForward
    have hValue :=
      Sat.forall_elim (M := M) (w := t)
        (body := fun value' =>
          (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, value']⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, value']⟩))
        (v := v) hLearner
    have hDeliverGuard :
        ⟪t⟫ ⊨[M]
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v]⟩)) :=
      (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v]⟩))).2
        ⟨hLiveLocal, hVoteLocal⟩
    have hDeliverLocal :
        ⟪t⟫ ⊨[M]
          ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩) :=
      (Sat.imp (M := M) (w := t)
        (φ := predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v]⟩))
        (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩))).1
        hValue hDeliverGuard
    -- Push the deliver event back to the top of the history.
    have hPastDeliverEnd :
        ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]
          ↓ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩) :=
      (Sat.atEnd (M := M)
        (w := t)
        (φ := ↓ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩))).1
        (by
          simpa [Formula.sometime]
            using hDeliverLocal)
    have hPastDeliverTop :
        ⟪wTop⟫ ⊨[M]
          ↓ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩) := by
      cases ht_place
      simpa [wTop, World.place, World.time]
        using hPastDeliverEnd
    exact
      (Sat.atEnd (M := M)
        (w := wTop)
        (φ := ↓ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩))).2
        hPastDeliverTop

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

/-- Corollary of Proposition~\ref{prop.3.liveness.2}: a delivery for `l₁`
forces every member of `l₂`'s quorum to know (in the past) that `l₂` delivered
the same value. -/
lemma livenessTwoAtPastDownThyHBB3
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hLiveQuorum : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂]] (ofEvent ⟨deliverSymb, [l₂, v]⟩) := by
  classical
  let deliver₁ := ofEvent ⟨deliverSymb, [l₁, v]⟩
  let deliver₂ := ofEvent ⟨deliverSymb, [l₂, v]⟩
  have hMain :=
    livenessTwoThyHBB3 (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      (l₁ := l₁) (l₂ := l₂) (v := v)
      (hTheory := hTheory)
      (hCorrelation := hCorrelation)
      (hLiveQuorum := hLiveQuorum)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hLiveTop : ⟪wTop⟫ ⊨[M] □ᶠ[[l₂]] predicate0 liveSymb :=
    by simpa [wTop] using hLiveQuorum p
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver
  obtain ⟨rDeliver, hPastDeliver⟩ :=
    (Sat.diamond_nil (M := M) (w := wTop)
        (φ := Formula.past deliver₁)).1
      (by simpa [Formula.diamondPast, deliver₁, wTop] using hDeliver)
  obtain ⟨O, hO, hAllLive⟩ :=
    (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₂)
        (φ := predicate0 liveSymb)).1
      hLiveTop
  refine
    (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₂)
        (φ := ↓ᶠ deliver₂)).2
      ⟨O, hO, ?_⟩
  intro q hqO
  set wq : World P (Signature.EventType S) := ⟨q, †, M.history.val⟩
  have hDeliver_q :
      ⟪wq⟫ ⊨[M] ♢ᶠ↓[[]] deliver₁ := by
    have hPastWitness :
        ⟪⟨rDeliver, †, wq.time⟩⟫ ⊨[M] Formula.past deliver₁ := by
      simpa [wq, wTop, World.time, deliver₁] using hPastDeliver
    exact
      (Sat.diamond_nil (M := M) (w := wq)
          (φ := Formula.past deliver₁)).2
        ⟨rDeliver, hPastWitness⟩
  have hImp_q :
      ⟪wq⟫ ⊨[M]
        (♢ᶠ↓[[]] deliver₁) ⇒ᶠ
          (predicate0 liveSymb ⇒ᶠ ↕ᶠ deliver₂) := by
    simpa [wq, deliver₁, deliver₂] using hMain q
  have hStep :=
    Sat.imp_elim (M := M) (w := wq)
      (φ := ♢ᶠ↓[[]] deliver₁)
      (ψ := predicate0 liveSymb ⇒ᶠ ↕ᶠ deliver₂)
      hImp_q hDeliver_q
  have hLive_q : ⟪wq⟫ ⊨[M] predicate0 liveSymb :=
    by simpa [wq, wTop, World.time] using hAllLive q hqO
  have hEventual :=
    Sat.imp_elim (M := M) (w := wq)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ deliver₂)
      hStep hLive_q
  have hPastDeliver_q :
      ⟪wq⟫ ⊨[M] ↓ᶠ deliver₂ :=
    by
      have hPast :=
        (Sat.atEnd (M := M) (w := wq)
          (φ := Formula.past deliver₂)).1
          (by
            simpa [Formula.sometime]
              using hEventual)
      simpa using hPast
  exact hPastDeliver_q

/-- Corollary of Proposition~\ref{prop.3.liveness.2}: a delivery for `l₁`
produces a delivery for `l₂` somewhere in the past. -/
lemma livenessTwoAtPastThyHBB3
    (hTheory : M ⊨ᵀ
      ThyHBB3 liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hLiveQuorum : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂, v]⟩) := by
  classical
  let deliver₁ := ofEvent ⟨deliverSymb, [l₁, v]⟩
  let deliver₂ := ofEvent ⟨deliverSymb, [l₂, v]⟩
  have hBox :=
    livenessTwoAtPastDownThyHBB3 (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      (l₁ := l₁) (l₂ := l₂) (v := v)
      (hTheory := hTheory)
      (hCorrelation := hCorrelation)
      (hLiveQuorum := hLiveQuorum)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver
  have hBoxPast :=
    Sat.imp_elim (M := M) (w := wTop)
      (φ := ♢ᶠ↓[[]] deliver₁)
      (ψ := □ᶠ↓[[l₂]] deliver₂)
      (by simpa [wTop, deliver₁, deliver₂] using hBox p)
      hDeliver
  have hDiamond :=
    singletonBoxImpliesDiamond (M := M) (w := wTop)
      (l := l₂) (φ := deliver₂) hBoxPast
  simpa [wTop, deliver₁, deliver₂] using hDiamond

end ThyHBB3
end Examples
end ModalDistribution
