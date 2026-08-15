import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB2.Axioms
import ModalDistribution.Examples.ThyHBB2.Lemmas
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyHBB1.LivenessHelpers
import ModalDistribution.Core.Semifilter
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Properties.Modalities

/-!
# ThyHBB2 Liveness 1

This file records the Liveness~1 statement for `ThyHBB2`, mirroring
Liveness property 1 for ThyHBB2. Under a live quorum for learner `l` and a
unique proposed value, any live participant that learns about the proposal will
eventually deliver it for `(l,l)`.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB2

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

/-- If learner `l` has a live quorum and
there is exactly one proposed value, then any live participant that learns about
the proposal will eventually deliver it for `(l,l)`. -/
theorem livenessOneThyHBB2
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
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
  intro hSeenPropose
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLiveHere
  have hThyLive : M ⊨ᵀ ThyLive liveSymb := by
    intro ax hAx
    exact hTheory (Or.inl hAx)
  have hLiveQuorumTop :
      ⟪wTop⟫ ⊨[M] □ᶠ[[l]]predicate0 liveSymb := by
    -- Instantiate the live-quorum hypothesis (assumption preceding Step 1).
    simpa [wTop] using hLiveQuorum p
  have hUniqueTop :
      ⟪wTop⟫ ⊨[M] ∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩) := by
    -- Instantiate the uniqueness guard used in Step 2.
    simpa [wTop] using hUnique p
  have hProposeWitness :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) := by
    -- Restate the antecedent: beginning of Step 1.
    simpa [wTop] using hSeenPropose
  have hProposeQuorumGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :=
    live_eventually_knows_event (M := M)
      (liveSymb := liveSymb)
      (l := l)
      (evt := ⟨proposeSymb, [v]⟩)
      (hTheory := hThyLive)
      (hLive := hLiveQuorum)
      (hEvent :=
        by
          intro q
          obtain ⟨q', hPast⟩ :=
            (Sat.diamond_nil (M := M)
              (w := wTop)
              (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)))).1
              (by simpa [Formula.diamondPast] using hProposeWitness)
          have hDiamond :=
            (Sat.diamond_nil (M := M)
              (w := ⟨q, †, M.history.val⟩)
              (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)))).2
              ⟨q', by simpa [wTop] using hPast⟩
          simpa [Formula.diamondPast]
            using hDiamond)
  have hProposeQuorum :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :=
    by simpa [wTop] using hProposeQuorumGlobal p
  have hImpEcho :
      □W⊨[M]
        (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨echoSymb, [v]⟩) :=
    ThyHBB1.uniquePropose_eventually_echo (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (value := v)
      (hEcho := by
        apply hTheory
        simp [theory])
      (hEchoBack := by
        apply hTheory
        simp [theory])
      (hUnique := hUnique)
  have hEchoQuorumGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨echoSymb, [v]⟩) :=
    ThyHBB1.atddot_live_of_eventual_quorum
      (M := M)
      (liveSymb := liveSymb)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
      (ψ := ofEvent ⟨echoSymb, [v]⟩)
      (l := l)
      (hLiveTheory := hThyLive)
      (hQuorum := hProposeQuorumGlobal)
      (hImp := hImpEcho)
  have hEchoQuorum :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨echoSymb, [v]⟩) :=
    by simpa [wTop] using hEchoQuorumGlobal p
  have hEchoNestedGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
    promote_live_atddot
      (M := M)
      (liveSymb := liveSymb)
      (l := l)
      (φ := ofEvent ⟨echoSymb, [v]⟩)
      (hTheory := hThyLive)
      (hQuorum := hEchoQuorumGlobal)
  have hEchoNested :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
    by simpa [wTop] using hEchoNestedGlobal p
  have hVotesGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩) := by
    intro q
    have hEchoBox := hEchoNestedGlobal q
    have hVoteBox :=
      live_vote_box_from_echo (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (hTheory := hTheory)
        (l₂' := l) (learner := l) (value := v) (p := q)
        (hEchoBox := hEchoBox)
    exact hVoteBox
  have hVotesBox :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩) :=
    by simpa [wTop] using hVotesGlobal p

  have hVoteEventually :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩) := by
    classical
    have hBoxPast :
        ⟪wTop⟫ ⊨[M]
          □ᶠ[[l]]
            (↓ᶠ (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l, v]⟩)) := by
      simpa [Formula.boxPast]
        using hVotesBox
    obtain ⟨O, hO, hAll⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [l, v]⟩))).1 hBoxPast
    obtain ⟨q, hq⟩ :=
      (M.learner l).quorum_nonempty hO
    have hPastLiveVote :=
      hAll q hq
    have hDiamondConj :
        ⟪wTop⟫ ⊨[M]
          ♢ᶠ↓[[]]
            ((predicate0 liveSymb) ∧ᶠ
              ofEvent ⟨voteSymb, [l, v]⟩) := by
      have hDiamond :=
        (Sat.diamond_nil (M := M)
          (w := wTop)
          (φ := ↓ᶠ ((predicate0 liveSymb) ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩))).2
          ⟨q, hPastLiveVote⟩
      simpa [Formula.diamondPast]
        using hDiamond
    exact
      diamondPast_nil_strip_left (M := M)
        (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ofEvent ⟨voteSymb, [l, v]⟩)
        hDiamondConj

  have hLiveKnowsVotes :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l]] (ofEvent ⟨voteSymb, [l, v]⟩)) := by
    -- Step 5: knowledge axiom (`live_eventually_knows_box`) on the vote quorum.
    classical
    have hKnow :=
      live_eventually_knows_box (M := M)
        (liveSymb := liveSymb)
        (l := l)
        (φ := ofEvent ⟨voteSymb, [l, v]⟩)
        (hTheory := hThyLive)
        (hQuorum := hVotesGlobal)
    simpa [wTop]
      using hKnow p
  have hDeliverEventually :
      ⟪wTop⟫ ⊨[M]
        ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
    -- Step 6: combine Step 5 with `Deliver!` via `ThyHBB1.deliver_from_vote_box`.
    classical
    have hDeliverAx : AllWorldValid M
        (deliverForwardAxiom liveSymb voteSymb deliverSymb) := by
      apply hTheory
      simp [theory]
    have hVotesSometime :
        ⟪wTop⟫ ⊨[M]
          ↕ᶠ (□ᶠ↓[[l]] (ofEvent ⟨voteSymb, [l, v]⟩)) :=
      (Sat.imp (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (□ᶠ↓[[l]] (ofEvent ⟨voteSymb, [l, v]⟩)))).1
        hLiveKnowsVotes hLiveHere
    exact
      ThyHBB1.deliver_from_vote_box (M := M)
        (liveSymb := liveSymb) (voteSymb := voteSymb) (deliverSymb := deliverSymb)
        (reporting := l) (learner := l) (value := v)
        (hThyLive := hThyLive)
        (hDeliverAx := hDeliverAx)
        (p := p)
        (hLiveTop := hLiveHere)
        (hVotesTop := hVotesSometime)
  have hGoal :
      ⟪wTop⟫ ⊨[M]
        ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
    -- Step 7: combine Step 6 with the local `live` hypothesis.
    exact
      (Sat.imp (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩))).1
        (Sat.imp_intro (M := M) (w := wTop)
          (φ := predicate0 liveSymb) (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩))
          (by
            intro hLive
            exact hDeliverEventually))
        hLiveHere
  simpa [wTop] using hGoal

/-- When the guarded proposal
diamond holds, every member of learner `l`'s quorum knows (in the past) that the
value was delivered. -/
theorem livenessOneAtPastDownThyHBB2
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M](♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
         □ᶠ↓[[l]] (ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
  classical
  let φAnte :=
    predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)
  let deliverEvt := ofEvent ⟨deliverSymb, [l, l, v]⟩
  have hMain :=
    livenessOneThyHBB2 (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (l := l) (v := v)
      (hTheory := hTheory)
      (hLiveQuorum := hLiveQuorum)
      (hUnique := hUnique)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hLiveTop : ⟪wTop⟫ ⊨[M] □ᶠ[[l]] predicate0 liveSymb :=
    by simpa [wTop] using hLiveQuorum p
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hAnte
  obtain ⟨rProp, hPastAnte⟩ :=
    (Sat.diamond_nil (M := M) (w := wTop)
        (φ := Formula.past φAnte)).1
      (by simpa [Formula.diamondPast, φAnte, wTop] using hAnte)
  obtain ⟨O, hO, hAllLive⟩ :=
    (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l)
        (φ := predicate0 liveSymb)).1
      hLiveTop
  refine
    (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l)
        (φ := ↓ᶠ deliverEvt)).2
      ⟨O, hO, ?_⟩
  intro q hqO
  set wq : World P (Signature.EventType S) := ⟨q, †, M.history.val⟩
  have hAnte_q :
      ⟪wq⟫ ⊨[M] ♢ᶠ↓[[]] φAnte := by
    have hPastWitness :
        ⟪⟨rProp, †, wq.time⟩⟫ ⊨[M] Formula.past φAnte := by
      simpa [wq, wTop, World.time, φAnte] using hPastAnte
    exact
      (Sat.diamond_nil (M := M) (w := wq)
          (φ := Formula.past φAnte)).2
        ⟨rProp, hPastWitness⟩
  have hImp_q :
      ⟪wq⟫ ⊨[M]
        (♢ᶠ↓[[]] φAnte) ⇒ᶠ
          (predicate0 liveSymb ⇒ᶠ ↕ᶠ deliverEvt) := by
    simpa [wq, φAnte, deliverEvt] using hMain q
  have hStep :=
    Sat.imp_elim (M := M) (w := wq)
      (φ := ♢ᶠ↓[[]] φAnte)
      (ψ := predicate0 liveSymb ⇒ᶠ ↕ᶠ deliverEvt)
      hImp_q hAnte_q
  have hLive_q : ⟪wq⟫ ⊨[M] predicate0 liveSymb :=
    by simpa [wq, wTop, World.time] using hAllLive q hqO
  have hEventual :=
    Sat.imp_elim (M := M) (w := wq)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ deliverEvt)
      hStep hLive_q
  have hPastDeliver_q :
      ⟪wq⟫ ⊨[M] ↓ᶠ deliverEvt :=
    by
      have hPast :=
        (Sat.atEnd (M := M) (w := wq)
          (φ := Formula.past deliverEvt)).1
          (by
            simpa [Formula.sometime]
              using hEventual)
      simpa using hPast
  exact hPastDeliver_q

/-- The guarded proposal diamond
ensures the delivery diamond for learner `l`. -/
theorem livenessOneAtPastThyHBB2
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M](♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
  classical
  let φAnte :=
    predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)
  let deliverEvt := ofEvent ⟨deliverSymb, [l, l, v]⟩
  have hBox :=
    livenessOneAtPastDownThyHBB2 (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (l := l) (v := v)
      (hTheory := hTheory)
      (hLiveQuorum := hLiveQuorum)
      (hUnique := hUnique)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hAnte
  have hBoxPast :=
    Sat.imp_elim (M := M) (w := wTop)
      (φ := ♢ᶠ↓[[]] φAnte)
      (ψ := □ᶠ↓[[l]] deliverEvt)
      (by simpa [wTop, φAnte, deliverEvt] using hBox p)
      hAnte
  have hDiamond :=
    singletonBoxImpliesDiamond (M := M) (w := wTop)
      (l := l) (φ := deliverEvt) hBoxPast
  simpa [wTop, φAnte, deliverEvt] using hDiamond

end ThyHBB2
end Examples
end ModalDistribution
