import ModalDistribution.Examples.ThyHBB2.Axioms
import ModalDistribution.Examples.ThyHBB2.Lemmas
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Examples.ThyHBB1.LivenessHelpers
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Properties.Modalities

/-!
# ThyHBB2 Liveness 2

This file records the Liveness~2 statement for `ThyHBB2`, matching
Liveness property 2 for ThyHBB2. Intersecting reporting quorums together
with a live quorum for `l₂'` ensure that deliveries for `(l₁',\thel)` propagate
to `(l₂',\thel)`.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB2

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

/-- If reporting learners `l₁'` and `l₂'`
have intersecting quorums and learner `l₂'` is live, then any delivery for
`(l₁', \thel)` propagates to `(l₂', \thel)`. -/
lemma livenessTwoThyHBB2
    (hTheory : M ⊨ᵀ
      ThyHBB2 liveSymb proposeSymb echoSymb voteSymb deliverSymb)
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
  have hIntersectTop :
      ⟪wTop⟫ ⊨[M] ♢ᶠ[[l₁', l₂']]⊤ᶠ := by
    -- Instantiate the quorum intersection assumption at the top world.
    simpa [wTop] using hIntersect p
  have hLiveQuorumTop :
      ⟪wTop⟫ ⊨[M] □ᶠ[[l₂']]predicate0 liveSymb := by
    -- Instantiate the live quorum assumption for `l₂'` at the top world.
    simpa [wTop] using hLive p
  have hVoteBox :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [ℓ, v]⟩) := by
    -- Use `Deliver?` to extract the votes that justify the source delivery.
    simpa [wTop]
      using
        deliver_to_vote_box_end (M := M)
          (hTheory := hTheory)
          (reporting := l₁') (learner := ℓ)
          (value := v) (p := p)
          (hDeliver := hDeliverSource)
  have hVoteTransfer :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [ℓ, v]⟩) := by
    -- Combine quorum intersection and live knowledge to move the vote to a live participant.
    simpa [wTop]
      using
        live_vote_transfer (M := M)
          (hTheory := hTheory)
          (l₁' := l₁') (l₂' := l₂')
          (learner := ℓ) (value := v)
          (p := p)
          (hIntersect := hIntersect)
          (hLive := hLive)
          (hVote := hVoteBox)
  have hVoteEchoDiamond :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    -- Refine the vote witness using `Vote?` to expose the echo quorum.
    simpa [wTop]
      using
        vote_live_to_echo_diamond
          (M := M)
          (hTheory := hTheory)
          (learner := ℓ) (value := v)
          (p := p)
          (hVote := hVoteTransfer)
  have hLiveEchoBox :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂']] (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    -- Promote the echo diamond across the intersecting quorums for `l₂'`.
    classical
    have hThyLive : M ⊨ᵀ ThyLive liveSymb := by
      intro ax hAx
      exact hTheory (Or.inl hAx)
    obtain ⟨qEcho, hPastEcho⟩ :=
      (Sat.diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)))).1
        (by simpa [Formula.diamondPast, wTop] using hVoteEchoDiamond)
    have hQuorumGlobal : ⊨[M] ♢ᶠ↓[[]](
        predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)) := by
      intro q
      refine (Sat.diamond_nil (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)))).2
        ⟨qEcho, ?_⟩
      simpa [wTop] using hPastEcho
    have hBoxGlobal :=
      live_eventually_knows_quorum (M := M) (liveSymb := liveSymb)
        (l := l₂') (l₁ := ℓ)
        (evt := ⟨echoSymb, [v]⟩)
        (hTheory := hThyLive) (hLive := hLive)
        (hQuorum := hQuorumGlobal)
    simpa [wTop] using hBoxGlobal p
  have hVoteBoxTarget :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂']] (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [ℓ, v]⟩) := by
    -- Use `Vote!` to turn echo quorums for live learners into votes.
    simpa [wTop]
      using
        live_vote_box_from_echo (M := M)
          (hTheory := hTheory)
          (l₂' := l₂') (learner := ℓ)
          (value := v) (p := p)
          (hEchoBox := hLiveEchoBox)
  have hLiveKnowsVotes :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [ℓ, v]⟩)) := by
    -- Live knowledge eventually learns the vote quorums.
    classical
    have hThyLive : M ⊨ᵀ ThyLive liveSymb := by
      intro ax hAx
      exact hTheory (Or.inl hAx)
    refine Sat.imp_intro (M := M) (w := wTop) ?_
    intro hLiveTop
    have hAtEnd :
        ⟪wTop⟫ ⊨[M]
          ⤒ᶠ (□ᶠ↓[[l₂']] (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [ℓ, v]⟩)) :=
      (Sat.atEnd (M := M)
        (w := wTop)
        (φ := □ᶠ↓[[l₂']] (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [ℓ, v]⟩))).2
        (by simpa [wTop] using hVoteBoxTarget)
    have hKnowledge : AllWorldValid M
        (knowledgeDiamondEventuallyAxiom (S := S)
          liveSymb [l₂'] (ofEvent ⟨voteSymb, [ℓ, v]⟩)) :=
      (@hThyLive
        (knowledgeDiamondEventuallyAxiom (S := S)
          liveSymb [l₂'] (ofEvent ⟨voteSymb, [ℓ, v]⟩)))
        (by
          dsimp [ThyLive]
          exact Or.inr (Or.inr (Or.inr ⟨[l₂'], ofEvent ⟨voteSymb, [ℓ, v]⟩, rfl⟩)))
    have hImp :=
      (Sat.imp (M := M) (w := wTop)
        (φ := ⤒ᶠ (□ᶠ↓[[l₂']] (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [ℓ, v]⟩)))
        (ψ := predicate0 liveSymb ⇒ᶠ
              ↕ᶠ (□ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [ℓ, v]⟩)))).1
        (AllWorldValid.at_end
          (M := M)
          (φ := knowledgeDiamondEventuallyAxiom (S := S)
              liveSymb [l₂'] (ofEvent ⟨voteSymb, [ℓ, v]⟩))
          hKnowledge p) hAtEnd
    exact
      (Sat.imp (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (□ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [ℓ, v]⟩)))).1
        hImp hLiveTop
  have hDeliverEventually :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
    -- Apply `Deliver!` once the vote quorum is known by all live members.
    classical
    have hThyLive : M ⊨ᵀ ThyLive liveSymb := by
      intro ax hAx
      exact hTheory (Or.inl hAx)
    have hDeliverAx : AllWorldValid M
        (deliverForwardAxiom liveSymb voteSymb deliverSymb) := by
      apply hTheory
      simp [ThyHBB2]
    refine Sat.imp_intro (M := M) (w := wTop) ?_
    intro hLiveTop
    have hVotesTop :
        ⟪wTop⟫ ⊨[M]
          ↕ᶠ (□ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [ℓ, v]⟩)) :=
      (Sat.imp (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (□ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [ℓ, v]⟩)))).1
        hLiveKnowsVotes hLiveTop
    exact
      deliver_from_vote_box (M := M)
        (liveSymb := liveSymb)
        (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (reporting := l₂') (learner := ℓ) (value := v)
        (hThyLive := hThyLive)
        (hDeliverAx := hDeliverAx)
        (p := p)
        (hLiveTop := hLiveTop)
        (hVotesTop := hVotesTop)
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

/-- A delivery for `(l₁', ℓ)`
forces every member of `l₂'`'s quorum to know (in the past) that `(l₂', ℓ)` was
delivered. -/
lemma livenessTwoAtPastDownThyHBB2
    (hTheory : M ⊨ᵀ
      ThyHBB2 liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂']] (ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
  classical
  let deliver₁ := ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩
  let deliver₂ := ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩
  have hMain :=
    livenessTwoThyHBB2 (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb)
      (l₁' := l₁') (l₂' := l₂') (ℓ := ℓ) (v := v)
      (hTheory := hTheory)
      (hIntersect := hIntersect)
      (hLive := hLive)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hLiveTop : ⟪wTop⟫ ⊨[M] □ᶠ[[l₂']] predicate0 liveSymb :=
    by simpa [wTop] using hLive p
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver
  obtain ⟨rDeliver, hPastDeliver⟩ :=
    (Sat.diamond_nil (M := M) (w := wTop)
        (φ := Formula.past deliver₁)).1
      (by simpa [Formula.diamondPast, deliver₁, wTop] using hDeliver)
  obtain ⟨O, hO, hAllLive⟩ :=
    (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₂')
        (φ := predicate0 liveSymb)).1
      hLiveTop
  refine
    (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₂')
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
    simpa [wq, deliver₁, deliver₂]
      using hMain q
  have hNext :=
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
      hNext hLive_q
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

/-- A delivery for `(l₁', ℓ)`
eventually yields a delivery for `(l₂', ℓ)`. -/
lemma livenessTwoAtPastThyHBB2
    (hTheory : M ⊨ᵀ
      ThyHBB2 liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
  classical
  let deliver₁ := ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩
  let deliver₂ := ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩
  have hBox :=
    livenessTwoAtPastDownThyHBB2 (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb)
      (l₁' := l₁') (l₂' := l₂') (ℓ := ℓ) (v := v)
      (hTheory := hTheory)
      (hIntersect := hIntersect)
      (hLive := hLive)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver
  have hBoxPast :=
    Sat.imp_elim (M := M) (w := wTop)
      (φ := ♢ᶠ↓[[]] deliver₁)
      (ψ := □ᶠ↓[[l₂']] deliver₂)
      (by simpa [wTop, deliver₁, deliver₂] using hBox p)
      hDeliver
  have hDiamond :=
    singletonBoxImpliesDiamond (M := M) (w := wTop)
      (l := l₂') (φ := deliver₂) hBoxPast
  simpa [wTop, deliver₁, deliver₂] using hDiamond

end ThyHBB2
end Examples
end ModalDistribution
