import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB2.Axioms
import ModalDistribution.Examples.ThyHBB2.Lemmas
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Examples.ThyHBB1.Safety
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

/-- Paper: Proposition 7.2.2 (Liveness 2). If reporting learners `l₁'` and `l₂'`
have intersecting quorums and learner `l₂'` is live, then any delivery for
`(l₁', \thel)` propagates to `(l₂', \thel)`. -/
theorem livenessTwo
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
  have hLiveEchoBoxGlobal :
      ⊨[M]□ᶠ↓[[l₂']] (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    -- Promote the echo diamond across the intersecting quorums for `l₂'`.
    classical
    have hThyLive : M ⊨ᵀ ThyLive liveSymb := by
      exact fun _ hAx => hTheory (Or.inl hAx)
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
    exact hBoxGlobal
  have hVoteBoxGlobal :
      ⊨[M]□ᶠ↓[[l₂']] (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [ℓ, v]⟩) := by
    -- Use `Vote!` to turn echo quorums for live learners into votes.
    intro q
    exact
      live_vote_box_from_echo (M := M)
        (hTheory := hTheory)
        (l₂' := l₂') (learner := ℓ)
        (value := v) (p := q)
        (hEchoBox := by simpa [wTop] using hLiveEchoBoxGlobal q)
  -- Lemma 6.4.3, applied to (Knowledge□↓) and (Deliver!): eventual vote
  -- knowledge becomes eventual delivery.
  have hThyLive : M ⊨ᵀ ThyLive liveSymb :=
    fun _ hAx => hTheory (Or.inl hAx)
  have hDeliverEventually :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
    have hGlobal :=
      ThyHBB1.live_eventually_consequent (M := M)
        (hLiveTheory := hThyLive)
        (φ := □ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [ℓ, v]⟩))
        (ψ := ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩)
        (hLive :=
          live_eventually_knows_box (M := M)
            (liveSymb := liveSymb)
            (l := l₂') (φ := ofEvent ⟨voteSymb, [ℓ, v]⟩)
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

/-- Paper: Proposition 7.2.2, first corollary. A delivery for `(l₁', ℓ)`
forces every member of `l₂'`'s quorum to know (in the past) that `(l₂', ℓ)` was
delivered. -/
theorem livenessTwo_boxPast
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
      livenessTwo (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (l₁' := l₁') (l₂' := l₂') (ℓ := ℓ) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hLive := hLive))
/-- Paper: Proposition 7.2.2, second corollary. A delivery for `(l₁', ℓ)`
eventually yields a delivery for `(l₂', ℓ)`. -/
theorem livenessTwo_diamondPast
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
      livenessTwo (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (l₁' := l₁') (l₂' := l₂') (ℓ := ℓ) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hLive := hLive))
end ThyHBB2
end Examples
end ModalDistribution
