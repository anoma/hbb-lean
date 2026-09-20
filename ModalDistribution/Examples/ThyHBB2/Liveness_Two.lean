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
with a live quorum for `reporting₂` ensure that deliveries for `(reporting₁,\thel)` propagate
to `(reporting₂,\thel)`.
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

/-- Paper: Proposition 7.2.2 (Liveness 2). Under the stated quorum
conditions, a delivery reported by `reporting₁` entails a delivery reported by
`reporting₂` at every participant live at the final history. The target learner
and value are preserved; delivery is somewhere in the participant's history. -/
theorem livenessTwo
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {reporting₁ reporting₂ ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ∀ Q ∈ (M.learner reporting₁).quorums,
      ∀ R ∈ (M.learner reporting₂).quorums, ∃ q, q ∈ Q ∧ q ∈ R)
    (hLive : ∃ Q ∈ (M.learner reporting₂).quorums,
      ∀ q ∈ Q, ⟪finalWorld M q⟫ ⊨[M] predicate0 liveSymb)
    (hDelivered : Occurs M (ofEvent ⟨deliverSymb, [reporting₁, ℓ, v]⟩))
    (p : P) (hLiveParticipant : ⟪finalWorld M p⟫ ⊨[M] predicate0 liveSymb) :
    OccursAt M p (ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩) := by
  classical
  have hIntersect : ⊨[M]♢ᶠ[[reporting₁, reporting₂]]⊤ᶠ := by
    intro q
    apply (sat_diamond_pair_iff M _ reporting₁ reporting₂ ⊤ᶠ).2
    intro Q hQ R hR
    obtain ⟨r, hrQ, hrR⟩ := hIntersect Q hQ R hR
    exact ⟨r, ⟨hrQ, hrR⟩, by intro h; exact h⟩
  have hLive : ⊨[M]□ᶠ[[reporting₂]]predicate0 liveSymb := by
    intro q
    exact quorumAt_iff.mp hLive
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hDeliverSource := (occurs_iff_end_diamondPast.mp hDelivered) p
  have hLiveHere := hLiveParticipant
  change ⟪wTop⟫ ⊨[M] ↕ᶠ (ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩)
  have hVoteBox :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[reporting₁]] (ofEvent ⟨voteSymb, [ℓ, v]⟩) := by
    -- Use `Deliver?` to extract the votes that justify the source delivery.
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := theory_deliverBackward (M := M) hTheory)
          (reporting := reporting₁) (learner := ℓ)
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
          (reporting₁ := reporting₁) (reporting₂ := reporting₂)
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
      ⊨[M]□ᶠ↓[[reporting₂]] (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[ℓ]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    -- Promote the echo diamond across the intersecting quorums for `reporting₂`.
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
        (l := reporting₂) (l₁ := ℓ)
        (evt := ⟨echoSymb, [v]⟩)
        (hTheory := hThyLive) (hLive := hLive)
        (hQuorum := hQuorumGlobal)
    exact hBoxGlobal
  have hVoteBoxGlobal :
      ⊨[M]□ᶠ↓[[reporting₂]] (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [ℓ, v]⟩) := by
    -- Use `Vote!` to turn echo quorums for live learners into votes.
    intro q
    exact
      live_vote_box_from_echo (M := M)
        (hTheory := hTheory)
        (reporting₂ := reporting₂) (learner := ℓ)
        (value := v) (p := q)
        (hEchoBox := by simpa [wTop] using hLiveEchoBoxGlobal q)
  -- Lemma 6.4.3, applied to (Knowledge□↓) and (Deliver!): eventual vote
  -- knowledge becomes eventual delivery.
  have hThyLive : M ⊨ᵀ ThyLive liveSymb :=
    fun _ hAx => hTheory (Or.inl hAx)
  have hDeliverEventually :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩) := by
    have hGlobal :=
      ThyHBB1.live_eventually_consequent (M := M)
        (hLiveTheory := hThyLive)
        (φ := □ᶠ↓[[reporting₂]] (ofEvent ⟨voteSymb, [ℓ, v]⟩))
        (ψ := ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩)
        (hLive :=
          live_eventually_knows_box (hAllowed := .event _) (M := M)
            (liveSymb := liveSymb)
            (l := reporting₂) (φ := ofEvent ⟨voteSymb, [ℓ, v]⟩)
            (hTheory := hThyLive)
            (hQuorum := hVoteBoxGlobal))
        (hImp := HBB.deliverForward_imp (M := M)
          (theory_deliverForward (M := M) hTheory))
    simpa [wTop] using hGlobal p
  have hGoal :
      ⟪wTop⟫ ⊨[M]
        ↕ᶠ (ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩) := by
    -- Combine the eventual delivery implication with the local `live` hypothesis.
    exact
      (Sat.imp (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩))).1
        hDeliverEventually hLiveHere
  simpa [wTop] using hGoal

/-- Paper-facing modal form of livenessTwo. -/
theorem livenessTwo_modal
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {reporting₁ reporting₂ ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[reporting₁, reporting₂]]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[reporting₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, ℓ, v]⟩)) ⇒ᶠ
         predicate0 liveSymb ⇒ᶠ
         ↕ᶠ(ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩) := by
  intro p hObserved hLiveParticipant
  apply livenessTwo hTheory
  · intro Q hQ R hR
    obtain ⟨q, hq, _⟩ := (sat_diamond_pair_iff M _ reporting₁ reporting₂ ⊤ᶠ).mp (hIntersect p) Q hQ R hR
    exact ⟨q, hq.1, hq.2⟩
  · exact quorumAt_iff.mpr (hLive p)
  · exact observedAt_final_iff.mp (observedAt_iff.mpr hObserved)
  · exact hLiveParticipant

/-- Paper: Proposition 7.2.2, first corollary. A delivery for `(reporting₁, ℓ)`
forces every member of `reporting₂`'s quorum to know (in the past) that `(reporting₂, ℓ)` was
delivered. -/
theorem livenessTwo_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {reporting₁ reporting₂ ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[reporting₁, reporting₂]]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[reporting₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, ℓ, v]⟩)) ⇒ᶠ
         □ᶠ↓[[reporting₂]] (ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      livenessTwo_modal (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (reporting₁ := reporting₁) (reporting₂ := reporting₂) (ℓ := ℓ) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hLive := hLive))
/-- Paper: Proposition 7.2.2, second corollary. A delivery for `(reporting₁, ℓ)`
eventually yields a delivery for `(reporting₂, ℓ)`. -/
theorem livenessTwo_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {reporting₁ reporting₂ ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[reporting₁, reporting₂]]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[reporting₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, ℓ, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      livenessTwo_modal (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (reporting₁ := reporting₁) (reporting₂ := reporting₂) (ℓ := ℓ) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hLive := hLive))
end ThyHBB2
end Examples
end ModalDistribution
