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

/-- Paper: Proposition 6.4.5 (Liveness 2). Under the stated quorum and safety
conditions, a delivery reported by `reporting₁` entails a delivery reported by
`reporting₂` at every participant live at the final history. The target learner
and value are preserved; delivery is somewhere in the participant's history. -/
theorem livenessTwo
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {reporting₁ reporting₂ l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ∀ Q ∈ (M.learner reporting₁).quorums,
      ∀ R ∈ (M.learner reporting₂).quorums, ∃ q, q ∈ Q ∧ q ∈ R)
    (hSafe : ∀ q, ⟪finalWorld M q⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ∃ Q ∈ (M.learner reporting₂).quorums,
      ∀ q ∈ Q, ⟪finalWorld M q⟫ ⊨[M] predicate0 liveSymb)
    (hDelivered : Occurs M (ofEvent ⟨deliverSymb, [reporting₁, l, v]⟩))
    (p : P) (hLiveParticipant : ⟪finalWorld M p⟫ ⊨[M] predicate0 liveSymb) :
    OccursAt M p (ofEvent ⟨deliverSymb, [reporting₂, l, v]⟩) := by
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
  have hDeliver := (occurs_iff_end_diamondPast.mp hDelivered) p
  have hLivep := hLiveParticipant
  change ⟪wTop⟫ ⊨[M] ↕ᶠ (ofEvent ⟨deliverSymb, [reporting₂, l, v]⟩)

  have hThyLiveTheory : M ⊨ᵀ ThyLive liveSymb :=
    theory_thyLive (M := M) hTheory

  -- (Deliver?) with Lemma 4.2.3(2): the delivery forces an end-of-time
  -- quorum of votes at the reporting learner.
  have hVoteBoxTop :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[reporting₁]] (ofEvent ⟨voteSymb, [l, v]⟩) := by
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := theory_deliverBackward (M := M) hTheory)
          (reporting := reporting₁) (learner := l)
          (value := v) (p := p)
          (hDeliver := hDeliver)
  have hVoteBoxGlobal :
      ⊨[M]□ᶠ↓[[reporting₁]] (ofEvent ⟨voteSymb, [l, v]⟩) := fun q => by
    simpa [wTop] using hVoteBoxTop

  -- Proposition 5.2.11: the intersecting live quorum exposes a live voter.
  have hLiveVote :
      ⊨[M]♢ᶠ↓[[]]
        ((predicate0 liveSymb) ∧ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
    have h :=
      intertwined_two_quorums (M := M)
        (liveSymb := liveSymb) (l := reporting₁) (l₁ := reporting₂)
        (φ := ofEvent ⟨voteSymb, [l, v]⟩)
        (hTheory := hThyLiveTheory)
        (hIntersect := by intro q; simpa using hIntersect q)
        (hLiveQuorum := by intro q; simpa using hLive q)
        (hWitness := by intro q; simpa using hVoteBoxGlobal q)
    intro q
    simpa using h q

  -- (Vote?): each live voter knows an echo quorum.
  have hLiveEcho :
      ⊨[M]♢ᶠ↓[[]]
        ((predicate0 liveSymb) ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    intro q
    obtain ⟨qVote, hPastConj⟩ :=
      (Sat.diamond_nil (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [l, v]⟩))).1
        (by simpa [Formula.diamondPast] using hLiveVote q)
    obtain ⟨tVote, ht_mem, ht_place, hConjLocal⟩ :=
      (Sat.past (M := M)
        (w := ⟨qVote, †, M.history.val⟩)
        (φ := predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [l, v]⟩)).1 hPastConj
    have hConjSplit :=
      (Sat.and (M := M) (w := tVote)
        (φ := predicate0 liveSymb)
        (ψ := ofEvent ⟨voteSymb, [l, v]⟩)).1
        (by simpa using hConjLocal)
    have ht_mem_history : tVote ∈ M.history.val := by
      simpa [World.time] using ht_mem
    have hEchoBox :
        ⟪tVote⟫ ⊨[M] □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩) :=
      (voteBackward_elim (M := M)
        (hAx := theory_voteBackward (M := M) hTheory)
        (hMem := ht_mem_history)
        (hVote := hConjSplit.2)).2
    have hConjTarget :
        ⟪tVote⟫ ⊨[M]
          predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩) :=
      (Sat.and (M := M) (w := tVote)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).2
        ⟨hConjSplit.1, hEchoBox⟩
    have hPastConj' :
        ⟪⟨qVote, †, M.history.val⟩⟫ ⊨[M]
          ↓ᶠ (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
      Sat.past_intro_of_prefix (M := M)
        (w := ⟨qVote, †, M.history.val⟩)
        (t := tVote)
        (ht := ht_mem)
        (hp := ht_place)
        (hφ := hConjTarget)
    have hDiamond :=
      sat_diamondEmpty_of_local (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)))
        ⟨qVote, hPastConj'⟩
    simpa [Formula.diamondPast, Formula.diamondEmpty, id]
      using hDiamond

  -- Corollary 5.2.9(3): the live quorum eventually knows the echo quorum.
  have hStep4Global :
      ⊨[M]□ᶠ↓[[reporting₂]]
        (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    have hLiveGlobal :
        ⊨[M]□ᶠ[id [reporting₂]] predicate0 liveSymb := by
      intro q
      simpa using hLive q
    have hBoxGlobal :=
      live_eventually_knows_quorum
        (M := M) (liveSymb := liveSymb)
        (l := reporting₂) (l₁ := l)
        (evt := ⟨echoSymb, [v]⟩)
        (hTheory := hThyLiveTheory)
        (hLive := hLiveGlobal)
        (hQuorum := by intro q; simpa using hLiveEcho q)
    intro q
    simpa using hBoxGlobal q

  -- Lemma 6.4.2(2) with (Vote!): the safe learner's quorum eventually votes.
  -- Safety enters through `voteForward_imp`, i.e. Lemma 6.4.1.
  have hVotesGlobal :
      ⊨[M]□ᶠ↓[[reporting₂]]
        (predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [l, v]⟩) :=
    boxPast_live_of_eventual_quorum
      (M := M) (liveSymb := liveSymb)
      (φ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
      (ψ := ofEvent ⟨voteSymb, [l, v]⟩)
      (l := reporting₂)
      (hLiveTheory := hThyLiveTheory)
      (hQuorum := hStep4Global)
      (hImp := voteForward_imp (M := M)
        (hTheory := hTheory) (hSafe := hSafe))

  -- Lemma 6.4.3, applied to (Knowledge□↓) and (Deliver!): eventual vote
  -- knowledge becomes eventual delivery.
  have hDeliverEventually :
      ⊨[M](predicate0 liveSymb ⇒ᶠ
        ↕ᶠ (ofEvent ⟨deliverSymb, [reporting₂, l, v]⟩)) :=
    live_eventually_consequent (M := M)
      (hLiveTheory := hThyLiveTheory)
      (φ := □ᶠ↓[[reporting₂]] (ofEvent ⟨voteSymb, [l, v]⟩))
      (ψ := ofEvent ⟨deliverSymb, [reporting₂, l, v]⟩)
      (hLive :=
        _root_.ModalDistribution.Examples.live_eventually_knows_box (hAllowed := .event _)
          (M := M) (liveSymb := liveSymb)
          (l := reporting₂) (φ := ofEvent ⟨voteSymb, [l, v]⟩)
          (hTheory := hThyLiveTheory)
          (hQuorum := hVotesGlobal))
      (hImp := HBB.deliverForward_imp (M := M)
        (theory_deliverForward (M := M) hTheory))
  exact
    Sat.imp_elim (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [reporting₂, l, v]⟩))
      (by simpa [wTop] using hDeliverEventually p) hLivep

/-- Paper-facing modal form of livenessTwo. -/
theorem livenessTwo_modal
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {reporting₁ reporting₂ l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[reporting₁, reporting₂]]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[reporting₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, l, v]⟩)) ⇒ᶠ
         predicate0 liveSymb ⇒ᶠ
         ↕ᶠ(ofEvent ⟨deliverSymb, [reporting₂, l, v]⟩) := by
  intro p hObserved hLiveParticipant
  apply livenessTwo hTheory
  · intro Q hQ R hR
    obtain ⟨q, hq, _⟩ := (sat_diamond_pair_iff M _ reporting₁ reporting₂ ⊤ᶠ).mp (hIntersect p) Q hQ R hR
    exact ⟨q, hq.1, hq.2⟩
  · exact hSafe
  · exact quorumAt_iff.mpr (hLive p)
  · exact observedAt_final_iff.mp (observedAt_iff.mpr hObserved)
  · exact hLiveParticipant

/-- Paper: Proposition 6.4.5, first corollary. Corollary: a delivery for `(reporting₁, l)`
forces every `reporting₂`-quorum member to know (in the past) that `(reporting₂, l)` was
delivered. -/
theorem livenessTwo_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {reporting₁ reporting₂ l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[reporting₁, reporting₂]]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[reporting₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, l, v]⟩)) ⇒ᶠ
         □ᶠ↓[[reporting₂]] (ofEvent ⟨deliverSymb, [reporting₂, l, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      livenessTwo_modal (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hSafe := hSafe)
        (hLive := hLive))
/-- Paper: Proposition 6.4.5, second corollary. Corollary: a delivery for `(reporting₁, l)`
forces a delivery for `(reporting₂, l)` somewhere in the past of the history. -/
theorem livenessTwo_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {reporting₁ reporting₂ l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[reporting₁, reporting₂]]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[reporting₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, l, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₂, l, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      livenessTwo_modal (M := M)
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
