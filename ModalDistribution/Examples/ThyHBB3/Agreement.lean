import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB3.Axioms
import ModalDistribution.Examples.ThyHBB3.Lemmas
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# ThyHBB3 Agreement Property

This file states the agreement property for `ThyHBB3`, formalising
Agreement property for ThyHBB3. If two learners are everywhere correlated,
then any two deliveries for those learners must agree on the value.
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

/-- Paper: Proposition 8.3.1 (Agreement). Agreement property for ThyHBB3.

Correlation between l₁ and l₂ forces any deliveries for those learners
to agree on the value. This uses the correlation predicate to establish quorum
intersection, which is the key innovation of HBB3.

See also: `agreementThyHBB1`, `agreementThyHBB2`, `agreementFromDeliveriesThyHBB3`. -/
theorem agreementThyHBB3
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v₁ v₂ : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]
      ((♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v₁]⟩)) ⇒ᶠ
        ((♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂, v₂]⟩)) ⇒ᶠ
          (v₁ ≃ᶠ v₂))) := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  -- Instances of key axioms.
  have hVoteNE :
      AllWorldValid M (voteNonEquivAxiom voteSymb correlationSymb) := by
    apply hTheory
    simp [theory]
  -- Correlation supplies sequential intersections and persistence.
  have hSeqGlobal :
      ⊨[M]♢ᶠ[[l₁, l₂]] Formula.seq :=
    correlation_seq_diamond
      (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (voteSymb := voteSymb)
      (deliverSymb := deliverSymb)
      (correlationSymb := correlationSymb)
      (hTheory := hTheory)
      (hCorrelation := hCorrelation)
  have hSeqTop :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[l₁, l₂]] Formula.seq :=
    by simpa [wTop] using hSeqGlobal p
  have hCorrAll :
      □W⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) :=
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
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver₁
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver₂
  by_cases hEq : v₁ = v₂
  · simpa [Sat] using hEq
  -- Back out the supporting vote quorums from the deliveries.
  have hVoteBox₁ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₁]] (ofEvent ⟨voteSymb, [l₁, v₁]⟩) :=
    by
      simpa [wTop]
        using
          deliver_to_vote_box_end
            (M := M)
            (liveSymb := liveSymb)
            (proposeSymb := proposeSymb)
            (echoSymb := echoSymb)
            (voteSymb := voteSymb)
            (deliverSymb := deliverSymb)
            (correlationSymb := correlationSymb)
            (hTheory := hTheory)
            (learner := l₁) (value := v₁)
            (p := p) (hDeliver := hDeliver₁)
  have hVoteBox₂ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂]] (ofEvent ⟨voteSymb, [l₂, v₂]⟩) :=
    by
      simpa [wTop]
        using
          deliver_to_vote_box_end
            (M := M)
            (liveSymb := liveSymb)
            (proposeSymb := proposeSymb)
            (echoSymb := echoSymb)
            (voteSymb := voteSymb)
            (deliverSymb := deliverSymb)
            (correlationSymb := correlationSymb)
            (hTheory := hTheory)
            (learner := l₂) (value := v₂)
            (p := p) (hDeliver := hDeliver₂)
  -- Sequentiality forces one vote to follow the other.
  have hDistinctVotes :
      (⟨voteSymb, [l₁, v₁]⟩ : Signature.EventType S) ≠
        ⟨voteSymb, [l₂, v₂]⟩ := by
    intro hEvt
    cases hEvt
    exact hEq rfl
  have hVoteCollision :
      ⟪wTop⟫ ⊨[M]
        (♢ᶠ↓[[]]
            ((ofEvent ⟨voteSymb, [l₁, v₁]⟩) ∧ᶠ
              ↓ᶠ (ofEvent ⟨voteSymb, [l₂, v₂]⟩))) ∨ᶠ
        (♢ᶠ↓[[]]
            ((ofEvent ⟨voteSymb, [l₂, v₂]⟩) ∧ᶠ
              ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v₁]⟩))) :=
    seq_two_quorums_eventually
      (M := M)
      (H := M.history)
      (w := wTop)
      (l := l₁) (l' := l₂)
      (evt := ⟨voteSymb, [l₁, v₁]⟩)
      (evt' := ⟨voteSymb, [l₂, v₂]⟩)
      (hTime := rfl)
      (hSeq := hSeqTop)
      (hEvt :=
        by simpa [wTop] using hVoteBox₁)
      (hEvt' :=
        by simpa [wTop] using hVoteBox₂)
      (hDistinct := hDistinctVotes)
  have hCases :=
    sat_or_cases (M := M) (w := wTop) hVoteCollision
  cases hCases with
  | inl hLeft =>
      -- The first vote occurs now, the second lies in the past.
      have hLeft' :
          ⟪wTop⟫ ⊨[M]
            ♢ᶠ[[]]
              (↓ᶠ
                ((ofEvent ⟨voteSymb, [l₁, v₁]⟩) ∧ᶠ
                  ↓ᶠ (ofEvent ⟨voteSymb, [l₂, v₂]⟩))) :=
        by simpa [Formula.diamondPast] using hLeft
      obtain ⟨q, hPast⟩ :=
        (Sat.diamond_nil (M := M)
            (w := wTop)
            (φ :=
              ↓ᶠ
                ((ofEvent ⟨voteSymb, [l₁, v₁]⟩) ∧ᶠ
                  ↓ᶠ (ofEvent ⟨voteSymb, [l₂, v₂]⟩)))).1
          hLeft'
      obtain ⟨wVote, hw_mem, hw_place, hConj⟩ :=
        (Sat.past (M := M)
            (w := ⟨q, †, wTop.time⟩)
            (φ :=
              (ofEvent ⟨voteSymb, [l₁, v₁]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨voteSymb, [l₂, v₂]⟩))).1
          hPast
      have hPair :=
        (Sat.and (M := M) (w := wVote)
          (φ := ofEvent ⟨voteSymb, [l₁, v₁]⟩)
          (ψ := ↓ᶠ (ofEvent ⟨voteSymb, [l₂, v₂]⟩))).1 hConj
      have hVote_now := hPair.1
      have hVote_past := hPair.2
      have hTimeLe :
          wVote.time ⪯ M.history.val :=
        PreHistory.happensBeforeEq_of_mem
          (P := P) (Event := Signature.EventType S)
          (hmem :=
            by
              simpa [World.place, World.event, World.time]
                using hw_mem)
      have hCorrAlways :=
        hCorrAll (t := wVote) hTimeLe
      have hCorr_now :
          ⟪wVote⟫ ⊨[M] ofPredicate ⟨correlationSymb, [l₁, l₂]⟩ :=
        ModalDistribution.Logic.everytime_now_of_mem
          (M := M) (w := wVote)
          hw_mem hCorrAlways
      have hEqVotes :
          v₁ = v₂ :=
        voteNonEquiv_local
          (M := M)
          (voteSymb := voteSymb)
          (correlationSymb := correlationSymb)
          (hVoteNE := hVoteNE)
          (w := wVote)
          (hMem := hw_mem)
          (learner := l₁)
          (correlated := l₂)
          (valNow := v₁)
          (valPast := v₂)
          (hVote_now := hVote_now)
          (hVote_past := hVote_past)
          (hCorr := hCorr_now)
      exact by simp [Sat, hEqVotes]
  | inr hRight =>
      -- Symmetric case: the second vote is current.
      have hRight' :
          ⟪wTop⟫ ⊨[M]
            ♢ᶠ[[]]
              (↓ᶠ
                ((ofEvent ⟨voteSymb, [l₂, v₂]⟩) ∧ᶠ
                  ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v₁]⟩))) :=
        by simpa [Formula.diamondPast] using hRight
      obtain ⟨q, hPast⟩ :=
        (Sat.diamond_nil (M := M)
            (w := wTop)
            (φ :=
              ↓ᶠ
                ((ofEvent ⟨voteSymb, [l₂, v₂]⟩) ∧ᶠ
                  ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v₁]⟩)))).1
          hRight'
      obtain ⟨wVote, hw_mem, hw_place, hConj⟩ :=
        (Sat.past (M := M)
            (w := ⟨q, †, wTop.time⟩)
            (φ :=
              (ofEvent ⟨voteSymb, [l₂, v₂]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v₁]⟩))).1
          hPast
      have hPair :=
        (Sat.and (M := M) (w := wVote)
          (φ := ofEvent ⟨voteSymb, [l₂, v₂]⟩)
          (ψ := ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v₁]⟩))).1 hConj
      have hVote_now := hPair.1
      have hVote_past := hPair.2
      have hTimeLe :
          wVote.time ⪯ M.history.val :=
        PreHistory.happensBeforeEq_of_mem
          (P := P) (Event := Signature.EventType S)
          (hmem :=
            by
              simpa [World.place, World.event, World.time]
                using hw_mem)
      have hCorrAlways :=
        hCorrAll (t := wVote) hTimeLe
      have hCorrSymmAlways :
          ⟪wVote⟫ ⊨[M]
            ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩) :=
        always_corr_symm
          (M := M)
          (liveSymb := liveSymb)
          (proposeSymb := proposeSymb)
          (echoSymb := echoSymb)
          (voteSymb := voteSymb)
          (deliverSymb := deliverSymb)
          (correlationSymb := correlationSymb)
          (hTheory := hTheory)
          (w := wVote)
          (l₁ := l₁) (l₂ := l₂)
          hCorrAlways
      have hCorr_now :
          ⟪wVote⟫ ⊨[M] ofPredicate ⟨correlationSymb, [l₂, l₁]⟩ :=
        ModalDistribution.Logic.everytime_now_of_mem
          (M := M) (w := wVote)
          hw_mem hCorrSymmAlways
      have hEqVotes :
          v₂ = v₁ :=
        voteNonEquiv_local
          (M := M)
          (voteSymb := voteSymb)
          (correlationSymb := correlationSymb)
          (hVoteNE := hVoteNE)
          (w := wVote)
          (hMem := hw_mem)
          (learner := l₂)
          (correlated := l₁)
          (valNow := v₂)
          (valPast := v₁)
          (hVote_now := hVote_now)
          (hVote_past := hVote_past)
          (hCorr := hCorr_now)
      exact by simp [Sat, hEqVotes.symm]

/-- Paper: Proposition 8.3.1, hypothesis form. If deliveries for learners
`l₁` and `l₂` both occur, their values coincide. -/
theorem agreementThyHBB3_of_deliveries
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v₁ v₂ : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hDeliver₁ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v₁]⟩))
    (hDeliver₂ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂, v₂]⟩)) :
    ⊨[M] v₁ ≃ᶠ v₂ := by
  classical
  exact
    EndValid.imp_elim (M := M)
      (EndValid.imp_elim (M := M)
        (agreementThyHBB3 (M := M)
      (hTheory := hTheory)
      (l₁ := l₁) (l₂ := l₂)
      (v₁ := v₁) (v₂ := v₂)
      (hCorrelation := hCorrelation))
        hDeliver₁)
      hDeliver₂
end ThyHBB3
end Examples
end ModalDistribution
