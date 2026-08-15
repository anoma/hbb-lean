import ModalDistribution.Examples.ThyHBB2.Axioms
import ModalDistribution.Examples.ThyHBB2.Lemmas
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# ThyHBB2 Agreement Property

This file records the agreement statement for the `ThyHBB2` broadcast theory.
Agreement property for ThyHBB2: under a
sequential quorum intersection between the source learners, any two deliveries
agree on the value.
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

variable {S : Signature}
variable {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Agreement property for ThyHBB2.

Sequential quorum intersections between l₁ and l₂ force any deliveries for
(l₁', l₁) and (l₂', l₂) to agree on the value. This is the agreement property
for the simplified HBB2 protocol without the safe predicate.

See also: `agreementThyHBB1`, `agreementThyHBB3`. -/
theorem agreementThyHBB2
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ l₁' l₂' : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]♢ᶠ[[l₁, l₂]]Formula.seq) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩)) ⇒ᶠ
         (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) ⇒ᶠ
         (v₁ ≃ᶠ v₂) := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hSeqTop : ⟪wTop⟫ ⊨[M] ♢ᶠ[[l₁, l₂]]Formula.seq := by
    simpa [wTop] using hSeq p
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver₁
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver₂
  by_cases hNe : v₁ = v₂
  · simpa [Sat] using hNe
  have hVoteBox₁ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [l₁, v₁]⟩) := by
    -- Apply `Deliver?` to back out the vote quorum supporting the first delivery.
    simpa [wTop]
      using
        deliver_to_vote_box_end (M := M)
          (hTheory := hTheory)
          (reporting := l₁') (learner := l₁)
          (value := v₁) (p := p)
          (hDeliver := hDeliver₁)
  have hVoteBox₂ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [l₂, v₂]⟩) := by
    -- Apply `Deliver?` to back out the vote quorum supporting the second delivery.
    simpa [wTop]
      using
        deliver_to_vote_box_end (M := M)
          (hTheory := hTheory)
          (reporting := l₂') (learner := l₂)
          (value := v₂) (p := p)
          (hDeliver := hDeliver₂)
  have hVoteDiamond₁ :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v₁]⟩) := by
    -- Turn the first vote box into a concrete past vote witness.
    simpa [wTop]
      using
        boxPast_singleton_to_diamond_nil
          (M := M) (w := wTop) (learner := l₁')
          (φ := ofEvent ⟨voteSymb, [l₁, v₁]⟩)
          hVoteBox₁
  have hVoteDiamond₂ :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₂, v₂]⟩) := by
    -- Turn the second vote box into a concrete past vote witness.
    simpa [wTop]
      using
        boxPast_singleton_to_diamond_nil
          (M := M) (w := wTop) (learner := l₂')
          (φ := ofEvent ⟨voteSymb, [l₂, v₂]⟩)
          hVoteBox₂
  have hEchoBox₁ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₁]] (ofEvent ⟨echoSymb, [v₁]⟩) := by
    -- Use `Vote?` to obtain an echo quorum for `v₁`.
    simpa [wTop]
      using
        Vote.to_echo_box_end (M := M)
          (hTheory := hTheory)
          (learner := l₁) (value := v₁)
          (p := p) (hVote := hVoteDiamond₁)
  have hEchoBox₂ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂]] (ofEvent ⟨echoSymb, [v₂]⟩) := by
    -- Use `Vote?` to obtain an echo quorum for `v₂`.
    simpa [wTop]
      using
        ModalDistribution.Examples.ThyHBB2.Vote.to_echo_box_end (M := M)
          (hTheory := hTheory)
          (learner := l₂) (value := v₂)
          (p := p) (hVote := hVoteDiamond₂)
  have hEchoCollision :
      ⟪wTop⟫ ⊨[M]
        (♢ᶠ↓[[]]
            ((ofEvent ⟨echoSymb, [v₁]⟩) ∧ᶠ
              ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))) ∨ᶠ
        (♢ᶠ↓[[]]
            ((ofEvent ⟨echoSymb, [v₂]⟩) ∧ᶠ
              ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))) := by
    -- Use sequentiality between learners to order the two echo events.
    have hDistinct :
        (⟨echoSymb, [v₁]⟩ : Signature.Event S) ≠
          ⟨echoSymb, [v₂]⟩ := by
      intro h
      injection h with _ hArgs
      cases hArgs
      exact hNe rfl
    exact
      seq_two_quorums_eventually
        (M := M) (H := M.history) (w := wTop)
        (l := l₁) (l' := l₂)
        (evt := ⟨echoSymb, [v₁]⟩)
        (evt' := ⟨echoSymb, [v₂]⟩)
        (hTime := rfl)
        (hSeq := hSeqTop)
        (hEvt := hEchoBox₁)
        (hEvt' := hEchoBox₂)
        (hDistinct := hDistinct)
  have hEchoNE : AllWorldValid M (echoNonEquivAxiom echoSymb) := by
    -- Reuse the axiom `EchoNE` from the `ThyHBB2` theory.
    apply hTheory
    simp [theory]
  have hEquality :
      ⟪wTop⟫ ⊨[M] v₁ ≃ᶠ v₂ := by
    -- Combining the ordered echoes with `EchoNE` forces the values to coincide.
    have hSubset : wTop.time ⊆trn M.history.val := by
      simpa [wTop] using History.transitiveSubset_refl (H := M.history)
    cases
        sat_or_cases (M := M) (w := wTop)
          (φ := ♢ᶠ↓[[]]
              ((ofEvent ⟨echoSymb, [v₁]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
          (ψ := ♢ᶠ↓[[]]
              ((ofEvent ⟨echoSymb, [v₂]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)))
          hEchoCollision with
    | inl hLeft =>
        have hEq :=
          ThyHBB1.echoNonEquiv_diamond (M := M)
            (echoSymb := echoSymb)
            (hEchoNE := hEchoNE)
            (hSubset := hSubset)
            (valNow := v₁) (valPast := v₂)
            hLeft
        simpa [Sat] using hEq
    | inr hRight =>
        have hEq :=
          ThyHBB1.echoNonEquiv_diamond (M := M)
            (echoSymb := echoSymb)
            (hEchoNE := hEchoNE)
            (hSubset := hSubset)
            (valNow := v₂) (valPast := v₁)
            hRight
        simpa [Sat] using hEq.symm
  simpa [wTop] using hEquality

/-- When both deliveries for
`(l₁', l₁)` and `(l₂', l₂)` occur, their values coincide. -/
theorem agreementThyHBB2_of_deliveries
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ l₁' l₂' : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]♢ᶠ[[l₁, l₂]]Formula.seq)
    (hDeliver₁ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩))
    (hDeliver₂ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) :
    ⊨[M] v₁ ≃ᶠ v₂ := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hImp :=
    agreementThyHBB2 (M := M)
      (hTheory := hTheory)
      (l₁ := l₁) (l₂ := l₂)
      (l₁' := l₁') (l₂' := l₂')
      (v₁ := v₁) (v₂ := v₂)
      (hSeq := hSeq) p
  have hDeliver₁Top :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩) :=
    by simpa [wTop] using hDeliver₁ p
  have hDeliver₂Top :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩) :=
    by simpa [wTop] using hDeliver₂ p
  have hStep :=
    Sat.imp_elim (M := M) (w := wTop)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩))
      (ψ :=
        (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) ⇒ᶠ
          (v₁ ≃ᶠ v₂))
      hImp hDeliver₁Top
  have hResult :=
    Sat.imp_elim (M := M) (w := wTop)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩))
      (ψ := v₁ ≃ᶠ v₂)
      hStep hDeliver₂Top
  simpa [wTop] using hResult

end ThyHBB2
end Examples
end ModalDistribution
