import ModalDistribution.Examples.HBB
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

open HBB

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

/-- Paper: Proposition 7.2.1 (Agreement). Agreement property for ThyHBB2.

Sequential quorum intersections between l₁ and l₂ force any deliveries for
(reporting₁, l₁) and (reporting₂, l₂) to agree on the value. This is the agreement property
for the simplified HBB2 protocol without the safe predicate.

The paper-facing modal form is `agreement_modal`. -/
theorem agreement
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ reporting₁ reporting₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ∀ Q ∈ (M.learner l₁).quorums,
      ∀ R ∈ (M.learner l₂).quorums,
        ∃ p ∈ Q ∩ R, isSequential (Event := S.EventType) p M.history.val)
    (hDeliver₁ : Occurs M (ofEvent ⟨deliverSymb, [reporting₁, l₁, v₁]⟩))
    (hDeliver₂ : Occurs M (ofEvent ⟨deliverSymb, [reporting₂, l₂, v₂]⟩)) :
    v₁ = v₂ := by
  classical
  let p : P := Classical.choice inferInstance
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hSeq : ⊨[M]♢ᶠ[[l₁, l₂]]Formula.seq := by
    intro q
    exact (sat_diamond_pair_iff M _ l₁ l₂ Formula.seq).2 hSeq
  have hDeliver₁ := (occurs_iff_end_diamondPast).1 hDeliver₁ p
  have hDeliver₂ := (occurs_iff_end_diamondPast).1 hDeliver₂ p
  have hSeqTop : ⟪wTop⟫ ⊨[M] ♢ᶠ[[l₁, l₂]]Formula.seq := by
    simpa [wTop] using hSeq p
  by_cases hNe : v₁ = v₂
  · simpa [Sat] using hNe
  have hVoteBox₁ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[reporting₁]] (ofEvent ⟨voteSymb, [l₁, v₁]⟩) := by
    -- Apply `Deliver?` to back out the vote quorum supporting the first delivery.
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := theory_deliverBackward (M := M) hTheory)
          (reporting := reporting₁) (learner := l₁)
          (value := v₁) (p := p)
          (hDeliver := hDeliver₁)
  have hVoteBox₂ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[reporting₂]] (ofEvent ⟨voteSymb, [l₂, v₂]⟩) := by
    -- Apply `Deliver?` to back out the vote quorum supporting the second delivery.
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := theory_deliverBackward (M := M) hTheory)
          (reporting := reporting₂) (learner := l₂)
          (value := v₂) (p := p)
          (hDeliver := hDeliver₂)
  have hVoteDiamond₁ :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v₁]⟩) := by
    -- Turn the first vote box into a concrete past vote witness.
    simpa [wTop]
      using
        boxPast_singleton_to_diamond_nil
          (M := M) (w := wTop) (learner := reporting₁)
          (φ := ofEvent ⟨voteSymb, [l₁, v₁]⟩)
          hVoteBox₁
  have hVoteDiamond₂ :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₂, v₂]⟩) := by
    -- Turn the second vote box into a concrete past vote witness.
    simpa [wTop]
      using
        boxPast_singleton_to_diamond_nil
          (M := M) (w := wTop) (learner := reporting₂)
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
        (M := M) (w := wTop)
        (l := l₁) (l' := l₂)
        (evt := ⟨echoSymb, [v₁]⟩)
        (evt' := ⟨echoSymb, [v₂]⟩)
        (hSeq := hSeqTop)
        (hEvt := hEchoBox₁)
        (hEvt' := hEchoBox₂)
        (hDistinct := hDistinct)
  have hEchoNE : AllWorldValid M (echoNonEquivAxiom echoSymb) :=
    theory_echoNonEquiv (M := M) hTheory
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

/-- Paper-facing modal form of agreement. -/
theorem agreement_modal
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ reporting₁ reporting₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]♢ᶠ[[l₁, l₂]]Formula.seq) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, l₁, v₁]⟩)) ⇒ᶠ
         (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₂, l₂, v₂]⟩)) ⇒ᶠ
         (v₁ ≃ᶠ v₂) := by
  intro p hDeliver₁ hDeliver₂
  apply agreement hTheory
  · exact (sat_diamond_pair_iff M _ l₁ l₂ Formula.seq).1 (hSeq p)
  · exact observedAt_final_iff.mp (observedAt_iff.mpr hDeliver₁)
  · exact observedAt_final_iff.mp (observedAt_iff.mpr hDeliver₂)


end ThyHBB2
end Examples
end ModalDistribution
