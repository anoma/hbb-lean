import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBCorr.Axioms
import ModalDistribution.Examples.HBBCorr.Lemmas
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# HBBCorr Agreement Property

Proposition 8.3.1 (Agreement) for `HBBCorr`: if two learners are everywhere
correlated, then any two deliveries for those learners agree on the value.
-/

namespace ModalDistribution
namespace Examples
namespace HBBCorr

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

/-- Paper: Proposition 8.3.1 (Agreement). Agreement property for HBBCorr.

Correlation between l₁ and l₂ forces any deliveries for those learners
to agree on the value. This uses the correlation predicate to establish quorum
intersection, which is the key innovation of HBBCorr.

See also: `agreement_of_deliveries`. -/
theorem agreement
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v₁ v₂ : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]
      ((♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v₁]⟩)) ⇒ᶠ
        ((♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂, v₂]⟩)) ⇒ᶠ
          (v₁ ≃ᶠ v₂))) := by
  intro p hDeliver₁ hDeliver₂
  show v₁ = v₂
  refine Classical.byContradiction fun hNe => ?_
  -- `(Deliver?)`: each delivery is backed by a quorum of votes for its value.
  have hVotes₁ := deliver_to_vote_box_end hTheory hDeliver₁
  have hVotes₂ := deliver_to_vote_box_end hTheory hDeliver₂
  -- `(≐seq)`: the quorums of `l₁` and `l₂` intersect sequentially.
  have hSeq : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] ♢ᶠ[[l₁, l₂]] Formula.seq :=
    AllWorldValid.at_end M (theory_correlation_seq hTheory) p l₁ l₂
      (EndValid.boxEmpty_guard M _ hCorrelation p)
  -- `(VoteNE)` at a vote that follows a vote of the other learner, which is
  -- correlated with it there by `(≐⇓)` (and `(≐symm)`), equates the values.
  have hVoteNE {a b : Signature.Value S} {k₁ k₂ : Signature.Value S}
      (hCorr : ∀ {t : World P (Signature.EventType S)}, t ∈ M.history.val →
        ⟪t⟫ ⊨[M] ofPredicate ⟨correlationSymb, [k₁, k₂]⟩)
      (h : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] ♢ᶠ↓[[]]
        (ofEvent ⟨voteSymb, [k₁, a]⟩ ∧ᶠ ↓ᶠ ofEvent ⟨voteSymb, [k₂, b]⟩)) : a = b := by
    obtain ⟨t, ht, hVotes⟩ := sat_diamondPast_nil_iff.1 h
    obtain ⟨hNow, hBefore⟩ := (Sat.and ..).1 hVotes
    exact theory_vote_non_equiv hTheory (M.time_le_of_mem ht) _ _ _ _ hNow hBefore (hCorr ht)
  -- Sequentiality: one of the two votes follows the other.
  rcases sat_or_cases (seq_two_quorums_eventually hSeq hVotes₁ hVotes₂ (by simp [hNe])) with
    h | h
  · exact hNe (hVoteNE (correlation_of_mem hTheory hCorrelation) h)
  · exact hNe (hVoteNE (fun ht => theory_correlation_symm hTheory (M.time_le_of_mem ht) _ _
      (correlation_of_mem hTheory hCorrelation ht)) h).symm

/-- Paper: Proposition 8.3.1, hypothesis form. If deliveries for learners
`l₁` and `l₂` both occur, their values coincide. -/
theorem agreement_of_deliveries
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v₁ v₂ : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hDeliver₁ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v₁]⟩))
    (hDeliver₂ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂, v₂]⟩)) :
    ⊨[M] v₁ ≃ᶠ v₂ :=
  fun p => agreement hTheory hCorrelation p (hDeliver₁ p) (hDeliver₂ p)

end HBBCorr
end Examples
end ModalDistribution
