import ModalDistribution.Examples.HBB.Uniqueness
import ModalDistribution.Examples.HBBSimp.Lemmas
import ModalDistribution.Logic.Properties.Modalities
import ModalDistribution.Logic.Properties.Sequentiality

/-!
# HBBSimp Agreement

Proposition 7.3.1: if learners `l₁` and `l₂` have sequential quorum
intersections, then any delivery for `(l₁', l₁)` and any delivery for
`(l₂', l₂)` carry the same value.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSimp

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}
variable {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 7.3.1 (Agreement). Sequential quorum intersections
between `l₁` and `l₂` force any deliveries for `(l₁', l₁)` and `(l₂', l₂)` to
agree on the value. -/
theorem agreement
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ l₁' l₂' : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]♢ᶠ[[l₁, l₂]]Formula.seq) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩)) ⇒ᶠ
         (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) ⇒ᶠ
         (v₁ ≃ᶠ v₂) := by
  intro p
  refine Sat.imp_intro _ _ fun hDeliver₁ => Sat.imp_intro _ _ fun hDeliver₂ => ?_
  -- If `v₁ = v₂` we are done, so suppose `v₁ ≠ v₂`.
  by_cases hEq : v₁ = v₂
  · simpa [Sat] using hEq
  -- (Deliver?), Lemma 4.2.3(1): `□↓[l₁'] vote(l₁, v₁)` and `□↓[l₂'] vote(l₂, v₂)`.
  have hVotes₁ := deliver_to_vote_box_end (theory_deliver_backward hTheory) hDeliver₁
  have hVotes₂ := deliver_to_vote_box_end (theory_deliver_backward hTheory) hDeliver₂
  -- Lemma 4.2.1(1): `♢↓ vote(l₁, v₁)` and `♢↓ vote(l₂, v₂)`.
  have hVote₁ := singleton_box_implies_diamond _ _ _ _ hVotes₁
  have hVote₂ := singleton_box_implies_diamond _ _ _ _ hVotes₂
  -- (Vote?): `□↓[l₁] echo(v₁)` and `□↓[l₂] echo(v₂)`.
  have hEchoes₁ := boxPast_end_of_diamondPast_end
    (fun _ ht => vote_backward_elim (theory_vote_backward hTheory) ht) hVote₁
  have hEchoes₂ := boxPast_end_of_diamondPast_end
    (fun _ ht => vote_backward_elim (theory_vote_backward hTheory) ht) hVote₂
  -- Proposition 5.1.5(3), `v₁ ≠ v₂`, `⊨ ♢[l₁ l₂] seq`: one participant echoed
  -- both values, one after the other; (EchoNE) then forces `v₁ = v₂`.
  have hEchoNE := fun {a b : Signature.Value S} =>
    echo_non_equiv_diamond (theory_echo_non_equiv hTheory) (w := ⟨p, †, M.history.val⟩)
      (valNow := a) (valPast := b) (History.transitiveSubset_refl M.history)
  rcases sat_or_cases (seq_two_quorums_eventually (hSeq p) hEchoes₁ hEchoes₂
      (by simpa using hEq)) with h | h
  · exact absurd (hEchoNE h) hEq
  · exact absurd (hEchoNE h).symm hEq

/-- Paper: Proposition 7.3.1, hypothesis form. When both deliveries for
`(l₁', l₁)` and `(l₂', l₂)` occur, their values coincide. -/
theorem agreement_of_deliveries
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ l₁' l₂' : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]♢ᶠ[[l₁, l₂]]Formula.seq)
    (hDeliver₁ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩))
    (hDeliver₂ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) :
    ⊨[M] v₁ ≃ᶠ v₂ :=
  EndValid.imp_elim M (EndValid.imp_elim M (agreement hTheory hSeq) hDeliver₁) hDeliver₂

end HBBSimp
end Examples
end ModalDistribution
