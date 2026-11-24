import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBSimp.Axioms

/-!
# HBBSimp Helper Lemmas

The two ways the HBBSimp correctness proofs use the vote rules:

- `boxPast_end_of_diamondPast_end`: a backward rule read at end of time, which
  is how `(Vote?)` turns a past vote into an echo quorum in the Agreement proof;
- `vote_forward_imp`: `(Vote!)` in the form Lemma 6.5.2(2) consumes, used by
  both termination proofs.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSimp

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- A backward rule `φ ⇒ □↓[l] ψ`, valid at every event of the history, holds
at end of time in the form `♢↓ φ ⇒ □↓[l] ψ`: the past `φ`-event knows of an
`l`-quorum of `ψ`, and end of time knows everything that event knows
(Lemma 4.2.3(1) at end of time). -/
theorem boxPast_end_of_diamondPast_end
    {p : P} {l : Signature.Value S} {φ ψ : Formula S}
    (hRule : ∀ t ∈ M.history.val, (⟪t⟫ ⊨[M] φ) → ⟪t⟫ ⊨[M] □ᶠ↓[[l]] ψ)
    (h : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] ♢ᶠ↓[[]] φ) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] □ᶠ↓[[l]] ψ := by
  obtain ⟨q, hq⟩ := (Sat.diamond_nil M _ (↓ᶠ φ)).1 h
  obtain ⟨t, ht, -, hφ⟩ := (Sat.past _ _ _).1 hq
  exact lift_boxPast_to_end M
    (History.subset_of_happensBefore (History.happensBefore_of_mem ht)) (hRule t ht hφ) p

/-- `(Vote!)` instantiated at every world: a sometime-live quorum of past echoes
yields an eventual vote. This is the form consumed by Lemma 6.5.2(2). -/
theorem vote_forward_imp
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l v : Signature.Value S} :
    □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) :=
  fun ht => Sat.imp_intro _ _ (vote_forward_elim (theory_vote_forward hTheory) ht)

end HBBSimp
end Examples
end ModalDistribution
