import ModalDistribution.Examples.HBBCorr.Agreement
import ModalDistribution.Examples.HBBCorr.HappyTermination
import ModalDistribution.Examples.HBBCorr.CascadeTermination

/-!
# Correctness properties for HBBCorr

The paper's Theorem 8.2.3 collects the three correctness properties of
`HBBCorr` (Figure 13): Agreement, Happy Termination, and Cascade Termination. This file
bundles the corresponding Lean theorems into a single statement.
-/

namespace ModalDistribution
namespace Examples
namespace HBBCorr

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {correlationSymb : Signature.PredSymb S}

/-- Paper: Theorem 8.2.3 / Figure 13. The correctness properties of `HBBCorr`, collected: Agreement
(Proposition 8.3.1), Happy Termination (Proposition 8.5.1), and Cascade Termination
(Proposition 8.4.5). -/
theorem correctness
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    -- Agreement
    (∀ {l₁ l₂ v₁ v₂ : Signature.Value S},
      (⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v₁]⟩)) ⇒ᶠ
           ((♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂, v₂]⟩)) ⇒ᶠ
             (v₁ ≃ᶠ v₂))) ∧
    -- Happy Termination
    (∀ {l v : Signature.Value S},
      (⊨[M]□ᶠ[[l]]predicate0 liveSymb) →
      (⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) →
      ⊨[M](♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l, v]⟩)) ∧
    -- Cascade Termination
    (∀ {l₁ l₂ v : Signature.Value S},
      (⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) →
      (⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l₂, v]⟩)) :=
  ⟨agreement hTheory, happy_termination hTheory, cascade_termination hTheory⟩

end HBBCorr
end Examples
end ModalDistribution
