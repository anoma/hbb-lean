import ModalDistribution.Examples.ThyHBB3.Agreement
import ModalDistribution.Examples.ThyHBB3.Liveness_One
import ModalDistribution.Examples.ThyHBB3.Liveness_Two

/-!
# Correctness properties for ThyHBB3

The paper's Theorem 8.2.3 collects the three correctness properties of
`ThyHBB3` (Figure 12): Agreement, Liveness 1, and Liveness 2. This file
bundles the corresponding Lean theorems into a single statement.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB3

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

/-- Paper: Theorem 8.2.3 / Figure 12. The correctness properties of `ThyHBB3`, collected: Agreement
(Proposition 8.3.1), Liveness 1 (Proposition 8.5.1), and Liveness 2
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
    -- Liveness 1
    (∀ {l v : Signature.Value S},
      (⊨[M]□ᶠ[[l]]predicate0 liveSymb) →
      (⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) →
      ⊨[M](♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l, v]⟩)) ∧
    -- Liveness 2
    (∀ {l₁ l₂ v : Signature.Value S},
      (⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) →
      (⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l₂, v]⟩)) :=
  ⟨fun hCorrelation =>
      agreementThyHBB3 (M := M) (hTheory := hTheory)
        (hCorrelation := hCorrelation),
   fun hLiveQuorum hUnique =>
      livenessOneThyHBB3 (M := M) (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum) (hUnique := hUnique),
   fun hCorrelation hLiveQuorum =>
      livenessTwoThyHBB3 (M := M) (hTheory := hTheory)
        (hCorrelation := hCorrelation) (hLiveQuorum := hLiveQuorum)⟩

end ThyHBB3
end Examples
end ModalDistribution
