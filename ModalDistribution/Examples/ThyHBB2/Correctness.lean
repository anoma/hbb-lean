import ModalDistribution.Examples.ThyHBB2.Agreement
import ModalDistribution.Examples.ThyHBB2.Liveness_One
import ModalDistribution.Examples.ThyHBB2.Liveness_Two

/-!
# Correctness properties for ThyHBB2

The paper's Theorem 7.1.3 collects the three correctness properties of
`ThyHBB2` (Figure 10): Agreement, Liveness 1, and Liveness 2. This file
bundles the corresponding Lean theorems into a single statement.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB2

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Theorem 7.1.3 / Figure 10. The correctness properties of `ThyHBB2`, collected: Agreement
(Proposition 7.2.1), Liveness 1 (Proposition 7.2.3), and Liveness 2
(Proposition 7.2.2). -/
theorem correctness
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    -- Agreement
    (∀ {l₁ l₂ l₁' l₂' v₁ v₂ : Signature.Value S},
      (⊨[M]♢ᶠ[[l₁, l₂]]Formula.seq) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩)) ⇒ᶠ
           (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) ⇒ᶠ
           (v₁ ≃ᶠ v₂)) ∧
    -- Liveness 1
    (∀ {l v : Signature.Value S},
      (⊨[M]□ᶠ[[l]]predicate0 liveSymb) →
      (⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) →
      ⊨[M](♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l, l, v]⟩)) ∧
    -- Liveness 2
    (∀ {l₁' l₂' l v : Signature.Value S},
      (⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ) →
      (⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l₂', l, v]⟩)) :=
  ⟨fun hSeq =>
      agreement (M := M) (hTheory := hTheory) (hSeq := hSeq),
   fun hLiveQuorum hUnique =>
      livenessOne (M := M) (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum) (hUnique := hUnique),
   fun hIntersect hLive =>
      livenessTwo (M := M) (hTheory := hTheory)
        (hIntersect := hIntersect) (hLive := hLive)⟩

end ThyHBB2
end Examples
end ModalDistribution
