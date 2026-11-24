import ModalDistribution.Examples.HBBSimp.Agreement
import ModalDistribution.Examples.HBBSimp.HappyTermination
import ModalDistribution.Examples.HBBSimp.CascadeTermination

/-!
# Correctness properties for HBBSimp

The paper's Theorem 7.1.3 collects the three correctness properties of
`HBBSimp` (Figure 11): Agreement, Happy Termination, and Cascade Termination. This file
bundles the corresponding Lean theorems into a single statement.
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

/-- Paper: Theorem 7.1.3 / Figure 11. The correctness properties of `HBBSimp`, collected: Agreement
(Proposition 7.3.1), Happy Termination (Proposition 7.3.3), and Cascade Termination
(Proposition 7.3.2). -/
theorem correctness
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    -- Agreement
    (∀ {l₁ l₂ l₁' l₂' v₁ v₂ : Signature.Value S},
      (⊨[M]♢ᶠ[[l₁, l₂]]Formula.seq) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩)) ⇒ᶠ
           (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) ⇒ᶠ
           (v₁ ≃ᶠ v₂)) ∧
    -- Happy Termination
    (∀ {l v : Signature.Value S},
      (⊨[M]□ᶠ[[l]]predicate0 liveSymb) →
      (⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) →
      ⊨[M](♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l, l, v]⟩)) ∧
    -- Cascade Termination
    (∀ {l₁' l₂' l v : Signature.Value S},
      (⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ) →
      (⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l₂', l, v]⟩)) :=
  ⟨fun hSeq =>
      agreement (M := M) (hTheory := hTheory) (hSeq := hSeq),
   fun hLiveQuorum hUnique =>
      happy_termination (M := M) (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum) (hUnique := hUnique),
   fun hIntersect hLive =>
      cascade_termination (M := M) (hTheory := hTheory)
        (hIntersect := hIntersect) (hLive := hLive)⟩

end HBBSimp
end Examples
end ModalDistribution
