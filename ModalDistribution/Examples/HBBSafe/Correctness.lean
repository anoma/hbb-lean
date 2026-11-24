import ModalDistribution.Examples.HBBSafe.Agreement
import ModalDistribution.Examples.HBBSafe.HappyTermination
import ModalDistribution.Examples.HBBSafe.CascadeTermination

/-!
# Correctness properties for HBBSafe

The paper's Theorem 6.2.6 collects the three correctness properties of
`HBBSafe` (Figure 9): Agreement, Happy Termination, and Cascade Termination. This file
bundles the corresponding Lean theorems into a single statement.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSafe

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Theorem 6.2.6 / Figure 9. The correctness properties of `HBBSafe`, collected: Agreement
(Proposition 6.4.1), Happy Termination (Proposition 6.6.3), and Cascade Termination
(Proposition 6.5.5). -/
theorem correctness
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) :
    -- Agreement
    (∀ {l₁ l₂ l₁' l₂' v₁ v₂ : Signature.Value S},
      (⊨[M]♢ᶠ[[l₁', l₂']]Formula.seq) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩)) ⇒ᶠ
           (♢ᶠ↓[[]] (ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) ⇒ᶠ
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
      (⊨[M]ofPredicate ⟨safeSymb, [l]⟩) →
      (⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l₂', l, v]⟩)) :=
  ⟨fun hSeq =>
      agreement (M := M) (hTheory := hTheory) (hSeq := hSeq),
   fun hLiveQuorum hUnique =>
      happy_termination (M := M) (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum) (hUnique := hUnique),
   fun hIntersect hSafe hLive =>
      cascade_termination (M := M) (hTheory := hTheory)
        (hIntersect := hIntersect) (hSafe := hSafe) (hLive := hLive)⟩

end HBBSafe
end Examples
end ModalDistribution
