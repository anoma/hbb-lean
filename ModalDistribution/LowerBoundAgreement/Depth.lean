import ModalDistribution.LowerBoundAgreement.Basic
import ModalDistribution.Examples.ThyAgreement.Axioms

/-!
# Causal depth: generic facts

Facts about `worldDepth` that depend on no protocol rule: every world has depth
at least `1`, depth increases strictly along `≪`, and a participant with no event
in a prehistory is sequential there. HBB4's rule-based consequences (an echo is
at least `2` deep, a rank-`n` vote at least `n+3` deep, a delivery at least
`maxDepth + 4` deep) live in `LowerBound/Depth.lean`; `ThyAgreement` assumes no
event rules, so they have no counterpart here — and indeed the lower-bound half
of the HBB4 theorem fails for `ThyAgreement` (`Counterexample.lean`).
-/

namespace ModalDistribution.LowerBoundAgreement
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyAgreement
open scoped Formula PreHistory

variable {S : Signature} {P : Type}

/-- Every world has depth at least `1`. -/
theorem worldDepth_pos (w : World P S.EventType) : 1 ≤ worldDepth w := by
  unfold worldDepth
  rcases w with ⟨p, e, h⟩
  cases h with
  | mk l => show _ + 1 ≥ 1; omega

/-- A participant with no event in a prehistory is sequential in it. -/
theorem isSequential_of_absent {q : P} {H : PreHistory P S.EventType}
    (hq : ∀ t ∈ H, t.place ≠ q) : isSequential (Event := S.EventType) q H := by
  intro t₁ t₂ h₁ _ hp₁ _
  exact absurd hp₁ (hq t₁ h₁)

/-- Depth strictly increases along accessibility. -/
theorem worldDepth_lt_of_accessible {u w : World P S.EventType} (h : u ≪ w) :
    worldDepth u < worldDepth w :=
  PreHistory.height_lt_of_accessible h

end ModalDistribution.LowerBoundAgreement
