import ModalDistribution.Examples.ThyHBB4.Axioms

namespace ModalDistribution.Examples.ThyHBB4

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}
/-- A constant correlation row has depth zero, in any finite model. -/
theorem maxDepth_eq_zero_of_constant
    {R : World P S.EventType → S.Value → S.Value → Prop} {a : S.Value}
    (hconstant : ∀ w u, correlationRow R a w = correlationRow R a u) :
    maxDepth M R a = 0 := by
  by_cases hn : maxDepth M R a = 0
  · exact hn
  apply False.elim
  have hpos : 0 < maxDepth M R a := by omega
  obtain ⟨ws, _, _, hrows⟩ := maxDepth_attained M R a
  exact hrows ⟨0, by omega⟩ ⟨1, by omega⟩ (by show 0 < 1; omega) (hconstant _ _)

end ModalDistribution.Examples.ThyHBB4
