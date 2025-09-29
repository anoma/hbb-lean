import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Syntax

/-!
# Axiom systems (Definition 5.2.1)

We package closed formulas as axioms and formalise the notion of when a model
satisfies an axiom or a theory (Definition 5.2.1 of the paper).  A theory is a
(possibly infinite) set of axioms, and a model satisfies a theory exactly when
it satisfies each of its axioms at every event in history (our event-driven
validity judgement `□⇓⊨`).
-/

namespace ModalDistribution
namespace Logic

open scoped Formula

set_option autoImplicit false

universe u₁ u₂ u₃

/-- Closed formulas regarded as axioms (Definition 5.2.1). -/
structure Axiom (S : Signature) [DecidableEq S.VarSymb] where
  /-- Underlying formula. -/
  formula : Formula S
  /-- The axiom is closed (no free variables). -/
  isClosed : formula.IsClosed

namespace Axiom

variable {S : Signature} [DecidableEq S.VarSymb]

instance : Coe (Axiom S) (Formula S) where
  coe ax := ax.formula

@[simp] lemma coe_formula (ax : Axiom S) : (ax : Formula S) = ax.formula := rfl

@[simp] lemma isClosed_coe (ax : Axiom S) : (ax : Formula S).IsClosed := ax.isClosed

/-- An axiom holds in a model when it is valid at every event (Definition 5.2.1). -/
@[simp] def Valid
    {P : Type u₃} [Nonempty P]
    (M : Model S P) (ax : Axiom S) : Prop :=
  ∀ σ : Assignment S, EventValid M σ ax.formula

end Axiom

/-- A theory is a (possibly infinite) set of axioms (Definition 5.2.1). -/
abbrev Theory (S : Signature) [DecidableEq S.VarSymb] : Type :=
  Set (Axiom S)

namespace Theory

variable {S : Signature} [DecidableEq S.VarSymb]
variable {P : Type u₃} [Nonempty P]

/-- A model satisfies a theory when it satisfies each of its axioms (Definition 5.2.1). -/
@[simp] def Valid (M : Model S P) (T : Theory S) : Prop :=
  ∀ ⦃ax : Axiom S⦄, ax ∈ T → Axiom.Valid (M := M) ax

end Theory

/-- Notation for models satisfying theories. -/
notation:55 M " ⊨ᵀ " T => Theory.Valid (M := M) T

end Logic
end ModalDistribution
