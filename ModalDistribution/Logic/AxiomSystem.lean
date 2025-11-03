import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Syntax

/-!
# Axiom systems

We package closed formulas as axioms and formalise the notion of when a model
satisfies an axiom or a theory.  A theory is a
(possibly infinite) set of axioms, and a model satisfies a theory exactly when
it satisfies each of its axioms at every event in history (our event-driven
validity judgement `□W⊨`).
-/

namespace ModalDistribution
namespace Logic

open scoped Formula

set_option autoImplicit false

-- Fix at Type 0 to match Semantics.lean
variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

/-- Formulas regarded as axioms.
In HOAS, all formulas are inherently closed. -/
abbrev Axiom (S : Signature.{0, 0, 0}) : Type 1 :=
  Formula S

namespace Axiom

/-- An axiom holds in a model when it is valid at every event. -/
@[simp] def Valid
    (M : Model S P) (ax : Axiom S) : Prop :=
  AllWorldValid M ax

end Axiom

/-- A theory is a (possibly infinite) set of axioms. -/
abbrev Theory (S : Signature.{0, 0, 0}) : Type 1 :=
  Set (Axiom S)

namespace Theory

/-- A model satisfies a theory when it satisfies each of its axioms. -/
@[simp] def Valid (M : Model S P) (T : Theory S) : Prop :=
  ∀ ⦃ax : Axiom S⦄, ax ∈ T → Axiom.Valid (M := M) ax

end Theory

/-- Notation for models satisfying theories. -/
notation:55 M " ⊨ᵀ " T => Theory.Valid (M := M) T

end Logic
end ModalDistribution
