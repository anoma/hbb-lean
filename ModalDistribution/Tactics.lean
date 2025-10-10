import Mathlib.Tactic
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# Tactics for Modal Distribution Proofs

This module provides specialized tactics to automate common proof patterns in modal logic.
These tactics significantly reduce boilerplate in proofs, especially in ThyHBB1.

Note: This file currently contains simple macro tactics. More complex elab tactics
could be added in the future to handle axiom instantiation and quantifier elimination patterns.
-/

namespace ModalDistribution.Tactics

open Lean Elab Tactic
open ModalDistribution Logic

/-!
## Simple Macros

These macros provide basic automation for common patterns.
-/

/-- Extract the left conjunct from a satisfied conjunction. -/
syntax "split_sat_left" ident : tactic

macro_rules
  | `(tactic| split_sat_left $h:ident) =>
    `(tactic| exact Logic.Sequentiality.sat_and_left $h)

/-- Extract the right conjunct from a satisfied conjunction. -/
syntax "split_sat_right" ident : tactic

macro_rules
  | `(tactic| split_sat_right $h:ident) =>
    `(tactic| exact Logic.Sequentiality.sat_and_right $h)

/-!
## Future Enhancements

The following tactics are planned but require more complex elab implementations:

- `extract_diamond`: Unpack diamond-past-nil witnesses with proper naming
- `transfer_subset`: Transfer box properties across transitive subsets

For now, these patterns should be handled manually or via helper lemmas
in `ModalDistribution.Logic.Lemmas`.

Note: Quantifier elimination chains are best handled directly using `forall_elim'`
from Logic.Lemmas, e.g., `forall_elim' v₃ (forall_elim' v₂ (forall_elim' v₁ h))`
-/

end ModalDistribution.Tactics
