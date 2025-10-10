import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyHBB1.Agreement
import ModalDistribution.Examples.ThyHBB1.Liveness_One
import ModalDistribution.Examples.ThyHBB1.Liveness_Two

/-!
# Theory `ThyHBB1`

This file re-exports the complete formalization of the ThyHBB1 broadcast protocol theory.
The implementation has been modularized for better organization and maintainability:

- **`ThyHBB1.Axioms`**: Axiom schemes (backward rules, forward rules, safety formula, EchoNE)
- **`ThyHBB1.Safety`**: Safety and liveness helper lemmas
- **`ThyHBB1.Uniqueness`**: Uniqueness of proposals lemmas
- **`ThyHBB1.Agreement`**: Main agreement theorem (Theorem 6.6.1)
- **`ThyHBB1.Liveness`**: Liveness properties (Propositions 6.5.3 and 6.5.4)
- **`ThyHBB1.Liveness_One`**: Liveness properties (Proposition 6.5.3)
- **`ThyHBB1.Liveness_Two`**: Liveness properties (Proposition 6.5.4)

This reorganization maintains backward compatibility - all definitions, lemmas, and theorems
are still accessible via `ModalDistribution.Examples.ThyHBB1`.

## Main Results

- **Agreement** (`hbb1_agreement`): Two different values implies sequentiality violation
- **Liveness 1** (`hbb1_liveness_one`): Under uniqueness, live proposals are eventually delivered
- **Liveness 2** (`hbb1_liveness_two`): Deliveries propagate across intersecting learner quorums

## Theory Definition

The theory `ThyHBB1` extends `ThyLive` with protocol-specific axiomsfor the HBB1 broadcast algorithm
-/

-- All definitions, lemmas, and theorems are automatically available through the imports above
