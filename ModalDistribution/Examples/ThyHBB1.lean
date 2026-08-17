import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyHBB1.Agreement
import ModalDistribution.Examples.ThyHBB1.Liveness_One
import ModalDistribution.Examples.ThyHBB1.Liveness_Two
import ModalDistribution.Examples.ThyHBB1.Correctness

/-!
# Theory `ThyHBB1`

This file re-exports the complete formalization of the ThyHBB1 broadcast protocol theory,
organized into the following modules:

- **`ThyHBB1.Axioms`**: Axiom schemes (backward rules, forward rules, safety formula, EchoNE)
- **`ThyHBB1.Safety`**: Safety and liveness helper lemmas
- **`ThyHBB1.Uniqueness`**: Uniqueness of proposals lemmas
- **`ThyHBB1.Agreement`**: Main agreement theorem
- **`ThyHBB1.Liveness_One`**: Liveness property 1
- **`ThyHBB1.Liveness_Two`**: Liveness property 2
- **`ThyHBB1.Correctness`**: The three properties collected (Theorem 6.1.6)

## Main Results

- **Agreement** (`agreement`): Two different values implies sequentiality violation
- **Liveness 1** (`livenessOne`): Under uniqueness, live proposals are eventually delivered
- **Liveness 2** (`livenessTwo`): Deliveries propagate across intersecting learner quorums

## Theory Definition

The theory `ThyHBB1` extends `ThyLive` with protocol-specific axioms for the HBB1 broadcast algorithm
-/

-- All definitions, lemmas, and theorems are automatically available through the imports above
