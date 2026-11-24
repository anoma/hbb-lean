import ModalDistribution.Examples.HBBSafe.Axioms
import ModalDistribution.Examples.HBBSafe.Safety
import ModalDistribution.Examples.HBBSafe.Agreement
import ModalDistribution.Examples.HBBSafe.HappyTermination
import ModalDistribution.Examples.HBBSafe.CascadeTermination
import ModalDistribution.Examples.HBBSafe.Correctness

/-!
# Theory `HBBSafe`

This file re-exports the complete formalization of the HBBSafe broadcast protocol theory,
organized into the following modules:

- **`HBBSafe.Axioms`**: Axiom schemes (backward rules, forward rules, safety formula, EchoNE)
- **`HBBSafe.Safety`**: Safety of a learner (Lemmas 6.5.1 and 6.6.2) and the `Vote!`
  instantiations
- **`HBBSafe.Agreement`**: Main agreement theorem
- **`HBBSafe.HappyTermination`**: Happy Termination
- **`HBBSafe.CascadeTermination`**: Cascade Termination
- **`HBBSafe.Correctness`**: The three properties collected (Theorem 6.2.6)

## Main Results

- **Agreement** (`agreement`): Two different values implies sequentiality violation
- **Happy Termination** (`happyTermination`): Under uniqueness, live proposals are
  eventually delivered
- **Cascade Termination** (`cascadeTermination`): Deliveries propagate across
  intersecting learner quorums

## Theory Definition

The theory `HBBSafe` extends `ThyLive` with the protocol-specific axioms of
Figure 8.
-/

-- All definitions, lemmas, and theorems are automatically available through the imports above
