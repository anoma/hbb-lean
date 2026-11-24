import ModalDistribution.Examples.HBBSimp.Axioms
import ModalDistribution.Examples.HBBSimp.Lemmas
import ModalDistribution.Examples.HBBSimp.Agreement
import ModalDistribution.Examples.HBBSimp.HappyTermination
import ModalDistribution.Examples.HBBSimp.CascadeTermination
import ModalDistribution.Examples.HBBSimp.Correctness

/-!
# Theory `HBBSimp`

This module re-exports the components of the `HBBSimp` formalisation
(Section 7 of the paper):

- **`HBBSimp.Axioms`**: the theory (Definition 7.1.1, Figure 10)
- **`HBBSimp.Lemmas`**: the vote rules in the forms the correctness proofs use
- **`HBBSimp.Agreement`**: Agreement (Proposition 7.3.1)
- **`HBBSimp.CascadeTermination`**: Cascade Termination (Proposition 7.3.2)
- **`HBBSimp.HappyTermination`**: Happy Termination (Proposition 7.3.3)
- **`HBBSimp.Correctness`**: the three properties collected (Theorem 7.1.3)
-/
