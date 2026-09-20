import ModalDistribution.Examples.ThyHBB4.Depth
import ModalDistribution.Examples.ThyHBB4.Axioms
import ModalDistribution.Examples.ThyHBB4.Semantics
import ModalDistribution.Examples.ThyHBB4.Safety
import ModalDistribution.Examples.ThyHBB4.Liveness
import ModalDistribution.Examples.ThyHBB4.LivenessTwo
import ModalDistribution.Examples.ThyHBB4.FiniteModel

/-!
# Capped HBB4 with causal monotonicity

The corrected CM protocol uses exact correlation depth, bounded rounds,
self-source advancement, eventual delivery, and event-restricted Knowledge.
The existing finite-history foundation is unchanged. `Protocol` states the
semantic axiom schemata; `agreement`, `livenessOne`, and `livenessTwo` prove
correctness, and `FiniteModel` supplies a finite live execution.
-/
