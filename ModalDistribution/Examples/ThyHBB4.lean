import ModalDistribution.Examples.ThyHBB4.Depth
import ModalDistribution.Examples.ThyHBB4.Axioms
import ModalDistribution.Examples.ThyHBB4.Semantics
import ModalDistribution.Examples.ThyHBB4.Safety
import ModalDistribution.Examples.ThyHBB4.Liveness
import ModalDistribution.Examples.ThyHBB4.LivenessTwo
import ModalDistribution.Examples.ThyHBB4.StrictDepth
import ModalDistribution.Examples.ThyHBB4.CM
import ModalDistribution.Examples.ThyHBB4.VM
import ModalDistribution.Examples.ThyHBB4.FiniteModel

/-!
# Capped HBB4: CM and VM

The two theories share finite histories, exact correlation depth, bounded
rounds, source-free votes, eventual delivery, and restricted Knowledge.
`ProtocolCM` assumes causal monotonicity; `ProtocolVM` assumes only vote
monotonicity, the instances of causal monotonicity the proofs use (round-zero
votes and same-round switch votes), and `ProtocolCM.toVM` records CM ⇒ VM.
Agreement, Liveness 1 and Liveness 2 are proved for both; `FiniteModel`
supplies a common finite live execution.
-/
