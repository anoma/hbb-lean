import ModalDistribution.Examples.ThyHBB4.Depth
import ModalDistribution.Examples.ThyHBB4.Axioms
import ModalDistribution.Examples.ThyHBB4.Semantics
import ModalDistribution.Examples.ThyHBB4.Safety
import ModalDistribution.Examples.ThyHBB4.Liveness
import ModalDistribution.Examples.ThyHBB4.LivenessTwo
import ModalDistribution.Examples.ThyHBB4.Coherence
import ModalDistribution.Examples.ThyHBB4.StrictDepth
import ModalDistribution.Examples.ThyHBB4.CM
import ModalDistribution.Examples.ThyHBB4.CW
import ModalDistribution.Examples.ThyHBB4.SW
import ModalDistribution.Examples.ThyHBB4.FiniteModel

/-!
# Capped HBB4: CM, SW, and CW

The three theories share finite histories, exact correlation depth, bounded
rounds, self-source advancement, eventual delivery, and restricted Knowledge.
`ProtocolCM`, `ProtocolSW`, and `ProtocolCW` specify the separate coherence
conditions over `BaseProtocol`. Agreement and both liveness results are proved
for all three; `FiniteModel` supplies a common finite live execution.
-/
