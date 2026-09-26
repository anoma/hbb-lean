import ModalDistribution.Examples.ThyHBB4.Depth
import ModalDistribution.Examples.ThyHBB4.Axioms
import ModalDistribution.Examples.ThyHBB4.Semantics
import ModalDistribution.Examples.ThyHBB4.Safety
import ModalDistribution.Examples.ThyHBB4.Liveness
import ModalDistribution.Examples.ThyHBB4.LivenessTwo
import ModalDistribution.Examples.ThyHBB4.StrictDepth
import ModalDistribution.Examples.ThyHBB4.FastPath
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
Deliveries are backed either by a decision-rank certificate or by the fast path
(an echo for the value from every participant not yet seen to equivocate, i.e.
every participant sequential in the delivering world's past, together with the
end-of-time guarantee that the learner, if still correlated with itself, has a
quorum sequential at the end of time); the fast path's safety rests on that
guarantee and these echoes rather than depth (`FastPath`). Agreement, Liveness 1 and Liveness 2 are proved for both
theories; `FiniteModel` supplies a common finite live execution.
-/
