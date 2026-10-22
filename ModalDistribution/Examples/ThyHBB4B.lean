import ModalDistribution.Examples.ThyHBB4B.Depth
import ModalDistribution.Examples.ThyHBB4B.Axioms
import ModalDistribution.Examples.ThyHBB4B.Semantics
import ModalDistribution.Examples.ThyHBB4B.Safety
import ModalDistribution.Examples.ThyHBB4B.Liveness
import ModalDistribution.Examples.ThyHBB4B.LivenessTwo
import ModalDistribution.Examples.ThyHBB4B.StrictDepth
import ModalDistribution.Examples.ThyHBB4B.FastPath
import ModalDistribution.Examples.ThyHBB4B.CM
import ModalDistribution.Examples.ThyHBB4B.VM
import ModalDistribution.Examples.ThyHBB4B.FiniteModel

/-!
# Budgeted HBB4: CM and VM with a static depth budget

`ThyHBB4B` is `ThyHBB4` with the decision rank `maxDepth` (an omniscient
quantity of the completed model) replaced by a static per-learner budget
`depthBound`, together with the environment axiom `depthBound_dominates :
maxDepth M l ≤ depthBound l`. Its rules are therefore local to the acting
participant's past, which is what the protocol-level lower bound
(`LowerBound/HBB4Protocol.lean`) needs. Agreement, Liveness 1 and 2 are proved
for CM and VM exactly as for `ThyHBB4`; `FiniteModel` gives a finite live
execution.
-/
