import ModalDistribution.Examples.ThyAgreement.Depth
import ModalDistribution.Examples.ThyAgreement.Axioms
import ModalDistribution.Examples.ThyAgreement.Semantics
import ModalDistribution.Examples.ThyAgreement.StrictDepth
import ModalDistribution.Examples.ThyAgreement.CM
import ModalDistribution.Examples.ThyAgreement.VM
import ModalDistribution.Examples.ThyAgreement.FiniteModel
import ModalDistribution.Examples.ThyAgreement.FromHBB4

/-!
# ThyAgreement: a generalization of HBB4 (CM and VM)

`ThyAgreement` keeps HBB4's liveness theory, correlation axioms and the static
depth budget `depthBound` (dominating the realized `maxDepth`), assumes
agreement, Liveness 1 and Liveness 2 as axioms, and assumes none of HBB4's event
rules. `FromHBB4` proves that every HBB4 model (CM or VM) is a `ThyAgreement`
model; `FiniteModel` gives a finite live execution; the depth lower bound's
witness survives but its lower-bound half fails (`LowerBoundAgreement`).
-/
