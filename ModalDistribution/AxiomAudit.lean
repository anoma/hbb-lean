import ModalDistribution.Examples.ThyHBB1
import ModalDistribution.Examples.ThyHBB2
import ModalDistribution.Examples.ThyHBB3

/-!
# Axiom audit

Build-enforced check that every headline correctness theorem depends only on
the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
If any custom axiom ever enters the proof of one of these theorems, the
`#guard_msgs` below fail and the build breaks.
-/

/-- info: 'ModalDistribution.Examples.ThyHBB1.agreementThyHBB1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB1.agreementThyHBB1

/-- info: 'ModalDistribution.Examples.ThyHBB1.livenessOneThyHBB1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB1.livenessOneThyHBB1

/-- info: 'ModalDistribution.Examples.ThyHBB1.livenessTwoThyHBB1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB1.livenessTwoThyHBB1

/-- info: 'ModalDistribution.Examples.ThyHBB2.agreementThyHBB2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB2.agreementThyHBB2

/-- info: 'ModalDistribution.Examples.ThyHBB2.livenessOneThyHBB2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB2.livenessOneThyHBB2

/-- info: 'ModalDistribution.Examples.ThyHBB2.livenessTwoThyHBB2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB2.livenessTwoThyHBB2

/-- info: 'ModalDistribution.Examples.ThyHBB3.agreementThyHBB3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB3.agreementThyHBB3

/-- info: 'ModalDistribution.Examples.ThyHBB3.livenessOneThyHBB3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB3.livenessOneThyHBB3

/-- info: 'ModalDistribution.Examples.ThyHBB3.livenessTwoThyHBB3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB3.livenessTwoThyHBB3
