import ModalDistribution.Examples.HBBSafe
import ModalDistribution.Examples.HBBSimp
import ModalDistribution.Examples.HBBCorr
import ModalDistribution.Examples.NonVacuity

/-!
# Axiom audit

Build-enforced check that every headline correctness and non-vacuity theorem depends only on
the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
If any custom axiom ever enters the proof of one of these theorems, the
`#guard_msgs` below fail and the build breaks.
-/

/-- info: 'ModalDistribution.Examples.HBBSafe.agreement' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBSafe.agreement

/-- info: 'ModalDistribution.Examples.HBBSafe.happyTermination' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBSafe.happyTermination

/-- info: 'ModalDistribution.Examples.HBBSafe.cascadeTermination' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBSafe.cascadeTermination

/-- info: 'ModalDistribution.Examples.HBBSimp.agreement' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBSimp.agreement

/-- info: 'ModalDistribution.Examples.HBBSimp.happyTermination' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBSimp.happyTermination

/-- info: 'ModalDistribution.Examples.HBBSimp.cascadeTermination' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBSimp.cascadeTermination

/-- info: 'ModalDistribution.Examples.HBBCorr.agreement' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBCorr.agreement

/-- info: 'ModalDistribution.Examples.HBBCorr.happyTermination' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBCorr.happyTermination

/-- info: 'ModalDistribution.Examples.HBBCorr.cascadeTermination' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBCorr.cascadeTermination

/-- info: 'ModalDistribution.Examples.HBBSafe.correctness' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBSafe.correctness

/-- info: 'ModalDistribution.Examples.HBBSimp.correctness' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBSimp.correctness

/-- info: 'ModalDistribution.Examples.HBBCorr.correctness' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.HBBCorr.correctness

/--
info: 'ModalDistribution.Examples.NonVacuity.hbbSafe_nonvacuous' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ModalDistribution.Examples.NonVacuity.hbbSafe_nonvacuous

/--
info: 'ModalDistribution.Examples.NonVacuity.hbbSimp_nonvacuous' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ModalDistribution.Examples.NonVacuity.hbbSimp_nonvacuous

/--
info: 'ModalDistribution.Examples.NonVacuity.hbbCorr_nonvacuous' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ModalDistribution.Examples.NonVacuity.hbbCorr_nonvacuous
