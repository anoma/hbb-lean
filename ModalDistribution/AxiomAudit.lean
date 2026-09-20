import ModalDistribution.Examples.ThyHBB1
import ModalDistribution.Examples.ThyHBB2
import ModalDistribution.Examples.ThyHBB3
import ModalDistribution.Examples.ThyHBB4
import ModalDistribution.Examples.ThyLive.FiniteHistory
import ModalDistribution.Examples.ThyLive.FiniteModel

/-!
# Axiom audit

Build-enforced check that every headline correctness theorem depends only on
the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
If any custom axiom ever enters the proof of one of these theorems, the
`#guard_msgs` below fail and the build breaks.
-/

/-- info: 'ModalDistribution.Examples.ThyHBB1.agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB1.agreement

/-- info: 'ModalDistribution.Examples.ThyHBB1.livenessOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB1.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB1.livenessTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB1.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB2.agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB2.agreement

/-- info: 'ModalDistribution.Examples.ThyHBB2.livenessOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB2.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB2.livenessTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB2.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB3.agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB3.agreement

/-- info: 'ModalDistribution.Examples.ThyHBB3.livenessOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB3.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB3.livenessTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB3.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB1.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB1.correctness

/-- info: 'ModalDistribution.Examples.ThyHBB2.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB2.correctness

/-- info: 'ModalDistribution.Examples.ThyHBB3.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB3.correctness

/-- info: 'ModalDistribution.Examples.FiniteHistory.no_live_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.FiniteHistory.no_live_event


/-- info: 'ModalDistribution.Examples.FiniteModel.exists_live_event_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.FiniteModel.exists_live_event_model

/-- info: 'ModalDistribution.Examples.ThyHBB4.maxDepth_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB4.maxDepth_attained

/-- info: 'ModalDistribution.Examples.ThyHBB4.vote_provenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB4.vote_provenance

/-- info: 'ModalDistribution.Examples.ThyHBB4.deliver_provenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB4.deliver_provenance

/-- info: 'ModalDistribution.Examples.ThyHBB4.conflict_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB4.conflict_depth

/-- info: 'ModalDistribution.Examples.ThyHBB4.agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB4.agreement

/-- info: 'ModalDistribution.Examples.ThyHBB4.livenessOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB4.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB4.livenessTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB4.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB4.FiniteModel.finite_protocol_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.ThyHBB4.FiniteModel.finite_protocol_nonvacuous
