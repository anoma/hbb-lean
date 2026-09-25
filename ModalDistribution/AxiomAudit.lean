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
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB1.agreement

/-- info: 'ModalDistribution.Examples.ThyHBB1.livenessOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB1.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB1.livenessTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB1.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB2.agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB2.agreement

/-- info: 'ModalDistribution.Examples.ThyHBB2.livenessOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB2.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB2.livenessTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB2.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB3.agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB3.agreement

/-- info: 'ModalDistribution.Examples.ThyHBB3.livenessOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB3.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB3.livenessTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB3.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB1.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB1.correctness

/-- info: 'ModalDistribution.Examples.ThyHBB2.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB2.correctness

/-- info: 'ModalDistribution.Examples.ThyHBB3.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB3.correctness

/-- info: 'ModalDistribution.Examples.FiniteHistory.no_live_event'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.FiniteHistory.no_live_event

/-- info: 'ModalDistribution.Examples.FiniteModel.exists_live_event_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.FiniteModel.exists_live_event_model

/-- info: 'ModalDistribution.Examples.ThyHBB4.maxDepth_attained'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.maxDepth_attained

/-- info: 'ModalDistribution.Examples.ThyHBB4.vote_provenance'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.vote_provenance

/-- info: 'ModalDistribution.Examples.ThyHBB4.deliver_provenance'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.deliver_provenance

/-- info: 'ModalDistribution.Examples.ThyHBB4.CM.conflict_yields_depth_chain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.CM.conflict_yields_depth_chain

/-- info: 'ModalDistribution.Examples.ThyHBB4.CM.agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.CM.agreement

/-- info: 'ModalDistribution.Examples.ThyHBB4.livenessOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB4.CM.livenessOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.CM.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB4.CM.livenessTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.CM.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB4.FiniteModel.finite_protocol_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.FiniteModel.finite_protocol_nonvacuous

/-! VM: vote monotonicity, the instances of causal monotonicity that the CM
proofs use. -/

/-- info: 'ModalDistribution.Examples.ThyHBB4.ProtocolCM.toVM'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.ProtocolCM.toVM

/-- info: 'ModalDistribution.Examples.ThyHBB4.VM.conflict_yields_strict_depth_chain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.VM.conflict_yields_strict_depth_chain

/-- info: 'ModalDistribution.Examples.ThyHBB4.VM.conflicting_rank_lt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.VM.conflicting_rank_lt

/-- info: 'ModalDistribution.Examples.ThyHBB4.VM.agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.VM.agreement

/-- info: 'ModalDistribution.Examples.ThyHBB4.VM.livenessOne'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.VM.livenessOne

/-- info: 'ModalDistribution.Examples.ThyHBB4.VM.livenessTwo'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.VM.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB4.VM.agreement_modal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.VM.agreement_modal

/-- info: 'ModalDistribution.Examples.ThyHBB4.VM.livenessOne_modal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.VM.livenessOne_modal

/-- info: 'ModalDistribution.Examples.ThyHBB4.VM.livenessTwo_modal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.VM.livenessTwo_modal

/-! Semantic correspondences and paper-facing correctness corollaries. -/

/-- info: 'ModalDistribution.Logic.observedAt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Logic.observedAt_iff

/-- info: 'ModalDistribution.Logic.occursAt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Logic.occursAt_iff

/-- info: 'ModalDistribution.Logic.uniqueOccurrence_iff_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Logic.uniqueOccurrence_iff_end

/-- info: 'ModalDistribution.Logic.correlated_final_iff_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Logic.correlated_final_iff_end

/-- info: 'ModalDistribution.Logic.quorum_final_iff_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Logic.quorum_final_iff_end

/-- info: 'ModalDistribution.Logic.occurrence_agreement_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Logic.occurrence_agreement_iff

/-- info: 'ModalDistribution.Logic.occurrence_liveness_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Logic.occurrence_liveness_iff

/-- info: 'ModalDistribution.Logic.correlated_at_event_of_final' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Logic.correlated_at_event_of_final

/-- info: 'ModalDistribution.Examples.HBB.echo_of_unique_proposal' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.HBB.echo_of_unique_proposal

/-- info: 'ModalDistribution.Examples.ThyHBB1.agreement_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB1.agreement_modal

/-- info: 'ModalDistribution.Examples.ThyHBB1.livenessOne_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB1.livenessOne_modal

/-- info: 'ModalDistribution.Examples.ThyHBB1.livenessTwo_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB1.livenessTwo_modal

/-- info: 'ModalDistribution.Examples.ThyHBB2.agreement_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB2.agreement_modal

/-- info: 'ModalDistribution.Examples.ThyHBB2.livenessOne_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB2.livenessOne_modal

/-- info: 'ModalDistribution.Examples.ThyHBB2.livenessTwo_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB2.livenessTwo_modal

/-- info: 'ModalDistribution.Examples.ThyHBB3.agreement_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB3.agreement_modal

/-- info: 'ModalDistribution.Examples.ThyHBB3.livenessOne_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB3.livenessOne_modal

/-- info: 'ModalDistribution.Examples.ThyHBB3.livenessTwo_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB3.livenessTwo_modal

/-- info: 'ModalDistribution.Examples.ThyHBB4.CM.agreement_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.CM.agreement_modal

/-- info: 'ModalDistribution.Examples.ThyHBB4.CM.livenessOne_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.CM.livenessOne_modal

/-- info: 'ModalDistribution.Examples.ThyHBB4.CM.livenessTwo_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.CM.livenessTwo_modal

