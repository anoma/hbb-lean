import ModalDistribution.Examples.ThyHBB1
import ModalDistribution.Examples.ThyHBB2
import ModalDistribution.Examples.ThyHBB3
import ModalDistribution.Examples.ThyHBB4
import ModalDistribution.Examples.ThyHBB4B
import ModalDistribution.Examples.ThyLive.FiniteHistory
import ModalDistribution.Examples.ThyLive.FiniteModel
import ModalDistribution.LowerBound.HBB4
import ModalDistribution.LowerBound.Theorem
import ModalDistribution.LowerBound.HBB4Protocol
import ModalDistribution.Examples.ThyAgreement
import ModalDistribution.LowerBoundAgreement.Theorem

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

/-- info: 'ModalDistribution.Examples.ThyHBB4.CM.livenessTwo'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.CM.livenessTwo

/-- info: 'ModalDistribution.Examples.ThyHBB4.FiniteModel.finite_protocol_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.FiniteModel.finite_protocol_nonvacuous

/-! Fast delivery path: safety rests on echoes from every not-yet-equivocating
participant, not on depth. -/

/-- info: 'ModalDistribution.Examples.ThyHBB4.zero_quorum_of_delivery'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.zero_quorum_of_delivery

/-- info: 'ModalDistribution.Examples.ThyHBB4.value_of_echo_unanimity_at'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModalDistribution.Examples.ThyHBB4.value_of_echo_unanimity_at

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

/-- info: 'ModalDistribution.Examples.ThyHBB4.VM.livenessTwo_modal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-! ## Depth lower bound for HBB4 -/
#print axioms ModalDistribution.LowerBound.delivery_depth_of_usesOnly
#print axioms ModalDistribution.LowerBound.HBB4.Witness.protocol
#print axioms ModalDistribution.LowerBound.HBB4.hbb4_depth_lower_bound

/-! ## ThyAgreement (initially a verbatim copy of HBB4; every result re-established) -/
#print axioms ModalDistribution.Examples.ThyAgreement.CM.agreement
#print axioms ModalDistribution.Examples.ThyAgreement.CM.livenessOne
#print axioms ModalDistribution.Examples.ThyAgreement.CM.livenessTwo
#print axioms ModalDistribution.Examples.ThyAgreement.VM.agreement
#print axioms ModalDistribution.Examples.ThyAgreement.VM.livenessOne
#print axioms ModalDistribution.Examples.ThyAgreement.VM.livenessTwo
#print axioms ModalDistribution.Examples.ThyAgreement.VM.agreement_modal
#print axioms ModalDistribution.Examples.ThyAgreement.VM.livenessOne_modal
#print axioms ModalDistribution.Examples.ThyAgreement.VM.livenessTwo_modal
#print axioms ModalDistribution.Examples.ThyAgreement.CM.agreement_modal
#print axioms ModalDistribution.Examples.ThyAgreement.CM.livenessOne_modal
#print axioms ModalDistribution.Examples.ThyAgreement.CM.livenessTwo_modal
#print axioms ModalDistribution.Examples.ThyAgreement.ProtocolCM.toVM
#print axioms ModalDistribution.Examples.ThyAgreement.FiniteModel.finite_protocol_nonvacuous
#print axioms ModalDistribution.LowerBoundAgreement.Witness.protocol
#print axioms ModalDistribution.LowerBoundAgreement.Counterexample.protocol
#print axioms ModalDistribution.LowerBoundAgreement.agreement_witness
#print axioms ModalDistribution.LowerBoundAgreement.agreement_depth_lower_bound_fails
#print axioms ModalDistribution.Examples.ThyHBB4.ProtocolCM.toAgreement
#print axioms ModalDistribution.Examples.ThyHBB4.ProtocolVM.toAgreement

/-! ## The general depth lower bound (any correct, local, fairly completable protocol) -/
#print axioms ModalDistribution.LowerBound.depth_lower_bound

/-! ## Budgeted HBB4 (`ThyHBB4B`) -/
#print axioms ModalDistribution.Examples.ThyHBB4B.CM.agreement
#print axioms ModalDistribution.Examples.ThyHBB4B.CM.livenessOne
#print axioms ModalDistribution.Examples.ThyHBB4B.CM.livenessTwo
#print axioms ModalDistribution.Examples.ThyHBB4B.VM.agreement
#print axioms ModalDistribution.Examples.ThyHBB4B.VM.livenessOne
#print axioms ModalDistribution.Examples.ThyHBB4B.VM.livenessTwo
#print axioms ModalDistribution.Examples.ThyHBB4B.FiniteModel.finite_protocol_nonvacuous

/-! ## HBB4 as a protocol (fair completion assumed as a hypothesis) -/
#print axioms ModalDistribution.LowerBound.HBB4.hbb4Protocol_correct
#print axioms ModalDistribution.LowerBound.HBB4.hbb4_protocol_depth_bound
