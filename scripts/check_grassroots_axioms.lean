import ModalDistribution.Grassroots.Sequentiality
import ModalDistribution.Grassroots.Coalescent
import ModalDistribution.Grassroots.LeaderRooted
import ModalDistribution.Grassroots.Abstract
import ModalDistribution.Grassroots.HBBBridge
import ModalDistribution.Grassroots.LiftableFragment
import ModalDistribution.Grassroots.LiftHistory
import ModalDistribution.Grassroots.LiftPreservation

/-!
Print the axioms each main theorem of the Grassroots modules depends on.
Used to verify there are no `sorryAx` in the development.
-/

-- Sequentiality module
#print axioms ModalDistribution.Grassroots.projectPreHistory_isHereditarilyTransitive
#print axioms ModalDistribution.Grassroots.mem_projectPreHistory_iff
#print axioms ModalDistribution.Grassroots.accessible_project_of_accessible
#print axioms ModalDistribution.Grassroots.isSequential_projection
#print axioms ModalDistribution.Grassroots.History_isSequential_project

-- Coalescent module
#print axioms ModalDistribution.Grassroots.liftAgent_injective
#print axioms ModalDistribution.Grassroots.restrict_lift_eq_self
#print axioms ModalDistribution.Grassroots.lift_restrict_eq_inter_range
#print axioms ModalDistribution.Grassroots.restrictQuorumSet_inter
#print axioms ModalDistribution.Grassroots.quorum_descent
#print axioms ModalDistribution.Grassroots.lifted_membership
#print axioms ModalDistribution.Grassroots.coalescence_quorum_witness
#print axioms ModalDistribution.Grassroots.restrict_intersection_witness
#print axioms ModalDistribution.Grassroots.lift_intersection_witness
#print axioms ModalDistribution.Grassroots.mem_restrictedQuorums_imp_quorum
#print axioms ModalDistribution.Grassroots.quorum_in_restrictedQuorums
#print axioms ModalDistribution.Grassroots.quorums_eq_restrictedQuorums

-- LeaderRooted module
#print axioms ModalDistribution.Grassroots.LeaderRooted.semifilter
#print axioms ModalDistribution.Grassroots.LeaderRooted.semifilter_quorums_iff
#print axioms ModalDistribution.Grassroots.LeaderRooted.family
#print axioms ModalDistribution.Grassroots.LeaderRooted.family_leader
#print axioms ModalDistribution.Grassroots.LeaderRooted.family_quorums_iff
#print axioms ModalDistribution.Grassroots.LeaderRooted.instCoalescent
#print axioms ModalDistribution.Grassroots.LeaderRooted.family_interactive

-- Abstract module
#print axioms ModalDistribution.Grassroots.Abstract.project_lift_eq
#print axioms ModalDistribution.Grassroots.Abstract.liftConfig_inP
#print axioms ModalDistribution.Grassroots.Abstract.liftConfig_outP
#print axioms ModalDistribution.Grassroots.Abstract.DTS.initialConfig_mem_reachable
#print axioms ModalDistribution.Grassroots.Abstract.IsOblivious.lift_reachable
#print axioms ModalDistribution.Grassroots.Abstract.IsOblivious.lift_reachable_set
#print axioms ModalDistribution.Grassroots.Abstract.Trivial.trivialDTS_oblivious
#print axioms ModalDistribution.Grassroots.Abstract.Trivial.trivialDTS_reachableConfigs

-- HBBBridge module
#print axioms ModalDistribution.Grassroots.HBBBridge.liftConfig_apply_lift
#print axioms ModalDistribution.Grassroots.HBBBridge.broadcastDTS_oblivious

-- LiftableFragment module
#print axioms ModalDistribution.Grassroots.LiftableFragment.echoBackwardAxiom_isLiftable
#print axioms ModalDistribution.Grassroots.LiftableFragment.voteBackwardAxiom_isLiftable
#print axioms ModalDistribution.Grassroots.LiftableFragment.deliverBackwardAxiom_isLiftable
#print axioms ModalDistribution.Grassroots.LiftableFragment.echoNonEquivAxiom_isLiftable
#print axioms ModalDistribution.Grassroots.LiftableFragment.safeFormula_isLiftable
#print axioms ModalDistribution.Grassroots.LiftableFragment.safeFormula_isAntiLiftable
#print axioms ModalDistribution.Grassroots.LiftableFragment.isAntiLiftable_boxPastEvent
#print axioms ModalDistribution.Grassroots.LiftableFragment.echoForwardAxiom_isLiftable
#print axioms ModalDistribution.Grassroots.LiftableFragment.voteForwardAxiom_isLiftable
#print axioms ModalDistribution.Grassroots.LiftableFragment.deliverForwardAxiom_isLiftable

-- LiftHistory module
#print axioms ModalDistribution.Grassroots.mem_liftPreHistory_iff
#print axioms ModalDistribution.Grassroots.liftPreHistory_isHereditarilyTransitive
#print axioms ModalDistribution.Grassroots.liftAgent_injective
#print axioms ModalDistribution.Grassroots.isSequential_lift
#print axioms ModalDistribution.Grassroots.History_isSequential_lift

-- LiftPreservation module
#print axioms ModalDistribution.Grassroots.LiftPreservation.projectPreHistory_liftPreHistory
#print axioms ModalDistribution.Grassroots.LiftPreservation.liftPredInterp_at_lifted
#print axioms ModalDistribution.Grassroots.LiftPreservation.canonicalLift_predInterp_at_lifted

-- Session 3: mutual preservation theorem (NOTE: has sorry for diamond cases)
-- These will show `sorryAx` until Session 4 fills in the diamond proofs.
#print axioms ModalDistribution.Grassroots.lift_preserves
#print axioms ModalDistribution.Grassroots.anti_lift_preserves
-- Helper lemma (no sorry)
-- #print axioms ModalDistribution.Grassroots.liftWorld_injective  -- private
