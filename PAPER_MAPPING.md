# Paper to Formalization Mapping

This file maps paper definitions, lemmas, propositions, and theorems to their Lean formalization locations. Entries are organized by paper section in strict numerical order for easy reference while reading the paper.

---

## Section 2: History Structures and Their Logic

### Definition 2.2.4 (Prehistories)
- `PreHistory` (ModalDistribution/Core/Prehistory.lean)

### Definition 2.2.6 (Event-tuples)
- `World` (ModalDistribution/Core/Prehistory.lean)
- Projections: `place`, `event`, `time` (ModalDistribution/Core/Prehistory.lean)

### Definition 2.2.6(5) ("knows of" relation)
- `mem` (ModalDistribution/Core/Prehistory.lean)
- Membership instance (ModalDistribution/Core/Prehistory.lean)

### Remark 2.2.7 (Fixpoint characterization)
- `prehistory_fixpoint` (ModalDistribution/Core/Prehistory.lean)

### Definition 2.3.1 (Element-of relation)
- `happensBefore` (ModalDistribution/Core/Prehistory.lean)
- `happensBeforeEq` (ModalDistribution/Core/Prehistory.lean)

### Definition 2.3.2 (Transitive prehistory)
- `isTransitive` (ModalDistribution/Core/History.lean)
- `TransitiveSubset` (ModalDistribution/Core/History.lean)

### Definition 2.3.5 (History structures)
- `History` (ModalDistribution/Core/History.lean)
- `isHereditarilyTransitive` (ModalDistribution/Core/History.lean)

### Definition 2.3.13 (Initial/final event-tuples)
- `isInitialTuple` (ModalDistribution/Core/History.lean)
- `isFinalTuple` (ModalDistribution/Core/History.lean)
- `isInitialAt` (ModalDistribution/Core/History.lean)
- `isFinalAt` (ModalDistribution/Core/History.lean)

---

## Section 3: Logic over History Structures

### Figure 2 (Syntax of predicates)
**Terms:** Higher-order abstract syntax (HOAS); values as `S.Value` (ModalDistribution/Logic/Syntax.lean)

**Formulas:** `Formula` inductive type (ModalDistribution/Logic/Syntax.lean)
- `Formula.bot` (⊥)
- `Formula.imp` (φ⇒φ)
- `Formula.eq` (t≡t)
- `Formula.forall` (∀a.φ)
- `Formula.event` (E(t,...,t))
- `Formula.predicate` (P(t,...,t))
- `Formula.past` (↓φ)
- `Formula.atEnd` (⤒φ)
- `Formula.diamond` (♢{t₁...tₙ}φ)
- `Formula.seq`

**Supporting structures:**
- `EventAtom` (ModalDistribution/Logic/Syntax.lean)
- `PredicateAtom` (ModalDistribution/Logic/Syntax.lean)

### Definition 3.1.1 (Signature)
- `Signature` (ModalDistribution/Core/Model.lean)

### Definition 3.1.1(2) (Events and Atomic Predicates)
- `Signature.Event` (ModalDistribution/Core/Model.lean)
- `Signature.AtomicPred` (ModalDistribution/Core/Model.lean)

### Definition 3.1.3 (Syntax of terms and predicates)
Same as Figure 2 (ModalDistribution/Logic/Syntax.lean)

### Notation 3.3.1 (Intersects relation)
- `intersects` (ModalDistribution/Core/Semifilter.lean)

### Definition 3.3.2 (Semifilters)
- `Semifilter` (ModalDistribution/Core/Semifilter.lean)

### Definition 3.3.3 (Models)
- `Model` (ModalDistribution/Core/Model.lean)

### Definition 3.3.3(2) (History structure H)
- `Model.history` (ModalDistribution/Core/Model.lean)

### Definition 3.3.3(3) (Predicate interpretation ϱ)
- `Model.predInterp` (ModalDistribution/Core/Model.lean)

### Definition 3.3.3(4) (Learner interpretation ς)
- `Model.learner` (ModalDistribution/Core/Model.lean)

### Remark 3.3.8 (Values used for learners)
- `Signature.Value` (ModalDistribution/Core/Model.lean)

### Definition 3.4.2 (Kripke-style semantics)
- `accessible` (ModalDistribution/Core/Prehistory.lean)
- `accessibleLe` (ModalDistribution/Core/Prehistory.lean)

### Lemma 3.4.3 (Accessibility implies proper subset of time)
- `height_lt_of_accessible` (ModalDistribution/Core/Prehistory.lean)

### Figure 3 (Validity/satisfaction clauses)
**Satisfaction relation:** `Sat` (ModalDistribution/Logic/Semantics.lean)
- `⊥` clause
- Implication `φ ⇒ ψ`
- Equality `v₁ = v₂`
- Universal quantification `∀`
- Event atoms
- Predicate atoms
- Past modality `↓ᶠφ`
- At-end modality `⤒ᶠφ`
- Diamond modality `♢ᶠ[learners]φ`
- Sequential predicate `seq`

**Notation:** `⟪w⟫ ⊨[M]φ` (ModalDistribution/Logic/Semantics.lean)

### Proposition 3.4.5 (Transitivity and irreflexivity of accessibility)
- `accessible_irrefl` (ModalDistribution/Core/Prehistory.lean)

### Definition 3.4.7 (History H at p)
- Part 1: `historyAt` (ModalDistribution/Core/Prehistory.lean)
- Part 2: `historyAt` (ModalDistribution/Core/History.lean)

### Definition 3.4.9 (Sequentiality)
- `isSequential` (ModalDistribution/Core/History.lean)

### Definition 3.4.10 (Validity)
- `EndValid` (ModalDistribution/Logic/Semantics.lean)
- `AllWorldValid` (ModalDistribution/Logic/Semantics.lean)

### Definition 3.5.1 (Active participants)
- `IsActive` (ModalDistribution/Logic/Semantics.lean)

### Lemma 3.5.3 (Active participants characterization)
- `active_iff_past_top` (ModalDistribution/Logic/Semantics.lean)

### Remark 3.7.7 (De Morgan dualities)
- Part 1: `diamond_valid_iff_not_box_not` (ModalDistribution/Logic/Properties/Modalities.lean)
- Part 2: `box_valid_iff_not_diamond_not` (ModalDistribution/Logic/Properties/Modalities.lean)
- Part 3: `diamondPast_valid_iff_not_boxEventually_not` (ModalDistribution/Logic/Properties/Modalities.lean)
- Part 4: `boxEventually_valid_iff_not_diamondPast_not` (ModalDistribution/Logic/Properties/Modalities.lean)
- Part 5: `diamondEventually_valid_iff_not_boxPast_not` (ModalDistribution/Logic/Properties/Modalities.lean)
- Part 6: `boxPast_valid_iff_not_diamondEventually_not` (ModalDistribution/Logic/Properties/Modalities.lean)

---

## Section 4: The Modalities

### Lemma 4.1.1 (N-way quorum intersection)
**Supporting semifilter definitions:**
- `familyQuorums`, `familyInter`, `familyInterNonempty`, `familyInterWitness` (ModalDistribution/Core/Semifilter.lean)
- `allFamilyInterNonempty`, `allFamilyInterWitness`, `sequentialFamilyIntersections` (ModalDistribution/Core/Semifilter.lean)

- Part 1: `familyInterWitness_iff`, `nWayQuorumIntersectionWitness` (ModalDistribution/Core/Semifilter.lean, ModalDistribution/Logic/Properties/Modalities.lean)
- Part 2: `familyInterNonempty_iff`, `nWayQuorumIntersectionNonempty` (ModalDistribution/Core/Semifilter.lean, ModalDistribution/Logic/Properties/Modalities.lean)
- Part 3: `familyInterWitness_imp_nonempty`, `quorumWitnessImpliesNonempty` (ModalDistribution/Core/Semifilter.lean, ModalDistribution/Logic/Properties/Modalities.lean)

**Supporting lemmas:**
- `hasQuorumWitness`, `presentBoxImpliesPastBox`, `pastBoxAtTopWorld` (ModalDistribution/Logic/Properties/Modalities.lean)
- `pastBoxTopImpliesPredecessor`, `pastBoxSeqImpliesPredecessor` (ModalDistribution/Logic/Properties/Modalities.lean)

### Notation 4.1.2 (Intersecting quorums)
- `hasNonemptyIntersections` (ModalDistribution/Logic/Properties/Modalities.lean)
- `hasSequentialIntersections` (ModalDistribution/Logic/Properties/Modalities.lean)
- `hasLiveIntersections` (ModalDistribution/Logic/Properties/Modalities.lean)

### Lemma 4.2.2 (Idempotency)
- `quorumBoxGlobalImpliesEmptyDiamond` (ModalDistribution/Logic/Properties/Modalities.lean)

### Lemma 4.2.3 (Box implies diamond / Collapsing properties)
- `singletonBoxImpliesDiamond` (ModalDistribution/Logic/Properties/Modalities.lean)
- `globalSingletonBoxImpliesDiamond` (ModalDistribution/Logic/Properties/Modalities.lean)
- `quorumBoxImpliesEmptyDiamond` (ModalDistribution/Logic/Properties/Modalities.lean)
- `pastBoxCollapsesToPresentBox` (ModalDistribution/Logic/Properties/Modalities.lean)
- `pastDiamondBoxCollapsesToPresentBox` (ModalDistribution/Logic/Properties/Modalities.lean)

---

## Section 5: Sequentiality and Liveness

### Lemma 5.1.2 (Sequentiality characterization)
- `seq_iff_linear_accessible` (ModalDistribution/Logic/Properties/Sequentiality.lean)

### Lemma 5.1.3 (Accessible subset preservation)
- `accessible_subset_of_accessible` (ModalDistribution/Logic/Properties/Sequentiality.lean)

### Proposition 5.1.4 (Sequentiality monotonicity)
- Part 1: `seq_monotone_of_subset` (ModalDistribution/Logic/Properties/Sequentiality.lean)
- Part 2: `seq_monotone_allItp` (ModalDistribution/Logic/Properties/Sequentiality.lean)
Also: `sequentiality_monotone` (ModalDistribution/Core/History.lean)

### Proposition 5.1.5 (Two quorums interaction with sequentiality)
- `two_quorums_exists` (ModalDistribution/Logic/Properties/Sequentiality.lean)
- `seq_two_quorums_events` (ModalDistribution/Logic/Properties/Sequentiality.lean)
- `seq_two_quorums_eventually` (ModalDistribution/Logic/Properties/Sequentiality.lean)

### Definition 5.2.1 (Axioms and their validity)
- `Axiom` (ModalDistribution/Logic/AxiomSystem.lean)
- `Axiom.Valid` (ModalDistribution/Logic/AxiomSystem.lean)
- `Theory` (ModalDistribution/Logic/AxiomSystem.lean)
- `Theory.Valid` (ModalDistribution/Logic/AxiomSystem.lean)

### Lemma 5.2.7 (Sometime knowledge lifts to end of time)
- `sometime_past_end` (ModalDistribution/Examples/ThyLive.lean)

### Proposition 5.2.8 (Live quorums eventually know past facts)
- `live_eventually_knows` (ModalDistribution/Examples/ThyLive.lean)

### Corollary 5.2.9 (Consequences of eventual knowledge)
- Part 1: `live_eventually_knows_event` (ModalDistribution/Examples/ThyLive.lean)
- Part 2: `live_eventually_knows_performed` (ModalDistribution/Examples/ThyLive.lean)
- Part 3: `live_eventually_knows_quorum` (ModalDistribution/Examples/ThyLive.lean)

### Lemma 5.2.9(1) (Liveness at world equivalent to liveness at end-of-time)
- `alwaysLiveEquivForward` (ModalDistribution/Examples/ThyLive.lean)

### Lemma 5.2.10 (Liveness preservation across worlds at same place)
- `alwaysLiveEquivBackward` (ModalDistribution/Examples/ThyLive.lean)

### Proposition 5.2.11 (Intertwined quorums)
- `intertwined_two_quorums` (ModalDistribution/Examples/ThyLive.lean)

### Lemma 5.2.12 (Liveness quorum boxes promote to nested boxes)
- `promote_live_atddot` (ModalDistribution/Examples/ThyLive.lean)

---

## Section 6: Theory ThyHBB1

### Figure 7 (Theory ThyHBB1 axiom system)
Safety axioms for echo, vote, and deliver predicates (ModalDistribution/Examples/ThyHBB1/Axioms.lean)

### Proposition 6.3.1 (Agreement property for ThyHBB1)
- `agreementThyHBB1` (ModalDistribution/Examples/ThyHBB1/Agreement.lean)
- `agreementFromDeliveriesThyHBB1` (ModalDistribution/Examples/ThyHBB1/Agreement.lean)

### Lemma 6.4.1 (Safety monotonicity)
- Part 1: `safe_monotone_subset` (ModalDistribution/Examples/ThyHBB1/Safety.lean)
- Part 2: `safe_allPast` (ModalDistribution/Examples/ThyHBB1/Safety.lean)

### Lemma 6.4.2 (Eventual quorum lifting)
- Part 1: `atddot_of_eventual_quorum` (ModalDistribution/Examples/ThyHBB1/Safety.lean)
- Part 2: `atddot_live_of_eventual_quorum` (ModalDistribution/Examples/ThyHBB1/Safety.lean)

### Lemma 6.4.3 (End-of-time consequence composition)
- `live_eventually_consequent` (ModalDistribution/Examples/ThyHBB1/Safety.lean)

### Lemma 6.4.4 (Box-sometime equivalence)
- `atd_sometime_iff_atddot` (ModalDistribution/Examples/ThyHBB1/Safety.lean)

### Proposition 6.4.5 (Liveness property 2)
- `livenessTwoThyHBB1` (ModalDistribution/Examples/ThyHBB1/Liveness_Two.lean)
- `livenessTwoAtPastDownThyHBB1` (ModalDistribution/Examples/ThyHBB1/Liveness_Two.lean)
- `livenessTwoAtPastThyHBB1` (ModalDistribution/Examples/ThyHBB1/Liveness_Two.lean)

### Lemma 6.4.6 (Delivery from vote quorum)
- `deliver_from_vote_box` (ModalDistribution/Examples/ThyHBB1/LivenessHelpers.lean)

### Lemma 6.5.1 (Unique proposals imply eventual echoes)
- `uniquePropose_eventually_echo` (ModalDistribution/Examples/ThyHBB1/Uniqueness.lean)

### Lemma 6.5.2 (Uniqueness implies safety)
- `atMostOnePropose_safe` (ModalDistribution/Examples/ThyHBB1/Uniqueness.lean)

### Proposition 6.5.3 (Liveness property 1)
- `livenessOneThyHBB1` (ModalDistribution/Examples/ThyHBB1/Liveness_One.lean)
- `livenessOneAtPastDownThyHBB1` (ModalDistribution/Examples/ThyHBB1/Liveness_One.lean)
- `livenessOneAtPastThyHBB1` (ModalDistribution/Examples/ThyHBB1/Liveness_One.lean)

### Theorem 6.6.1 (Main agreement theorem)
Same as Proposition 6.3.1 above (ModalDistribution/Examples/ThyHBB1/Agreement.lean)

---

## Section 7: Theory ThyHBB2

### Figure 9 (Theory ThyHBB2 axiom system)
**Backward rules:** `echoBackwardAxiom`, `voteBackwardAxiom`, `deliverBackwardAxiom` (ModalDistribution/Examples/ThyHBB2/Axioms.lean)

**Non-equivocation:** `echoNonEquivAxiom` (ModalDistribution/Examples/ThyHBB2/Axioms.lean)

**Forward rules:** `echoForwardAxiom`, `voteForwardAxiom`, `deliverForwardAxiom` (ModalDistribution/Examples/ThyHBB2/Axioms.lean)

### Definition 7.1.1 (Theory ThyHBB2)
- `ThyHBB2.theory` (ModalDistribution/Examples/ThyHBB2/Axioms.lean)
- `ThyHBB2` (ModalDistribution/Examples/ThyHBB2/Axioms.lean)

### Proposition 7.2.1 (Agreement for ThyHBB2)
- `agreementThyHBB2` (ModalDistribution/Examples/ThyHBB2/Agreement.lean)
- `agreementThyHBB2_of_deliveries` (ModalDistribution/Examples/ThyHBB2/Agreement.lean)

### Proposition 7.2.2 (Liveness property 2 for ThyHBB2)
- `livenessTwoThyHBB2` (ModalDistribution/Examples/ThyHBB2/Liveness_Two.lean)
- `livenessTwoAtPastDownThyHBB2` (ModalDistribution/Examples/ThyHBB2/Liveness_Two.lean)
- `livenessTwoAtPastThyHBB2` (ModalDistribution/Examples/ThyHBB2/Liveness_Two.lean)

### Proposition 7.2.3 (Liveness property 1 for ThyHBB2)
- `livenessOneThyHBB2` (ModalDistribution/Examples/ThyHBB2/Liveness_One.lean)
- `livenessOneAtPastDownThyHBB2` (ModalDistribution/Examples/ThyHBB2/Liveness_One.lean)
- `livenessOneAtPastThyHBB2` (ModalDistribution/Examples/ThyHBB2/Liveness_One.lean)

---

## Section 8: Theory ThyHBB3

### Definition 8.2.1 (Theory ThyHBB3)
- `ThyHBB3.theory` (ModalDistribution/Examples/ThyHBB3/Axioms.lean)
- `ThyHBB3` (ModalDistribution/Examples/ThyHBB3/Axioms.lean)

### Proposition 8.3.1 (Agreement for ThyHBB3)
- `agreementThyHBB3` (ModalDistribution/Examples/ThyHBB3/Agreement.lean)
- `agreementThyHBB3_of_deliveries` (ModalDistribution/Examples/ThyHBB3/Agreement.lean)

### Lemma 8.4.1 (3twined combines three guarded box facts)
- `threeTwined_phi` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)

### Lemma 8.4.2 (Votes imply quorum of echoes)
- Part 1: `vote_implies_echo_quorum_local` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)
- Part 2: `vote_implies_echo_quorum_end` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)

### Lemma 8.4.3 (Echo quorums/votes agreeing)
- Part 1: `echo_quorums_agree` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)
- Part 2: `votes_eventually_agree` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)
- Part 3: `correlated_vote_eventually` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)
- Part 4: `live_echo_eventually_vote` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)

### Lemma 8.4.4 (Correlation implies intersections)
- Part 1: `correlationImpliesPairwiseQuorumIntersection` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)
- Part 2: `correlationImpliesQuorumIntersection` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)
Also: `correlationEveryoneImpliesIntersection` (ModalDistribution/Examples/ThyHBB3/Lemmas.lean)

### Proposition 8.4.5 (Liveness property 2 for ThyHBB3)
- `livenessTwoThyHBB3` (ModalDistribution/Examples/ThyHBB3/Liveness_Two.lean)
- `livenessTwoAtPastDownThyHBB3` (ModalDistribution/Examples/ThyHBB3/Liveness_Two.lean)
- `livenessTwoAtPastThyHBB3` (ModalDistribution/Examples/ThyHBB3/Liveness_Two.lean)

### Proposition 8.5.1 (Liveness property 1 for ThyHBB3)
- `livenessOneThyHBB3` (ModalDistribution/Examples/ThyHBB3/Liveness_One.lean)
- `livenessOneAtPastDownThyHBB3` (ModalDistribution/Examples/ThyHBB3/Liveness_One.lean)
- `livenessOneAtPastThyHBB3` (ModalDistribution/Examples/ThyHBB3/Liveness_One.lean)

### Figure 11 (Theory ThyHBB3 axiom system)
**Backward rules:** `echoBackwardAxiom`, `voteBackwardAxiom`, `deliverBackwardAxiom` (ModalDistribution/Examples/ThyHBB3/Axioms.lean)

**Non-equivocation:** `echoNonEquivAxiom`, `voteNonEquivAxiom` (ModalDistribution/Examples/ThyHBB3/Axioms.lean)

**Correlation:** `threeTwinedAxiom`, `mntaSeqAxiom`, `mntaEventuallyAxiom`, `mntaSymmAxiom`, `mntaTransAxiom` (ModalDistribution/Examples/ThyHBB3/Axioms.lean)

**Forward rules:** `echoForwardAxiom`, `voteForwardAxiom`, `voteForwardCorrelatedAxiom`, `deliverForwardAxiom` (ModalDistribution/Examples/ThyHBB3/Axioms.lean)

---
