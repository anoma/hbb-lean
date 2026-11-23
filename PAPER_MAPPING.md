# Paper to Formalization Mapping

This file maps the numbered items of the paper (draft of 2026/11/18) to
their Lean formalizations. The same information is embedded in the sources:
every anchored declaration's doc comment begins with `Paper: <item>.`, so
`grep -rn "Paper: Lemma 4.2.2" ModalDistribution` finds an item directly.

Items are listed in paper order; theory axioms are listed at the position of
the figure that defines them. Declarations inside a theory's namespace are
written without the `HBBSafe.`, `HBBSimp.` or `HBBCorr.` prefix; e.g.
Proposition 6.4.1 is `HBBSafe.agreement`.

## Not formalized

- Notation 2.2.1 (finite subsets): implicit — `PreHistory` is list-backed, so
  every prehistory is finite by construction.
- Notations 2.3.6, 3.1.2, 3.3.7, 6.2.3 and the Remarks: prose conventions
  and discussion, no formal content.
- Definitions 1.1.4 and 1.1.5: informal introductory definitions.
- The paper's illustrative Examples (2.2.5, 2.3.8-2.3.10, 3.3.5, 3.3.6, 5.1.1).

## Beyond the paper

- `NonVacuity.hbbSafe_nonvacuous`, `NonVacuity.hbbSimp_nonvacuous` and
  `NonVacuity.hbbCorr_nonvacuous`
  ([ModalDistribution/Examples/NonVacuity.lean](ModalDistribution/Examples/NonVacuity.lean)):
  each theory has a finite model in which the hypotheses of its three
  correctness properties hold at once and a live participant delivers, so the
  correctness theorems are not vacuously true. The paper does not state this.

## Representation note

`PreHistory` is backed by lists rather than finite sets, so it realises the
paper's inductive-datatype presentation (Section 2.1) instead of the
quotiented set-theoretic Definition 2.2.4: distinct terms can denote the same
intended prehistory. This is benign here because every result is stated
through membership, never through equality of prehistories — exactly the
"little harm will come of it" reading the paper offers for the datatype view.


## Section 2: History Structures

- **Notation 2.2.2 (maybe-sets)** — `MaybeEvent` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 2.2.4 (Prehistories)** — `PreHistory` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 2.2.6(1) (event-tuples)** — `World` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 2.2.6(2)** — `place` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 2.2.6(2)** — `event` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 2.2.6(2)** — `time` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 2.2.6(5) (the "knows of" relation)** — `mem` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Remark 2.2.7 (fixpoint characterisation)** — `prehistory_fixpoint` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 2.3.1(1) (element-of, ≺−)** — `happensBefore` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 2.3.1(2) (non-strict element-of, ⪯)** — `happensBeforeEq` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 2.3.2 (transitive prehistories)** — `isTransitive` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 2.3.5** — `isHereditarilyTransitive` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 2.3.5 (history structures)** — `History` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 2.3.11 (element-transitive)** — `isElementTransitive` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Lemma 2.3.12(1)** — `isTransitive.isElementTransitive` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Lemma 2.3.12(2)** — `exists_elementTransitive_not_transitive` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Lemma 2.3.12(3)** — `History.isElementTransitive` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 2.3.13(2)** — `isInitialTuple` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 2.3.13(2)** — `isInitialAt` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 2.3.13(3)** — `isFinalTuple` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 2.3.13(3)** — `isFinalAt` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))

## Section 3: Logic over History Structures

- **Definition 3.1.1(1); values double as learners per Remark 3.3.8** — `Signature` ([ModalDistribution/Core/Model.lean](ModalDistribution/Core/Model.lean))
- **Definition 3.1.1(2) (events over Σ)** — `Event` ([ModalDistribution/Core/Model.lean](ModalDistribution/Core/Model.lean))
- **Definition 3.1.1(2) (atomic predicates over Σ)** — `AtomicPred` ([ModalDistribution/Core/Model.lean](ModalDistribution/Core/Model.lean))
- **Definition 3.1.3 / Figure 3 (syntax of predicates)** — `Formula` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 3 (event atoms)** — `EventAtom` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 3 (predicate atoms)** — `PredicateAtom` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Notation 3.3.1 (≬)** — `intersects` ([ModalDistribution/Core/Semifilter.lean](ModalDistribution/Core/Semifilter.lean))
- **Definition 3.3.2 (semifilters)** — `Semifilter` ([ModalDistribution/Core/Semifilter.lean](ModalDistribution/Core/Semifilter.lean))
- **Definition 3.3.3 (models)** — `Model` ([ModalDistribution/Core/Model.lean](ModalDistribution/Core/Model.lean))
- **Definition 3.4.2(3) (accessibility, ≪)** — `accessible` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 3.4.2(4) (in-place accessibility, ≪⁻)** — `accessibleLe` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Lemma 3.4.3** — `happensBefore_of_accessible` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Lemma 3.4.4** — `accessible_happensBefore_history` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Proposition 3.4.5 (irreflexivity)** — `accessible_irrefl` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Proposition 3.4.5 (transitivity)** — `accessible_trans` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 3.4.7 (H at p)** — `historyAt` ([ModalDistribution/Core/Prehistory.lean](ModalDistribution/Core/Prehistory.lean))
- **Definition 3.4.9(1) (p sequential at H)** — `isSequential` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 3.4.9(2) (H sequential)** — `isSequentialAll` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Definition 3.4.10(1) / Figure 4 (possible-world validity)** — `Sat` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Definition 3.4.10(2) (end-of-time validity ⊨)** — `EndValid` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Definition 3.4.10(3) (all-world validity □W⊨)** — `AllWorldValid` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Definition 3.5.1 (active participants)** — `IsActive` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Lemma 3.5.3** — `active_iff_past_top` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Figure 5 sugar (¬)** — `not` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (⊤)** — `top` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (∧)** — `and` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (∨)** — `or` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (⇔)** — `iff` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (∃)** — `exists_` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (∃≤1)** — `existsAtMostOne` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (∃=1)** — `existsUnique` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (⇓)** — `allPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (↕)** — `sometime` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (⇕)** — `everytime` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (□ l₁…lₙ)** — `box` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (♢↓)** — `diamondPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (□↓)** — `boxPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (♢⇓)** — `diamondAllPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 5 sugar (□⇓)** — `boxAllPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Lemma 3.6.4(1)** — `sometime` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Lemma 3.6.4(2)** — `everytime` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Lemma 3.6.4(3)** — `sat_diamondPast_iff_quorum_witness` ([ModalDistribution/Logic/Properties/Satisfaction.lean](ModalDistribution/Logic/Properties/Satisfaction.lean))

## Section 4: The Modalities

- **Lemma 4.1.1(1)** — `nWayQuorumIntersectionWitness` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.1.1(2)** — `nWayQuorumIntersectionNonempty` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.1.1(3)** — `quorumWitnessImpliesNonempty` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Notation 4.1.2 (nonempty quorum intersections)** — `hasNonemptyIntersections` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Notation 4.1.2 (sequential quorum intersections)** — `hasSequentialIntersections` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Notation 4.1.2 (live quorum intersections)** — `hasLiveIntersections` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.2.1(1)** — `singletonBoxImpliesDiamond` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.2.1(2)** — `globalSingletonBoxImpliesDiamond` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.2.1(2)** — `quorumBoxImpliesEmptyDiamond` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.2.1(3)** — `box_not_implies_diamondEmpty` ([ModalDistribution/Examples/Counterexamples.lean](ModalDistribution/Examples/Counterexamples.lean))
- **Lemma 4.2.1(4)** — `sat_not_implies_diamond` ([ModalDistribution/Examples/Counterexamples.lean](ModalDistribution/Examples/Counterexamples.lean))
- **Lemma 4.2.2 (the (4) axiom of S4)** — `diamondPast_idem` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.2.3(1)** — `pastDiamondBoxCollapsesToPresentBox` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.2.3(2)** — `pastBoxCollapsesToPresentBox` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.2.3(3)** — `pastBox_does_not_reverse` ([ModalDistribution/Examples/Counterexamples.lean](ModalDistribution/Examples/Counterexamples.lean))

## Section 5: Sequentiality and Liveness

- **Lemma 5.1.2** — `seq_iff_linear_accessible` ([ModalDistribution/Logic/Properties/Sequentiality.lean](ModalDistribution/Logic/Properties/Sequentiality.lean))
- **Lemma 5.1.3** — `accessible_subset_of_accessible` ([ModalDistribution/Logic/Properties/Sequentiality.lean](ModalDistribution/Logic/Properties/Sequentiality.lean))
- **Proposition 5.1.4 (variant)** — `sequentiality_monotone` ([ModalDistribution/Core/History.lean](ModalDistribution/Core/History.lean))
- **Proposition 5.1.4(1)** — `seq_monotone_of_subset` ([ModalDistribution/Logic/Properties/Sequentiality.lean](ModalDistribution/Logic/Properties/Sequentiality.lean))
- **Proposition 5.1.4(2)** — `seq_monotone_allItp` ([ModalDistribution/Logic/Properties/Sequentiality.lean](ModalDistribution/Logic/Properties/Sequentiality.lean))
- **Proposition 5.1.5(1)** — `two_quorums_exists` ([ModalDistribution/Logic/Properties/Sequentiality.lean](ModalDistribution/Logic/Properties/Sequentiality.lean))
- **Proposition 5.1.5(2)** — `seq_two_quorums_events` ([ModalDistribution/Logic/Properties/Sequentiality.lean](ModalDistribution/Logic/Properties/Sequentiality.lean))
- **Proposition 5.1.5(3)** — `seq_two_quorums_eventually` ([ModalDistribution/Logic/Properties/Sequentiality.lean](ModalDistribution/Logic/Properties/Sequentiality.lean))
- **Definition 5.2.1(1)** — `Axiom` ([ModalDistribution/Logic/AxiomSystem.lean](ModalDistribution/Logic/AxiomSystem.lean))
- **Definition 5.2.1(2)** — `Axiom.Valid` ([ModalDistribution/Logic/AxiomSystem.lean](ModalDistribution/Logic/AxiomSystem.lean))
- **Definition 5.2.1(3)** — `Theory` ([ModalDistribution/Logic/AxiomSystem.lean](ModalDistribution/Logic/AxiomSystem.lean))
- **Definition 5.2.1(4)** — `Theory.Valid` ([ModalDistribution/Logic/AxiomSystem.lean](ModalDistribution/Logic/AxiomSystem.lean))
- **Figure 7, axiom (LiveAlways)** — `liveAlwaysAxiom` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Figure 7, axiom (LiveSeq)** — `liveSeqAxiom` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Figure 7, axiom-scheme (Knowledge♢↓)** — `knowledgeDiamondAxiom` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Figure 7, axiom-scheme (Knowledge□↓)** — `knowledgeBoxAxiom` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Definition 5.2.4 (the theory of liveness)** — `ThyLive` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.7** — `sometime_past_end` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Proposition 5.2.8** — `live_eventually_knows` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.9(1)** — `alwaysLiveEquivForward` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.9(2)** — `alwaysLiveEquivBackward` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.9(3)** — `live_allPast` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Proposition 5.2.10** — `intertwined_two_quorums` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.11** — `live_boxPast_nests` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))

## Section 6: Theory HBBSafe

- **Figures 8/10/12, rule (Echo?)** — `echoBackwardAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figures 8/10/12, axiom (EchoNE)** — `echoNonEquivAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figures 8/10/12, rule (Echo!)** — `echoForwardAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figures 8/10, rule (Deliver?)** — `deliverBackwardAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figures 8/10, rule (Deliver!)** — `deliverForwardAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figure 8, right-hand side of axiom (Safe)** — `safeFormula` ([ModalDistribution/Examples/HBBSafe/Axioms.lean](ModalDistribution/Examples/HBBSafe/Axioms.lean))
- **Figure 8, axiom (Safe)** — `safeAxiom` ([ModalDistribution/Examples/HBBSafe/Axioms.lean](ModalDistribution/Examples/HBBSafe/Axioms.lean))
- **Figure 8, rule (Vote?)** — `voteBackwardAxiom` ([ModalDistribution/Examples/HBBSafe/Axioms.lean](ModalDistribution/Examples/HBBSafe/Axioms.lean))
- **Figure 8, rule (Vote!)** — `voteForwardAxiom` ([ModalDistribution/Examples/HBBSafe/Axioms.lean](ModalDistribution/Examples/HBBSafe/Axioms.lean))
- **Definition 6.2.2 (theory HBBSafe)** — `theory` ([ModalDistribution/Examples/HBBSafe/Axioms.lean](ModalDistribution/Examples/HBBSafe/Axioms.lean))
- **Theorem 6.2.6 / Figure 9** — `correctness` ([ModalDistribution/Examples/HBBSafe/Correctness.lean](ModalDistribution/Examples/HBBSafe/Correctness.lean))
- **Proposition 6.4.1 (Agreement)** — `agreement` ([ModalDistribution/Examples/HBBSafe/Agreement.lean](ModalDistribution/Examples/HBBSafe/Agreement.lean))
- **Proposition 6.4.1, hypothesis form** — `agreement_of_deliveries` ([ModalDistribution/Examples/HBBSafe/Agreement.lean](ModalDistribution/Examples/HBBSafe/Agreement.lean))
- **Lemma 6.5.1(1)** — `safe_monotone` ([ModalDistribution/Examples/HBBSafe/Safety.lean](ModalDistribution/Examples/HBBSafe/Safety.lean))
- **Lemma 6.5.1(2)** — `safe_allPast` ([ModalDistribution/Examples/HBBSafe/Safety.lean](ModalDistribution/Examples/HBBSafe/Safety.lean))
- **Lemma 6.5.2(1)** — `boxPast_of_eventual_quorum` ([ModalDistribution/Examples/HBBSafe/Safety.lean](ModalDistribution/Examples/HBBSafe/Safety.lean))
- **Lemma 6.5.2(2)** — `boxPast_live_of_eventual_quorum` ([ModalDistribution/Examples/HBBSafe/Safety.lean](ModalDistribution/Examples/HBBSafe/Safety.lean))
- **Lemma 6.5.3** — `live_eventually_consequent` ([ModalDistribution/Examples/HBBSafe/Safety.lean](ModalDistribution/Examples/HBBSafe/Safety.lean))
- **Lemma 6.5.4** — `box_sometime_iff_boxPast` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Proposition 6.5.5 (Cascade Termination)** — `cascadeTermination` ([ModalDistribution/Examples/HBBSafe/CascadeTermination.lean](ModalDistribution/Examples/HBBSafe/CascadeTermination.lean))
- **Proposition 6.5.5, first corollary** — `cascadeTermination_boxPast` ([ModalDistribution/Examples/HBBSafe/CascadeTermination.lean](ModalDistribution/Examples/HBBSafe/CascadeTermination.lean))
- **Proposition 6.5.5, second corollary** — `cascadeTermination_diamondPast` ([ModalDistribution/Examples/HBBSafe/CascadeTermination.lean](ModalDistribution/Examples/HBBSafe/CascadeTermination.lean))
- **Lemma 6.6.1** — `uniquePropose_eventually_echo` ([ModalDistribution/Examples/HBBSafe/Uniqueness.lean](ModalDistribution/Examples/HBBSafe/Uniqueness.lean))
- **Lemma 6.6.2** — `atMostOnePropose_safe` ([ModalDistribution/Examples/HBBSafe/Uniqueness.lean](ModalDistribution/Examples/HBBSafe/Uniqueness.lean))
- **Proposition 6.6.3 (Happy Termination)** — `happyTermination` ([ModalDistribution/Examples/HBBSafe/HappyTermination.lean](ModalDistribution/Examples/HBBSafe/HappyTermination.lean))
- **Proposition 6.6.3, first corollary** — `happyTermination_boxPast` ([ModalDistribution/Examples/HBBSafe/HappyTermination.lean](ModalDistribution/Examples/HBBSafe/HappyTermination.lean))
- **Proposition 6.6.3, second corollary** — `happyTermination_diamondPast` ([ModalDistribution/Examples/HBBSafe/HappyTermination.lean](ModalDistribution/Examples/HBBSafe/HappyTermination.lean))

## Section 7: Theory HBBSimp

- **Figure 10, rule (Vote?)** — `voteBackwardAxiom` ([ModalDistribution/Examples/HBBSimp/Axioms.lean](ModalDistribution/Examples/HBBSimp/Axioms.lean))
- **Figure 10, rule (Vote!)** — `voteForwardAxiom` ([ModalDistribution/Examples/HBBSimp/Axioms.lean](ModalDistribution/Examples/HBBSimp/Axioms.lean))
- **Definition 7.1.1 (theory HBBSimp)** — `theory` ([ModalDistribution/Examples/HBBSimp/Axioms.lean](ModalDistribution/Examples/HBBSimp/Axioms.lean))
- **Theorem 7.1.3 / Figure 11** — `correctness` ([ModalDistribution/Examples/HBBSimp/Correctness.lean](ModalDistribution/Examples/HBBSimp/Correctness.lean))
- **Proposition 7.3.1 (Agreement)** — `agreement` ([ModalDistribution/Examples/HBBSimp/Agreement.lean](ModalDistribution/Examples/HBBSimp/Agreement.lean))
- **Proposition 7.3.1, hypothesis form** — `agreement_of_deliveries` ([ModalDistribution/Examples/HBBSimp/Agreement.lean](ModalDistribution/Examples/HBBSimp/Agreement.lean))
- **Proposition 7.3.2 (Cascade Termination)** — `cascadeTermination` ([ModalDistribution/Examples/HBBSimp/CascadeTermination.lean](ModalDistribution/Examples/HBBSimp/CascadeTermination.lean))
- **Proposition 7.3.2, first corollary** — `cascadeTermination_boxPast` ([ModalDistribution/Examples/HBBSimp/CascadeTermination.lean](ModalDistribution/Examples/HBBSimp/CascadeTermination.lean))
- **Proposition 7.3.2, second corollary** — `cascadeTermination_diamondPast` ([ModalDistribution/Examples/HBBSimp/CascadeTermination.lean](ModalDistribution/Examples/HBBSimp/CascadeTermination.lean))
- **Proposition 7.3.3 (Happy Termination)** — `happyTermination` ([ModalDistribution/Examples/HBBSimp/HappyTermination.lean](ModalDistribution/Examples/HBBSimp/HappyTermination.lean))
- **Proposition 7.3.3, first corollary** — `happyTermination_boxPast` ([ModalDistribution/Examples/HBBSimp/HappyTermination.lean](ModalDistribution/Examples/HBBSimp/HappyTermination.lean))
- **Proposition 7.3.3, second corollary** — `happyTermination_diamondPast` ([ModalDistribution/Examples/HBBSimp/HappyTermination.lean](ModalDistribution/Examples/HBBSimp/HappyTermination.lean))

## Section 8: Theory HBBCorr

- **Figure 12, rule (Vote?)** — `voteBackwardAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, rule (Deliver?)** — `deliverBackwardAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, axiom (VoteNE)** — `voteNonEquivAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, axiom (3twined)** — `threeTwinedAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, axiom (≐seq)** — `correlationSeqAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, axiom (≐⇓)** — `correlationMonotoneAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, axiom (≐symm)** — `correlationSymmAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, axiom (≐tran)** — `correlationTransAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, rule (Vote!)** — `voteForwardAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, rule (Vote'!)** — `voteForwardCorrelatedAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Figure 12, rule (Deliver!)** — `deliverForwardAxiom` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Definition 8.2.1 (theory HBBCorr)** — `theory` ([ModalDistribution/Examples/HBBCorr/Axioms.lean](ModalDistribution/Examples/HBBCorr/Axioms.lean))
- **Theorem 8.2.3 / Figure 13** — `correctness` ([ModalDistribution/Examples/HBBCorr/Correctness.lean](ModalDistribution/Examples/HBBCorr/Correctness.lean))
- **Proposition 8.3.1 (Agreement)** — `agreement` ([ModalDistribution/Examples/HBBCorr/Agreement.lean](ModalDistribution/Examples/HBBCorr/Agreement.lean))
- **Proposition 8.3.1, hypothesis form** — `agreement_of_deliveries` ([ModalDistribution/Examples/HBBCorr/Agreement.lean](ModalDistribution/Examples/HBBCorr/Agreement.lean))
- **Lemma 8.4.1** — `threeTwined_boxes_intersect` ([ModalDistribution/Examples/HBBCorr/Lemmas.lean](ModalDistribution/Examples/HBBCorr/Lemmas.lean))
- **Lemma 8.4.2(1)** — `vote_implies_echo_quorum_local` ([ModalDistribution/Examples/HBBCorr/Lemmas.lean](ModalDistribution/Examples/HBBCorr/Lemmas.lean))
- **Lemma 8.4.2(2)** — `vote_implies_echo_quorum_end` ([ModalDistribution/Examples/HBBCorr/Lemmas.lean](ModalDistribution/Examples/HBBCorr/Lemmas.lean))
- **Lemma 8.4.3(1)** — `echo_quorums_agree` ([ModalDistribution/Examples/HBBCorr/Lemmas.lean](ModalDistribution/Examples/HBBCorr/Lemmas.lean))
- **Lemma 8.4.3(2)** — `votes_eventually_agree` ([ModalDistribution/Examples/HBBCorr/Lemmas.lean](ModalDistribution/Examples/HBBCorr/Lemmas.lean))
- **Lemma 8.4.3(3)** — `correlated_vote_eventually` ([ModalDistribution/Examples/HBBCorr/Lemmas.lean](ModalDistribution/Examples/HBBCorr/Lemmas.lean))
- **Lemma 8.4.3(4)** — `live_echo_eventually_vote` ([ModalDistribution/Examples/HBBCorr/Lemmas.lean](ModalDistribution/Examples/HBBCorr/Lemmas.lean))
- **Lemma 8.4.4(1)** — `correlationImpliesPairwiseQuorumIntersection` ([ModalDistribution/Examples/HBBCorr/Lemmas.lean](ModalDistribution/Examples/HBBCorr/Lemmas.lean))
- **Lemma 8.4.4(2)** — `correlationImpliesQuorumIntersection` ([ModalDistribution/Examples/HBBCorr/Lemmas.lean](ModalDistribution/Examples/HBBCorr/Lemmas.lean))
- **Proposition 8.4.5 (Cascade Termination)** — `cascadeTermination` ([ModalDistribution/Examples/HBBCorr/CascadeTermination.lean](ModalDistribution/Examples/HBBCorr/CascadeTermination.lean))
- **Proposition 8.4.5, first corollary** — `cascadeTermination_boxPast` ([ModalDistribution/Examples/HBBCorr/CascadeTermination.lean](ModalDistribution/Examples/HBBCorr/CascadeTermination.lean))
- **Proposition 8.4.5, second corollary** — `cascadeTermination_diamondPast` ([ModalDistribution/Examples/HBBCorr/CascadeTermination.lean](ModalDistribution/Examples/HBBCorr/CascadeTermination.lean))
- **Proposition 8.5.1 (Happy Termination)** — `happyTermination` ([ModalDistribution/Examples/HBBCorr/HappyTermination.lean](ModalDistribution/Examples/HBBCorr/HappyTermination.lean))
- **Proposition 8.5.1, first corollary** — `happyTermination_boxPast` ([ModalDistribution/Examples/HBBCorr/HappyTermination.lean](ModalDistribution/Examples/HBBCorr/HappyTermination.lean))
- **Proposition 8.5.1, second corollary** — `happyTermination_diamondPast` ([ModalDistribution/Examples/HBBCorr/HappyTermination.lean](ModalDistribution/Examples/HBBCorr/HappyTermination.lean))
