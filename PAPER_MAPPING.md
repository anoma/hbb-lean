# Paper to Formalization Mapping

This file maps the numbered items of the paper (as of the current draft) to
their Lean formalizations. The same information is embedded in the sources:
every anchored declaration's doc comment begins with `Paper: <item>.`, so
`grep -rn "Paper: Lemma 4.2.2" ModalDistribution` finds an item directly.

Items are listed in paper order; theory axioms are listed at the position of
the figure that defines them. Declarations inside a theory's namespace are
written without the `ThyHBB<n>.` prefix; e.g. Proposition 6.3.1 is
`ThyHBB1.agreement`.

## Not formalized

- Notation 2.2.1 (finite subsets): implicit — `PreHistory` is list-backed, so
  every prehistory is finite by construction.
- Notations 2.3.6, 3.1.2, 3.3.7, 6.1.3 and the Remarks: prose conventions
  and discussion, no formal content.
- Definitions 1.1.1 and 1.1.2: informal introductory definitions.
- The paper's illustrative Examples (2.2.5, 2.3.8-2.3.10, 3.3.5, 3.3.6, 5.1.1).

## Representation note

This branch amends Figure 6 and Definition 5.2.4: Knowledge bodies are exactly
`E`, `K E`, and `Q_l E` (`KnowledgeBody`), with arbitrary outer learner lists.
Shared lemmas involving Knowledge now require that admissibility premise;
HBB1–3 correctness statements and the finite-history foundation are unchanged.
`FiniteModel.exists_live_event_model` exhibits a finite model of the restricted
shared theory with a live performed event.

`FiniteHistory.no_live_event` in
[FiniteHistory.lean](ModalDistribution/Examples/ThyLive/FiniteHistory.lean)
diagnoses unrestricted Knowledge, explicitly assumed for every causal-depth
formula. It does not apply to the restricted theory. See
[HBB4_FINITE_HISTORIES.md](HBB4_FINITE_HISTORIES.md) for historical context.

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
- **Definition 3.1.3 / Figure 2 (syntax of predicates)** — `Formula` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 2 (event atoms)** — `EventAtom` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 2 (predicate atoms)** — `PredicateAtom` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
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
- **Definition 3.4.10(1) / Figure 3 (possible-world validity)** — `Sat` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Definition 3.4.10(2) (end-of-time validity ⊨)** — `EndValid` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Definition 3.4.10(3) (all-world validity □W⊨)** — `AllWorldValid` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Definition 3.5.1 (active participants)** — `IsActive` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Lemma 3.5.3** — `active_iff_past_top` ([ModalDistribution/Logic/Semantics.lean](ModalDistribution/Logic/Semantics.lean))
- **Figure 4 sugar (¬)** — `not` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (⊤)** — `top` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (∧)** — `and` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (∨)** — `or` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (⇔)** — `iff` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (∃)** — `exists_` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (∃01)** — `existsAtMostOne` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (∃1)** — `existsUnique` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (⇓)** — `allPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (↕)** — `sometime` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (⇕)** — `everytime` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (□ l₁…lₙ)** — `box` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (♢↓)** — `diamondPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (□↓)** — `boxPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (♢⇓)** — `diamondAllPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
- **Figure 4 sugar (□⇓)** — `boxAllPast` ([ModalDistribution/Logic/Syntax.lean](ModalDistribution/Logic/Syntax.lean))
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
- **Lemma 4.2.2 (the S4 axiom)** — `diamondPast_idem` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.2.3(1)** — `pastBoxCollapsesToPresentBox` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Lemma 4.2.3(2)** — `pastDiamondBoxCollapsesToPresentBox` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
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
- **Figure 6, axiom (LiveAlways)** — `liveAlwaysAxiom` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Figure 6, axiom (LiveSeq)** — `liveSeqAxiom` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Figure 6, axiom-scheme (Knowledge♢↓)** — `knowledgeDiamondAxiom` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Figure 6, axiom-scheme (Knowledge□↓)** — `knowledgeBoxAxiom` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Definition 5.2.4 (the theory of liveness)** — `ThyLive` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.7** — `sometime_past_end` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Proposition 5.2.8, restricted to `KnowledgeBody`** — `live_eventually_knows` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Corollary 5.2.9(1)** — `live_eventually_knows_event` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Corollary 5.2.9(2)** — `live_eventually_knows_performed` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Corollary 5.2.9(3)** — `live_eventually_knows_quorum` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.10(1)** — `alwaysLiveEquivForward` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.10(2)** — `alwaysLiveEquivBackward` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.10(3)** — `live_allPast` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Proposition 5.2.11** — `intertwined_two_quorums` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))
- **Lemma 5.2.12, restricted to `KnowledgeBody`** — `live_boxPast_nests` ([ModalDistribution/Examples/ThyLive.lean](ModalDistribution/Examples/ThyLive.lean))

## Section 6: Theory ThyHBB1

- **Figures 7/9/11, rule (Echo?)** — `echoBackwardAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figures 7/9/11, axiom (EchoNE)** — `echoNonEquivAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figures 7/9/11, rule (Echo!)** — `echoForwardAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figures 7/9, rule (Deliver?)** — `deliverBackwardAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figures 7/9, rule (Deliver!)** — `deliverForwardAxiom` ([ModalDistribution/Examples/HBB.lean](ModalDistribution/Examples/HBB.lean))
- **Figure 7, right-hand side of axiom (Safe)** — `safeFormula` ([ModalDistribution/Examples/ThyHBB1/Axioms.lean](ModalDistribution/Examples/ThyHBB1/Axioms.lean))
- **Figure 7, axiom (Safe)** — `safeAxiom` ([ModalDistribution/Examples/ThyHBB1/Axioms.lean](ModalDistribution/Examples/ThyHBB1/Axioms.lean))
- **Figure 7, rule (Vote?)** — `voteBackwardAxiom` ([ModalDistribution/Examples/ThyHBB1/Axioms.lean](ModalDistribution/Examples/ThyHBB1/Axioms.lean))
- **Figure 7, rule (Vote!)** — `voteForwardAxiom` ([ModalDistribution/Examples/ThyHBB1/Axioms.lean](ModalDistribution/Examples/ThyHBB1/Axioms.lean))
- **Definition 6.1.2 (theory ThyHBB1)** — `theory` ([ModalDistribution/Examples/ThyHBB1/Axioms.lean](ModalDistribution/Examples/ThyHBB1/Axioms.lean))
- **Theorem 6.1.6 / Figure 8** — `correctness` ([ModalDistribution/Examples/ThyHBB1/Correctness.lean](ModalDistribution/Examples/ThyHBB1/Correctness.lean))
- **Proposition 6.3.1 (Agreement)** — `agreement` ([ModalDistribution/Examples/ThyHBB1/Agreement.lean](ModalDistribution/Examples/ThyHBB1/Agreement.lean))
- **Proposition 6.3.1, hypothesis form** — `agreement_of_deliveries` ([ModalDistribution/Examples/ThyHBB1/Agreement.lean](ModalDistribution/Examples/ThyHBB1/Agreement.lean))
- **Lemma 6.4.1(1)** — `safe_monotone` ([ModalDistribution/Examples/ThyHBB1/Safety.lean](ModalDistribution/Examples/ThyHBB1/Safety.lean))
- **Lemma 6.4.1(2)** — `safe_allPast` ([ModalDistribution/Examples/ThyHBB1/Safety.lean](ModalDistribution/Examples/ThyHBB1/Safety.lean))
- **Lemma 6.4.2(1)** — `boxPast_of_eventual_quorum` ([ModalDistribution/Examples/ThyHBB1/Safety.lean](ModalDistribution/Examples/ThyHBB1/Safety.lean))
- **Lemma 6.4.2(2)** — `boxPast_live_of_eventual_quorum` ([ModalDistribution/Examples/ThyHBB1/Safety.lean](ModalDistribution/Examples/ThyHBB1/Safety.lean))
- **Lemma 6.4.3** — `live_eventually_consequent` ([ModalDistribution/Examples/ThyHBB1/Safety.lean](ModalDistribution/Examples/ThyHBB1/Safety.lean))
- **Lemma 6.4.4** — `box_sometime_iff_boxPast` ([ModalDistribution/Logic/Properties/Modalities.lean](ModalDistribution/Logic/Properties/Modalities.lean))
- **Proposition 6.4.5 (Liveness 2)** — `livenessTwo` ([ModalDistribution/Examples/ThyHBB1/Liveness_Two.lean](ModalDistribution/Examples/ThyHBB1/Liveness_Two.lean))
- **Proposition 6.4.5, first corollary** — `livenessTwo_boxPast` ([ModalDistribution/Examples/ThyHBB1/Liveness_Two.lean](ModalDistribution/Examples/ThyHBB1/Liveness_Two.lean))
- **Proposition 6.4.5, second corollary** — `livenessTwo_diamondPast` ([ModalDistribution/Examples/ThyHBB1/Liveness_Two.lean](ModalDistribution/Examples/ThyHBB1/Liveness_Two.lean))
- **Lemma 6.5.1** — `uniquePropose_eventually_echo` ([ModalDistribution/Examples/ThyHBB1/Uniqueness.lean](ModalDistribution/Examples/ThyHBB1/Uniqueness.lean))
- **Lemma 6.5.2** — `atMostOnePropose_safe` ([ModalDistribution/Examples/ThyHBB1/Uniqueness.lean](ModalDistribution/Examples/ThyHBB1/Uniqueness.lean))
- **Proposition 6.5.3 (Liveness 1)** — `livenessOne` ([ModalDistribution/Examples/ThyHBB1/Liveness_One.lean](ModalDistribution/Examples/ThyHBB1/Liveness_One.lean))
- **Proposition 6.5.3, first corollary** — `livenessOne_boxPast` ([ModalDistribution/Examples/ThyHBB1/Liveness_One.lean](ModalDistribution/Examples/ThyHBB1/Liveness_One.lean))
- **Proposition 6.5.3, second corollary** — `livenessOne_diamondPast` ([ModalDistribution/Examples/ThyHBB1/Liveness_One.lean](ModalDistribution/Examples/ThyHBB1/Liveness_One.lean))

## Section 7: Theory ThyHBB2

- **Figure 9, rule (Vote?)** — `voteBackwardAxiom` ([ModalDistribution/Examples/ThyHBB2/Axioms.lean](ModalDistribution/Examples/ThyHBB2/Axioms.lean))
- **Figure 9, rule (Vote!)** — `voteForwardAxiom` ([ModalDistribution/Examples/ThyHBB2/Axioms.lean](ModalDistribution/Examples/ThyHBB2/Axioms.lean))
- **Definition 7.1.1 (theory ThyHBB2)** — `theory` ([ModalDistribution/Examples/ThyHBB2/Axioms.lean](ModalDistribution/Examples/ThyHBB2/Axioms.lean))
- **Theorem 7.1.3 / Figure 10** — `correctness` ([ModalDistribution/Examples/ThyHBB2/Correctness.lean](ModalDistribution/Examples/ThyHBB2/Correctness.lean))
- **Proposition 7.2.1 (Agreement)** — `agreement` ([ModalDistribution/Examples/ThyHBB2/Agreement.lean](ModalDistribution/Examples/ThyHBB2/Agreement.lean))
- **Proposition 7.2.1, hypothesis form** — `agreement_of_deliveries` ([ModalDistribution/Examples/ThyHBB2/Agreement.lean](ModalDistribution/Examples/ThyHBB2/Agreement.lean))
- **Proposition 7.2.2 (Liveness 2)** — `livenessTwo` ([ModalDistribution/Examples/ThyHBB2/Liveness_Two.lean](ModalDistribution/Examples/ThyHBB2/Liveness_Two.lean))
- **Proposition 7.2.2, first corollary** — `livenessTwo_boxPast` ([ModalDistribution/Examples/ThyHBB2/Liveness_Two.lean](ModalDistribution/Examples/ThyHBB2/Liveness_Two.lean))
- **Proposition 7.2.2, second corollary** — `livenessTwo_diamondPast` ([ModalDistribution/Examples/ThyHBB2/Liveness_Two.lean](ModalDistribution/Examples/ThyHBB2/Liveness_Two.lean))
- **Proposition 7.2.3 (Liveness 1)** — `livenessOne` ([ModalDistribution/Examples/ThyHBB2/Liveness_One.lean](ModalDistribution/Examples/ThyHBB2/Liveness_One.lean))
- **Proposition 7.2.3, first corollary** — `livenessOne_boxPast` ([ModalDistribution/Examples/ThyHBB2/Liveness_One.lean](ModalDistribution/Examples/ThyHBB2/Liveness_One.lean))
- **Proposition 7.2.3, second corollary** — `livenessOne_diamondPast` ([ModalDistribution/Examples/ThyHBB2/Liveness_One.lean](ModalDistribution/Examples/ThyHBB2/Liveness_One.lean))

## Section 8: Theory ThyHBB3

- **Figure 11, rule (Vote?)** — `voteBackwardAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, rule (Deliver?)** — `deliverBackwardAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, axiom (VoteNE)** — `voteNonEquivAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, axiom (3twined)** — `threeTwinedAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, axiom (≐seq)** — `correlationSeqAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, axiom (≐⇓)** — `correlationMonotoneAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, axiom (≐symm)** — `correlationSymmAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, axiom (≐tran)** — `correlationTransAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, rule (Vote!)** — `voteForwardAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, rule (Vote'!)** — `voteForwardCorrelatedAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Figure 11, rule (Deliver!)** — `deliverForwardAxiom` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Definition 8.2.1 (theory ThyHBB3)** — `theory` ([ModalDistribution/Examples/ThyHBB3/Axioms.lean](ModalDistribution/Examples/ThyHBB3/Axioms.lean))
- **Theorem 8.2.3 / Figure 12** — `correctness` ([ModalDistribution/Examples/ThyHBB3/Correctness.lean](ModalDistribution/Examples/ThyHBB3/Correctness.lean))
- **Proposition 8.3.1 (Agreement)** — `agreement` ([ModalDistribution/Examples/ThyHBB3/Agreement.lean](ModalDistribution/Examples/ThyHBB3/Agreement.lean))
- **Proposition 8.3.1, hypothesis form** — `agreement_of_deliveries` ([ModalDistribution/Examples/ThyHBB3/Agreement.lean](ModalDistribution/Examples/ThyHBB3/Agreement.lean))
- **Lemma 8.4.1** — `threeTwined_boxes_intersect` ([ModalDistribution/Examples/ThyHBB3/Lemmas.lean](ModalDistribution/Examples/ThyHBB3/Lemmas.lean))
- **Lemma 8.4.2(1)** — `vote_implies_echo_quorum_local` ([ModalDistribution/Examples/ThyHBB3/Lemmas.lean](ModalDistribution/Examples/ThyHBB3/Lemmas.lean))
- **Lemma 8.4.2(2)** — `vote_implies_echo_quorum_end` ([ModalDistribution/Examples/ThyHBB3/Lemmas.lean](ModalDistribution/Examples/ThyHBB3/Lemmas.lean))
- **Lemma 8.4.3(1)** — `echo_quorums_agree` ([ModalDistribution/Examples/ThyHBB3/Lemmas.lean](ModalDistribution/Examples/ThyHBB3/Lemmas.lean))
- **Lemma 8.4.3(2)** — `votes_eventually_agree` ([ModalDistribution/Examples/ThyHBB3/Lemmas.lean](ModalDistribution/Examples/ThyHBB3/Lemmas.lean))
- **Lemma 8.4.3(3)** — `correlated_vote_eventually` ([ModalDistribution/Examples/ThyHBB3/Lemmas.lean](ModalDistribution/Examples/ThyHBB3/Lemmas.lean))
- **Lemma 8.4.3(4)** — `live_echo_eventually_vote` ([ModalDistribution/Examples/ThyHBB3/Lemmas.lean](ModalDistribution/Examples/ThyHBB3/Lemmas.lean))
- **Lemma 8.4.4(1)** — `correlationImpliesPairwiseQuorumIntersection` ([ModalDistribution/Examples/ThyHBB3/Lemmas.lean](ModalDistribution/Examples/ThyHBB3/Lemmas.lean))
- **Lemma 8.4.4(2)** — `correlationImpliesQuorumIntersection` ([ModalDistribution/Examples/ThyHBB3/Lemmas.lean](ModalDistribution/Examples/ThyHBB3/Lemmas.lean))
- **Proposition 8.4.5 (Liveness 2)** — `livenessTwo` ([ModalDistribution/Examples/ThyHBB3/Liveness_Two.lean](ModalDistribution/Examples/ThyHBB3/Liveness_Two.lean))
- **Proposition 8.4.5, first corollary** — `livenessTwo_boxPast` ([ModalDistribution/Examples/ThyHBB3/Liveness_Two.lean](ModalDistribution/Examples/ThyHBB3/Liveness_Two.lean))
- **Proposition 8.4.5, second corollary** — `livenessTwo_diamondPast` ([ModalDistribution/Examples/ThyHBB3/Liveness_Two.lean](ModalDistribution/Examples/ThyHBB3/Liveness_Two.lean))
- **Proposition 8.5.1 (Liveness 1)** — `livenessOne` ([ModalDistribution/Examples/ThyHBB3/Liveness_One.lean](ModalDistribution/Examples/ThyHBB3/Liveness_One.lean))
- **Proposition 8.5.1, first corollary** — `livenessOne_boxPast` ([ModalDistribution/Examples/ThyHBB3/Liveness_One.lean](ModalDistribution/Examples/ThyHBB3/Liveness_One.lean))
- **Proposition 8.5.1, second corollary** — `livenessOne_diamondPast` ([ModalDistribution/Examples/ThyHBB3/Liveness_One.lean](ModalDistribution/Examples/ThyHBB3/Liveness_One.lean))


## HBB4: corrected capped CM version

These results implement the CM repair in `hbb4_proofs_revised.pdf`, Sections 3–5,
with the finite foundation and the restricted shared Knowledge scheme.
Natural ranks index the vote-symbol family, and legality quantifies over those
ranks semantically. `ProtocolCM` contains the explicit axiom schemata, not assumed
correctness properties. Correctness permits arbitrary symbol families; the
finite witness uses distinct vote symbols for distinct ranks.

| Source claim | Declaration | File |
| --- | --- | --- |
| Manuscript MaxDepth, exact maximum | `maxDepth`, `maxDepth_attained`, `le_maxDepth` | [Depth.lean](ModalDistribution/Examples/ThyHBB4/Depth.lean) |
| Finite-history bound | `maxDepth_bounded` | [Depth.lean](ModalDistribution/Examples/ThyHBB4/Depth.lean) |
| Revised note §3.3, equations (1)–(16), CM, cap | `Legal`, `ProtocolCM` | [Axioms.lean](ModalDistribution/Examples/ThyHBB4/Axioms.lean) |
| Lemma 4.1, conflict-depth lower bound | `conflict_depth` | [Safety.lean](ModalDistribution/Examples/ThyHBB4/Safety.lean) |
| Corollary 4.2, dominance and legality | `conflicting_rank_lt`, `high_vote_legal` | [Safety.lean](ModalDistribution/Examples/ThyHBB4/Safety.lean) |
| Lemma 5.1, provenance | `vote_provenance`, `deliver_provenance` | [Safety.lean](ModalDistribution/Examples/ThyHBB4/Safety.lean) |
| Theorem 5.2, agreement | `agreement` | [Safety.lean](ModalDistribution/Examples/ThyHBB4/Safety.lean) |
| Lemma 5.4, capped round progression | `capped_round_progress` | [Liveness.lean](ModalDistribution/Examples/ThyHBB4/Liveness.lean) |
| Theorem 5.5, Liveness 1 | `livenessOne` | [Liveness.lean](ModalDistribution/Examples/ThyHBB4/Liveness.lean) |
| Theorem 5.6, Liveness 2 | `livenessTwo` | [LivenessTwo.lean](ModalDistribution/Examples/ThyHBB4/LivenessTwo.lean) |
| Finite nonvacuity of the corrected protocol | `FiniteModel.finite_protocol_nonvacuous` | [FiniteModel.lean](ModalDistribution/Examples/ThyHBB4/FiniteModel.lean) |

The conflict-depth theorem constructs a chain with pairwise-distinct rows, enough
for the exact MaxDepth bound. Its proof uses CM's strict row expansion at each
inductive step. The certificate-learning step used by Liveness 2 fixes a source
before applying Knowledge and then forgets that source existentially. It does
not assume Knowledge for arbitrary existential-source certificate bodies.


## HBB4: positive-round switch and comparison-witness coherence

`BaseProtocol` contains the shared capped rules and participant-local correlation
persistence. `ProtocolCM`, `ProtocolSW`, and `ProtocolCW` extend that base with CM,
SW, and CW respectively. In particular, SW and CW do not assume CM. These two
versions follow `hbb4_weaker_coherence.pdf`, Sections 1–4.

| Source claim | Declaration | File |
| --- | --- | --- |
| Definition 2.1, SW | `SwitchCoherence`, `ProtocolSW` | [Axioms.lean](ModalDistribution/Examples/ThyHBB4/Axioms.lean) |
| Definition 2.2, CW | `ComparisonWitness`, `ProtocolCW` | [Axioms.lean](ModalDistribution/Examples/ThyHBB4/Axioms.lean) |
| Proposition 2.3, CM ⇒ SW ⇒ CW | `ProtocolCM.toSW`, `ProtocolSW.toCW` | [Coherence.lean](ModalDistribution/Examples/ThyHBB4/Coherence.lean) |
| Strict nonempty row-chain invariant | `StrictEndingDepthChain` | [StrictDepth.lean](ModalDistribution/Examples/ThyHBB4/StrictDepth.lean) |
| Lemma 3.1, CW conflict-depth | `CW.conflict_depth` | [WeakSafety.lean](ModalDistribution/Examples/ThyHBB4/WeakSafety.lean) |
| Corollary 3.2, legality at delivery rank | `CW.high_vote_legal`, `CW.delivery_legal` | [WeakSafety.lean](ModalDistribution/Examples/ThyHBB4/WeakSafety.lean) |
| Theorem 4.1, CW agreement | `CW.agreement` | [WeakSafety.lean](ModalDistribution/Examples/ThyHBB4/WeakSafety.lean) |
| Theorem 4.1, SW agreement | `SW.agreement` | [Variants.lean](ModalDistribution/Examples/ThyHBB4/Variants.lean) |
| Sections 4.4–4.5, SW/CW liveness | `SW.livenessOne`, `SW.livenessTwo`, `CW.livenessOne`, `CW.livenessTwo` | [Variants.lean](ModalDistribution/Examples/ThyHBB4/Variants.lean) |
| Common finite nonvacuity | `FiniteModel.finite_protocol_nonvacuous` | [FiniteModel.lean](ModalDistribution/Examples/ThyHBB4/FiniteModel.lean) |

CW's induction retains strict row inclusion, yielding a chain of `r` worlds from
conflicting votes of ranks at least `r ≥ 1`. Legality requires a vote at rank
`MaxDepth(a)+1`, exactly the existing delivery-certificate rank. SW uses the
proved implication to CW. Provenance, proposal initialization, bounded round
progression, and certificate transfer are shared over `BaseProtocol`.

The strictness witnesses from Section 5 and the optional finite-learner counting
bound from Section 6 are not formalized. They are not premises of correctness:
exact MaxDepth is already finite by the history-height bound.
