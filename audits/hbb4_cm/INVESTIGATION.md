# Finite HBB4 with causal monotonicity

The corrected, capped CM formulation is now formalized in
`ModalDistribution/Examples/ThyHBB4`. Lean checks provenance, conflict-depth,
agreement, both liveness theorems, and an eight-event full-protocol model
satisfying both liveness premises. The 52-event executable check below is a
separate witness with distinct learners and no three-quorum intersection.

The formalization now also contains separately stated SW and CW theories,
CM ⇒ SW ⇒ CW proofs, and agreement and both liveness results for each. The
kernel-checked finite witness satisfies all three. The investigation below
specifically explains the CM candidate and its finite execution.

## Formulation examined

The basis is `hbb4_proofs_revised.pdf`, Sections 3–5, adapted to the existing
finite-history semantics:

- Knowledge bodies are exactly `E`, `K E`, and `Q_l E`.
- Correlation is a partial equivalence relation and propagates to every causal
  predecessor (CM). Correlated quorums intersect at a sequential participant.
- Votes for target `l` have ranks `0 .. MaxDepth(l)+1`. Positive-round forward
  obligations apply only for `1 <= n <= MaxDepth(l)+1`.
- Positive-round advancement permits equality of target and source as well as
  their end-of-time correlation.
- Liveness 1 concludes `Sometime Deliver(l,v)`.
- The remaining backward rules, legality, echo non-equivocation, forward rules,
  and source-correlation condition are those displayed in Section 3.3.

The cap is on the target's rank. A transfer still requires the source's
rank-`MaxDepth(source)` certificate. The source threshold is within the source's
own permitted range.

## Why uncapped progress is still an obstruction

Suppose a live `l`-quorum exists, all live participants have the end-of-time
legality and source guards, and all have cast a fixed-source rank-zero vote.
If they have all cast rank `n`, their live quorum supplies
`EOT Q_l(live AND Vote(l,s,v,n))`. Restricted Knowledge applies to this event
atom and gives each live participant an actual event observing that quorum.
Uncapped `VoteN!` then requires a rank-`n+1` vote at each live participant.
Induction requires a vote at every natural-number rank. The quorum is nonempty,
and distinct ranks label distinct events, contradicting finiteness.

The corrected Liveness 1 argument supplies the rank-zero votes and guards.
Thus uncapped rules exclude its intended premises even with restricted Knowledge.
This is a mathematical argument, not yet a kernel-checked HBB4 theorem. Raising
the candidate model's cap from 2 to 3 also makes the checker report the concrete
unmet `VoteN!` obligation; that test alone is not the universal argument.

## Finite witness and executable checks

Run `python3 audits/hbb4_cm/check_finite_model.py`.

There are three live participants and two distinct learners. Each learner's
quorums are all participant subsets of size at least two. Correlation is total
and constant, so every row is constant and `MaxDepth` is exactly 1. All event
histories are prefixes of a total causal order. The execution contains:

1. One proposal and three echoes for value `0`.
2. Eighteen self-sourced votes: both learners, all participants, ranks 0–2.
3. Eighteen cross-sourced votes, justified by the self-sourced certificates.
4. Six deliveries, one per participant and learner.
5. Two sweeps of silent events through the three participants.

That is 52 events and 159 participant/prefix worlds, including the final history.
The checker evaluates the backward rules at every actual event and forward
rules at every participant/prefix world. Event atoms at other worlds are false
because actual membership is required. Values include `0`, `1`, and both learner
names; all actual votes have value `0`. Every other value is still considered by
legality and the forward checks.

All participants are sequential, and every pair of quorums intersects. The three
quorums `{0,1}`, `{0,2}`, `{1,2}` have empty common intersection: the witness does
not rely on three-quorum intersection. Constant total correlation satisfies CM,
symmetry, transitivity, same-participant persistence, and the vote-source rule.

Knowledge is checked for every performed atom and one representative of all
unperformed atoms, with its `K E` and `Q_l E` bodies. Unperformed atoms, including
higher-rank votes, are uniformly false. The 68 body cases cover these semantic
possibilities. Every finite outer learner list is covered by closure of quorum
intersection families: the families reach a fixed point after four distinct
states, and both learners have the same quorum interpretation. Diamond means
every intersection meets the satisfying set; box means some intersection is
contained in that set, exactly as in `Sat.check` and its dual.

The first silent sweep observes all performed atoms. The second observes the
first sweep's witnesses for `K E` and `Q_l E`. Further observations do not
introduce new performed atoms, so there is no recursive Knowledge demand.
A check of the protocol-event prefix alone fails Knowledge, as expected.

Both liveness antecedents hold, including transfer between distinct learners:
there is a unique proposed value known at a live event, live quorums exist, the
learners are correlated everywhere, and learner `a` has delivered. Every live
participant delivers for both learners.

This is a direct finite semantic calculation, not a Lean theorem and not a proof
that every partial execution extends to a completed model. It establishes a
concrete nonvacuity candidate without an infinite tail or a scheduling axiom.

## Review of the general proof

The CM conflict-depth lemma (PDF Lemma 4.1) uses finite causal minima, nonempty
quorums, sequential intersections, legality, and backward rules. Each minimal
rank-at-least-`r` vote has rank exactly `r`, since a larger rank supplies an earlier
vote of the same target and value. The cap does not interfere: the predecessor
of an admitted positive-rank vote is within the same target's range.

At rank zero, two direct echo certificates would contradict echo
non-equivocation. A transfer source outside the observer's correlation row
therefore supplies a strictly larger earlier row. At positive rank, intersecting
predecessor quorums supplies comparable conflicting votes. Legality at the later
vote supplies a higher-rank witness; causal minimality forces its target outside
the observer's row. CM makes this a strict row expansion backwards. Induction
then gives `r+2` distinct rows. No new gap was found in these steps.

For agreement, choose the delivered learner with smaller `MaxDepth` as anchor.
There is no need to equate the depths of correlated learners. For Liveness 2,
the source delivery's high-rank vote establishes legality throughout the target's
end-of-time row by the conflict-depth bound.

The PDF's unrestricted certificate-learning lemma needs a narrower formulation.
The live signer selected from a delivery certificate cast a vote with a specific
source `s`. Its backward rule provides `Q_a Vote(a,s,v,MaxDepth(a))`, which is an
allowed `Q_a E` Knowledge body. Disseminate that fixed-source certificate, then
infer `Q_a (exists s, Vote(a,s,v,MaxDepth(a)))` for the transfer rule. No Knowledge
instance with an existential body is needed. Finite round induction then reaches
the delivery rank using only atomic-vote Knowledge.

`MaxDepth` can retain the manuscript's definition. In the existing finite
foundation, a causal chain's history heights strictly increase and are bounded
by the complete history's height. Its length is at most that height plus one.
The nonempty set of attainable row-chain lengths therefore has a finite maximum,
even without assuming finitely many learners. A sharper learner-count bound is
unnecessary for these correctness proofs.

## Formalization outcome

`Depth.lean` defines the attained exact maximum and proves its finite bound.
`Axioms.lean` states every corrected capped CM rule as a semantic schema over
existing satisfaction. `Safety.lean` proves the causal conflict-depth argument,
provenance, dominance, legality, and agreement. `Liveness.lean` and
`LivenessTwo.lean` prove the two liveness implications with restricted Knowledge.

`FiniteModel.finite_protocol_nonvacuous` kernel-checks a separate singleton
execution: proposal, echo, votes at ranks 0/1/2, delivery, and two silent events.
Its exact depth is one. It proves the full protocol assumptions and actual
liveness premises. The larger 52-event witness remains an executable semantic
audit; the singleton Lean witness does not establish failure of three-quorum
intersection. The general correctness theorems do not assume that property.

No further foundation change or expansion of Knowledge was needed.
