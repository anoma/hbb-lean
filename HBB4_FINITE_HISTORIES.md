# HBB4 with finite histories: obstruction and progress assumptions

The existing finite-history foundation can be retained while HBB4's progress
assumptions are reformulated. Lean now proves that `LiveAlways` and the current
unrestricted Knowledge scheme exclude every live event. This establishes an
obstruction in the assumptions, not a necessity to admit infinite histories.

The obstruction is kernel-checked. The HBB4 progress audit below is a mathematical
analysis of the supplied proofs; a finite HBB4 reformulation and its correctness
and nonvacuity proofs are not yet implemented.

## What Lean proves

[FiniteHistory.lean](ModalDistribution/Examples/ThyLive/FiniteHistory.lean)
contains three theorems:

| Theorem | Exact consequence |
| --- | --- |
| `no_live_event` | `LiveAlways`, together with empty-index Knowledge for causal-depth formulas at end of time, excludes every live event in the model's history. |
| `thyLive_no_live_event` | The existing `ThyLive` theory implies that consequence. |
| `thyLive_no_live_witness` | For every formula `φ`, `K(live ∧ φ)` is false at end of time under `ThyLive`. Taking `φ = K Propose(v)` covers the live-witness antecedent of Liveness 1. |

Here `K φ` means that a causal predecessor satisfies `φ`. The proof defines
`δ₀ = ⊤` and `δₙ₊₁ = K δₙ`. Satisfaction of `δₙ` implies that the existing
prehistory height is at least `n`. Starting from one live event, Knowledge and
`LiveAlways` produce live events satisfying `δₙ` for every natural number `n`.
Every event's history has height strictly below the complete finite history's
height, which gives the contradiction.

The proof uses the existing `Model`, `Formula`, satisfaction relation, and height
lemmas. Its assumptions do not include `LiveSeq`, quorum Knowledge, correlation,
or any protocol rule. The build audits all three theorems for dependence only on
Lean's standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.

The conclusion concerns actual live events. It does not say that no participant
can be designated live, or that all models of the theory are inconsistent.
Previously checked liveness implications remain checked implications; this
result shows that their live-witness antecedents cannot occur.

## Knowledge instances used by the HBB4 proofs

Sources: `hbb4_proofs_revised.pdf`, Sections 3.3 and 5.1, and
`hbb4_weaker_coherence.pdf`, Sections 4.3–4.5. The source documents supply
mathematical claims to assess, not implementation instructions.

Write `D_l = MaxDepth(l)`. Let `Q_l φ` mean a past `l`-quorum of events
satisfying `φ`. In
`C_l(v,n) = Q_l (∃s Vote(l,s,v,n))`, the source may vary by signer. In
`C_{l,s}(v,n) = Q_l Vote(l,s,v,n)`, the source is fixed for the whole quorum.
`Sometime` retains the current meaning: an event at that participant somewhere
in the complete history.

The proofs instantiate two Knowledge schemes:

```
EOT K(live ∧ φ)  → live → Sometime K φ
EOT Q_l(live ∧ φ) → live → Sometime Q_l φ
```

Their uses in the three headline properties are:

| Scheme | Formula `φ` | Purpose |
| --- | --- | --- |
| Empty-index Knowledge | `K Propose(v)` | Disseminate a proposal known at a live event in Liveness 1. Causal transitivity collapses `K K Propose(v)` to `K Propose(v)`. |
| Empty-index Knowledge | `C_a(v,D_a)` | Disseminate the certificate known by the live signer obtained in Liveness 2. Transitivity collapses `K C_a(v,D_a)` to `C_a(v,D_a)`. |
| Quorum Knowledge for `[l]` | `Echo(v)` | Let each live participant observe a quorum of the live participants' echoes. |
| Quorum Knowledge for `[l]` | `Vote(l,s,v,n)`, `0 ≤ n ≤ D_l + 1` | Build each next round's fixed-source certificate, and the final certificate for delivery. |

The general certificate-learning lemma in the revised note also covers arbitrary
ranks and fixed-source certificates. Its Liveness 2 application only needs the
existential-source certificate at the source learner's transfer threshold.
The final fixed-source delivery certificate implies the existential-source
certificate used by `Deliver!`; the reverse implication is not used.

These applications do not require closure of Knowledge under arbitrary formulas
or arbitrary modal nesting. The causal-depth formulas used in the obstruction
are therefore not required by these proof arguments. This is a sufficient
inventory of the displayed proof applications, not a proof of minimality or of
satisfiability of the proposed restriction.

## Other assumptions used by progress

Liveness 1 uses proposal provenance and uniqueness to establish legality, then
proposal dissemination, `Echo!`, echo-quorum Knowledge, `Vote0E!`, positive-round
progression, and `Deliver!`. No additional coherence condition is needed for
this argument.

Liveness 2 first uses the conflict-depth theorem to obtain end-of-time legality
for the destination learner. `Rseq` intersects the delivery certificate's quorum
with the destination's live quorum. `LiveAlways` makes the intersecting signer's
vote live. Its backward rule supplies the transfer certificate. Dissemination,
`Vote0V!`, fixed-source round progression, and `Deliver!` then give delivery.
CM, SW, and CW differ in how the conflict-depth result is obtained; their progress
steps are shared.

The positive-round rule needs the revised self-source condition
`l = s ∨ EOT(l R s)`. Partial equivalence permits an empty correlation row, so
self-correlation cannot replace equality. Liveness 1's conclusion needs
`Sometime Deliver(l,v)`: an event atom evaluated at the end-of-time null event
does not assert an earlier delivery.

## Restricting Knowledge alone is insufficient

An uncapped positive-round rule can independently force infinitely many votes.
Suppose a learner has a live quorum, all live participants cast its rank-zero
vote with a fixed source and value, and the rule's end-of-time guards hold.
Quorum Knowledge at each rank supplies the preceding-round certificate, and
`VoteN!` forces the next rank. Induction requires every rank. A finite history
cannot contain a vote of every natural-number rank.

For finite completed executions, the PDFs' cap through `MaxDepth(l) + 1` is a
candidate stopping rule. It is sufficient for the displayed round-progression
argument, but its consistency with all other axioms still needs a finite model.
With distinct natural-number vote ranks, this cap is a substantive protocol
choice, not merely a representation choice.

Finite completed executions also constrain how many participants can be required
to act. If one triggered obligation requires every live participant to deliver,
only finitely many participants can be live in such an execution: each delivery
event has one participant. The current participant type need not be finite.
A finite participant set is a simple sufficient assumption; a finite live set
is weaker. A reformulation must state the intended scope explicitly.

## Recommended next decision

For the finite-completion reading closest to the manuscript's current
`Sometime` semantics, formulate HBB4-specific progress assumptions using the
Knowledge instances above, with a delivery-round cap. Preserve the actual
`MaxDepth`, finite histories, source quantifier order, and CM/SW/CW conditions.
State an appropriate finiteness condition on the live participants. Before
claiming meaningful liveness, construct a finite model satisfying all assumptions
with actual deliveries and with the liveness premises true.

An alternative is to state progress over extensions of finite histories. This
would retain finite histories but introduce a scheduling/admissibility relation
and a different liveness statement. Existence of one successful extension is
only reachability. A liveness claim needs conditions excluding indefinite
postponement, together with a proof of delivery under those conditions.

Extension-based reasoning also needs to account for changing `MaxDepth` and
end-of-time legality: both depend on the completed history and cannot be assumed
stable when that history is extended. No such stability theorem is established
here. The finite-completion approach avoids that additional extension obligation
by evaluating them on the selected complete finite history.

Neither approach has yet been proved equivalent to the PDFs' complete-run
semantics. The evidence presently supports reformulating progress, not changing
the finite-history foundation.
