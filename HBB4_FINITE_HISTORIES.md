# HBB4 with finite histories: obstruction and progress assumptions

The manuscript and the Lean formalization both use finite histories. The
manuscript's definitions and axioms control this formalization; the HBB4 PDFs
supply proposed results to check within that foundation. Their adoption of
countably infinite complete runs is a deviation from the manuscript's defined
model, not an authorized change to this project.

Lean proves that `LiveAlways` and the current unrestricted Knowledge scheme
exclude every live event. The matching manuscript assumptions have the same
mathematical obstruction. This is a finding to report, not permission to alter
those assumptions or substitute a different liveness statement.

The obstruction is kernel-checked. The HBB4 progress inventory below is an
analysis of the supplied proofs, not an alternative axiom system. The three
HBB4 extension theories and their requested proofs are not yet implemented.

## Foundation correspondence

In the supplied `hbb-disc.tex`, the prehistory definition (source lines
1515–1531) takes the least set closed under finite sets of event-tuples.
The remark at line 1609 explicitly states: “we plan to model finite runs of
distributed algorithms, so finite subsets suffice.” It discusses countable
subsets as a possible generalization, not the definition adopted in the paper.

Lean's `PreHistory` is an inductive, list-backed representation, and `Model`
contains one `History`. Both the complete history and each event's past are
finite. The set-versus-list representation differs; it does not affect the
height argument establishing this obstruction. The manuscript itself discusses
a redundant datatype presentation in Section 2.1.

The manuscript's Figure 6 (source lines 4825–4843) gives `LiveAlways` and
Knowledge for a closed predicate `φ`, without a protocol-specific restriction.
Its `Sometime` expansion at line 3339 is `EOT Past`, matching Lean. These are
the assumptions and modalities used by the formal obstruction.

This comparison establishes agreement on the foundation relevant to the
obstruction. It is not a claim that every part of the formalization has been
proved equivalent to the manuscript's set-theoretic presentation.

## Historical check: the initial commit already has the obstruction

The same no-live-event result has been kernel-checked against initial commit
`005103b4e9f6362c5810a2a628b0527655a8544d` (September 29, 2025).
The historical proof is preserved in
[FiniteHistoryAudit.lean](audits/005103b/FiniteHistoryAudit.lean).
It imports the initial commit's `ThyLive` directly and is intended to compile
against that revision, not the current modules.

Two differences in the initial semantics were checked explicitly. Its theory
validity requires axioms only at actual events, so the historical proof applies
Knowledge at the assumed live event, not at an end-of-time world. Its diamond
modality evaluates the body in a local model. The proof handles this by proving
the causal-depth bound for every model and using the identity
`M.localView M.history = M` when constructing the Knowledge antecedent.
The original closed-formula requirement is also proved for each depth formula.

Validation used an isolated checkout of that exact commit, its unchanged
`leanprover/lean4:v4.24.0-rc1` toolchain declaration, and all nine dependencies at
the revisions in its original lockfile. The original sources and dependency
checkouts have no tracked edits. Building `ModalDistribution.Examples.ThyLive`
succeeded, and the historical audit file compiled with its axiom guard allowing
only `propext`, `Classical.choice`, and `Quot.sound`.

The historical check can be reproduced by building that module in a checkout
of the pinned revision and running `lake env lean` there on the audit file's
absolute path. The proof's `#guard_msgs` rejects a dependency on `sorryAx` or a
custom axiom. No modern obstruction theorem is imported into this check.

Thus the obstruction was already present in the earliest repository commit;
it was not introduced by the later change to event-world semantics or the
August 2026 generalization of a derived knowledge lemma.

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
satisfiability of a restricted theory. The manuscript still requires the full
Knowledge scheme; an inventory of proof uses does not authorize narrowing it.

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

## Consequences for the HBB4 formalization

The source definitions remain controlling. In particular, retain finite
histories, the manuscript's `ThyLive`, and the stated liveness judgements.
Protocol-specific hypotheses from the PDFs must be identified explicitly as
extensions and checked against that fixed foundation.

The PDFs' use of countably infinite complete runs cannot serve as a model
witness in this formalization. Under the current assumptions, the checked
obstruction also prevents any finite witness containing a live event.
Consequently a theorem whose premise includes a live event may be formally
provable while admitting no instance with that premise true. Such a proof
must not be presented as evidence of actual protocol progress.

Restricting Knowledge, adopting an optional round cap, imposing finiteness of
the live set, or changing liveness to a statement about extensions would each
require a separate change to the specification. None is the current task.
The source-proof inventory above remains useful for understanding the arguments,
but does not resolve the manuscript-level obstruction.

The next work must distinguish results provable in the manuscript's foundation
from claims in the PDFs that depend on a different foundation, and report any
unachievable nonvacuity claim explicitly. A faithful formalization may expose a
problem in its source; it must not repair that source by changing its meaning.
