# Depth lower bound — statement and plan

Two results live here.

* **The HBB4 special case is proved** (`HBB4.lean`, `hbb4_depth_lower_bound`,
  no `sorry`, standard axioms only — see `AxiomAudit.lean`). For every `D`
  there are a topology, an *exposure-based* correlation relation
  (a function of the pair of learners and of the set of participants exposed as
  non-sequential in the observed prehistory), a learner `L` and a proper
  `L`-quorum `Q` such that
  - (`Depth.lean`, `delivery_depth_of_usesOnly`) in every `BaseProtocol` model —
    on *any* topology and correlation — every `L`-delivery whose causal history
    lies inside `Q` has `worldDepth ≥ maxDepth(L) + 4`, hence `≥ D + 4` when
    `maxDepth(L) ≥ D`: a rank-`r` vote is at least `r+3` deep (`vote_depth`),
    the certificate clause of `Deliver?` sits above a rank-`maxDepth(L)` vote,
    and the fast path is closed because a participant outside `Q` is vacuously
    sequential in the delivering world's past without having echoed there
    (`no_fast_path_of_usesOnly`);
  - (`Witness.lean`, `hbb4_witness`) a causally monotone HBB4 model on that
    topology and correlation realizes `maxDepth(L) = D`, has `L ⋈ L` at every
    possible world, and `Q` `L`-delivers at `worldDepth = D + 4` exactly, so the
    bound is tight. (The `ThyAgreement` version, `LowerBoundAgreement/`, reads
    the vocabulary with the static budget `depthBound L = D`.)

  The witness: participants are `ℕ`; `a₀ = 0` is the only live participant and
  `Q = {0}`; `e₁, …, e_D` each have two causally incomparable `propose` events
  (values `0`, `1`, empty pasts). `a₀` runs `propose, echo, vote 0 … vote D,
  deliver` seeing only its own past (depth `D+4`, `Q`-only), then has `D+2`
  silent worlds, the `i`-th of which (for `i ≤ D`) first sees both proposals of
  `eᵢ`. Learner `l`'s quorums are the sets containing `0` and `l`; learners
  `a, b ≤ D` are correlated iff both are sequential in the observed prehistory
  (and every learner is self-correlated). The row of `L = 0` loses learner `i`
  at the `i`-th exposure, giving a chain with `D` row changes; no chain has more
  because rows are a function of the exposure level, which is monotone along
  `≪` and bounded by `D` (`depthChain_le`). The silent worlds after the
  delivery also make `L` correlated only with itself at the end of time, which
  is what keeps `Vote0!`-by-transfer from obliging `a₀` to vote for other
  learners.

* **The general statement is proved too** (`Theorem.lean`, `depth_lower_bound`,
  no `sorry`, standard axioms only): for every correct protocol — a set of
  executions closed under locality (`local_closure`), free proposals
  (`propose_free`) and fair completion (`fair_completion`), with agreement on
  `EnvOK` executions and Liveness 1 and 2 on fair `EnvOK` ones — and every
  `D ≥ 2`, there are a topology and a causally monotone correlation relation on
  which every honest `Q`-only `L`-delivery (`HonestCone`: no member of `Q` has two
  incomparable events in the delivery's causal cone) has depth `≥ D`. The
  honesty hypothesis is necessary (see the docstring of `depth_lower_bound`).
  The protocol's environment assumptions `env` are abstract; the theorem needs
  them to follow from `EnvOK ∧ Coherent ∧ DepthLE D` and to imply `EnvOK`
  (`henv`, `henv'`).
  The construction (`Topology.lean`): hub `c`, fuses `q₁ … q_D` with
  `Q = {q₁, …, q_D}`, `Qᵢ = {qᵢ, c}`, `L ⋈ Lᵢ` iff `qᵢ` is sequential,
  `Lᵢ ⋈ Lⱼ` iff both fuses are; `EnvOK` reduces to "`c` and some fuse are
  sequential". The argument (`Proof.lean`): stage `1` fairly completes a lone
  proposal of `v₁ ≠ v` with `{q₁, c}` live, so `c` `L₁`-delivers `v₁`
  (Liveness 1); stage `j+1` fairly completes `E_j ∪ Y_{j+1}` with `{q_{j+1}, c}`
  live, where the schedule `Y` (`Schedule.lean`) adds the cone of `d` while never
  exposing the fuse that just became live, so Liveness 2 transfers `c`'s delivery
  to `L_{j+1}`; after `n+1 ≤ D` stages (`n` the depth of `d`) the whole cone has
  been added (an event outside `Y_{t+1}` sits above a chain of `t` fuse events)
  and `E_{n+1} ∪ d`'s cone is an `EnvOK` execution in which `L` delivers `v`,
  `L_{n+1}` delivers `v₁`, and `L ⋈ L_{n+1}` — contradicting agreement.

* **HBB4 instantiates the protocol notion** (`HBB4Protocol.lean`), up to one
  assumption. `hbb4Protocol σ hdist hcomp : Protocol S P σ.toBase` takes the
  budgeted theory `ThyHBB4B` (decision rank = static `depthBound`; `ThyHBB4`'s
  omniscient `maxDepth` is not local) with `executions` = histories satisfying
  the local slow-path rules (`LocalRules`: backward rules with certificate
  delivery, non-equivocation — the fast path's end-of-time guarantee is not
  local), `env` = `correlationSeq` ∧ coherence of `⋈` ∧ budget dominance, and
  `fair` = `ThyLive` ∧ forward rules. `local_closure`, `propose_free`,
  `fair_sequential` and `fair_observes` are proved; `Protocol.Correct` follows
  from `ThyHBB4B.CM.agreement/livenessOne/livenessTwo` (agreement via
  `stripLive`, which erases the live designation so that `ThyLive` and the forward
  rules hold vacuously). The one assumption is `Completion σ` — fair completion of
  any `env` execution with a prescribed live set, adding no proposals — a
  nonvacuity theorem about HBB4 still to be proved. Under it,
  `hbb4_protocol_depth_bound`: budget-`B` HBB4 (`B ≥ 2`) cannot deliver on an
  honest `Q`-only branch below depth `B`, by `depth_lower_bound` alone.

## The statement, in words

For every protocol `Proto` over the HBB4 vocabulary `σ` that is *correct*
(agreement on all executions; Liveness 1 and 2 on fair executions), and every
`D ≥ 2`, there exist a topology `T` (quorum system per learner), a causally
monotone interpretation `ρ` (fixing `⋈` and `live` as functions of a
participant's local prehistory), a learner `L` and an `L`-quorum `Q`, such that in
every execution of `Proto` on `(T, ρ)`, every `L`-delivery whose event and
entire causal past are placed in `Q` has `worldDepth ≥ D`.

`worldDepth w = PreHistory.height w.time`: an event with empty past has depth 1;
otherwise depth is 1 + the maximum depth of the worlds in its past.

## Does this notion of protocol fit ThyHBB1–4?

Only after separating the three kinds of axiom the theories mix:

* *Local rules* — backward rules (`Echo?`, `Vote0?`, `VoteN?`, `Deliver?`'s
  certificate clause), `echoNonEquivocation`, `voteNonEquivocation`. Each is a
  property of an event and its own causal past, so "executions = histories all
  of whose events satisfy the backward rules" is closed under `local_closure`.
  (Whether an event is permitted does not depend on `live`, which is why locality
  is stated modulo `live`.)
* *Environment safety assumptions* — `correlationSeq`, causal/vote monotonicity,
  correlation symmetry/transitivity, and the fast path's end-of-time guarantee
  `⤒(l ⋈ l ⇒ □[[l]] seq)`. These are not local (they mention the whole history
  or all possible worlds). `correlationSeq` is `EnvOK`; monotonicity and
  symmetry/transitivity are properties of `κ`, which the theorem chooses; the
  fast-path guarantee would have to be folded into `EnvOK` or the fast path
  dropped for this exercise.
* *Liveness* — `ThyLive` (Knowledge, LiveAlways, LiveSeq) is `fair`; the forward
  rules are the protocol's *obligations*, i.e. what makes fair completions in
  which the protocol actually delivers exist. Showing `fair_completion` for
  HBB4 amounts to a general nonvacuity theorem (a fair execution extending any
  prefix, in which the forward rules are met) — plausible, in the spirit of
  `FiniteModel`, but a real theorem, not a triviality.

With that split, agreement is HBB4's agreement theorem on `EnvOK` executions and
the two liveness properties are its liveness theorems on fair `EnvOK` executions,
so ThyHBB4 (and, with their own rule sets, ThyHBB1–3) instantiate `Protocol`.
The statement has been adjusted accordingly: agreement and liveness are
required only of `EnvOK` (and fair) executions, and the theorem quantifies over
`EnvOK` executions on the chosen topology and correlation.

## Modelling decisions to assess

1. **What a protocol is.** `Protocol` is a set of complete executions plus two
   closure properties. Neither can be derived for an arbitrary set of models,
   and both are used by the intended proof:
   - `local_closure` (indistinguishability/grafting): a history whose events
     are each permitted — occur with the same participant and causal past in
     some execution on the same `(T, ρ)` — is an execution. This lets the
     adversary combine the `Q_a`-only branch and the `Q_i`-only branches, with
     shared participants acting on both (equivocating).
   - `fair_completion`: any execution plus a set `Live` of so-far-sequential
     participants (the ones `ρ` marks live) extends to a *fair* execution in
     which only `Live` acts further. This is how each "`Q_i` is obliged by
     liveness to deliver" step is invoked: complete the current prefix fairly
     with `Q_i`'s honest members live and everyone else silent, and apply
     Liveness 2 to the completion.
   `fair` is abstract. HBB4 itself encodes fairness through `ThyLive`
   (Knowledge, LiveAlways, LiveSeq); for an arbitrary protocol we only assume
   the liveness guarantees hold on whatever `fair` means. If you prefer a
   concrete protocol notion (e.g. a per-participant permission relation
   `allowed : P → PreHistory → Event → Prop` with executions = all locally
   permitted histories, and an explicit fairness definition), both closure
   properties become theorems rather than fields.

2. **Where `⋈` and `live` live.** Both are read off `Model.predInterp`, a function
   of `(participant, local prehistory)`. The theorem chooses only the correlation
   part `κ` (`Correlation`) and restricts to executions carrying it
   (`executionsOn`); the `live` designation is free, so auxiliary executions in
   the proof can have different live sets, and locality is required modulo
   `live`. Causal monotonicity of `κ` is `CausalMonotonicity M σ` for every
   model carrying `κ`. (Confirmed: `⋈` is a function of the observed prehistory.)

3. **The end-of-time subtlety.** Liveness 2 requires `a ⋈ b` at every *final*
   world, and final worlds see the whole history. The adversarial `⋈`
   ("`L_i` disconnects once an equivocation in `Q_i ∩ Q_a` has been observed")
   must therefore be arranged so that, in the completion used at step `i`, the
   equivocations that would disconnect `L_i` are *not yet in the history*. This
   forces the proof to build the `Q_a` branch layer by layer alongside the
   `L_i` branches rather than assuming the whole `a`-delivery is present from
   the start, and it is why the bound is on the depth of the `a`-delivery: an
   `a`-delivery of depth `d` exposes at most `d` layers of `Q_a`, and the
   argument shows a disagreeing `L_i`-delivery survives for some `i ≤ d` when
   `d < D`. The statement does not commit to this; it is a proof concern, but
   it is the one most likely to force a change of statement, so it is worth
   confirming now that the intended `⋈` really is a function of the observed
   prehistory in this sense.

4. **Cardinalities.** `hP` (infinitely many participants) and `hV` (infinitely
   many learner/value constants — recall learners and values share `S.Value`)
   give the construction `Q_a, Q_1, …, Q_D` and `a, L_1, …, L_D` plus two
   distinct values. Finite bounds (`≈ 2(D+1)` participants, `D+3` values) would do.

5. **`D ≥ 2`.** Kept as in the informal statement; the construction may or may
   not need it (with `D = 1` the claim is that a `Q`-only `L`-delivery cannot be
   an initial event, which may hold for other reasons).

## Intended proof (sketch, following the informal argument)

Fix `D`. Learners `a, L_1, …, L_D`; quorums `Q_a` and `Q_i` with `Q_i ∩ Q_a`
pairwise disjoint across `i` and each `Q_i` having a private honest part.
`⋈` at prehistory `h`: `L_i ⋈ x` for `x ≠ L_i` iff no equivocation by a member of
`Q_j ∩ Q_a` with `j ≤ i` is visible in `h`; all `L_j` with `j > n` remain
correlated with each other and with `a` once layers `≤ n` are exposed.

Suppose an execution has an `a`-delivery of depth `d < D` using only `Q_a`.
Its causal past decomposes into layers by depth; the members of `Q_i ∩ Q_a`
act at layer `i`. Build, by grafting, an `L_1`-delivery of `v_1 ≠ v_0` using
only `Q_1` (Liveness 1 on a fair completion in which `Q_1` is live and `v_1` is
the only proposal *visible on that branch*; locality makes `Q_1`'s honest
members behave as in that completion). Then for `i = 2, …`: graft the layer
`i-1` of the `a`-branch and the `L_{i-1}`-delivery into a prefix in which
`Q_i` is live; at the end of its fair completion only layers `< i` are visible,
so only `L_j` with `j < i` are disconnected, `L_{i-1} ⋈ L_i` still holds, and
Liveness 2 obliges `Q_i` to `L_i`-deliver `v_1`. Since `d < D` the `a`-branch
runs out of layers before the `L_i` run out, so some `L_i ⋈ a` survives to the
end of a completion containing both the `a`-delivery of `v_0` and an
`L_i`-delivery of `v_1`, contradicting agreement.
