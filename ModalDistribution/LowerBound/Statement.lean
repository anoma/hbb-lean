import ModalDistribution.LowerBound.Basic

/-!
# A depth lower bound for correlated broadcast: the statement

This file only *states* the theorem; the proof is `sorry`. It is meant for
assessing that we are trying to prove the right thing.

## Informal statement

For every protocol `Proto` (over a fixed event/predicate vocabulary `σ`) that
guarantees HBB4's three correctness properties — agreement, Liveness 1 and
Liveness 2, as stated for `ThyHBB4` — and every `D ≥ 2`, there is a topology
(a set of learners with a quorum system each) and a correlation relation `⋈`
obeying causal monotonicity, and a learner `L` with a quorum `Q`, such that in
every execution of `Proto` on that topology and correlation, every `L`-delivery
that involves only participants of `Q` (the delivery event and every world in
its causal past are placed in `Q`) has causal depth at least `D`.

## What "protocol" means here

HBB4 is given axiomatically, so "a protocol" cannot simply be "a set of models":
the lower-bound argument builds executions by grafting branches together and by
completing finite prefixes fairly, and an arbitrary set of models need not be
closed under those operations. Moreover the HBB theories mix three kinds of
axiom: *local rules* (backward rules, non-equivocation: properties of an event
and its own causal past), *environment assumptions* (`correlationSeq`: quorums
of correlated learners meet in a participant sequential at the world; causal
monotonicity of `⋈`; the fast path's end-of-time guarantee), and *liveness
assumptions and obligations* (`ThyLive`, the forward rules). Only the first kind
is local, so a protocol is modelled as follows:

* `executions`: the histories all of whose events are locally permitted. Closed
  under `local_closure` (grafting/indistinguishability): a history each of whose
  events occurs, with the same participant and causal past, in some execution
  on the same topology and correlation, is an execution.
* `EnvOK`: the environment's safety assumption, `correlationSeq`, stated
  generically. Agreement is required only of executions satisfying it.
* `fair`: environment fairness (abstract). Liveness is required only of fair,
  `EnvOK` executions. `fair_completion` lets the adversary complete any `EnvOK`
  execution fairly with a chosen set of so-far-sequential participants live and
  everyone else silent, preserving `EnvOK`.
* `propose_free`: proposals are environment events and may be added anywhere.

The interpretation of the predicate symbols is split: the theorem fixes the
correlation relation `κ` (a function of a participant's local prehistory) but
leaves the `live` designation free, so that different auxiliary executions can
have different live sets. Locality is required modulo `live`: which events a
participant may perform does not depend on who is designated live.

Whether ThyHBB1–4 are `Protocol`s in this sense is discussed in `PLAN.md`.
-/

namespace ModalDistribution.LowerBound
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyHBB4 (ProtocolSignature)
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]

/-! ## Protocols -/

/-- A protocol: a set of complete executions (models) with the closure
properties the lower-bound argument uses. See the module docstring. -/
structure Protocol (S : Signature) (P : Type) [Nonempty P] (σ : ProtocolSignature S) where
  /-- The complete executions of the protocol. -/
  executions : Set (Model S P)
  /-- Environment fairness of a complete execution, relative to the participants the
  model marks live. Left abstract; intended meaning: live participants are
  sequential, eventually see every event of the history, and are eventually
  scheduled whenever they have something to do. -/
  fair : Model S P → Prop
  /-- Locality, modulo `live`. A history each of whose events occurs, with the same
  acting participant and the same causal past, in some execution with the same
  topology and correlation, is itself an execution. -/
  local_closure : ∀ M : Model S P,
    (∀ w ∈ M.history.val, ∀ e : S.EventType, w.event = .some e →
      ∃ M' ∈ executions, M'.learner = M.learner ∧ corrOf σ M' = corrOf σ M ∧
        w ∈ M'.history.val) →
    M ∈ executions
  /-- Proposals are environment events: a history that differs from an execution only
  by an additional `propose` event (of any value, by any participant, with any
  causal past) is an execution. -/
  propose_free : ∀ M M' : Model S P, M ∈ executions →
    M'.learner = M.learner → M'.predInterp = M.predInterp →
    ∀ (w : World P S.EventType) (v : S.Value), w.event = .some ⟨σ.proposeSymb, [v]⟩ →
    (∀ t : World P S.EventType, t ∈ M'.history.val ↔ (t ∈ M.history.val ∨ t = w)) →
    M' ∈ executions
  /-- Fair completion. Any `EnvOK` execution, together with a set `Live` of
  participants that have not equivocated in it, extends to a fair `EnvOK`
  execution that marks exactly `Live` live and in which only members of `Live`
  act further. -/
  fair_completion : ∀ M ∈ executions, EnvOK σ M → ∀ Live : Set P,
    (∀ p ∈ Live, isSequential (Event := S.EventType) p M.history.val) →
    ∃ M' ∈ executions, fair M' ∧ EnvOK σ M' ∧
      M'.learner = M.learner ∧ corrOf σ M' = corrOf σ M ∧
      (∀ p h, IsLive σ M' p h ↔ p ∈ Live) ∧
      M.history.val ⊆ M'.history.val ∧
      ∀ w ∈ M'.history.val, w ∉ M.history.val → w.place ∈ Live

namespace Protocol

variable {σ : ProtocolSignature S} (Proto : Protocol S P σ)

/-- Agreement, as in `ThyHBB4.CM.agreement`, required of every `EnvOK` execution. -/
def Agreement : Prop :=
  ∀ M ∈ Proto.executions, EnvOK σ M → ∀ (a b v u : S.Value),
    (∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b) →
    Occurs M (σ.deliver a v) → Occurs M (σ.deliver b u) → v = u

/-- Liveness 1, as in `ThyHBB4.livenessOne`, required of every fair `EnvOK` execution. -/
def LivenessOne : Prop :=
  ∀ M ∈ Proto.executions, EnvOK σ M → Proto.fair M → ∀ (l v : S.Value),
    (∃ Q ∈ (M.learner l).quorums, ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live) →
    UniqueOccurrence M σ.propose →
    (∃ e ∈ M.history.val, (⟪e⟫ ⊨[M] σ.live) ∧ ObservedAt M e (σ.propose v)) →
    ∀ p : P, (⟪finalWorld M p⟫ ⊨[M] σ.live) → OccursAt M p (σ.deliver l v)

/-- Liveness 2, as in `ThyHBB4.CM.livenessTwo`, required of every fair `EnvOK` execution. -/
def LivenessTwo : Prop :=
  ∀ M ∈ Proto.executions, EnvOK σ M → Proto.fair M → ∀ (a b v : S.Value),
    (∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b) →
    (∃ Q ∈ (M.learner b).quorums, ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live) →
    Occurs M (σ.deliver a v) →
    ∀ p : P, (⟪finalWorld M p⟫ ⊨[M] σ.live) → OccursAt M p (σ.deliver b v)

/-- The protocol guarantees HBB4's three correctness properties. -/
def Correct : Prop := Proto.Agreement ∧ Proto.LivenessOne ∧ Proto.LivenessTwo

/-- The `EnvOK` executions of the protocol on a given topology and correlation. -/
def executionsOn (T : Topology S P) (κ : Correlation S P) : Set (Model S P) :=
  fun M => M ∈ Proto.executions ∧ EnvOK σ M ∧ M.learner = T ∧ corrOf σ M = κ

end Protocol

/-! ## The theorem -/

/-- **Depth lower bound.** For every correct protocol and every `D ≥ 2` there are a
topology, a causally monotone correlation relation, a learner `L` and an
`L`-quorum `Q` such that, in every `EnvOK` execution of the protocol on that
topology and correlation, every `L`-delivery involving only participants of `Q`
has causal depth at least `D`.

The cardinality hypotheses give the construction enough participants and enough
distinct learners/values (the topology uses learners `a, L₁, …, L_D`, quorums
`Q_a, Q₁, …, Q_D`, and two distinct values). -/
theorem depth_lower_bound {σ : ProtocolSignature S} (Proto : Protocol S P σ)
    (hProto : Proto.Correct)
    (hP : ∃ f : Nat → P, Function.Injective f)
    (hV : ∃ g : Nat → S.Value, Function.Injective g)
    (D : Nat) (hD : 2 ≤ D) :
    ∃ (T : Topology S P) (κ : Correlation S P),
      CausallyMonotone σ κ ∧
      ∃ (L : S.Value) (Q : Set P), Q ∈ (T L).quorums ∧
        ∀ M ∈ Proto.executionsOn T κ, ∀ d ∈ M.history.val, ∀ v : S.Value,
          (⟪d⟫ ⊨[M] σ.deliver L v) → UsesOnly Q d → D ≤ worldDepth d := by
  sorry

end ModalDistribution.LowerBound
