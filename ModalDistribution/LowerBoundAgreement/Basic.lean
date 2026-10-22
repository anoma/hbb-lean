import ModalDistribution.Examples.ThyAgreement.Axioms

/-!
# Depth lower bound: basic notions

Causal depth of a world, quorum-local events, topologies and correlation
relations. Shared by the general statement (`Statement.lean`) and the proved
ThyAgreement special case (`Depth.lean`, `Witness.lean`, `Theorem.lean`).
-/

namespace ModalDistribution.LowerBoundAgreement
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyAgreement (ProtocolSignature)
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]

/-! ## Depth and quorum-local events -/

/-- The causal depth of a world: the height of its causal past, so an event with
empty past has depth `1`, and in general depth is `1 +` the maximum depth of the
worlds in its past (`max (1, …)` in the informal statement, read as
`1 + max ∅ = 1`). -/
def worldDepth (w : World P S.EventType) : Nat := PreHistory.height w.time

/-- An event that involves only participants of `Q`: it is placed in `Q`, and so
is every world in its causal past. -/
def UsesOnly (Q : Set P) (w : World P S.EventType) : Prop :=
  w.place ∈ Q ∧ ∀ t ∈ w.time, t.place ∈ Q

/-! ## Topology, interpretation, causal monotonicity -/

/-- A topology assigns each learner a quorum system. -/
abbrev Topology (S : Signature) (P : Type) := S.Value → Semifilter P

/-- A correlation relation: for each participant and local prehistory, which pairs
of learners are correlated. This is the part of a `Model.predInterp` concerning
`σ.correlationSymb`. -/
abbrev Correlation (S : Signature) (P : Type) :=
  P → PreHistory P S.EventType → S.Value → S.Value → Prop

/-- The correlation relation read off a model. -/
def corrOf (σ : ProtocolSignature S) (M : Model S P) : Correlation S P :=
  fun p h a b => ⟨σ.correlationSymb, [a, b]⟩ ∈ M.predInterp p h

/-- Causal monotonicity of a correlation relation: `CausalMonotonicity M σ` for
every model carrying it. -/
def CausallyMonotone (σ : ProtocolSignature S) (κ : Correlation S P) : Prop :=
  ∀ M : Model S P, corrOf σ M = κ →
    ModalDistribution.Examples.ThyAgreement.CausalMonotonicity M σ

/-- Whether a participant is marked live by a model at a prehistory. -/
def IsLive (σ : ProtocolSignature S) (M : Model S P)
    (p : P) (h : PreHistory P S.EventType) : Prop :=
  ⟨σ.liveSymb, []⟩ ∈ M.predInterp p h

/-- The environment's safety assumption, ThyAgreement's `correlationSeq`: at every possible
world, quorums of correlated learners share a participant sequential at that
world. -/
def EnvOK (σ : ProtocolSignature S) (M : Model S P) : Prop :=
  ∀ {w : World P S.EventType}, w.time ⪯ M.history.val → ∀ {a b : S.Value},
    Correlated M σ.correlationSymb w a b → (⟪w⟫ ⊨[M] ♢ᶠ[[a, b]] Formula.seq)

end ModalDistribution.LowerBoundAgreement
