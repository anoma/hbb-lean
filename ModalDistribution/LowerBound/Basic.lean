import ModalDistribution.Examples.ThyHBB4.Axioms

/-!
# Depth lower bound: basic notions

Causal depth of a world, quorum-local events, topologies and correlation
relations. Shared by the general statement (`Statement.lean`) and the proved
HBB4 special case (`Depth.lean`, `Witness.lean`, `HBB4.lean`).
-/

namespace ModalDistribution.LowerBound
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyHBB4 (ProtocolSignature)
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

/-- The causal cone of a world: the world together with its causal past, as a
prehistory. -/
def cone {E : Type} (w : World P E) : PreHistory P E :=
  match w with
  | (p, e, .mk l) => .mk ((p, e, .mk l) :: l)

omit [Nonempty P] in
theorem mem_cone {E : Type} {w t : World P E} : t ∈ cone w ↔ t = w ∨ t ≪ w := by
  rcases w with ⟨p, e, l⟩
  cases l with
  | mk l =>
    show t ∈ (p, e, PreHistory.mk l) :: l ↔ _
    rw [List.mem_cons]
    rfl

/-- An honest branch: every participant is sequential in the world's causal cone.
(Only the participants that act in the cone matter; the others are vacuously
sequential.) -/
def HonestCone (w : World P S.EventType) : Prop :=
  ∀ p : P, isSequential (Event := S.EventType) p (cone w)

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
    ModalDistribution.Examples.ThyHBB4.CausalMonotonicity M σ

/-- Whether a participant is marked live by a model at a prehistory. -/
def IsLive (σ : ProtocolSignature S) (M : Model S P)
    (p : P) (h : PreHistory P S.EventType) : Prop :=
  ⟨σ.liveSymb, []⟩ ∈ M.predInterp p h

/-- The environment's safety assumption, HBB4's `correlationSeq`: at every possible
world, quorums of correlated learners share a participant sequential at that
world. -/
def EnvOK (σ : ProtocolSignature S) (M : Model S P) : Prop :=
  ∀ {w : World P S.EventType}, w.time ⪯ M.history.val → ∀ {a b : S.Value},
    Correlated M σ.correlationSymb w a b → (⟪w⟫ ⊨[M] ♢ᶠ[[a, b]] Formula.seq)

/-- Coherence of the correlation relation carried by a model: symmetry,
transitivity, persistence along a participant's own past, and causal
monotonicity (HBB4's `correlationSymm`, `correlationTrans`, `correlationPast`,
`CausalMonotonicity`). A property of `κ` as a function of prehistories, not of
the protocol. -/
structure Coherent (σ : ProtocolSignature S) (M : Model S P) : Prop where
  symm : ∀ {w : World P S.EventType}, w.time ⪯ M.history.val → ∀ {a b : S.Value},
    Correlated M σ.correlationSymb w a b → Correlated M σ.correlationSymb w b a
  trans : ∀ {w : World P S.EventType}, w.time ⪯ M.history.val → ∀ {a b c : S.Value},
    Correlated M σ.correlationSymb w a b → Correlated M σ.correlationSymb w b c →
    Correlated M σ.correlationSymb w a c
  past : ∀ {w : World P S.EventType}, w.time ⪯ M.history.val → ∀ {a b : S.Value},
    Correlated M σ.correlationSymb w a b → ∀ {u : World P S.EventType}, u ≪ w →
    u.place = w.place → Correlated M σ.correlationSymb u a b
  mono : ModalDistribution.Examples.ThyHBB4.CausalMonotonicity M σ

/-- The realized depth of every learner is bounded by `D`. -/
def DepthLE (σ : ProtocolSignature S) (M : Model S P) (D : Nat) : Prop :=
  ∀ l : S.Value,
    ModalDistribution.Examples.ThyHBB4.maxDepth M (Correlated M σ.correlationSymb) l ≤ D

end ModalDistribution.LowerBound
