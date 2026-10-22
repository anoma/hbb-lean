import ModalDistribution.LowerBound.Proof

/-!
# The depth lower bound

See `Statement.lean` for the notion of protocol and the discussion of the
statement, and `Proof.lean` for the argument.
-/

namespace ModalDistribution.LowerBound
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyHBB4 (ProtocolSignature)
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]

/-! ## The theorem -/

/-- **Depth lower bound.** For every correct protocol and every `D ≥ 2` there are a
topology, a causally monotone correlation relation, a learner `L` and an
`L`-quorum `Q` such that, in every `EnvOK` execution of the protocol on that
topology and correlation, every `L`-delivery involving only participants of `Q`,
in a branch where those participants behave honestly (`HonestCone`: every
participant is sequential in the delivery's causal cone), has causal depth at
least `D`.

Honesty of the branch is necessary: a `Q`-only branch in which all but one
member of `Q` equivocate disconnects, through `EnvOK`, every learner whose
quorums meet `Q`, and leaves no unique proposal, so a protocol may deliver
shallowly there without violating agreement or liveness.

The cardinality hypotheses give the construction enough participants and enough
distinct learners/values (the topology uses learners `a, L₁, …, L_D`, quorums
`Q_a, Q₁, …, Q_D`, and two distinct values). -/
theorem depth_lower_bound {σ : ProtocolSignature S} (Proto : Protocol S P σ)
    (hProto : Proto.Correct)
    (hP : ∃ f : Nat → P, Function.Injective f)
    (hV : ∃ g : Nat → S.Value, Function.Injective g)
    (D : Nat) (hD : 2 ≤ D)
    (henv : ∀ M : Model S P, EnvOK σ M → Coherent σ M → DepthLE σ M D → Proto.env M)
    (henv' : ∀ M : Model S P, Proto.env M → EnvOK σ M) :
    ∃ (T : Topology S P) (κ : Correlation S P),
      CausallyMonotone σ κ ∧
      ∃ (L : S.Value) (Q : Set P), Q ∈ (T L).quorums ∧
        ∀ M ∈ Proto.executionsOn T κ, ∀ d ∈ M.history.val, ∀ v : S.Value,
          (⟪d⟫ ⊨[M] σ.deliver L v) → UsesOnly Q d → HonestCone d → D ≤ worldDepth d := by
  obtain ⟨f, hf⟩ := hP
  obtain ⟨g, hg⟩ := hV
  let π : Params S P := ⟨f, g, D, hf, hg, by omega⟩
  refine ⟨π.T, π.κ, π.causallyMonotone, π.g 0, π.Q, π.Q_quorum, ?_⟩
  intro M hM d hd v hdel hQ hHon
  obtain ⟨hexec, hpenv, hT, hκ⟩ := hM
  have hEnv : EnvOK σ M := henv' M hpenv
  refine Classical.byContradiction fun hlt => ?_
  have hlt' : worldDepth d < D := by omega
  -- a value different from the delivered one
  have hv1 : ∃ v1 : S.Value, v1 ≠ v := by
    by_cases h : v = g (D + 1)
    · exact ⟨g (D + 2), fun e => by have := hg (e.trans h); omega⟩
    · exact ⟨g (D + 1), fun e => h e.symm⟩
  obtain ⟨v1, hv1⟩ := hv1
  let c : Ctx π Proto :=
    { henv := henv, henv' := henv', M := M, hM := hexec, hEnv := hEnv, hT := hT, hκ := hκ, d := d, hd := hd, v := v,
      hdel := hdel, hQ := hQ, hHon := hHon, v1 := v1, hv1 := hv1 }
  exact c.no_shallow hProto hlt'

end ModalDistribution.LowerBound
