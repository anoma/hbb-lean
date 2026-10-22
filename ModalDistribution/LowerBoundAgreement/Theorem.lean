import ModalDistribution.LowerBoundAgreement.Witness
import ModalDistribution.LowerBoundAgreement.Counterexample

/-!
# The depth lower bound and ThyAgreement

HBB4's `hbb4_depth_lower_bound` has two halves: a witness model realizing
`maxDepth(L) = D` whose quorum `Q` delivers at world-depth `D + 4`, and the
lower bound proper — in every model on that topology and correlation realizing
`maxDepth(L) ≥ D`, `Q`-only `L`-deliveries are at least `D + 4` deep. For
`ThyAgreement`, which assumes agreement and both liveness properties as axioms
but none of HBB4's event rules:

* the witness half survives (`agreement_witness`): the HBB4 witness is a
  `ThyAgreement` model with budget `D` (`Witness.protocol`);
* the lower-bound half **fails** (`agreement_depth_lower_bound_fails`): on the
  very same topology, correlation, learner and quorum, `Counterexample.model D`
  is a causally monotone `ThyAgreement` model with `maxDepth(L) = D` in which
  `a₀` `L`-delivers with empty past, at world-depth `1`. Without event rules
  nothing ties a delivery to a causal history, and agreement and liveness —
  properties of one completed execution — cannot supply the missing causal
  constraint. Recovering a lower bound from agreement and liveness alone needs
  the cross-execution argument of `LowerBound/Statement.lean` (grafting and
  fair completion), not a single-model statement.
-/

namespace ModalDistribution.LowerBoundAgreement
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyAgreement
open scoped Formula PreHistory

/-- The exposure-based correlation relation shared by the witness and the
countermodel. -/
theorem exposureBased_corr (D : Nat) :
    ExposureBased (S := sig) (P := Nat) (fun _ h a b => Witness.corr D h a b) := by
  refine ⟨fun a b E => a = b ∨ (a ≤ D ∧ b ≤ D ∧ a ∉ E ∧ b ∉ E), fun p h a b => ?_⟩
  show Witness.corr D h a b ↔ _
  unfold Witness.corr
  constructor
  · rintro (h | ⟨ha, hb, sa, sb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ha, hb, fun hn => hn sa, fun hn => hn sb⟩
  · rintro (h | ⟨ha, hb, na, nb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ha, hb, Classical.byContradiction fun hs => na hs,
        Classical.byContradiction fun hs => nb hs⟩

/-- **Nonvacuity for ThyAgreement.** The HBB4 witness is a `ThyAgreement` model:
`maxDepth(L) = D`, `L ⋈ L` everywhere, and `Q` delivers at world-depth `D + 4`. -/
theorem agreement_witness (D : Nat) :
    ∃ (P : Type) (_ : Nonempty P) (T : Topology sig P) (κ : Correlation sig P)
      (L : Nat) (Q : Set P),
      Q ∈ (T L).quorums ∧ (∃ q, q ∉ Q) ∧ ExposureBased κ ∧
      ∃ M' : Model sig P, ProtocolCM M' (symbols D) ∧
        M'.learner = T ∧ corrOf (symbols D) M' = κ ∧
        maxDepth M' (Correlated M' Pred.corr) L = D ∧
        (∀ w : World P sig.EventType, w.time ⪯ M'.history.val →
          Correlated M' Pred.corr w L L) ∧
        ∃ v : Nat, ∀ p ∈ Q, ∃ d ∈ M'.history.val, d.place = p ∧
          (⟪d⟫ ⊨[M'] (symbols D).deliver L v) ∧ worldDepth d = D + 4 :=
  Witness.agreement_witness D

/-- **The lower bound fails for ThyAgreement.** On the witness's topology,
correlation, learner and quorum, the clause "every `ThyAgreement` model realizing
`maxDepth(L) ≥ D` has its `Q`-only `L`-deliveries at depth `≥ D + 4`" is false:
`Counterexample.model D` delivers at depth `1`. -/
theorem agreement_depth_lower_bound_fails (D : Nat) :
    ∃ (P : Type) (_ : Nonempty P) (T : Topology sig P) (κ : Correlation sig P)
      (L : Nat) (Q : Set P),
      Q ∈ (T L).quorums ∧ ExposureBased κ ∧
      -- the witness half holds …
      (∃ M' : Model sig P, ProtocolCM M' (symbols D) ∧
        M'.learner = T ∧ corrOf (symbols D) M' = κ ∧
        maxDepth M' (Correlated M' Pred.corr) L = D ∧
        (∀ w : World P sig.EventType, w.time ⪯ M'.history.val →
          Correlated M' Pred.corr w L L) ∧
        (∃ v : Nat, ∀ p ∈ Q, ∃ d ∈ M'.history.val, d.place = p ∧
          (⟪d⟫ ⊨[M'] (symbols D).deliver L v) ∧ worldDepth d = D + 4)) ∧
      -- … but the lower-bound half does not.
      ¬ (∀ M : Model sig P, ProtocolCM M (symbols D) →
        M.learner = T → corrOf (symbols D) M = κ →
        D ≤ maxDepth M (Correlated M Pred.corr) L →
        ∀ d ∈ M.history.val, ∀ v : Nat,
          (⟪d⟫ ⊨[M] (symbols D).deliver L v) → UsesOnly Q d → D + 4 ≤ worldDepth d) := by
  refine ⟨Nat, inferInstance, Witness.quorums, fun _ h a b => Witness.corr D h a b, 0,
    fun p => p = 0, ⟨rfl, rfl⟩, exposureBased_corr D, ?_, ?_⟩
  · refine ⟨Witness.model D, Witness.protocol D, rfl, ?_, Witness.maxDepth_eq D,
      fun w _ => (Witness.corr_iff D w 0 0).mpr (Or.inl rfl), 0, ?_⟩
    · funext p h a b
      exact propext (Witness.corr_iff D ⟨p, †, h⟩ a b)
    · intro p hp
      have hp0 : p = 0 := hp
      subst hp0
      refine ⟨Witness.A D (D + 3), Witness.A_mem (by show D + 3 < 2 * D + 6; omega), rfl,
        Witness.deliver_actual D, ?_⟩
      show PreHistory.height (Witness.TA D (D + 3)) = D + 4
      rw [Witness.height_TA D (D + 3) (Nat.le_refl _)]
  · intro hbound
    obtain ⟨M, hM, hT, hκ, hdepth, d, hd, hdel, hQ, hdepth1⟩ := Counterexample.shallow_delivery D
    have := hbound M hM hT hκ (Nat.le_of_eq hdepth.symm) d hd 0 hdel hQ
    omega

end ModalDistribution.LowerBoundAgreement
