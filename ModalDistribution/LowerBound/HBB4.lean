import ModalDistribution.LowerBound.Witness

/-!
# A depth lower bound for HBB4 itself

Special case of the lower bound for the (implementable) HBB4 theories, whose
decision rank is the static budget `depthBound`. For every `D` (the interesting
case being `D > 2`), read the vocabulary with `depthBound L = D` (`symbols D`). Then there are participants
`P`, a topology `T`, an exposure-based correlation relation `κ`, a learner `L`
and an `L`-quorum `Q` such that

* (nonvacuity, `Witness.hbb4_witness`) some causally monotone HBB4 model `M'` on
  `(T, κ)` realizes `maxDepth(L) = D`, has `L ⋈ L` at every possible world, and
  every member of `Q` `L`-delivers a common value at world-depth exactly
  `D + 4`;
* (sharpness) consequently no smaller budget is sound on `(T, κ)`: `M'` violates
  `depthBound_dominates` for every reading with `depthBound L < D`;
* (lower bound, `delivery_depth_of_usesOnly`) in *every* HBB4 model on `(T, κ)`
  — indeed in every `BaseProtocol` model whatsoever — every `L`-delivery whose
  causal history lies entirely within `Q` has world-depth at least `D + 4`.

`worldDepth` counts every event (an event with empty past has depth `1`), and an
HBB4 delivery at rank `r` costs at least `r + 4` levels (propose, echo, votes at
ranks `0 … r`, deliver), which is where the `+ 4` comes from; the witness shows
the bound is tight.

A correlation relation is *exposure-based* when, at a prehistory, it depends
only on the pair of learners and on the set of participants that are
non-sequential (exposed as equivocators) in that prehistory. In the witness the
row of `L` shrinks by one learner at each of `D` successive exposures observed
along the delivering participant's chain, which is what makes `maxDepth(L)`
equal to `D`. `UsesOnly Q d` excludes the fast path when some participant lies
outside `Q`: such a participant is vacuously sequential in `d`'s past but has
echoed nothing there.
-/

namespace ModalDistribution.LowerBound.HBB4
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyHBB4
open ModalDistribution.LowerBound
open scoped Formula PreHistory

/-! ## The theorem -/

/-- **Depth lower bound for HBB4.** -/
theorem hbb4_depth_lower_bound (D : Nat) :
    ∃ (P : Type) (_ : Nonempty P) (T : Topology sig P) (κ : Correlation sig P)
      (L : Nat) (Q : Set P),
      Q ∈ (T L).quorums ∧ ExposureBased κ ∧
      -- Nonvacuity: a witness model realizes `maxDepth(L) = D` and `Q` delivers
      -- at depth `D + 4` …
      (∃ M' : Model sig P, ProtocolCM M' (symbols D) ∧
        M'.learner = T ∧ corrOf (symbols D) M' = κ ∧
        maxDepth M' (Correlated M' Pred.corr) L = D ∧
        (∀ w : World P sig.EventType, w.time ⪯ M'.history.val →
          Correlated M' Pred.corr w L L) ∧
        (∃ v : Nat, ∀ p ∈ Q, ∃ d ∈ M'.history.val, d.place = p ∧
          (⟪d⟫ ⊨[M'] (symbols D).deliver L v) ∧ worldDepth d = D + 4) ∧
        -- … so no smaller budget is sound on `(T, κ)`.
        (∀ D' < D, ¬ BaseProtocol M' (symbols D'))) ∧
      -- Lower bound: `Q`-only `L`-deliveries are at least `D + 4` deep.
      (∀ M : Model sig P, BaseProtocol M (symbols D) →
        M.learner = T → corrOf (symbols D) M = κ →
        ∀ d ∈ M.history.val, ∀ v : Nat,
          (⟪d⟫ ⊨[M] (symbols D).deliver L v) → UsesOnly Q d → D + 4 ≤ worldDepth d) := by
  obtain ⟨P, hP, T, κ, L, Q, hQ, hQne, hκ, M', hCM, hT, hκ', hdepth, hLL, hdel⟩ :=
    Witness.hbb4_witness D
  refine ⟨P, hP, T, κ, L, Q, hQ, hκ, ⟨M', hCM, hT, hκ', hdepth, hLL, hdel, ?_⟩, ?_⟩
  · intro D' hD' h
    have := h.depthBound_dominates L
    simp only [symbols] at this
    omega
  · intro M h _ _ d hd v hdel hu
    exact delivery_depth_of_usesOnly h hQne (M.time_le_of_mem hd) hdel hu

end ModalDistribution.LowerBound.HBB4
