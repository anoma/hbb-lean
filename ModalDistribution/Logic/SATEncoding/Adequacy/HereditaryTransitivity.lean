import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.Bitmask.Core
import ModalDistribution.Logic.SATEncoding.ListLemmas
import ModalDistribution.Logic.SATEncoding.FormulaEncoding

/-!
# Hereditary Transitivity from WF Constraints

This file proves that decoded prehistories satisfy hereditary transitivity when the
CNF well-formedness constraints are satisfied.

## Main Results

- `mem_edge_subset`: Edge(H, H') implies decodePre(H') ⊆ decodePre(H)
- `transitive_at_time`: Each prehistory is transitive
- `hered_at_time`: Each prehistory is hereditarily transitive
- `heredFromWF`: The root prehistory has hereditary transitivity

## Strategy

The proof uses a three-lemma chain:
1. Edge variables enforce subset relationships via transitivity clauses
2. Each prehistory is transitive using acyclic predecessor constraints
3. Hereditary transitivity follows by induction on time index

## References

- Structure.lean for CNF constraint definitions
- Plan.md section "Hereditary Transitivity from CNF"
-/

open ModalDistribution Encoding

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Edge Subset Lemma -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If Edge(H, H') is true in the assignment, then decodePre(H') ⊆ decodePre(H).
    Uses the transitivity clauses from cnfEdge. -/
lemma mem_edge_subset (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H H' : b.times)
    (hEdge : σ (Var.Edge H H') = true) :
    decodePre b σ hWF H' ⊆ decodePre b σ hWF H := by
  -- Strategy: Show ∀ world, world ∈ decodePre H' → world ∈ decodePre H
  -- Use transitivity clause: Edge(H,H') ∧ Mem(H',w) → Mem(H,w)
  -- This clause is in cnfEdge (Structure.lean:96-104)

  -- Extract cnfEdge using the extraction lemma
  have ⟨_, _, hEdgeCNF, _, _, _, _, _, _, _, _⟩ := (cnfWellFormed_eval_iff b σ).mp hWF

  -- Show the subset relationship
  intro world hmem
  -- hmem : world ∈ decodePre b σ hWF H'
  -- Need to show: world ∈ decodePre b σ hWF H

  -- Unfold decodePre to access members
  unfold decodePre at hmem ⊢

  -- Handle fuel check
  split at hmem
  · rename_i hFuelH'
    -- H' has positive fuel, so world came from some w' with Mem(H', w')
    simp only [PreHistory.mem_mk, List.mem_map, List.mem_attach, true_and,
      Subtype.exists, List.mem_filter] at hmem
    obtain ⟨w', ⟨_, hmemH'⟩, heq⟩ := hmem

    -- Use transitivity clause: Edge(H,H') ∧ Mem(H',w') → Mem(H,w')
    have hmemH : σ (Var.Mem H w') = true := by
      -- The clause [¬Edge(H,H'), ¬Mem(H',w'), Mem(H,w')] is in cnfEdge
      classical
      let clause := [SAT.Lit.neg (Var.Edge H H'),
                     SAT.Lit.neg (Var.Mem H' w'),
                     SAT.Lit.pos (Var.Mem H w')]
      have h_clause_in : clause ∈ (cnfEdge b).clauses := by
        -- This is the transitivity clause from Structure.lean:96-104
        unfold cnfEdge
        let transitiveClauses :=
          (Bounds.timesL b).flatMap fun H₀ =>
            (Bounds.timesL b).flatMap fun H₁ =>
              (WId.allWorlds b).map fun w =>
                [ SAT.Lit.neg (Var.Edge H₀ H₁),
                  SAT.Lit.neg (Var.Mem H₁ w),
                  SAT.Lit.pos (Var.Mem H₀ w) ]
        have h_trans : clause ∈ transitiveClauses := by
          refine List.mem_flatMap.mpr ⟨H, by simp [Bounds.timesL], ?_⟩
          refine List.mem_flatMap.mpr ⟨H', by simp [Bounds.timesL], ?_⟩
          refine List.mem_map.mpr ?_
          exact ⟨w', WId.mem_allWorlds b w', rfl⟩
        simp only [clause]
        exact List.mem_append.mpr (Or.inr h_trans)
      have hEdgeCNF' := hEdgeCNF
      exact SAT.clause_three_unit σ (cnfEdge b) (Var.Edge H H') (Var.Mem H' w') (Var.Mem H w')
        h_clause_in hEdgeCNF' hEdge hmemH'

    -- Show world ∈ decodePre H using membership hmemH
    split
    · rename_i hFuelH
      simp only [PreHistory.mem_mk, List.mem_map, List.mem_attach, true_and,
        Subtype.exists, List.mem_filter]
      exact ⟨w', ⟨WId.mem_allWorlds b w', hmemH⟩, heq⟩
    · -- H has zero fuel, but we proved Mem(H, w'), contradiction with termination
      rename_i hNoFuelH
      -- If Mem(H, w') is true, then decodePre H should have positive fuel
      -- This is guaranteed by cnfMemRequiresFuel
      exfalso
      have hLevelH : σ (Var.Level H ⟨1, Nat.succ_lt_succ b.posTimes⟩) = true := by
        -- Extract cnfMemRequiresFuel
        have h := (cnfWellFormed_eval_iff b σ).mp hWF
        have hMemReqFuel := h.2.2.2.2.2.2.2.1
        -- cnfMemRequiresFuel contains: Mem(H, w') → Level(H, 1)
        have hAll : ∀ c ∈ (cnfMemRequiresFuel b).clauses, SAT.Clause.eval σ c = true := by
          simpa [SAT.CNF.eval] using hMemReqFuel
        let clause := [SAT.Lit.neg (Var.Mem H w'),
                      SAT.Lit.pos (Var.Level H ⟨1, Nat.succ_lt_succ b.posTimes⟩)]
        have hClauseIn : clause ∈ (cnfMemRequiresFuel b).clauses := by
          unfold cnfMemRequiresFuel
          simp only []
          refine List.mem_flatMap.mpr ⟨H, by simp [Bounds.timesL], ?_⟩
          refine List.mem_map.mpr ?_
          exact ⟨w', WId.mem_allWorlds b w', rfl⟩
        have hClauseTrue := hAll _ hClauseIn
        unfold SAT.Clause.eval at hClauseTrue
        simp only [clause, List.foldl_cons, List.foldl_nil, SAT.Lit.eval,
          hmemH, Bool.false_or] at hClauseTrue
        exact hClauseTrue
      -- Level(H, 1) implies fuelOf H ≥ 1
      have hFuel : 1 ≤ fuelOf b σ H := level_true_le_fuelOf b σ H ⟨1, _⟩ hLevelH
      omega
  · -- H' has zero fuel, so no worlds in it
    simp at hmem


/-! ## Helper Lemmas for Transitivity -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Each decoded prehistory is transitive.
    Uses the Edge transitivity constraints and mem_edge_subset. -/
lemma transitive_at_time (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) :
    isTransitive (decodePre b σ hWF H) := by
  -- Unfold isTransitive: ∀ H', H' ≺− H → H' ⊆ H
  unfold isTransitive
  intro H' hHB
  -- Happens-before means ∃ p e, (p, e, H') ∈ decodePre H
  unfold PreHistory.happensBefore at hHB
  obtain ⟨p, e, hMem⟩ := hHB
  -- Extract world from membership in decodePre
  unfold decodePre at hMem

  -- Handle fuel check
  split at hMem
  · rename_i hFuelH
    -- H has positive fuel
    simp only [PreHistory.mem_mk, List.mem_map, List.mem_attach, true_and,
      Subtype.exists, List.mem_filter] at hMem
    obtain ⟨w, ⟨_, hMemW⟩, hDecoded⟩ := hMem

    -- The decoded world is (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti)
    -- Extract: H' = decodePre b σ hWF w.ti
    have hH'_eq : H' = decodePre b σ hWF w.ti := by
      have : (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti) = (p, e, H') := hDecoded
      injection this with _ h_rest
      injection h_rest with _ h_third
      exact h_third.symm

    -- Show Edge(H, w.ti) is true
    -- We need to show that Mem(H, w) ∧ w.ti = w.ti → Edge(H, w.ti)
    -- This follows from the Edge aggregation clauses in cnfEdge (Structure.lean:84-94)
    have hEdge : σ (Var.Edge H w.ti) = true := by
      classical
      have ⟨_, _, hEdgeCNF, _, _, _, _, _, _, _, _⟩ := (cnfWellFormed_eval_iff b σ).mp hWF
      -- Edge(H, H') holds when ∃ w' with Mem(H, w') and w'.ti = H'
      -- The backward clause: Mem(H, w) → Edge(H, w.ti) (for our w)
      -- Actually, the encoding has: Edge(H, H') ↔ ⋁_{w | w.ti = H'} Mem(H, w)
      -- So Mem(H, w) → Edge(H, w.ti) comes from the backward clauses
      let clause := [SAT.Lit.neg (Var.Mem H w), SAT.Lit.pos (Var.Edge H w.ti)]
      have hClauseIn : clause ∈ (cnfEdge b).clauses := by
        unfold cnfEdge
        -- The backward clauses are at Structure.lean:92-93
        let edgeClauses :=
          (Bounds.timesL b).flatMap fun H₀ =>
            (Bounds.timesL b).flatMap fun H₁ =>
              let witnesses := (WId.allWorlds b).filter (fun w0 => w0.ti == H₁)
                               |>.map (Var.Mem H₀ ·)
              let fwd := SAT.Lit.neg (Var.Edge H₀ H₁) :: witnesses.map SAT.Lit.pos
              let bwd := witnesses.map fun m => [SAT.Lit.neg m, SAT.Lit.pos (Var.Edge H₀ H₁)]
              [fwd] ++ bwd
        have hInBwd : clause ∈ edgeClauses := by
          refine List.mem_flatMap.mpr ⟨H, by simp [Bounds.timesL], ?_⟩
          refine List.mem_flatMap.mpr ⟨w.ti, by simp [Bounds.timesL], ?_⟩
          let witnesses := (WId.allWorlds b).filter (fun w0 => w0.ti == w.ti)
                           |>.map (Var.Mem H ·)
          have hWInWitnesses : Var.Mem H w ∈ witnesses := by
            simp [witnesses]
            exact WId.mem_allWorlds b w
          let bwd := witnesses.map fun m => [SAT.Lit.neg m, SAT.Lit.pos (Var.Edge H w.ti)]
          have hInBwdList : clause ∈ bwd := by
            refine List.mem_map.mpr ?_
            exact ⟨Var.Mem H w, hWInWitnesses, rfl⟩
          simp only [List.mem_append]
          exact Or.inr hInBwdList
        simp only []
        exact List.mem_append.mpr (Or.inl hInBwd)
      have hClauseTrue := SAT.clause_unit_propagation σ (cnfEdge b) clause hClauseIn hEdgeCNF
      unfold SAT.Clause.eval at hClauseTrue
      simp only [clause, List.foldl_cons, List.foldl_nil, SAT.Lit.eval,
        hMemW, Bool.false_or] at hClauseTrue
      exact hClauseTrue

    -- Now apply mem_edge_subset: decodePre w.ti ⊆ decodePre H
    rw [hH'_eq]
    exact mem_edge_subset b σ hWF H w.ti hEdge
  · -- H has zero fuel, contradiction (can't have happened-before from empty prehistory)
    simp at hMem

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Each decoded prehistory is hereditarily transitive.
    Proves by induction on fuel using the structural time fields. -/
lemma hered_at_time (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) :
    isHereditarilyTransitive (decodePre b σ hWF H) := by
  classical
  have views := WF.views b σ hWF
  -- Helper: unpack a predecessor of `decodePre H` into its witness world.
  have extract :
      ∀ {H' : PreHistory (Fin b.nParticipants) (Signature.EventType S)} {H₀ : b.times},
        H' ≺− decodePre b σ hWF H₀ →
        ∃ (w : WId b),
          σ (Var.Mem H₀ w) = true ∧
          H' = decodePre b σ hWF w.ti ∧
          w.ti.val < H₀.val := by
    intro H' H₀ hHB
    unfold PreHistory.happensBefore at hHB
    obtain ⟨p, e, hMem⟩ := hHB
    unfold decodePre at hMem
    split at hMem
    · rename_i hFuel
      simp only [PreHistory.mem_mk, List.mem_map, List.mem_attach, true_and,
        Subtype.exists, List.mem_filter] at hMem
      obtain ⟨w, ⟨_, hMemW⟩, hDecoded⟩ := hMem
      have hH'_eq : H' = decodePre b σ hWF w.ti := by
        have : (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti) = (p, e, H') := hDecoded
        injection this with _ h_rest
        injection h_rest with _ h_third
        exact h_third.symm
      have hAcyclic : w.ti.val < H₀.val := views.acyclic H₀ w hMemW
      exact ⟨w, hMemW, hH'_eq, hAcyclic⟩
    · -- Zero fuel case - empty prehistory has no predecessors
      rename_i hNoFuel
      simp [] at hMem

  have hAll :
      ∀ n, ∀ H₀ : b.times,
        H₀.val ≤ n →
          isHereditarilyTransitive (decodePre b σ hWF H₀) := by
    refine Nat.rec ?base ?step
    · intro H₀ hLe
      have hValZero : H₀.val = 0 :=
        Nat.le_antisymm hLe (Nat.zero_le _)
      refine (isHereditarilyTransitive_unfold _).mpr ?_
      refine ⟨transitive_at_time b σ hWF H₀, ?_⟩
      intro H' hHB
      obtain ⟨w, hMemW, hEq, hLt⟩ := extract hHB
      have hContr : w.ti.val < 0 := by
        simp [hValZero] at hLt
      exact False.elim ((Nat.not_lt_zero (n := w.ti.val)) hContr)
    · intro n IH H₀ hLe
      by_cases hLe' : H₀.val ≤ n
      · exact IH H₀ hLe'
      · have hLt : n < H₀.val := Nat.lt_of_not_ge hLe'
        have hEq : H₀.val = n + 1 := by
          apply Nat.le_antisymm
          · exact hLe
          · exact Nat.succ_le_of_lt hLt
        refine (isHereditarilyTransitive_unfold _).mpr ?_
        refine ⟨transitive_at_time b σ hWF H₀, ?_⟩
        intro H' hHB
        obtain ⟨w, hMemW, hEqPre, hLtTi⟩ := extract hHB
        have hTiLe : w.ti.val ≤ n := by
          have hTiLtSucc : w.ti.val < n + 1 := by
            simpa [hEq] using hLtTi
          exact Nat.lt_succ_iff.mp hTiLtSucc
        have hIH := IH w.ti hTiLe
        simpa [hEqPre] using hIH

  exact hAll H.val H (Nat.le_refl _)

/-- The root prehistory is hereditarily transitive.
    This is the main property needed for Model construction. -/
def heredFromWF (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) :
    isHereditarilyTransitive (decodePre b σ hWF b.root) :=
  hered_at_time b σ hWF b.root

end Encoding
