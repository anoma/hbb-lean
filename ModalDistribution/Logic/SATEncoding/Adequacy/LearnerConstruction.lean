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
import ModalDistribution.Logic.SATEncoding.WFViews

/-!
# Learner Semifilter Construction

This file constructs valid `Semifilter` instances from SAT assignments that satisfy
the learner CNF constraints.

## Main Results

- `learnerOf`: Constructs a `Semifilter` from a WF assignment
- Helper lemmas establishing CNF constraint satisfaction

## Strategy

The construction proceeds by:
1. Extracting minimal quorum bitmasks from the assignment
2. Converting bitmasks to Finsets
3. Proving nonempty, upwardClosed, and pairwiseInter properties
4. Using CNF constraints to ensure validity

## References

- Structure.lean for cnfLearners definition
- Decoder.lean for decodeLearnerData
-/

open ModalDistribution Encoding
open Set

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Learner Construction -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: cnfLearners is satisfied when WF holds. -/
lemma cnfLearners_sat (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ) :
    (cnfLearners b).eval σ = true := by
  -- Extract cnfLearners from the foldl structure
  -- Extract cnfLearners using the extraction lemma
  exact (cnfWellFormed_eval_iff b σ).mp hWF |>.2.2.2.1

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: If a clause is in cnfLearners, it's satisfied under WF. -/
lemma clause_in_cnfLearners_satisfied (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hLearners : (cnfLearners b).eval σ = true)
    (clause : SAT.Clause (Var b))
    (hClause_mem : clause ∈ (cnfLearners b).clauses) :
    SAT.Clause.eval σ clause = true := by
  have hAll : (cnfLearners b).clauses.all (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hLearners
  exact (List.all_eq_true.mp hAll) clause hClause_mem

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: Membership in value index list. -/
lemma valIdx_mem (b : Bounds S) (vIdx : b.valIx) :
    vIdx ∈ Bounds.valIxL b := by
  simp [Bounds.valIxL, List.mem_finRange]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: Mask `0` decodes to the empty Finset. -/
lemma mask_zero_is_empty (b : Bounds S) :
    Encoding.bitmaskToFinset b.nParticipants 0
      = (∅ : Finset (Fin b.nParticipants)) := by
  ext i
  simp [Encoding.bitmaskToFinset_mem_iff]
omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
lemma mapIdxFrom_filterMap_spec (b : Bounds S) (σ : SAT.Assignment (Var b)) :
    ∀ (vars : List (Var b)) (start mask : Nat), mask ∈
        (vars.mapIdxFrom
            (fun i (var : Var b) => if σ var = true then some i else none)
            start).filterMap id →
        ∃ idx : Nat, ∃ hIdx : idx < vars.length, mask = start + idx ∧
          σ (vars.nthLe idx hIdx) = true := by
  classical
  intro vars start mask
  induction vars generalizing start mask with
  | nil =>
      intro h
      simp [List.mapIdxFrom] at h
  | cons var vars ih =>
      intro h
      by_cases hVar : σ var = true
      · simp [List.mapIdxFrom, hVar] at h
        rcases h with hHead | hTail
        · subst hHead
          refine ⟨0, ?_⟩
          refine ⟨by simp, ?_⟩
          refine ⟨by simp, ?_⟩
          simp [List.nthLe, hVar]
        · have hTail' :
            mask ∈
              (vars.mapIdxFrom
                  (fun i (var : Var b) => if σ var = true then some i else none)
                  (start + 1)).filterMap id := by
            refine (List.mem_filterMap.mpr ?_)
            exact ⟨some mask, hTail, rfl⟩
          obtain ⟨idx, h⟩ :=
            ih (start + 1) mask hTail'
          rcases h with ⟨hIdx, hMask, hTrue⟩
          refine ⟨idx + 1, ?_⟩
          refine ⟨by simpa using Nat.succ_lt_succ hIdx, ?_⟩
          refine ⟨?_, ?_⟩
          · simp [hMask, Nat.add_comm, Nat.add_left_comm]
          · simpa [List.nthLe, List.get_cons_succ] using hTrue
      · simp [List.mapIdxFrom, hVar] at h
        have h' :
            mask ∈
              (vars.mapIdxFrom
                  (fun i (var : Var b) => if σ var = true then some i else none)
                  (start + 1)).filterMap id := by
          refine (List.mem_filterMap.mpr ?_)
          exact ⟨some mask, h, rfl⟩
        obtain ⟨idx, h⟩ :=
          ih (start + 1) mask h'
        rcases h with ⟨hIdx, hMask, hTrue⟩
        refine ⟨idx + 1, ?_⟩
        refine ⟨by simpa using Nat.succ_lt_succ hIdx, ?_⟩
        refine ⟨?_, ?_⟩
        · simp [hMask, Nat.add_comm, Nat.add_left_comm]
        · simpa [List.nthLe, List.get_cons_succ] using hTrue

@[simp] lemma disjoint_inter_card_zero {α : Type} [DecidableEq α]
    {s t : Finset α} (hDisj : Disjoint s t) :
    (s ∩ t).card = 0 := by
  classical
  have hEmpty : s ∩ t = (∅ : Finset α) := by
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
    exact (Finset.disjoint_left.mp hDisj hx₁ hx₂)
  simp [hEmpty]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: The no-empty clause for a given index is in the withinIndexClauses for that index. -/
lemma nonempty_clause_in_within (b : Bounds S) (vIdx : b.valIx) :
    [SAT.Lit.neg (Var.MinQ vIdx ∅)] ∈
      (let quorumVars := Var.allMinQ b vIdx
       let minimalityClauses := quorumVars.flatMap fun q1 =>
         quorumVars.filterMap fun q2 =>
           match q1, q2 with
           | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
               if Q2 ⊂ Q1 ∧ Q2 ≠ Q1 then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
           | _, _ => none
       let intersectionClauses := quorumVars.flatMap fun q1 =>
         quorumVars.filterMap fun q2 =>
           match q1, q2 with
           | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
               if (Q1 ∩ Q2).card = 0 ∧ Q1 ≠ Q2 then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
           | _, _ => none
       let noEmptyClauses := quorumVars.filterMap fun q =>
         match q with
         | Var.MinQ _ Q => if Q.card = 0 then some [SAT.Lit.neg q] else none
         | _ => none
       minimalityClauses ++ intersectionClauses ++ noEmptyClauses) := by
  classical
  let quorumVars := Var.allMinQ b vIdx
  let clause := [SAT.Lit.neg (Var.MinQ vIdx ∅)]
  let minimalityClauses :=
    quorumVars.flatMap fun q1 =>
      quorumVars.filterMap fun q2 =>
        match q1, q2 with
        | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
            if Q2 ⊂ Q1 ∧ Q2 ≠ Q1 then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
        | _, _ => none
  let intersectionClauses :=
    quorumVars.flatMap fun q1 =>
      quorumVars.filterMap fun q2 =>
        match q1, q2 with
        | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
            if (Q1 ∩ Q2).card = 0 ∧ Q1 ≠ Q2 then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
        | _, _ => none
  let noEmptyClauses :=
    quorumVars.filterMap fun q =>
      match q with
      | Var.MinQ _ Q => if Q.card = 0 then some [SAT.Lit.neg q] else none
      | _ => none

  have hMaskPos :
      0 < Nat.shiftLeft 1 b.nParticipants := by
    have : 0 < 2 := by decide
    simp [Nat.shiftLeft_eq]
  let maskZero : Fin (Nat.shiftLeft 1 b.nParticipants) := ⟨0, hMaskPos⟩
  have hMask_mem :
      maskZero ∈ List.finRange (Nat.shiftLeft 1 b.nParticipants) :=
    List.mem_finRange maskZero
  have hMask_zero :
      Encoding.bitmaskToFinset b.nParticipants maskZero.val
        = (∅ : Finset (Fin b.nParticipants)) := by
    simpa [maskZero] using mask_zero_is_empty b

  have hVar_mem : Var.MinQ vIdx ∅ ∈ quorumVars := by
    unfold quorumVars Var.allMinQ
    refine List.mem_map.mpr ?_
    refine ⟨maskZero, hMask_mem, ?_⟩
    simp [maskZero, hMask_zero]

  have hClause_noEmpty : clause ∈ noEmptyClauses := by
    unfold noEmptyClauses
    refine List.mem_filterMap.mpr ?_
    refine ⟨Var.MinQ vIdx ∅, hVar_mem, ?_⟩
    simp [clause, Finset.card_empty]

  have hTail :
      clause ∈ intersectionClauses ++ noEmptyClauses :=
    (List.mem_append).2 (Or.inr hClause_noEmpty)

  have hWithin' :
      clause ∈ minimalityClauses ++ (intersectionClauses ++ noEmptyClauses) :=
    (List.mem_append).2 (Or.inr hTail)

  simpa [quorumVars, minimalityClauses, intersectionClauses, noEmptyClauses] using hWithin'

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Auxiliary fact: the variable corresponding to a specific mask is present in `allMinQ`. -/
lemma minq_bitmask_mem_allMinQ (b : Bounds S) (vIdx : b.valIx)
    (mask : Nat) (hMask : mask < Nat.shiftLeft 1 b.nParticipants) :
    Var.MinQ vIdx (Encoding.bitmaskToFinset b.nParticipants mask) ∈ Var.allMinQ b vIdx := by
  classical
  let nParts := b.nParticipants
  let numSubsets := Nat.shiftLeft 1 nParts
  let maskFin : Fin numSubsets := ⟨mask, by simpa [numSubsets] using hMask⟩
  have hMask_mem : maskFin ∈ List.finRange numSubsets :=
    List.mem_finRange maskFin
  unfold Var.allMinQ
  have hIn :
      Var.MinQ vIdx (Encoding.bitmaskToFinset nParts maskFin.val) ∈
        (List.finRange numSubsets).map
          (fun m => Var.MinQ vIdx (Encoding.bitmaskToFinset nParts m.val)) := by
    refine List.mem_map.mpr ?_
    exact ⟨maskFin, hMask_mem, rfl⟩
  simpa [maskFin, nParts] using hIn

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Every MinQ variable appears in allMinQ at the position of its bitmask. -/
lemma minq_var_mem_allMinQ (b : Bounds S) (vIdx : b.valIx)
    (Q : Finset (Fin b.nParticipants)) :
    Var.MinQ vIdx Q ∈ Var.allMinQ b vIdx := by
  classical
  let maskNat := finsetToBitmask Q
  have hMask_lt : maskNat < Nat.shiftLeft 1 b.nParticipants :=
    finsetToBitmask_lt Q
  have hDecode :
      Encoding.bitmaskToFinset b.nParticipants maskNat = Q :=
    finsetToBitmask_inverse Q
  have hMem :=
    minq_bitmask_mem_allMinQ b vIdx maskNat hMask_lt
  simpa [maskNat, hDecode] using hMem

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Rep unit clauses are in cnfLearners (first component). -/
lemma repUnit_clause_in_cnfLearners (b : Bounds S) (v : Signature.Value S)
    (hVal : v ∈ classValues b) :
    [SAT.Lit.pos (Var.Rep (b.findValueIndex v))] ∈ (cnfLearners b).clauses := by
  unfold cnfLearners
  simp
  -- Navigate to repUnitClauses (first component)
  apply Or.inl
  -- Now in repUnitClauses - show our clause is there
  unfold repUnitClauses
  apply List.mem_map.mpr
  use v, hVal

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Gating clauses are in cnfLearners. -/
lemma gating_clause_in_cnfLearners (b : Bounds S) (vIdx : b.valIx)
    (Q : Finset (Fin b.nParticipants)) :
    [SAT.Lit.neg (Var.MinQ vIdx Q), SAT.Lit.pos (Var.Rep vIdx)] ∈ (cnfLearners b).clauses := by
  unfold cnfLearners
  simp
  -- Navigate to gatingClauses (third component: after repUnitClauses and repExoClauses)
  apply Or.inr
  apply Or.inr
  apply Or.inl
  -- Now in gatingClauses - show our clause is there
  unfold gatingClauses
  apply List.mem_flatMap.mpr
  use vIdx
  constructor
  · exact valIdx_mem b vIdx
  · apply List.mem_map.mpr
    use Var.MinQ vIdx Q
    constructor
    · exact minq_var_mem_allMinQ b vIdx Q
    · rfl

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Conditional ALO clauses are in cnfLearners. -/
lemma condAlo_clause_in_cnfLearners (b : Bounds S) (vIdx : b.valIx) :
    (SAT.Lit.neg (Var.Rep vIdx) :: (Var.allMinQ b vIdx).map SAT.Lit.pos) ∈
      (cnfLearners b).clauses := by
  unfold cnfLearners
  simp
  -- Navigate to condAloClauses
  -- (fourth component: after repUnitClauses, repExoClauses, gatingClauses)
  apply Or.inr
  apply Or.inr
  apply Or.inr
  apply Or.inl
  -- Now in condAloClauses - show our clause is there
  unfold condAloClauses
  apply List.mem_map.mpr
  use vIdx
  constructor
  · exact valIdx_mem b vIdx
  · rfl

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Rep exo clauses are in cnfLearners. -/
lemma repExo_clause_in_cnfLearners (b : Bounds S) (v : Signature.Value S)
    (hVal : v ∈ classValues b) (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (SAT.exo ((valueIndices b v).map Var.Rep)).clauses) :
    clause ∈ (cnfLearners b).clauses := by
  unfold cnfLearners
  simp
  -- Navigate to repExoClauses (second component: after repUnitClauses)
  apply Or.inr
  apply Or.inl
  -- Now in repExoClauses - show our clause is there
  unfold repExoClauses
  apply List.mem_flatMap.mpr
  use v, hVal

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Clauses in withinIndexClauses (for a specific index) are in cnfLearners. -/
lemma withinIndex_clause_mem (b : Bounds S) (vIdx : b.valIx) (clause : SAT.Clause (Var b))
    (hClause : clause ∈
        (let quorumVars := Var.allMinQ b vIdx
         let minimalityClauses := quorumVars.flatMap fun q1 =>
           quorumVars.filterMap fun q2 =>
             match q1, q2 with
             | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
                 if Q2 ⊂ Q1 ∧ Q2 ≠ Q1 then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
             | _, _ => none
         let intersectionClauses := quorumVars.flatMap fun q1 =>
           quorumVars.filterMap fun q2 =>
             match q1, q2 with
             | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
                 if (Q1 ∩ Q2).card = 0 ∧ Q1 ≠ Q2
                 then some [SAT.Lit.neg q1, SAT.Lit.neg q2]
                 else none
             | _, _ => none
         let noEmptyClauses := quorumVars.filterMap fun q =>
           match q with
           | Var.MinQ _ Q => if Q.card = 0 then some [SAT.Lit.neg q] else none
           | _ => none
         minimalityClauses ++ intersectionClauses ++ noEmptyClauses)) :
    clause ∈ (cnfLearners b).clauses := by
  unfold cnfLearners
  simp
  -- Navigate to withinIndexClauses
  -- (fifth component: after repUnitClauses, repExoClauses, gatingClauses, condAloClauses)
  apply Or.inr
  apply Or.inr
  apply Or.inr
  apply Or.inr
  -- Now in withinIndexClauses - show our clause is there
  unfold withinIndexClauses
  apply List.mem_flatMap.mpr
  use vIdx
  constructor
  · exact valIdx_mem b vIdx
  · exact hClause

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Empty quorum is never a minimal quorum under WF. -/
lemma empty_not_minq (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hLearners : (cnfLearners b).eval σ = true)
    (vIdx : b.valIx) :
    σ (Var.MinQ vIdx ∅) = false := by
  classical
  let clause := [SAT.Lit.neg (Var.MinQ vIdx ∅)]

  -- Clause membership inside withinIndexClauses for vIdx.
  have hWithin :
      clause ∈
        (let quorumVars := Var.allMinQ b vIdx
         let minimalityClauses := quorumVars.flatMap fun q1 =>
           quorumVars.filterMap fun q2 =>
             match q1, q2 with
             | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
                 if Q2 ⊂ Q1 ∧ Q2 ≠ Q1 then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
             | _, _ => none
         let intersectionClauses := quorumVars.flatMap fun q1 =>
           quorumVars.filterMap fun q2 =>
             match q1, q2 with
             | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
                 if (Q1 ∩ Q2).card = 0 ∧ Q1 ≠ Q2
                 then some [SAT.Lit.neg q1, SAT.Lit.neg q2]
                 else none
             | _, _ => none
         let noEmptyClauses := quorumVars.filterMap fun q =>
           match q with
           | Var.MinQ _ Q => if Q.card = 0 then some [SAT.Lit.neg q] else none
           | _ => none
         minimalityClauses ++ intersectionClauses ++ noEmptyClauses) :=
    nonempty_clause_in_within (b := b) (vIdx := vIdx)

  -- Promote to the full learner CNF clauses using the helper lemma
  have hClause_mem : clause ∈ (cnfLearners b).clauses :=
    withinIndex_clause_mem b vIdx clause hWithin

  -- Clause satisfaction enforces the literal `¬MinQ(vIdx, ∅)`.
  have hClauseEval := clause_in_cnfLearners_satisfied b σ hLearners clause hClause_mem
  unfold SAT.Clause.eval at hClauseEval
  simpa [clause, SAT.Lit.eval] using hClauseEval

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma value_mem_classValues_of_mem (b : Bounds S) (v : Signature.Value S)
    (h : v ∈ (List.finRange b.nVals).map (Bounds.values b).get) :
    v ∈ classValues b := by
  unfold classValues
  exact List.mem_dedup.mpr h

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Every value is in classValues due to values_complete. -/
lemma all_values_in_classValues (b : Bounds S) (v : Signature.Value S) :
    v ∈ classValues b := by
  rcases b.values_complete v with ⟨idx, hIdx⟩
  apply value_mem_classValues_of_mem
  exact List.mem_map.mpr ⟨idx, List.mem_finRange _, hIdx⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mem_valueIndices_iff (b : Bounds S) (v : Signature.Value S) (idx : b.valIx) :
    idx ∈ valueIndices b v ↔ idx ∈ List.finRange b.nVals ∧ b.values.get idx = v := by
  classical
  unfold valueIndices
  constructor
  · intro h
    simp only [List.mem_filterMap] at h
    rcases h with ⟨i, hRange, hIf⟩
    by_cases hVal : b.values.get i = v
    · simp [hVal] at hIf
      rcases hIf with rfl
      exact ⟨hRange, hVal⟩
    · have : False := by simp [hVal] at hIf
      exact (this.elim)
  · intro h
    rcases h with ⟨hRange, hVal⟩
    simp [List.mem_filterMap, hVal]

lemma find?_some_true_bool {α} (xs : List α) (p : α → Bool) {x} :
    xs.find? p = some x → p x = true := by
  intro h
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
      unfold List.find? at h
      cases hhd : p hd with
      | false =>
          have h' : tl.find? p = some x := by
            simpa [hhd] using h
          exact ih h'
      | true =>
          have hx : hd = x := by
            simpa [hhd] using h
          simp [hx.symm, hhd]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
def trivialLearnerSemifilter (b : Bounds S) : Semifilter (Fin b.nParticipants) :=
{ quorums := {O | Set.univ ⊆ O},
  nonempty := by
    refine ⟨Set.univ, ?_⟩
    intro _ _
    trivial,
  upwardClosed := by
    intro O O' hO hSubset
    exact subset_trans hO hSubset,
  pairwiseInter := by
    intro O O' hO hO'
    classical
    let p : Fin b.nParticipants := ⟨0, b.posParticipants⟩
    have hpO : p ∈ O := hO (Set.mem_univ _)
    have hpO' : p ∈ O' := hO' (Set.mem_univ _)
    exact Semifilter.intersects_of_mem hpO hpO' }

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Gating clause membership: `¬MinQ(vIdx,Q) ∨ Rep(vIdx)` appears in `cnfLearners`. -/
lemma gating_clause_mem (b : Bounds S) (vIdx : b.valIx)
    (Q : Finset (Fin b.nParticipants)) :
    [SAT.Lit.neg (Var.MinQ vIdx Q), SAT.Lit.pos (Var.Rep vIdx)]
      ∈ (cnfLearners b).clauses := by
  classical
  let quorumVars := Var.allMinQ b vIdx
  let clause := [SAT.Lit.neg (Var.MinQ vIdx Q), SAT.Lit.pos (Var.Rep vIdx)]
  have hVar_mem : Var.MinQ vIdx Q ∈ quorumVars :=
    minq_var_mem_allMinQ b vIdx Q

  -- Membership in the local map for this index.
  have hClause_gating :
      clause ∈ (Var.allMinQ b vIdx).map
        (fun v =>
          match v with
          | Var.MinQ _ _ => [SAT.Lit.neg v, SAT.Lit.pos (Var.Rep vIdx)]
          | _            => []) := by
    refine List.mem_map.mpr ?_
    refine ⟨Var.MinQ vIdx Q, hVar_mem, ?_⟩
    simp [clause]

  -- Lift to gatingClauses flatMap.
  have hClause_gatingClauses :
      clause ∈ (Bounds.valIxL b).flatMap fun i =>
        (Var.allMinQ b i).map fun v =>
          match v with
          | Var.MinQ _ _ => [SAT.Lit.neg v, SAT.Lit.pos (Var.Rep i)]
          | _            => [] := by
    refine List.mem_flatMap.mpr ?_
    refine ⟨vIdx, valIdx_mem b vIdx, ?_⟩
    simpa using hClause_gating

  -- Use the helper lemma
  exact gating_clause_in_cnfLearners b vIdx Q

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: The disjoint-quorum clause for a given index is in the withinIndexClauses. -/
lemma disjoint_clause_in_within (b : Bounds S) (vIdx : b.valIx)
    (Q1 Q2 : Finset (Fin b.nParticipants))
    (hDisj : Disjoint Q1 Q2) (hNe : Q1 ≠ Q2) :
    [SAT.Lit.neg (Var.MinQ vIdx Q1), SAT.Lit.neg (Var.MinQ vIdx Q2)] ∈
      (have quorumVars := Var.allMinQ b vIdx
       have minimalityClauses := quorumVars.flatMap fun q1 =>
         quorumVars.filterMap fun q2 =>
           match q1, q2 with
           | Var.MinQ _ Q1', Var.MinQ _ Q2' =>
               if Q2' ⊂ Q1' ∧ Q2' ≠ Q1' then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
           | _, _ => none
       have intersectionClauses := quorumVars.flatMap fun q1 =>
         quorumVars.filterMap fun q2 =>
           match q1, q2 with
           | Var.MinQ _ Q1', Var.MinQ _ Q2' =>
               if (Q1' ∩ Q2').card = 0 ∧ Q1' ≠ Q2'
               then some [SAT.Lit.neg q1, SAT.Lit.neg q2]
               else none
           | _, _ => none
       have noEmptyClauses := quorumVars.filterMap fun q =>
         match q with
         | Var.MinQ _ Q => if Q.card = 0 then some [SAT.Lit.neg q] else none
         | _ => none
       minimalityClauses ++ intersectionClauses ++ noEmptyClauses) := by
  classical
  let quorumVars := Var.allMinQ b vIdx
  let clause := [SAT.Lit.neg (Var.MinQ vIdx Q1), SAT.Lit.neg (Var.MinQ vIdx Q2)]
  let minimalityClauses :=
    quorumVars.flatMap fun q1 =>
      quorumVars.filterMap fun q2 =>
        match q1, q2 with
        | Var.MinQ _ Q1', Var.MinQ _ Q2' =>
            if Q2' ⊂ Q1' ∧ Q2' ≠ Q1' then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
        | _, _ => none
  let intersectionClauses :=
    quorumVars.flatMap fun q1 =>
      quorumVars.filterMap fun q2 =>
        match q1, q2 with
        | Var.MinQ _ Q1', Var.MinQ _ Q2' =>
            if (Q1' ∩ Q2').card = 0 ∧ Q1' ≠ Q2' then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
        | _, _ => none
  let noEmptyClauses :=
    quorumVars.filterMap fun q =>
      match q with
      | Var.MinQ _ Q => if Q.card = 0 then some [SAT.Lit.neg q] else none
      | _ => none

  have hQ1_mem : Var.MinQ vIdx Q1 ∈ quorumVars :=
    minq_var_mem_allMinQ (b := b) (vIdx := vIdx) (Q := Q1)
  have hQ2_mem : Var.MinQ vIdx Q2 ∈ quorumVars :=
    minq_var_mem_allMinQ (b := b) (vIdx := vIdx) (Q := Q2)

  have hCard : (Q1 ∩ Q2).card = 0 :=
    disjoint_inter_card_zero hDisj

  have hClause_inter :
      clause ∈ intersectionClauses := by
    unfold intersectionClauses
    refine List.mem_flatMap.mpr ?_
    refine ⟨Var.MinQ vIdx Q1, hQ1_mem, ?_⟩
    refine List.mem_filterMap.mpr ?_
    refine ⟨Var.MinQ vIdx Q2, hQ2_mem, ?_⟩
    simp [clause, hCard, hNe]

  have hTail :
      clause ∈ intersectionClauses ++ noEmptyClauses :=
    (List.mem_append).2 (Or.inl hClause_inter)

  simp only [List.append_assoc]
  exact (List.mem_append).2 (Or.inr hTail)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma minq_disjoint_clause_mem (b : Bounds S) (vIdx : b.valIx)
    (Q1 Q2 : Finset (Fin b.nParticipants))
    (hDisj : Disjoint Q1 Q2) (hNe : Q1 ≠ Q2) :
    [SAT.Lit.neg (Var.MinQ vIdx Q1), SAT.Lit.neg (Var.MinQ vIdx Q2)]
      ∈ (cnfLearners b).clauses := by
  classical
  let clause := [SAT.Lit.neg (Var.MinQ vIdx Q1), SAT.Lit.neg (Var.MinQ vIdx Q2)]

  -- Membership inside the per-index within block.
  have hWithin :
      clause ∈
        (have quorumVars := Var.allMinQ b vIdx
         have minimalityClauses := quorumVars.flatMap fun q1 =>
           quorumVars.filterMap fun q2 =>
             match q1, q2 with
             | Var.MinQ _ Q1', Var.MinQ _ Q2' =>
                 if Q2' ⊂ Q1' ∧ Q2' ≠ Q1' then some [SAT.Lit.neg q1, SAT.Lit.neg q2] else none
             | _, _ => none
         have intersectionClauses := quorumVars.flatMap fun q1 =>
           quorumVars.filterMap fun q2 =>
             match q1, q2 with
             | Var.MinQ _ Q1', Var.MinQ _ Q2' =>
                 if (Q1' ∩ Q2').card = 0 ∧ Q1' ≠ Q2'
                 then some [SAT.Lit.neg q1, SAT.Lit.neg q2]
                 else none
             | _, _ => none
         have noEmptyClauses := quorumVars.filterMap fun q =>
           match q with
           | Var.MinQ _ Q => if Q.card = 0 then some [SAT.Lit.neg q] else none
           | _ => none
         minimalityClauses ++ intersectionClauses ++ noEmptyClauses) :=
    disjoint_clause_in_within (b := b) (vIdx := vIdx)
      (Q1 := Q1) (Q2 := Q2) hDisj hNe

  -- Promote to the concatenated learner clause list using the helper lemma
  exact withinIndex_clause_mem b vIdx clause hWithin

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Disjoint minimal quorums are forbidden under WF. -/
lemma disjoint_minq_false (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hLearners : (cnfLearners b).eval σ = true) (vIdx : b.valIx)
    (Q1 Q2 : Finset (Fin b.nParticipants))
    (hDisj : Disjoint Q1 Q2)
    (hQ1 : σ (Var.MinQ vIdx Q1) = true)
    (hQ2 : σ (Var.MinQ vIdx Q2) = true) :
    False := by
  classical
  have hNe : Q1 ≠ Q2 := by
    intro hEq
    subst hEq
    have hDisjSelf : Disjoint Q1 Q1 := by simpa using hDisj
    have hEmpty : Q1 = (∅ : Finset (Fin b.nParticipants)) := by
      have hDisj_left := Finset.disjoint_left.mp hDisjSelf
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro a ha
      exact hDisj_left ha ha
    have hZero := empty_not_minq b σ hLearners vIdx
    have hFalse : σ (Var.MinQ vIdx Q1) = false := by
      simpa [hEmpty] using hZero
    have hContr : False := by
      simp [hFalse] at hQ1
    exact hContr

  let clause := [SAT.Lit.neg (Var.MinQ vIdx Q1), SAT.Lit.neg (Var.MinQ vIdx Q2)]
  have hClause_mem_raw := minq_disjoint_clause_mem b vIdx Q1 Q2 hDisj hNe
  have hClause_mem : clause ∈ (cnfLearners b).clauses := by
    simpa [clause] using hClause_mem_raw

  have hClauseEval :=
    clause_in_cnfLearners_satisfied b σ hLearners clause hClause_mem
  unfold SAT.Clause.eval at hClauseEval
  exact
    (by simp [clause, SAT.Lit.eval, hQ1, hQ2] at hClauseEval)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If Q is in the decoded minimal quorums list, then σ (Var.MinQ vIdx Q) = true. -/
lemma minq_in_decoded_imp_true (b : Bounds S) (σ : SAT.Assignment (Var b))
    (vIdx : b.valIx) (Q : Finset (Fin b.nParticipants))
    (hQ : Q ∈ (decodeLearnerData b σ).minimalQuorumsIx vIdx) :
    σ (Var.MinQ vIdx Q) = true := by
  classical
  unfold decodeLearnerData at hQ
  simp only [List.mem_filterMap] at hQ
  obtain ⟨var, hVar_in, hVar_eq⟩ := hQ
  -- var must be Var.MinQ vIdx Q' for some Q'
  unfold Var.allMinQ at hVar_in
  obtain ⟨maskFin, _, rfl⟩ := List.mem_map.mp hVar_in
  -- hVar_eq shows: if σ var = true then some (bitmaskToFinset ...) else none = some Q
  by_cases h : σ (Var.MinQ vIdx (bitmaskToFinset b.nParticipants maskFin.val)) = true
  · -- In this case, some (bitmaskToFinset ...) = some Q, so Q = bitmaskToFinset ...
    simp only [h, ↓reduceIte] at hVar_eq
    injection hVar_eq with hEq
    rw [← hEq]
    exact h
  · -- In this case, none = some Q, contradiction
    simp only [h] at hVar_eq
    -- hVar_eq : none = some Q, which is impossible
    cases hVar_eq

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- **Gating extraction**: If MinQ(vIdx, Q) is true, then Rep(vIdx) must be true.
    This follows from the gating clause (¬MinQ(i,Q)) ∨ Rep(i) in cnfLearners. -/
lemma minq_implies_rep (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hLearners : (cnfLearners b).eval σ = true)
    (vIdx : b.valIx) (Q : Finset (Fin b.nParticipants))
    (hMinQ : σ (Var.MinQ vIdx Q) = true) :
    σ (Var.Rep vIdx) = true := by
  classical
  -- The gating clause [¬MinQ(vIdx,Q), Rep(vIdx)] is in cnfLearners
  let gatingClause : SAT.Clause (Var b) :=
    [SAT.Lit.neg (Var.MinQ vIdx Q), SAT.Lit.pos (Var.Rep vIdx)]

  -- Show this clause is in cnfLearners using the helper lemma
  have hClause_mem : gatingClause ∈ (cnfLearners b).clauses :=
    gating_clause_in_cnfLearners b vIdx Q

  -- Clause is satisfied under σ
  have hClauseEval := clause_in_cnfLearners_satisfied b σ hLearners gatingClause hClause_mem

  -- Evaluate the clause: (¬MinQ(vIdx,Q)) ∨ Rep(vIdx)
  -- Since MinQ(vIdx,Q) = true, we need Rep(vIdx) = true
  unfold gatingClause at hClauseEval
  simpa [SAT.Clause.eval, SAT.Lit.eval, hMinQ] using hClauseEval

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The conditional ALO ensures at least one MinQ variable is true when Rep(vIdx) holds.
    Under WF, exactly one representative is chosen per value class. -/
lemma alo_minq_exists_ix (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hLearners : (cnfLearners b).eval σ = true)
    (vIdx : b.valIx)
    (hRep : σ (Var.Rep vIdx) = true) :
    ∃ Q : Finset (Fin b.nParticipants), σ (Var.MinQ vIdx Q) = true := by
  classical
  -- Strategy: The conditional ALO clause [¬Rep(vIdx) ∨ MinQ(vIdx,Q₁) ∨ ... ∨ MinQ(vIdx,Qₙ)]
  -- is in cnfLearners. Since Rep(vIdx) = true, at least one MinQ must be true.

  -- The conditional ALO clause for vIdx
  set condAloClause := SAT.Lit.neg (Var.Rep vIdx) :: (Var.allMinQ b vIdx).map SAT.Lit.pos

  -- This clause is in cnfLearners using the helper lemma
  have hClauseIn : condAloClause ∈ (cnfLearners b).clauses :=
    condAlo_clause_in_cnfLearners b vIdx

  -- The clause is satisfied
  have hClauseSat : SAT.Clause.eval σ condAloClause = true :=
    clause_in_cnfLearners_satisfied b σ hLearners condAloClause hClauseIn

  -- Convert to "any" form: at least one literal is true
  have hAny : condAloClause.any (SAT.Lit.eval σ) = true :=
    SAT.Clause.eval_eq_any σ condAloClause ▸ hClauseSat

  -- Extract a true literal
  obtain ⟨lit, hLitIn, hLitTrue⟩ := List.any_eq_true.mp hAny

  -- lit is either ¬Rep(vIdx) or Lit.pos var for some var in allMinQ
  cases List.mem_cons.mp hLitIn with
  | inl hRepLit =>
      -- lit = ¬Rep(vIdx), but this would mean Rep(vIdx) = false
      rw [hRepLit] at hLitTrue
      simp [SAT.Lit.eval, hRep] at hLitTrue
  | inr hMinQLit =>
      -- lit is in the MinQ literals
      obtain ⟨var, hVarIn, rfl⟩ := List.mem_map.mp hMinQLit
      simp [SAT.Lit.eval] at hLitTrue

      -- var must be Var.MinQ vIdx Q for some Q
      have : ∃ Q, var = Var.MinQ vIdx Q := by
        unfold Var.allMinQ at hVarIn
        obtain ⟨maskFin, _, rfl⟩ := List.mem_map.mp hVarIn
        exact ⟨bitmaskToFinset b.nParticipants maskFin.val, rfl⟩

      obtain ⟨Q, rfl⟩ := this
      exact ⟨Q, hLitTrue⟩

/-- Index-keyed learner: build semifilter from decoded minimal quorums for a value index.

    This construction assumes that the index `vIdx` is the representative selected by the
    CNF (i.e. `σ (Var.Rep vIdx) = true`). Value-keyed `learnerOf` supplies this witness by
    invoking `pickRep`. -/
noncomputable def learnerIxOf
    (b : Bounds S)
    (σ : SAT.Assignment (Var b))
    (hWF : WF b σ)
    (vIdx : b.valIx) (hRep : σ (Var.Rep vIdx) = true) :
    Semifilter (Fin b.nParticipants) :=
  let ld := decodeLearnerData b σ
  let mins := ld.minimalQuorumsIx vIdx
  let minSets : Set (Set (Fin b.nParticipants)) :=
    { Q' | ∃ Qf ∈ mins, Q' = (Qf : Set (Fin b.nParticipants)) }
  { quorums := { O | ∃ Q ∈ minSets, Q ⊆ O },
    nonempty := by
      -- From conditional ALO clause on MinQ(vIdx, ·) in cnfLearners and hWF
      have hLearners := cnfLearners_sat b σ hWF
      obtain ⟨Q, hQ_true⟩ := alo_minq_exists_ix b σ hLearners vIdx hRep

      -- Q is in mins because MinQ is true
      have hQ_in_mins : Q ∈ mins := by
        unfold mins ld decodeLearnerData
        simp only [List.mem_filterMap]
        let mask := finsetToBitmask Q
        have hMaskLt : mask < Nat.shiftLeft 1 b.nParticipants := finsetToBitmask_lt Q
        let maskFin : Fin (Nat.shiftLeft 1 b.nParticipants) := ⟨mask, hMaskLt⟩
        have hVarEq : Var.MinQ vIdx (bitmaskToFinset b.nParticipants mask) = Var.MinQ vIdx Q := by
          congr
          exact finsetToBitmask_inverse Q
        refine ⟨Var.MinQ vIdx (bitmaskToFinset b.nParticipants mask), ?_, ?_⟩
        · unfold Var.allMinQ
          simp only [List.mem_map]
          refine ⟨maskFin, ?_, rfl⟩
          exact List.mem_finRange _
        · simp only [hVarEq, hQ_true, ↓reduceIte]
          exact congr_arg some (finsetToBitmask_inverse Q)

      -- So Q ∈ minSets
      have hQ_minSet : (Q : Set (Fin b.nParticipants)) ∈ minSets := by
        exact ⟨Q, hQ_in_mins, rfl⟩

      -- And Q ∈ quorums (via Q ⊆ Q)
      exact Set.nonempty_def.mpr ⟨(Q : Set _), (Q : Set _), hQ_minSet, Set.Subset.rfl⟩,
    upwardClosed := by
      intro O₁ O₂ hO hsub
      rcases hO with ⟨Q, hQmin, hQsub⟩
      exact ⟨Q, hQmin, Set.Subset.trans hQsub hsub⟩,
    pairwiseInter := by
      -- From disjoint pairs forbidden clauses in cnfLearners and hWF
      intro O1 O2 hO1 hO2

      -- Extract minimal quorums Q1, Q2
      obtain ⟨Q1_set, hQ1_minSet, hQ1_O1⟩ := hO1
      obtain ⟨Q2_set, hQ2_minSet, hQ2_O2⟩ := hO2
      obtain ⟨Q1, hQ1_mins, rfl⟩ := hQ1_minSet
      obtain ⟨Q2, hQ2_mins, rfl⟩ := hQ2_minSet

      -- Assume by contradiction they're disjoint
      by_contra hEmpty

      -- Then Q1 ∩ Q2 = ∅
      have hQ1Q2_empty : (Q1 : Set (Fin b.nParticipants))
                         ∩ (Q2 : Set (Fin b.nParticipants)) = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        intro ⟨hx1, hx2⟩
        have hxO1 : x ∈ O1 := hQ1_O1 hx1
        have hxO2 : x ∈ O2 := hQ2_O2 hx2
        have hxInter : x ∈ O1 ∩ O2 := ⟨hxO1, hxO2⟩
        exact hEmpty ⟨x, hxInter⟩

      -- Convert to Finset disjointness
      have hDisj : Disjoint Q1 Q2 := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext p
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨hp1, hp2⟩
        have hp_inter : (p : Fin b.nParticipants) ∈ (Q1 : Set _) ∩ (Q2 : Set _) := ⟨hp1, hp2⟩
        rw [hQ1Q2_empty] at hp_inter
        exact hp_inter

      -- Q1 and Q2 are in the decoded data, so their MinQ variables are true
      have hQ1_true : σ (Var.MinQ vIdx Q1) = true :=
        minq_in_decoded_imp_true b σ vIdx Q1 hQ1_mins

      have hQ2_true : σ (Var.MinQ vIdx Q2) = true :=
        minq_in_decoded_imp_true b σ vIdx Q2 hQ2_mins

      -- Apply disjoint_minq_false to get contradiction
      have hLearners := cnfLearners_sat b σ hWF
      exact disjoint_minq_false b σ hLearners vIdx Q1 Q2 hDisj hQ1_true hQ2_true }

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Under WF, the representative chosen by `pickRep` evaluates to true for values
present in the bounds enumeration. -/
lemma pickRep_rep_true (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hLearners : (cnfLearners b).eval σ = true) {v : Signature.Value S}
    (hVal : v ∈ classValues b) :
    σ (Var.Rep (pickRep b σ v)) = true := by
  classical
  -- Use the exo encoding to find a true representative
  set indices := valueIndices b v
  -- Clauses selecting the representative for this value belong to cnfLearners.
  have hClause_mem :
      ∀ clause ∈ (SAT.exo (indices.map Var.Rep)).clauses,
        clause ∈ (cnfLearners b).clauses := by
    intro clause hClause
    exact repExo_clause_in_cnfLearners b v hVal clause hClause
  -- Evaluate the representative exo CNF under σ.
  have hClauseEval :
      ∀ clause ∈ (SAT.exo (indices.map Var.Rep)).clauses,
        SAT.Clause.eval σ clause = true := by
    intro clause hClause
    exact clause_in_cnfLearners_satisfied b σ hLearners clause (hClause_mem clause hClause)
  have hExoEval : (SAT.exo (indices.map Var.Rep)).eval σ = true := by
    have := List.all_eq_true.mpr hClauseEval
    simpa [SAT.CNF.eval] using this
  -- Extract the unique representative index.
  have hExactlyOne :=
    exo_eval_exactlyOne (σ := fun v => σ v) (xs := indices.map Var.Rep) hExoEval
  obtain ⟨hAtLeast, _⟩ := hExactlyOne
  rcases hAtLeast with ⟨repVar, hVar_mem, hVar_true⟩
  obtain ⟨idxRep, hIdxRep_mem, rfl⟩ := List.mem_map.mp hVar_mem
  have hIdxRep_true : σ (Var.Rep idxRep) = true := hVar_true
  -- The finder used in pickRep succeeds with this witness.
  have hFindWitness : ∃ i ∈ indices, σ (Var.Rep i) = true :=
    ⟨idxRep, hIdxRep_mem, hIdxRep_true⟩
  cases hFind : indices.find? (fun i => σ (Var.Rep i)) with
  | some j =>
      have hTrue : σ (Var.Rep j) = true :=
        find?_some_true_bool indices (fun i => σ (Var.Rep i)) hFind
      have hPick : pickRep b σ v = j := by
        unfold pickRep
        simp [indices, hFind]
      have : σ (Var.Rep (pickRep b σ v)) = true := by
        simpa [hPick] using hTrue
      exact this
  | none =>
      have hAllFalse :=
        Encoding.find?_none_forall (xs := indices) (p := fun i => σ (Var.Rep i)) hFind
      rcases hFindWitness with ⟨i, hi_mem, hi_true⟩
      have hi_false := hAllFalse i hi_mem
      have : False := by
        have hContr := hi_false
        simp [hi_true] at hContr
      exact False.elim this

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- **One-hot uniqueness**: If two indices in the same value class both have Rep true,
    they must be equal. This follows from the AMO (at-most-one) part of the exo encoding. -/
lemma rep_unique (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hLearners : (cnfLearners b).eval σ = true)
    {v : Signature.Value S} (hVal : v ∈ classValues b)
    {i j : b.valIx}
    (hi : i ∈ valueIndices b v) (hj : j ∈ valueIndices b v)
    (hRep_i : σ (Var.Rep i) = true) (hRep_j : σ (Var.Rep j) = true) :
    i = j := by
  classical
  -- The exo encoding for value v ensures at most one Rep is true
  let indices := valueIndices b v
  have hExo_mem : (SAT.exo (indices.map Var.Rep)).clauses ⊆ (cnfLearners b).clauses := by
    intro clause hClause
    exact repExo_clause_in_cnfLearners b v hVal clause hClause

  -- All clauses in exo are satisfied
  have hExo_eval : (SAT.exo (indices.map Var.Rep)).eval σ = true := by
    have hAll : (SAT.exo (indices.map Var.Rep)).clauses.all (SAT.Clause.eval σ) = true := by
      refine List.all_eq_true.mpr ?_
      intro clause hClause
      have hMem := hExo_mem hClause
      unfold SAT.CNF.eval at hLearners
      have hLearners_clauses := List.all_eq_true.mp hLearners
      exact hLearners_clauses clause hMem
    simpa [SAT.CNF.eval] using hAll

  -- Extract pairwise exclusivity from exo
  have hExactlyOne := exo_eval_exactlyOne (σ := fun v => σ v) (xs := indices.map Var.Rep) hExo_eval
  obtain ⟨_, hPairwise⟩ := hExactlyOne

  -- Apply pairwise exclusivity to Rep i and Rep j
  have hi_map : Var.Rep i ∈ indices.map Var.Rep := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hj_map : Var.Rep j ∈ indices.map Var.Rep := List.mem_map.mpr ⟨j, hj, rfl⟩

  by_contra hNeq
  -- If i ≠ j, then Rep i ≠ Rep j (by injectivity)
  have hRepNeq : Var.Rep i ≠ Var.Rep j := by
    intro hContr
    injection hContr with hEq
    exact hNeq hEq
  -- By pairwise exclusivity, if Rep i = true and Rep i ≠ Rep j, then Rep j = false
  have hRep_j_false := hPairwise hRepNeq hi_map hj_map hRep_i
  -- But we have Rep j = true, contradiction
  simp [hRep_j] at hRep_j_false

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- `findValueIndex` actually returns an index whose value is `v`. -/
lemma findValueIndex_value (b : Bounds S) (v : Signature.Value S) :
    b.values.get (b.findValueIndex v) = v := by
  classical
  unfold Bounds.findValueIndex
  cases hFind : (List.finRange b.nVals).find? (fun i => b.values.get i = v) with
  | some idx =>
      -- find? returns some idx when decide (b.values.get idx = v) = true
      have hPred : decide (b.values.get idx = v) = true :=
        find?_some_true_bool (List.finRange b.nVals) (fun i => decide (b.values.get i = v)) hFind
      exact decide_eq_true_iff.mp hPred
  | none =>
      rcases b.values_complete v with ⟨idx, hIdx⟩
      have hMem : idx ∈ List.finRange b.nVals := List.mem_finRange _
      have hAllFalse :=
        Encoding.find?_none_forall (xs := List.finRange b.nVals)
          (p := fun i => decide (b.values.get i = v)) hFind
      have hContr := hAllFalse idx hMem
      simp [hIdx] at hContr

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- With `repUnitClauses`, the representative for value `v` is forced to `findValueIndex v`. -/
lemma pickRep_eq_findValueIndex (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hLearners : (cnfLearners b).eval σ = true) {v : Signature.Value S}
    (hVal : v ∈ classValues b) :
    pickRep b σ v = b.findValueIndex v := by
  classical
  -- Rep(findValueIndex v) is a unit clause - use the helper lemma
  have hRepUnit : σ (Var.Rep (b.findValueIndex v)) = true := by
    have hClause_in :
        [SAT.Lit.pos (Var.Rep (b.findValueIndex v))] ∈ (cnfLearners b).clauses :=
      repUnit_clause_in_cnfLearners b v hVal
    have hAll := List.all_eq_true.mp (by simpa [SAT.CNF.eval] using hLearners)
    have hEval := hAll _ hClause_in
    simpa [SAT.Clause.eval, SAT.Lit.eval] using hEval

  have hFind_mem : b.findValueIndex v ∈ valueIndices b v := by
      unfold valueIndices
      simp [findValueIndex_value (b := b) (v := v)]

  unfold pickRep
  cases hFind : (valueIndices b v).find? (fun i => σ (Var.Rep i)) with
  | some i =>
      have hi_mem : i ∈ valueIndices b v := List.mem_of_find?_eq_some hFind
      have hRep_i : σ (Var.Rep i) = true :=
        find?_some_true_bool (valueIndices b v) (fun i => σ (Var.Rep i)) hFind
      -- Uniqueness of Rep forces i = findValueIndex v
      have hEq := rep_unique (b := b) (σ := σ) hLearners hVal hi_mem hFind_mem hRep_i hRepUnit
      simp [hEq]
  | none =>
      -- impossible, since Rep(findValueIndex v) is true
      have hAllFalse :=
        Encoding.find?_none_forall (xs := valueIndices b v)
          (p := fun i => σ (Var.Rep i)) hFind
      have hFalse := hAllFalse (b.findValueIndex v) hFind_mem
      simp [hRepUnit] at hFalse

/-- Value-keyed learner: uses the chosen representative index.

    The representative is selected by the one-hot Rep variables in cnfLearners.
    This eliminates the need for cross-index reasoning and guarantees nonemptiness. -/
noncomputable def learnerOf
    (b : Bounds S)
    (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) :
    Signature.Value S → Semifilter (Fin b.nParticipants) :=
  fun v =>
    by
      classical
      have hLearners := cnfLearners_sat b σ hWF
      by_cases hVal : v ∈ classValues b
      · let i := pickRep b σ v
        have hRep : σ (Var.Rep i) = true := pickRep_rep_true b σ hLearners hVal
        exact learnerIxOf b σ hWF i hRep
      · exact trivialLearnerSemifilter b

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Bridge (index-keyed): From true MinQ vIdx Q to semantic membership in learnerIxOf. -/
lemma MinQ_bridge_ix (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (vIdx : b.valIx) (Q : Finset b.participants)
    (hMinQ : σ (Var.MinQ vIdx Q) = true) :
    (Q : Set (Fin b.nParticipants))
      ∈ (learnerIxOf b σ hWF vIdx
          (minq_implies_rep b σ (cnfLearners_sat b σ hWF) vIdx Q hMinQ)).quorums := by
  classical
  have hLearners := cnfLearners_sat b σ hWF
  have hRep : σ (Var.Rep vIdx) = true := minq_implies_rep b σ hLearners vIdx Q hMinQ
  have hQ_in_mins : Q ∈ (decodeLearnerData b σ).minimalQuorumsIx vIdx := by
    unfold decodeLearnerData
    simp only [List.mem_filterMap]
    let mask := finsetToBitmask Q
    have hMaskLt : mask < Nat.shiftLeft 1 b.nParticipants := finsetToBitmask_lt Q
    let maskFin : Fin (Nat.shiftLeft 1 b.nParticipants) := ⟨mask, hMaskLt⟩
    have hMaskEq : bitmaskToFinset b.nParticipants mask = Q := by
      simpa [mask] using finsetToBitmask_inverse Q
    have hVarEq :
        Var.MinQ vIdx (bitmaskToFinset b.nParticipants mask) = Var.MinQ vIdx Q := by
      simp [hMaskEq]
    refine ⟨Var.MinQ vIdx (bitmaskToFinset b.nParticipants mask), ?_, ?_⟩
    · unfold Var.allMinQ
      exact List.mem_map.mpr ⟨maskFin, List.mem_finRange _, rfl⟩
    · simp [hMinQ, hMaskEq]
  unfold learnerIxOf
  set mins := (decodeLearnerData b σ).minimalQuorumsIx vIdx
  let minSets : Set (Set (Fin b.nParticipants)) :=
    { Q' | ∃ Qf ∈ mins, Q' = (Qf : Set (Fin b.nParticipants)) }
  have hQmin : (Q : Set _) ∈ minSets := by
    refine ⟨Q, hQ_in_mins, rfl⟩
  exact ⟨(Q : Set _), hQmin, Set.Subset.rfl⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Bridge (value-keyed): From true MinQ vIdx Q to semantic membership in learnerOf. -/
lemma MinQ_bridge (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (vIdx : b.valIx) (Q : Finset b.participants)
    (hMinQ : σ (Var.MinQ vIdx Q) = true) :
    (Q : Set b.participants) ∈ (learnerOf b σ hWF (b.values.get vIdx)).quorums := by
  classical
  have hLearners := cnfLearners_sat b σ hWF
  have hRep : σ (Var.Rep vIdx) = true := minq_implies_rep b σ hLearners vIdx Q hMinQ
  have hVal : b.values.get vIdx ∈ classValues b := by
    unfold classValues
    simp only [List.mem_dedup, List.mem_map]
    exact ⟨vIdx, by simp, rfl⟩
  unfold learnerOf
  simp only [hVal, ↓reduceDIte]
  have hvIdx_in : vIdx ∈ valueIndices b (b.values.get vIdx) := by
    unfold valueIndices
    simp only [List.mem_filterMap, List.mem_finRange]
    exact ⟨vIdx, ⟨by trivial, by simp⟩⟩
  have hPickRep : pickRep b σ (b.values.get vIdx) = vIdx := by
    have hLearnersTrue : (cnfLearners b).eval σ = true := hLearners
    have hValMem : b.values.get vIdx ∈ classValues b := by
      unfold classValues
      simp [List.mem_dedup, List.mem_map]
    have hPickEq := pickRep_eq_findValueIndex (b := b) (σ := σ) hLearnersTrue hValMem
    have hFindMem : b.findValueIndex (b.values.get vIdx) ∈ valueIndices b (b.values.get vIdx) := by
      unfold valueIndices
      simp [findValueIndex_value (b := b) (v := b.values.get vIdx)]
    have hRepFind : σ (Var.Rep (b.findValueIndex (b.values.get vIdx))) = true := by
      have hClause_in :
          [SAT.Lit.pos (Var.Rep (b.findValueIndex (b.values.get vIdx)))] ∈
            (cnfLearners b).clauses :=
        repUnit_clause_in_cnfLearners b (b.values.get vIdx) hValMem
      have hAll := List.all_eq_true.mp (by simpa [SAT.CNF.eval] using hLearnersTrue)
      have hEval := hAll _ hClause_in
      simpa [SAT.Clause.eval, SAT.Lit.eval] using hEval
    have hUnique := rep_unique b σ hLearnersTrue hValMem hFindMem hvIdx_in hRepFind hRep
    simpa [hPickEq] using hUnique
  simp [hPickRep]
  exact MinQ_bridge_ix b σ hWF vIdx Q hMinQ

end Encoding
