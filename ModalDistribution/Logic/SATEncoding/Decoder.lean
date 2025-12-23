import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.WFViews
import ModalDistribution.Logic.SATEncoding.ListLemmas

/-!
# Model Extraction from SAT Assignments

This file implements computable model extraction from satisfying assignments.
The key challenge is that `PreHistory` is a recursive structure, but we cannot
use mutual recursion directly because Lean's termination checker doesn't see
the CNF acyclic constraints.

## Solution: Fuel-Based Recursion

We use a fuel parameter to bound recursion depth:
- `decodePreFuel σ fuel H` returns the depth-`fuel` truncation of the prehistory at `H`
- At `fuel = 0`, we return `PreHistory.empty` (base case)
- The top-level `decodePre` uses `b.nTimes` as fuel, which is sufficient for acyclic structures

## Adequacy

The adequacy proof (in Adequacy.lean) will show that:
1. `decodePreFuel` is monotonic in fuel
2. For WF assignments, `b.nTimes` fuel captures the entire structure (no cycles)
3. `decodePreFuel σ b.nTimes H = decodePreFuel σ (b.nTimes + 1) H`

## References

- Plan.md section "Decoder Termination (CRITICAL)" for detailed explanation
-/

open ModalDistribution

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Canonical Decoding

With canonical decoding, world attributes (participant, event, time) are determined
by the structural fields of WId (w.p, w.ei, w.ti) rather than SAT variables.
This eliminates the need for pick* functions and their correctness lemmas.
-/

/-! ## Fuel Bounds -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- `fuelOf` returns a value bounded by `b.nTimes`. -/
lemma fuelOf_le_nTimes (b : Bounds S) (σ : SAT.Assignment (Var b)) (ti : b.times) :
    fuelOf b σ ti ≤ b.nTimes := by
  -- fuelOf searches in finRange (b.nTimes.succ), so any returned Fin value
  -- satisfies val < b.nTimes.succ, hence val ≤ b.nTimes. In the none case, returns 0.
  classical
  set o :=
      (List.finRange (b.nTimes.succ)).reverse.find?
        (fun j => σ (Var.Level ti j) = true) with ho
  have hpred :
      (fun j => decide (σ (Var.Level ti j) = true)) =
        fun j => σ (Var.Level ti j) := by
    funext j
    cases hσ : σ (Var.Level ti j) <;> simp
  cases ho_o : o with
  | none =>
      have hnone :
          List.find? (fun j => σ (Var.Level ti j))
              (List.finRange (b.nTimes + 1)).reverse = none := by
        simpa [ho, hpred, Nat.succ_eq_add_one] using ho_o
      have hfuel : fuelOf b σ ti = 0 := by
        simp [fuelOf, Nat.succ_eq_add_one, hnone]
      simp [hfuel]
  | some j =>
      have hsome :
          List.find? (fun j0 => σ (Var.Level ti j0))
              (List.finRange (b.nTimes + 1)).reverse = some j := by
        simpa [ho, hpred, Nat.succ_eq_add_one] using ho_o
      have hfuel : fuelOf b σ ti = j.val := by
        simp [fuelOf, Nat.succ_eq_add_one, hsome]
      have hj : j.val ≤ b.nTimes := Nat.lt_succ_iff.mp j.isLt
      simpa [hfuel] using hj

namespace Fin

lemma mem_finRange {n : Nat} (i : Fin n) : i ∈ List.finRange n := by
  classical
  simp [List.finRange, List.mem_ofFn]

end Fin

namespace List

lemma finRange_reverse (n : Nat) :
    (List.finRange n).reverse = (List.finRange n).map Fin.rev := by
  -- Proof using List.ofFn
  have h1 : List.finRange n = List.ofFn (n := n) id := by
    apply List.ext_getElem
    · simp [List.length_finRange, List.length_ofFn]
    · intro i hi1 hi2
      simp [List.getElem_finRange, List.getElem_ofFn]
  have h2 : (List.ofFn (n := n) id).reverse = List.ofFn (n := n) (fun i => Fin.rev i) := by
    apply List.ext_getElem
    · simp [List.length_reverse, List.length_ofFn]
    · intro i hi1 hi2
      simp [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Fin.rev]
      omega
  have h3 : (List.ofFn (n := n) fun i => Fin.rev i) = (List.ofFn (n := n) id).map Fin.rev := by
    apply List.ext_getElem
    · simp [List.length_ofFn]
    · intro i hi1 hi2
      simp [List.getElem_ofFn]
  rw [h1, h2, h3, ← h1]

end List

/-- In an ascending `finRange`, `find?` returns the minimal index satisfying the predicate. -/
lemma find_finRange_min {n : Nat} {p : Fin (n + 1) → Bool} {j : Fin (n + 1)}
    (hFind : (List.finRange (n + 1)).find? (fun k => p k) = some j) :
    ∀ {k : Fin (n + 1)}, p k = true → j ≤ k := by
  classical
  revert p j
  induction' n with n ih <;> intro p j hFind k hk
  · -- Base case: finRange 1 = [0]
    -- In Fin 1, only element is 0, so both j and k must be 0
    have hj : j = 0 := by
      have : j.val < 1 := j.isLt
      omega
    have hk : k = 0 := by
      have : k.val < 1 := k.isLt
      omega
    subst hj hk
    exact le_rfl
  · -- Inductive step: split off the head (0) and recurse on the remainder
    by_cases hp0 : p 0 = true
    · -- If p 0 is true, then j = 0 (since find? returns the first match)
      have hj : j = 0 := by
        have : List.finRange (n + 2) = (0 : Fin (n + 2))
                :: (List.finRange (n + 1)).map Fin.succ := by
          simp [List.finRange_succ]
        rw [this] at hFind
        simp [hp0] at hFind
        exact hFind.symm
      subst hj
      exact Fin.zero_le _
    · -- If p 0 is false, find? continues to the tail
      have hsplit :
          List.finRange (n + 2) =
            (0 : Fin (n + 2)) ::
              (List.finRange (n + 1)).map Fin.succ := by
        simp [ List.finRange_succ]
      rw [hsplit] at hFind
      rw [List.find?_cons] at hFind
      simp only [hp0, List.find?_map] at hFind
      rcases hFindEx : Option.map_eq_some_iff.mp hFind with ⟨j', hFind', rfl⟩
      -- Any witness must be a succ value (since p 0 = false)
      have hk_ne : k ≠ 0 := by
        intro hk0
        have : p (0 : Fin (n + 2)) = true := by
          simpa [hk0] using hk
        exact absurd this hp0
      obtain ⟨k', hk'⟩ := Fin.eq_succ_of_ne_zero hk_ne
      subst hk'
      -- Apply induction on the smaller predicate
      have hk_small : (fun t => p (Fin.succ t)) k' = true := by
        simpa using hk
      have hleSmall := ih hFind' hk_small
      -- Lift the inequality through Fin.succ
      simpa using (Fin.succ_le_succ_iff.mpr hleSmall)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If a level is true at `k`, then `fuelOf` realises a corresponding maximal witness. -/
lemma fuelOf_findWitness (b : Bounds S) (σ : SAT.Assignment (Var b))
    (ti : b.times) (k : Fin (b.nTimes.succ))
    (hk : σ (Var.Level ti k) = true) :
    ∃ j : Fin (b.nTimes.succ),
      (List.finRange (b.nTimes.succ)).find?
          (fun x => σ (Var.Level ti (Fin.rev x)) = true) = some j ∧
        fuelOf b σ ti = (Fin.rev j).val ∧
        σ (Var.Level ti (Fin.rev j)) = true := by
  classical
  let p := fun x : Fin (b.nTimes.succ) =>
    σ (Var.Level ti (Fin.rev x)) = true
  have hWitness : p (Fin.rev k) = true := by
    simp [p, hk]
  have hmem : Fin.rev k ∈ List.finRange (b.nTimes.succ) :=
    Fin.mem_finRange _
  have hIsSome :
      ((List.finRange (b.nTimes.succ)).find? (fun x => decide (p x))).isSome := by
    refine (List.find?_isSome).2 ?_
    use Fin.rev k, hmem
    simp [hWitness]
  cases hFind :
      (List.finRange (b.nTimes.succ)).find? (fun x => decide (p x)) with
  | none =>
      have : False := by
        simp [hFind] at hIsSome
      exact this.elim
  | some j =>
      have hLevel : σ (Var.Level ti (Fin.rev j)) = true := by
        have := List.find?_some hFind
        simp [p] at this
        exact this
      -- Rewrite the definition of `fuelOf` via the mapped search.
      have hRev :
          (List.finRange (b.nTimes.succ)).reverse =
            (List.finRange (b.nTimes.succ)).map Fin.rev :=
        List.finRange_reverse (b.nTimes.succ)
      have hfuel :
          fuelOf b σ ti = (Fin.rev j).val := by
        have hFindProp :
            (List.finRange (b.nTimes.succ)).find?
                (fun x => decide (σ (Var.Level ti (Fin.rev x)) = true)) = some j := by
          simpa [p] using hFind
        -- Convert decide version to plain Bool version
        have hFindPropBool :
            (List.finRange (b.nTimes.succ)).find?
                (fun x => σ (Var.Level ti (Fin.rev x))) = some j := by
          convert hFindProp using 2
          ext x
          cases hσ : σ (Var.Level ti (Fin.rev x)) <;> simp
        have hFindMapEq :=
          (List.find?_map (l := List.finRange (b.nTimes.succ))
            (f := Fin.rev) (p := fun x => σ (Var.Level ti x)))
        have hFindMap :
            ((List.finRange (b.nTimes.succ)).map Fin.rev).find?
                (fun x => σ (Var.Level ti x)) = some (Fin.rev j) := by
          have hRHS :
              Option.map Fin.rev
                  (List.find? (fun x => σ (Var.Level ti (Fin.rev x)))
                    (List.finRange (b.nTimes.succ))) = some (Fin.rev j) := by
            simp [hFindPropBool]
          exact hFindMapEq.trans hRHS
        have hFindRev :
            ((List.finRange (b.nTimes.succ)).reverse).find?
                (fun x => σ (Var.Level ti x)) = some (Fin.rev j) := by
          simpa [hRev] using hFindMap
        -- Now unfold fuelOf and use hFindRev
        unfold fuelOf
        simp only [Nat.succ_eq_add_one]
        -- The find? with Prop version should match the Bool version
        convert_to (match ((List.finRange (b.nTimes + 1)).reverse).find?
            (fun x => σ (Var.Level ti x)) with
          | some k => k.val
          | none => 0) = (Fin.rev j).val
        · congr 1
          ext x
          cases hσ : σ (Var.Level ti x) <;> simp
        simp [hFindRev]
      refine ⟨j, ?_, hfuel, hLevel⟩
      simp

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Any true `Level` literal lies beneath the decoded `fuelOf`. -/
lemma level_true_le_fuelOf (b : Bounds S) (σ : SAT.Assignment (Var b))
    (ti : b.times) (k : Fin (b.nTimes.succ))
    (hk : σ (Var.Level ti k) = true) :
    k.val ≤ fuelOf b σ ti := by
  classical
  obtain ⟨j, hFind, hfuel, _⟩ := fuelOf_findWitness b σ ti k hk
  let p := fun x : Fin (b.nTimes.succ) =>
    σ (Var.Level ti (Fin.rev x)) = true
  have hMin :
      j ≤ Fin.rev k :=
    find_finRange_min (n := b.nTimes) (p := p) (j := j) hFind
      (by simp [p, hk])
  -- Use the order-reversing property of `Fin.rev`
  have hFin :
      k ≤ Fin.rev j := by
    have hRevRev : Fin.rev (Fin.rev k) = k := Fin.rev_rev k
    rw [← hRevRev]
    exact Fin.rev_le_rev.mpr hMin
  -- Translate to natural numbers via the recorded fuel value
  simpa [hfuel, Fin.le_def] using (Fin.le_def.mp hFin)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Extract cnfLevel_decrease constraint from WF. -/
lemma level_decrease_from_wf (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) :
    (cnfLevel_decrease b).eval σ = true := by
  -- Extract from WF using cnfWellFormed_eval_iff
  -- cnfWellFormed = cnfAcyclic ∧ cnfReach ∧ cnfEdge ∧ cnfLearners ∧
  --   cnfLevel_monotone ∧ cnfLevel_decrease ∧ ...
  have h := (cnfWellFormed_eval_iff b σ).mp hWF
  exact h.2.2.2.2.2.1

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Extract cnfLevel_monotone constraint from WF. -/
lemma level_monotone_from_wf (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) :
    (cnfLevel_monotone b).eval σ = true := by
  -- Extract from WF using cnfWellFormed_eval_iff
  have h := (cnfWellFormed_eval_iff b σ).mp hWF
  exact h.2.2.2.2.1

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Extract cnfLevel_max_bound constraint from WF. -/
lemma level_max_bound_from_wf (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) :
    (cnfLevel_max_bound b).eval σ = true := by
  -- Extract from WF using cnfWellFormed_eval_iff
  have h := (cnfWellFormed_eval_iff b σ).mp hWF
  exact h.2.2.2.2.2.2.1

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Extract cnfMemRequiresFuel constraint from WF. -/
lemma mem_requires_fuel_from_wf (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) :
    (cnfMemRequiresFuel b).eval σ = true := by
  -- Extract from WF using cnfWellFormed_eval_iff
  have h := (cnfWellFormed_eval_iff b σ).mp hWF
  exact h.2.2.2.2.2.2.2.1

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Maximum fuel bound: Level(ti, b.nTimes) = false under WF.
    This ensures fuelOf returns values strictly less than b.nTimes. -/
lemma level_max_false (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (ti : b.times) :
    σ (Var.Level ti ⟨b.nTimes, Nat.lt_succ_self _⟩) = false := by
  -- Extract the CNF constraint
  have hCNF := level_max_bound_from_wf b σ hWF
  unfold cnfLevel_max_bound at hCNF
  -- The clause for ti is: [¬Level(ti, b.nTimes)]
  have hAll :
      ((Bounds.timesL b).map fun ti' =>
          [SAT.Lit.neg (Var.Level ti' ⟨b.nTimes, Nat.lt_succ_self _⟩)]).all
        (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hCNF
  let clause := [SAT.Lit.neg (Var.Level ti ⟨b.nTimes, Nat.lt_succ_self _⟩)]
  have hClauseMem :
      clause ∈
        (Bounds.timesL b).map fun ti' =>
          [SAT.Lit.neg (Var.Level ti' ⟨b.nTimes, Nat.lt_succ_self _⟩)] := by
    refine List.mem_map.2 ?_
    exact ⟨ti, by simp [Bounds.timesL], rfl⟩
  have hClauseEval : SAT.Clause.eval σ clause = true := by
    have hAllClauses := List.all_eq_true.mp hAll
    exact hAllClauses _ hClauseMem
  -- Simplify the clause evaluation
  have : (!σ (Var.Level ti ⟨b.nTimes, Nat.lt_succ_self _⟩)) = true := by
    unfold clause at hClauseEval
    simpa [SAT.Clause.eval, SAT.Lit.eval, List.foldl] using hClauseEval
  cases h : σ (Var.Level ti ⟨b.nTimes, Nat.lt_succ_self _⟩) with
  | false => rfl
  | true => simp [h] at this

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Monotonicity: If `Level(ti, j.succ)` then `Level(ti, j)`.
    This follows from the prefix-closed property of fuel levels. -/
lemma level_monotone_succ (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (ti : b.times)
    (j : Fin b.nTimes) (hj : j.succ < b.nTimes.succ)
    (hLevel : σ (Var.Level ti ⟨j.succ, hj⟩) = true) :
    σ (Var.Level ti ⟨j, Nat.lt_succ_of_lt j.isLt⟩) = true := by
  -- Extract the CNF constraint
  have hCNF := level_monotone_from_wf b σ hWF
  unfold cnfLevel_monotone at hCNF
  -- The clause we need is: ¬Level(ti, j.succ) ∨ Level(ti, j)
  have hAll :
      ((Bounds.timesL b).flatMap fun ti' =>
          let baseClause := [SAT.Lit.pos (Var.Level ti' ⟨0, Nat.zero_lt_succ _⟩)]
          let monotoneClauses := (List.range b.nTimes).filterMap fun j' =>
            if h : j' < b.nTimes ∧ j'.succ < b.nTimes.succ then
              some [ SAT.Lit.neg (Var.Level ti' ⟨j'.succ, h.2⟩)
                   , SAT.Lit.pos (Var.Level ti' ⟨j', Nat.lt_succ_of_lt h.1⟩) ]
            else none
          baseClause :: monotoneClauses).all (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hCNF
  let clause :=
    [ SAT.Lit.neg (Var.Level ti ⟨j.succ, hj⟩)
    , SAT.Lit.pos (Var.Level ti ⟨j, Nat.lt_succ_of_lt j.isLt⟩) ]
  have hClauseMem :
      clause ∈
        (Bounds.timesL b).flatMap fun ti' =>
          let baseClause := [SAT.Lit.pos (Var.Level ti' ⟨0, Nat.zero_lt_succ _⟩)]
          let monotoneClauses := (List.range b.nTimes).filterMap fun j' =>
            if h : j' < b.nTimes ∧ j'.succ < b.nTimes.succ then
              some [ SAT.Lit.neg (Var.Level ti' ⟨j'.succ, h.2⟩)
                   , SAT.Lit.pos (Var.Level ti' ⟨j', Nat.lt_succ_of_lt h.1⟩) ]
            else none
          baseClause :: monotoneClauses := by
    refine List.mem_flatMap.2 ?_
    refine ⟨ti, ?_, ?_⟩
    · simp [Bounds.timesL]
    · refine List.mem_cons.mpr (Or.inr ?_)
      refine List.mem_filterMap.2 ?_
      refine ⟨(j : Nat), ?_, ?_⟩
      · simp [List.mem_range]
      · have hcond : (j : Nat) < b.nTimes ∧ (j : Nat).succ < b.nTimes.succ := by
          exact ⟨j.isLt, hj⟩
        simp [clause, hcond, Nat.succ_eq_add_one]
  have hClauseEval : SAT.Clause.eval σ clause = true := by
    have hAllClauses := List.all_eq_true.mp hAll
    exact hAllClauses _ hClauseMem
  -- Simplify the clause evaluation to extract the conclusion.
  have hClauseBool :
      (!σ (Var.Level ti ⟨j.succ, hj⟩) ||
        σ (Var.Level ti ⟨j, Nat.lt_succ_of_lt j.isLt⟩)) = true := by
    unfold clause at hClauseEval
    simpa [SAT.Clause.eval, SAT.Lit.eval, List.foldl,
      Bool.or_assoc, Bool.or_left_comm, Bool.or_comm,
      Nat.succ_eq_add_one]
      using hClauseEval
  -- Unit propagation: since Level(ti, j.succ) = true, Level(ti, j) must be true
  cases hσj : σ (Var.Level ti ⟨j, Nat.lt_succ_of_lt j.isLt⟩) with
  | true => rfl
  | false =>
    -- If Level(ti, j) = false, then by hClauseBool, ¬Level(ti, j.succ) must be true
    -- But we have Level(ti, j.succ) = true (from hLevel), contradiction
    have hContr : (!true || false) = true := by
      convert hClauseBool using 2
      · rw [hLevel]
      · exact hσj.symm
    simp at hContr

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If `Mem(H,w)` and `Level(w.ti, j)`, then `Level(H, j+1)`.
    This follows from the strict increase constraint which ensures parents have
    more fuel than children. -/
lemma level_increase_mem (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (w : WId b)
    (j : Fin b.nTimes) (hj : j.succ < b.nTimes.succ)
    (hMem : σ (Var.Mem H w) = true)
    (hLevel : σ (Var.Level w.ti ⟨j, Nat.lt_succ_of_lt j.isLt⟩) = true) :
    σ (Var.Level H ⟨j.succ, hj⟩) = true := by
  -- Extract the CNF constraint (now using strict increase)
  have hCNF := level_decrease_from_wf b σ hWF
  unfold cnfLevel_decrease at hCNF
  -- The clause we need is:
  -- ¬Mem(H,w) ∨ ¬Level(w.ti, j) ∨ Level(H, j+1)
  -- Since Mem and Level(w.ti, j) are true, Level(H, j+1) must be true
  have hAll :
      ((Bounds.timesL b).flatMap fun H' =>
          (WId.allWorlds b).flatMap fun w' =>
            (List.range b.nTimes).filterMap fun j' =>
              if h : j' < b.nTimes ∧ j'.succ < b.nTimes.succ then
                some
                  [SAT.Lit.neg (Var.Mem H' w')
                  , SAT.Lit.neg (Var.Level w'.ti ⟨j', Nat.lt_succ_of_lt h.1⟩)
                  , SAT.Lit.pos (Var.Level H' ⟨j'.succ, h.2⟩)]
              else
                none).all (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hCNF
  let clause :=
    [ SAT.Lit.neg (Var.Mem H w)
    , SAT.Lit.neg (Var.Level w.ti ⟨j, Nat.lt_succ_of_lt j.isLt⟩)
    , SAT.Lit.pos (Var.Level H ⟨j.succ, hj⟩) ]
  have hClauseMem :
      clause ∈
        (Bounds.timesL b).flatMap fun H' =>
          (WId.allWorlds b).flatMap fun w' =>
            (List.range b.nTimes).filterMap fun j' =>
              if h : j' < b.nTimes ∧ j'.succ < b.nTimes.succ then
                some
                  [SAT.Lit.neg (Var.Mem H' w')
                  , SAT.Lit.neg (Var.Level w'.ti ⟨j', Nat.lt_succ_of_lt h.1⟩)
                  , SAT.Lit.pos (Var.Level H' ⟨j'.succ, h.2⟩)]
              else
                none := by
    refine List.mem_flatMap.2 ?_
    refine ⟨H, ?_, ?_⟩
    · simp [Bounds.timesL]
    · refine List.mem_flatMap.2 ?_
      refine ⟨w, ?_, ?_⟩
      · exact WId.mem_allWorlds b w
      · refine List.mem_filterMap.2 ?_
        refine ⟨(j : Nat), ?_, ?_⟩
        · simp [List.mem_range]
        · have hcond :
            (j : Nat) < b.nTimes ∧ (j : Nat).succ < b.nTimes.succ := by
            exact ⟨j.isLt, hj⟩
          simp [clause, hcond, Nat.succ_eq_add_one]
  have hClauseEval : SAT.Clause.eval σ clause = true := by
    have hAllClauses := List.all_eq_true.mp hAll
    exact hAllClauses _ hClauseMem
  -- Simplify the clause evaluation to extract the conclusion.
  have hClauseBool :
      (!σ (Var.Mem H w) || !σ (Var.Level w.ti ⟨j, Nat.lt_succ_of_lt j.isLt⟩) ||
        σ (Var.Level H ⟨j.succ, hj⟩)) = true := by
    -- Expand the clause to a boolean disjunction.
    unfold clause at hClauseEval
    simpa [SAT.Clause.eval, SAT.Lit.eval, List.foldl,
      Bool.or_assoc, Bool.or_left_comm, Bool.or_comm,
      Nat.succ_eq_add_one]
      using hClauseEval
  have hClauseBool' :
      (!σ (Var.Level w.ti ⟨j, Nat.lt_succ_of_lt j.isLt⟩) ||
        σ (Var.Level H ⟨j.succ, hj⟩)) = true := by
    have := hClauseBool
    simpa [hMem, Bool.false_or, Bool.or_assoc] using this
  -- Show that the parent level literal must be true.
  cases hp : σ (Var.Level H ⟨j.succ, hj⟩) with
  | true => rfl
  | false =>
    -- If Level(H, j.succ) = false, then by hClauseBool', Level(w.ti, j) must be false
    -- But we have Level(w.ti, j) = true (from hLevel), contradiction
    have hContr : (!true || false) = true := by
      convert hClauseBool' using 2
      · rw [hLevel]
      · exact hp.symm
    simp at hContr

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If `Mem(H,w)` is true and `fuelOf(H) > 0`, then `fuelOf(w.ti) < fuelOf(H)`.
    This strict inequality is crucial for termination of the decoder.

    This follows from the Level decrease constraint: if Level(w.ti, j+1) then Level(H, j).
    Since fuelOf finds the maximum level, and the child's max level j+1 implies the parent
    has level j, we get strict decrease when the child has positive fuel. -/
lemma fuelOf_strict_decrease_mem (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (w : WId b)
    (hMem : σ (Var.Mem H w) = true)
    (hFuel : 0 < fuelOf b σ H) :
    fuelOf b σ w.ti < fuelOf b σ H := by
  classical
  set childFuel := fuelOf b σ w.ti
  set parentFuel := fuelOf b σ H
  -- If child has zero fuel, we're done
  by_cases hChildZero : childFuel = 0
  · omega
  -- Child has positive fuel
  have hChildPos : 0 < childFuel := Nat.pos_of_ne_zero hChildZero
  -- Find the witness level for child fuel
  let q := fun j : Fin (b.nTimes.succ) => σ (Var.Level w.ti j) = true
  have hFuelDef :
      childFuel =
        match (List.finRange (b.nTimes.succ)).reverse.find? q with
        | some j => j.val
        | none => 0 := rfl
  have hFindSome :
      (List.finRange (b.nTimes.succ)).reverse.find? q ≠ none := by
    intro hnone
    have : childFuel = 0 := by simp [hFuelDef, hnone]
    omega
  obtain ⟨kChild, hFind⟩ := Option.ne_none_iff_exists.mp hFindSome
  have hkLevel : σ (Var.Level w.ti kChild) = true := by
    have hFind' : ((List.finRange (b.nTimes.succ)).reverse).find?
        (fun b_1 => decide (q b_1)) = some kChild := by
      exact hFind.symm
    have := Encoding.find?_some_prop _ _ hFind'
    exact this.2
  have hkFuel : childFuel = kChild.val := by
    rw [hFuelDef, hFind.symm]
  -- For strict inequality, we need to apply the constraint directly to kChild
  -- Check if kChild < b.nTimes (constraint applies) or kChild = b.nTimes (maximum fuel)
  by_cases hkBound : kChild.val < b.nTimes
  · -- Case 1: kChild < b.nTimes, can apply the increase constraint
    -- Apply constraint to kChild: Level(w.ti, kChild) → Level(H, kChild.succ)
    have hkSuccBound : kChild.val.succ < b.nTimes.succ := by omega
    -- Cast kChild.val to Fin b.nTimes for the lemma application
    let jCast : Fin b.nTimes := ⟨kChild.val, hkBound⟩
    have hkLevel' : σ (Var.Level w.ti ⟨jCast, Nat.lt_succ_of_lt jCast.isLt⟩) = true := by
      have : (⟨jCast, Nat.lt_succ_of_lt jCast.isLt⟩ : Fin (b.nTimes.succ)) = kChild := by
        simp [jCast]
      rw [this]
      exact hkLevel
    have hParentLevelSucc :
        σ (Var.Level H ⟨jCast.succ, hkSuccBound⟩) = true :=
      level_increase_mem b σ hWF H w jCast hkSuccBound hMem hkLevel'
    -- Parent fuel is at least kChild.succ
    have hkSuccLe : kChild.val.succ ≤ parentFuel := by
      have hParentLevelSucc' : σ (Var.Level H ⟨kChild.val.succ, hkSuccBound⟩) = true := by
        have : (⟨jCast.succ, hkSuccBound⟩ : Fin (b.nTimes.succ)) =
            ⟨kChild.val.succ, hkSuccBound⟩ := by
          simp [jCast]
        rw [← this]
        exact hParentLevelSucc
      exact level_true_le_fuelOf b σ H ⟨kChild.val.succ, hkSuccBound⟩ hParentLevelSucc'
    -- Therefore childFuel = kChild < kChild.succ ≤ parentFuel
    calc childFuel
        = kChild.val := hkFuel
      _ < kChild.val.succ := Nat.lt_succ_self _
      _ ≤ parentFuel := hkSuccLe
  · -- Case 2: kChild.val = b.nTimes (maximum fuel)
    -- This case is impossible under WF due to cnfLevel_max_bound constraint
    have hkMax : kChild.val = b.nTimes := by omega
    -- kChild = ⟨b.nTimes, _⟩
    have hkEq : kChild = ⟨b.nTimes, Nat.lt_succ_self _⟩ := by
      ext; exact hkMax
    -- But Level(w.ti, ⟨b.nTimes, _⟩) = false by max bound constraint
    have hMaxFalse := level_max_false b σ hWF w.ti
    -- Yet we have Level(w.ti, kChild) = true
    rw [hkEq] at hkLevel
    -- Contradiction
    rw [hkLevel] at hMaxFalse
    cases hMaxFalse

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If `Mem(H,w)` is true, then `fuelOf(w.ti) < fuelOf(H) + 2`. -/
lemma fuelOf_decrease_mem (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (w : WId b)
    (hMem : σ (Var.Mem H w) = true) :
    fuelOf b σ w.ti < fuelOf b σ H + 2 := by
  -- By level_increase_mem, if Level(w.ti, k) then Level(H, k+1)
  -- So fuelOf(w.ti) ≤ fuelOf(H) + 1 < fuelOf(H) + 2
  classical
  set childFuel := fuelOf b σ w.ti
  set parentFuel := fuelOf b σ H
  by_cases hSmall : childFuel ≤ 1
  · have hTwo : parentFuel + 2 ≥ 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
    have hChildLt : childFuel < 2 := Nat.lt_of_le_of_lt hSmall (by decide : 2 ≤ 2)
    exact lt_of_lt_of_le hChildLt hTwo
  · -- `childFuel` is at least 2
    have hOneLt : 1 < childFuel := Nat.lt_of_not_ge hSmall
    have hChildPos : childFuel ≠ 0 := ne_of_gt (Nat.lt_trans (Nat.succ_pos _) hOneLt)
    -- Analyse the search performed inside `fuelOf`
    let q := fun j : Fin (b.nTimes.succ) => σ (Var.Level w.ti j) = true
    have hFuelDef :
        childFuel =
          match (List.finRange (b.nTimes.succ)).reverse.find? q with
          | some j => j.val
          | none => 0 := rfl
    have hFindSome :
        (List.finRange (b.nTimes.succ)).reverse.find? q ≠ none := by
      intro hnone
      have : childFuel = 0 := by
        simp [hFuelDef, hnone]
      exact hChildPos this
    cases hFind :
        (List.finRange (b.nTimes.succ)).reverse.find? q with
    | none =>
        exfalso
        exact hFindSome hFind
    | some kChild =>
        have hkLevel : σ (Var.Level w.ti kChild) = true := by
          simpa [q] using List.find?_some hFind
        have hkFuel : childFuel = kChild.val := by
          simp [hFuelDef, hFind]
        -- Since `childFuel > 1`, the witness is non-zero
        have hk_ne_zero : kChild ≠ 0 := by
          intro hk
          have : childFuel = 0 := by
            simp [hkFuel, hk]
          exact hChildPos this
        obtain ⟨pred, hkSucc⟩ := Fin.eq_succ_of_ne_zero hk_ne_zero
        -- Interpret `kChild` as `pred.succ`
        have hkFuelSucc : childFuel = pred.succ.val := by
          simp [hkFuel, hkSucc]
        have hjSucc : pred.succ < b.nTimes.succ := by
          simp
        have hLevelSucc :
            σ (Var.Level w.ti ⟨pred.succ, hjSucc⟩) = true := by
          simpa [hkSucc] using hkLevel
        -- Use monotonicity to get Level(w.ti, pred) from Level(w.ti, pred.succ)
        have hLevelPred : σ (Var.Level w.ti ⟨pred, Nat.lt_succ_of_lt pred.isLt⟩) = true :=
          level_monotone_succ b σ hWF w.ti pred hjSucc hLevelSucc
        -- Apply level increase to obtain a parent level: Level(H, pred+1)
        have hParentLevel :
            σ (Var.Level H ⟨pred.succ, hjSucc⟩) = true :=
          level_increase_mem b σ hWF H w pred hjSucc hMem hLevelPred
        -- Bound child fuel via parent fuel
        have hPredSuccLe :
            pred.succ.val ≤ parentFuel :=
          level_true_le_fuelOf b σ H ⟨pred.succ, hjSucc⟩ hParentLevel
        have hChildLe :
            childFuel ≤ parentFuel := by
          simpa [hkFuelSucc] using hPredSuccLe
        -- Conclude with `< parentFuel + 2`
        omega

/-! ## Fuel-Based Decoder -/


/-- Decode a prehistory from a SAT assignment.
    Uses per-time fuel from Level variables to ensure termination.

    At fuel = 0, returns empty prehistory (base case).
    At fuel > 0, finds all worlds with Mem(H, w) = true and constructs them inline.

    Requires WF to prove termination via cnfLevel_decrease. -/
def decodePre (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ) (H : b.times) :
    PreHistory (Fin b.nParticipants) (Signature.EventType S) :=
  if hFuel : 0 < fuelOf b σ H then
    let members := (WId.allWorlds b).filter (fun w => σ (Var.Mem H w))
    -- Use attach to get membership proofs for termination checker
    have : ∀ w, w ∈ members → σ (Var.Mem H w) = true := by
      intro w hw
      simp [members] at hw
      exact hw.2
    PreHistory.mk (members.attach.map fun ⟨wSub, hw⟩ =>
      let w := wSub  -- wSub is the WId, hw is the membership proof
      have hMem : σ (Var.Mem H w) = true := this w (by simpa using hw)
      -- Inline world construction: extract fields from WId and recursively decode prehistory
      (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti))
  else
    PreHistory.empty
termination_by fuelOf b σ H
decreasing_by
  -- Remaining goal: decodePre recursively calls itself on w.ti with strictly less fuel
  -- Requires: fuelOf b σ w.ti < fuelOf b σ H
  have hFuel : 0 < fuelOf b σ H := by assumption
  have hMem : σ (Var.Mem H w) = true := by assumption
  exact fuelOf_strict_decrease_mem b σ hWF H w hMem hFuel

/-! ## Predicate Interpretation Decoder -/

/-- Time-accurate predicate table.
    Returns the set of predicates that hold for participant `p` at time index `ti`. -/
def predTbl (b : Bounds S) (σ : SAT.Assignment (Var b)) :
    (Fin b.nParticipants) → b.times → Set (Signature.AtomicPredType S) :=
  fun p ti =>
    { pred : Signature.AtomicPredType S |
      ∃ (k : b.predIx),
        σ (Var.Pred p ti k) = true ∧ b.preds.get k = pred }

/-- Boolean equality for MaybeEvent (uses DecidableEq on events). -/
def beqMaybeEvent {α} [DecidableEq α] : MaybeEvent α → MaybeEvent α → Bool
  | .none,   .none   => true
  | .some a, .some b => decide (a = b)
  | _,       _       => false

@[simp] lemma beqMaybeEvent_eq {α} [DecidableEq α]
    {e₁ e₂ : MaybeEvent α} :
    beqMaybeEvent e₁ e₂ = true → e₁ = e₂ := by
  cases e₁ with
  | none =>
      cases e₂ with
      | none =>
          intro _
          rfl
      | some _ =>
          intro h
          cases h
  | some a₁ =>
      cases e₂ with
      | none =>
          intro h
          cases h
      | some a₂ =>
          intro h
          have : a₁ = a₂ := of_decide_eq_true h
          subst this
          rfl

mutual
  /-- Boolean equality for worlds; recursive on the time component. -/
  def beqWorld (b : Bounds S) (σ : SAT.Assignment (Var b)) :
      World (Fin b.nParticipants) (Signature.EventType S) →
      World (Fin b.nParticipants) (Signature.EventType S) → Bool
    | (p₁, e₁, H₁), (p₂, e₂, H₂) =>
        (decide (p₁ = p₂)) &&
        (beqMaybeEvent e₁ e₂) &&
        (beqPre b σ H₁ H₂)

  /-- Boolean equality for prehistories; structural list comparison using beqWorld. -/
  def beqPre (b : Bounds S) (σ : SAT.Assignment (Var b)) :
      PreHistory (Fin b.nParticipants) (Signature.EventType S) →
      PreHistory (Fin b.nParticipants) (Signature.EventType S) → Bool
    | .mk l₁, .mk l₂ =>
        let rec beqList :
            List (World (Fin b.nParticipants) (Signature.EventType S)) →
            List (World (Fin b.nParticipants) (Signature.EventType S)) → Bool
          | [],      []      => true
          | x :: xs, y :: ys => beqWorld b σ x y && beqList xs ys
          | _,       _       => false
        beqList l₁ l₂
end

/-- Reflexivity for `beqMaybeEvent`. -/
@[simp] lemma beqMaybeEvent_refl {α} [DecidableEq α] (e : MaybeEvent α) :
    beqMaybeEvent e e = true := by
  cases e <;> simp [beqMaybeEvent]

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
mutual
  theorem beqWorld_refl_aux (b : Bounds S) (σ : SAT.Assignment (Var b)) :
      ∀ w, beqWorld b σ w w = true
    | (p, e, H) => by
        classical
        simp [beqWorld, beqMaybeEvent_refl, beqPre_refl_aux b σ H]

  theorem beqPre_refl_aux (b : Bounds S) (σ : SAT.Assignment (Var b)) :
      ∀ H, beqPre b σ H H = true
    | .mk [] => by simp [beqPre, beqPre.beqList]
    | .mk (w :: ws) => by
        classical
        have hw : beqWorld b σ w w = true :=
          beqWorld_refl_aux (b := b) (σ := σ) w
        have hTail : beqPre b σ (PreHistory.mk ws) (PreHistory.mk ws) = true :=
          beqPre_refl_aux b σ (PreHistory.mk ws)
        simp [beqPre, beqPre.beqList, hw]
        exact hTail
end

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Reflexivity of `beqWorld`. -/
@[simp] lemma beqWorld_refl (b : Bounds S) (σ : SAT.Assignment (Var b))
    (w : World (Fin b.nParticipants) (Signature.EventType S)) :
    beqWorld b σ w w = true :=
  beqWorld_refl_aux (b := b) (σ := σ) w

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Reflexivity of `beqPre`: any prehistory equals itself. -/
@[simp] lemma beqPre_refl (b : Bounds S) (σ : SAT.Assignment (Var b))
    (H : PreHistory (Fin b.nParticipants) (Signature.EventType S)) :
    beqPre b σ H H = true :=
  beqPre_refl_aux (b := b) (σ := σ) H

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
mutual
  lemma beqWorld_eq_aux (b : Bounds S) (σ : SAT.Assignment (Var b))
      (w₁ w₂ : World (Fin b.nParticipants) (Signature.EventType S)) :
      beqWorld b σ w₁ w₂ = true → w₁ = w₂ := by
    match w₁, w₂ with
    | (p₁, e₁, H₁), (p₂, e₂, H₂) =>
        intro h
        match hDec : decide (p₁ = p₂) with
        | false =>
            simp [beqWorld, hDec] at h
        | true =>
            have hp : p₁ = p₂ := of_decide_eq_true hDec
            simp only [beqWorld, hDec, Bool.true_and] at h
            match hMaybe : beqMaybeEvent e₁ e₂ with
            | false =>
                simp [hMaybe] at h
            | true =>
                have he : e₁ = e₂ := beqMaybeEvent_eq hMaybe
                simp [hMaybe] at h
                have hPre : H₁ = H₂ := beqPre_eq_aux b σ H₁ H₂ h
                subst hp he hPre
                rfl

  lemma beqPre_eq_aux (b : Bounds S) (σ : SAT.Assignment (Var b))
      (H₁ H₂ : PreHistory (Fin b.nParticipants) (Signature.EventType S)) :
      beqPre b σ H₁ H₂ = true → H₁ = H₂ := by
    match H₁, H₂ with
    | .mk [], .mk [] =>
        intro _
        rfl
    | .mk [], .mk (y :: ys) =>
        intro h
        simp [beqPre, beqPre.beqList] at h
    | .mk (x :: xs), .mk [] =>
        intro h
        simp [beqPre, beqPre.beqList] at h
    | .mk (x :: xs), .mk (y :: ys) =>
        intro h
        match hWorld : beqWorld b σ x y with
        | false =>
            simp [beqPre, beqPre.beqList, hWorld] at h
        | true =>
            have hx : x = y := beqWorld_eq_aux b σ x y hWorld
            simp [beqPre, beqPre.beqList, hWorld] at h
            have hTail : PreHistory.mk xs = PreHistory.mk ys :=
              beqPre_eq_aux b σ (PreHistory.mk xs) (PreHistory.mk ys) h
            subst hx
            cases hTail
            rfl
end

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
@[simp] lemma beqWorld_eq (b : Bounds S) (σ : SAT.Assignment (Var b))
    {w₁ w₂ :
      World (Fin b.nParticipants) (Signature.EventType S)} :
    beqWorld b σ w₁ w₂ = true → w₁ = w₂ :=
  beqWorld_eq_aux b σ w₁ w₂

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
@[simp] lemma beqPre_eq (b : Bounds S) (σ : SAT.Assignment (Var b))
    {H₁ H₂ :
      PreHistory (Fin b.nParticipants) (Signature.EventType S)} :
    beqPre b σ H₁ H₂ = true → H₁ = H₂ :=
  beqPre_eq_aux b σ H₁ H₂

/-- Collect all time indices whose decoded prehistory is `histEq` to `H`.

    This is used for the predicate interpreter: instead of trying to invert
    `decodePre` (which may not be injective), we collect all time indices that
    decode to a history extensionally equal to `H`.

    Requires WF for decodePre termination. -/
noncomputable def timeIndicesFor (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (H : PreHistory (Fin b.nParticipants) (Signature.EventType S)) : List b.times :=
  by
    classical
    exact (Bounds.timesL b).filter
      (fun ti => decide (PreHistory.histEq (decodePre b σ hWF ti) H))

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mem_timeIndicesFor_iff
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (H : PreHistory (Fin b.nParticipants) (Signature.EventType S)) (ti : b.times) :
    ti ∈ timeIndicesFor b σ hWF H ↔
      ti ∈ Bounds.timesL b ∧
        PreHistory.histEq (decodePre b σ hWF ti) H := by
  classical
  unfold timeIndicesFor
  constructor
  · intro hMem
    rcases List.mem_filter.1 hMem with ⟨hTi, hDec⟩
    refine ⟨hTi, ?_⟩
    exact of_decide_eq_true hDec
  · rintro ⟨hTi, hHist⟩
    exact List.mem_filter.2 ⟨hTi, by simp [hHist]⟩

/-- Computable predicate interpreter using union over all matching time indices.

    For any prehistory H, this returns the union of predicates from all time indices
    that decode to H. This avoids needing to invert decodePre (which may not be
    injective when multiple time indices decode to the same prehistory).

    For adequacy, we witness membership with the specific ti we start from.
    Requires WF for timeIndicesFor/decodePre. -/
def predInterp (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ) :
    (Fin b.nParticipants) →
    PreHistory (Fin b.nParticipants) (Signature.EventType S) →
    Set (Signature.AtomicPredType S) :=
  fun p H =>
    { a | ∃ ti ∈ timeIndicesFor b σ hWF H,
        ∃ H' : b.times,
          σ (Var.PreEq ti H') = true ∧ a ∈ predTbl b σ p H' }

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- `ti` is always among the indices decoding to its own prehistory. -/
lemma ti_mem_timeIndicesFor_decode (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (ti : b.times) :
    ti ∈ timeIndicesFor b σ hWF (decodePre b σ hWF ti) := by
  classical
  apply (mem_timeIndicesFor_iff (b := b) (σ := σ) (hWF := hWF)
    (H := decodePre b σ hWF ti) (ti := ti)).2
  refine ⟨by simp [Bounds.timesL], ?_⟩
  exact PreHistory.histEq_refl _

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma decodePre_histEq_of_mem_timeIndicesFor
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    {H : PreHistory (Fin b.nParticipants) (Signature.EventType S)}
    {ti : b.times}
    (hMem : ti ∈ timeIndicesFor b σ hWF H) :
    PreHistory.histEq (decodePre b σ hWF ti) H := by
  classical
  exact (mem_timeIndicesFor_iff (b := b) (σ := σ) (hWF := hWF)
    (H := H) (ti := ti)).1 hMem |>.2

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma timeIndicesFor_mem_of_histEq
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    {H H' : PreHistory (Fin b.nParticipants) (Signature.EventType S)}
    {ti : b.times}
    (hEq : PreHistory.histEq H' H)
    (hMem : ti ∈ timeIndicesFor b σ hWF H') :
    ti ∈ timeIndicesFor b σ hWF H := by
  classical
  rcases (mem_timeIndicesFor_iff (b := b) (σ := σ) (hWF := hWF)
    (H := H') (ti := ti)).1 hMem with ⟨hTi, hHist⟩
  exact
    (mem_timeIndicesFor_iff (b := b) (σ := σ) (hWF := hWF)
      (H := H) (ti := ti)).2
      ⟨hTi, PreHistory.histEq_trans hHist hEq⟩

/-! ## Learner/Semifilter Decoder -/

/-- Pure computational artifact representing learner structure.

    This structure stores only the data extracted from a SAT assignment,
    without any proof obligations. The full `Semifilter` construction with
    proofs is deferred to `Adequacy.lean`.

    IMPORTANT: This is index-keyed, not value-keyed, to avoid ambiguity
    when multiple indices have the same value. -/
structure LearnerData (b : Bounds S) where
  /-- For each value index, list of minimal quorum sets Q where MinQ(vIdx, Q) = true. -/
  minimalQuorumsIx : b.valIx → List (Finset (Fin b.nParticipants))

/-- Extract learner data from SAT assignment (computable, no proofs).

    For each value index, collects the Finsets Q where MinQ(vIdx, Q) = true.
    This is index-keyed to avoid issues with duplicate values in b.values. -/
def decodeLearnerData (b : Bounds S) (σ : SAT.Assignment (Var b)) : LearnerData b :=
  { minimalQuorumsIx := fun vIdx =>
      -- allMinQ b vIdx enumerates Var.MinQ vIdx Q for all quorums Q
      (Var.allMinQ b vIdx).filterMap (fun v =>
        match v with
        | Var.MinQ _ Q => if σ v = true then some Q else none
        | _            => none) }

/-- Pick the representative index for a value from SAT assignment.
    Returns the index where Rep(i) = true, or first valid index as default. -/
def pickRep (b : Bounds S) (σ : SAT.Assignment (Var b)) (v : Signature.Value S) : b.valIx :=
  match (valueIndices b v).find? (fun i => σ (Var.Rep i)) with
  | some i => i
  | none   => ⟨0, b.posVals⟩

/-- Value-keyed list of minimal quorums: union over all matching indices. -/
def minimalQuorumsByValue (b : Bounds S) (σ : SAT.Assignment (Var b))
    (v : Signature.Value S) : List (Finset (Fin b.nParticipants)) :=
  (valueIndices b v).flatMap (fun i => (decodeLearnerData b σ).minimalQuorumsIx i)

/-! ## Combined Model Data -/

/-- Pure computable model data extracted from a SAT assignment.

    This structure contains only computational data, no proofs.
    The `modelOf` function (in Adequacy.lean) will take this data
    plus a well-formedness proof to construct a full `Model`. -/
structure ModelData (S : Signature) (P : Type*) (b : Bounds S) where
  /-- Root prehistory decoded from assignment. -/
  Hroot : PreHistory P (Signature.EventType S)
  /-- Time-accurate predicate interpretation (computable). -/
  pred : P → PreHistory P (Signature.EventType S) → Set (Signature.AtomicPredType S)
  /-- Learner computational data (not full Semifilter). -/
  learnData : LearnerData b

/-- Extract model data from a SAT assignment.
    Requires WF for decodePre/predInterp termination. -/
def modelDataOf (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ) :
    ModelData S (Fin b.nParticipants) b :=
  { Hroot := decodePre b σ hWF b.root,
    pred := predInterp b σ hWF,
    learnData := decodeLearnerData b σ }

/-! ## Decoder Correctness Lemmas

## Important Note on Fuel-Based Decoding

The decoder uses fuel-based recursion to handle the potentially cyclic structure
before well-formedness is established. Key properties:

1. **Head Stability**: For k ≥ 1, the place/event pairs are identical across fuel levels
   (proven below as `preHeads_decodePreFuel_succ`)

2. **Stability at Bound**: Under WF, `b.nTimes` fuel is sufficient - adding more fuel
   doesn't change the result (to be proven as `decodePreFuel_stable`)

3. **No Subset Monotonicity**: Worlds do NOT form literal subsets as fuel increases!
   Time components deepen, so (p, e, empty) at fuel k becomes (p, e, actualHistory)
   at fuel k+1. These are different tuples.

For adequacy, we only need:
- Fixed-fuel evaluation at `b.nTimes`
- Stability at the bound (equality, not monotonicity)
- Time-accurate predicate interpretation

See Plan.md "Decoder Termination" section for full rationale.
-/

/-- The head of a world: place and (maybe-)event, ignoring time. -/
def worldHead (_b : Bounds S) (_σ : SAT.Assignment (Var _b))
    (t : World (Fin _b.nParticipants) (Signature.EventType S)) :
    (Fin _b.nParticipants) × MaybeEvent (Signature.EventType S) :=
  (t.1, t.2.1)

/-- The list of heads of a prehistory. -/
def preHeads (b : Bounds S) (σ : SAT.Assignment (Var b))
    (h : PreHistory (Fin b.nParticipants) (Signature.EventType S)) :
    List ((Fin b.nParticipants) × MaybeEvent (Signature.EventType S)) :=
  match h with
  | .mk l => l.map (worldHead b σ)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
@[simp] lemma preHeads_mk (b : Bounds S) (σ : SAT.Assignment (Var b))
    (l : List (World (Fin b.nParticipants) (Signature.EventType S))) :
    preHeads b σ (.mk l) = l.map (worldHead b σ) := rfl

/-! ## Decoder-to-Mem Correspondence -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If a `Mem` bit holds, the decoded world appears in `decodePre`.
    The world is constructed inline from WId fields. -/
lemma mem_decodePre_of_memVar (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (w : WId b)
    (hmem : σ (Var.Mem H w) = true) :
    (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti) ∈ decodePre b σ hWF H := by
  -- Mem(H, w) = true implies fuelOf H > 0 by cnfMemRequiresFuel constraint
  -- Extract the constraint: Mem(H, w) → Level(H, 1)
  have hCNF := mem_requires_fuel_from_wf b σ hWF
  have hLevel1 : σ (Var.Level H ⟨1, Nat.succ_lt_succ b.posTimes⟩) = true := by
    -- From cnfMemRequiresFuel, the clause [¬Mem(H,w), Level(H,1)] evaluates to true
    -- Since Mem(H,w) = true, we get Level(H,1) = true
    -- Step 1: Extract that all clauses in cnfMemRequiresFuel evaluate to true
    have hAllClauses : ∀ C ∈ (cnfMemRequiresFuel b).clauses, SAT.Clause.eval σ C = true := by
      have : (cnfMemRequiresFuel b).clauses.all (SAT.Clause.eval σ) = true := by
        simpa [SAT.CNF.eval] using hCNF
      exact List.all_eq_true.mp this
    -- Step 2: Show our specific clause is in the list
    let clause := [SAT.Lit.neg (Var.Mem H w)
                  , SAT.Lit.pos (Var.Level H ⟨1, Nat.succ_lt_succ b.posTimes⟩)]
    have hClauseMem : clause ∈ (cnfMemRequiresFuel b).clauses := by
      unfold cnfMemRequiresFuel
      simp only []
      refine List.mem_flatMap.mpr ?_
      exists H
      constructor
      · unfold Bounds.timesL
        exact List.mem_finRange H
      · refine List.mem_map.mpr ?_
        exists w
        exact ⟨WId.mem_allWorlds b w, rfl⟩
    -- Step 3: Extract that our clause evaluates to true
    have hClauseEval : SAT.Clause.eval σ clause = true := hAllClauses _ hClauseMem
    -- Step 4: Evaluate the clause
    -- clause = [¬Mem(H,w), Level(H,1)]
    -- eval = (¬σ(Mem(H,w))) || σ(Level(H,1))
    -- Since σ(Mem(H,w)) = true, we have ¬σ(Mem(H,w)) = false
    -- So eval = false || σ(Level(H,1)) = σ(Level(H,1))
    have : SAT.Clause.eval σ clause
         = (!(σ (Var.Mem H w)) || σ (Var.Level H ⟨1, Nat.succ_lt_succ b.posTimes⟩)) := by
      unfold clause
      rw [SAT.Clause.eval_two_lit]
      simp [SAT.Lit.eval]
    rw [this] at hClauseEval
    simp [hmem] at hClauseEval
    exact hClauseEval
  -- Level(H, 1) = true implies fuelOf H ≥ 1 > 0
  --Level variables are prefix-closed by monotonicity, so Level(H,1) → Level(H,0)
  -- find? on reversed finRange returns the max true level, which must be ≥ 1
  have hFuel : 0 < fuelOf b σ H := by
    have hLe :
        (1 : Nat) ≤ fuelOf b σ H :=
      level_true_le_fuelOf (b := b) (σ := σ) (ti := H)
        (k := ⟨1, Nat.succ_lt_succ b.posTimes⟩) hLevel1
    exact lt_of_lt_of_le (Nat.zero_lt_one) hLe
  -- Now proceed with membership proof
  unfold decodePre
  simp only [hFuel, dite_true, PreHistory.mem_mk, List.mem_map, List.mem_attach]
  use ⟨w, by simp [List.mem_filter]; exact ⟨WId.mem_allWorlds b w, hmem⟩⟩
  constructor
  · trivial
  · simp
    -- The goal asks us to show decodePre w.ti equals its definition
    -- This is true by the equation lemma for decodePre
    rw [decodePre.eq_def]
    simp

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If a world belongs to the decoded prehistory, it arises from some world identifier
    whose `Mem` bit is true. World is constructed inline from WId fields. -/
lemma exists_memVar_of_mem_decodePre (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (H : b.times)
    {w : World (Fin b.nParticipants) (Signature.EventType S)}
    (h : w ∈ decodePre b σ hWF H) :
    ∃ wId : WId b,
      (wId.p, b.decodeMaybeEvent wId.ei, decodePre b σ hWF wId.ti) = w ∧
      σ (Var.Mem H wId) = true := by
  by_cases hFuel : 0 < fuelOf b σ H
  · -- Case: fuelOf H > 0
    unfold decodePre at h
    simp [hFuel, PreHistory.mem_mk] at h
    obtain ⟨wId, hwId_mem, hwId_eq⟩ := h
    use wId
    constructor
    · exact hwId_eq
    · exact hwId_mem.2
  · -- Case: fuelOf H = 0, empty prehistory
    unfold decodePre at h
    simp [hFuel, PreHistory.not_mem_empty] at h

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The decoder enumerates exactly the worlds whose `Mem` literal is true. -/
lemma mem_decodePre_iff_memVar (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (H : b.times)
    (w : World (Fin b.nParticipants) (Signature.EventType S)) :
    w ∈ decodePre b σ hWF H ↔
      ∃ wId : WId b,
        σ (Var.Mem H wId) = true ∧
        (wId.p, b.decodeMaybeEvent wId.ei, decodePre b σ hWF wId.ti) = w := by
  constructor
  · -- Forward: membership → ∃ wId with Mem true
    intro h
    obtain ⟨wId, hwId_eq, hwId_mem⟩ := exists_memVar_of_mem_decodePre b σ hWF H h
    exact ⟨wId, hwId_mem, hwId_eq⟩
  · -- Backward: ∃ wId with Mem true → membership
    intro ⟨wId, hwId_mem, hwId_eq⟩
    rw [← hwId_eq]
    exact mem_decodePre_of_memVar b σ hWF H wId hwId_mem

/-! ## Root Membership with Exact Time

After the fuel alignment refactor, the third component of worlds stored in the root history
is decoded using the same per-time fuel as the semantic `decodePre`. This makes the
membership equivalence literally true without needing PreEq.
-/

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- Root membership with decoded prehistory matching.

    A world (p, evt, H) is in the root prehistory iff there exists a world ID
    with matching participant, event, and DECODED PREHISTORY whose Mem bit is true.

    IMPORTANT: This does NOT require exact time index matching, only that the
    decoded prehistories are equal. decodePre is not injective - multiple time
    indices can decode to the same prehistory.

    This lemma is provable by unfolding definitions. For event adequacy,
    PreEq provides the CNF-checkable proxy for decoded prehistory equality. -/
lemma root_mem_exact_decoded
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (p : Fin b.nParticipants) (evt : MaybeEvent (Signature.EventType S)) (ti : b.times) :
    ((p, evt, decodePre b σ hWF ti) ∈ (modelDataOf b σ hWF).Hroot) ↔
    ∃ (w : WId b),
        w.p = p
      ∧ evt = b.decodeMaybeEvent w.ei
      ∧ σ (Var.Mem b.root w) = true
      ∧ decodePre b σ hWF w.ti = decodePre b σ hWF ti := by
  simp only [modelDataOf]
  constructor
  · -- Forward: membership → witness with properties
    intro h
    obtain ⟨w, hw_eq, hw_mem⟩ := exists_memVar_of_mem_decodePre b σ hWF b.root h
    -- hw_eq: (w.p, b.decodeMaybeEvent w.ei, decodePre w.ti) = (p, evt, decodePre ti)
    have hp : w.p = p := by simp at hw_eq; exact hw_eq.1
    have hevt : b.decodeMaybeEvent w.ei = evt := by simp at hw_eq; exact hw_eq.2.1
    have hpre : decodePre b σ hWF w.ti = decodePre b σ hWF ti := by simp at hw_eq; exact hw_eq.2.2
    exact ⟨w, hp, hevt.symm, hw_mem, hpre⟩
  · -- Backward: witness → membership
    intro ⟨w, hw_p, hw_evt, hw_mem, hw_pre⟩
    have h : (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti) ∈ decodePre b σ hWF b.root :=
      mem_decodePre_of_memVar b σ hWF b.root w hw_mem
    convert h using 1
    simp [hw_p, hw_evt, hw_pre]

end Encoding
