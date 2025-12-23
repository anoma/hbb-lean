import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.TseytinGadgets

/-!
# Clause Preservation Lemmas

Helper lemmas for reasoning about `List.foldl` constructions that repeatedly
call `EncState.addClause`.  These facts are used by multiple encoding and
adequacy proofs, so they live in their own low-level module to avoid creating
import cycles higher in the stack.
-/

open ModalDistribution Encoding

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]
variable [DecidableEq S.Value]

/-! ## Basic Monotonicity -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Adding a clause preserves all existing clauses. -/
lemma addClause_preserves (b : Bounds S) (st : EncState b) (clause : SAT.Clause (Var b)) :
    st.clauses ⊆ (EncState.addClause b st clause).clauses := by
  exact EncState.addClause_subset_clauses (b := b) st clause

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Foldl preserves clauses: wrapper around `foldl_subset_state` for clarity. -/
lemma foldl_step_clauses_subset
    (b : Bounds S) {α : Type} (xs : List α) (st : EncState b)
    (f : EncState b → α → EncState b)
    (hStep : ∀ st a, st.clauses ⊆ (f st a).clauses) :
    st.clauses ⊆ (xs.foldl f st).clauses := by
  exact foldl_subset_state (b := b) (f := f) (hStep := hStep) xs st

/-! ## Clause Membership in Fold Results -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If a clause is added for an element in the list, it appears in the final fold result.

    This lemma shows that any clause added during a `foldl` iteration
    remains in the final clause set. Useful for extracting specific clauses
    from encoding constructions.

    Note: This is the "forward" direction (element → clause in result).
    See `foldl_addClause_mem` in Basic.lean for the "backward" direction
    (clause in result → characterization). -/
lemma foldl_addClause_elem_mem
    {α : Type} (b : Bounds S)
    (xs : List α) (st : EncState b)
    (clauseOf : α → SAT.Clause (Var b))
    (a : α) (ha : a ∈ xs) :
    clauseOf a ∈
      (xs.foldl (fun stAcc x => EncState.addClause b stAcc (clauseOf x)) st).clauses := by
  classical
  induction xs generalizing st with
  | nil =>
      cases ha
  | cons x xs ih =>
      have hMem : a = x ∨ a ∈ xs := by
        simpa [List.mem_cons] using ha
      let step : EncState b → α → EncState b :=
        fun stAcc y => EncState.addClause b stAcc (clauseOf y)
      have hStep : ∀ stAcc (y : α), stAcc.clauses ⊆ (step stAcc y).clauses := by
        intro stAcc y
        exact addClause_preserves b stAcc (clauseOf y)
      cases hMem with
      | inl hEq =>
          subst hEq
          have hHead : clauseOf a ∈ (step st a).clauses := by
            simp [step, EncState.addClause]
          have hSubset :=
            foldl_step_clauses_subset (b := b) (xs := xs) (st := step st a)
              (f := step) (hStep := hStep)
          simpa [List.foldl, step] using hSubset hHead
      | inr hTail =>
          have hRes := ih (step st x) hTail
          simpa [List.foldl, step] using hRes

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- For nested foldl with clause addition, clauses from any element pair are preserved.

    Useful when encoding uses nested `List.foldl` patterns. -/
lemma foldl_nested_addClause_elem_mem
    {α β : Type} (b : Bounds S)
    (xs : List α) (ys : List β) (st : EncState b)
    (clauseOf : α → β → SAT.Clause (Var b))
    (a : α) (ha : a ∈ xs)
    (b_elem : β) (hb : b_elem ∈ ys) :
    clauseOf a b_elem ∈
      (xs.foldl (fun stAcc x =>
        ys.foldl (fun stAcc' y =>
          EncState.addClause b stAcc' (clauseOf x y)
        ) stAcc) st).clauses := by
  classical
  revert st
  induction xs with
  | nil =>
      intro st
      cases ha
  | cons x xs ih =>
      intro st
      have hMem : a = x ∨ a ∈ xs := by
        simpa [List.mem_cons] using ha
      let stepOuter : EncState b → α → EncState b :=
        fun stAcc x' =>
          ys.foldl (fun stAcc' y' =>
            EncState.addClause b stAcc' (clauseOf x' y')
          ) stAcc
      have hStepOuter :
          ∀ stAcc (x' : α), stAcc.clauses ⊆ (stepOuter stAcc x').clauses := by
        intro stAcc x'
        simpa [stepOuter] using
          foldl_step_clauses_subset (b := b) (xs := ys) (st := stAcc)
            (f := fun acc y' => EncState.addClause b acc (clauseOf x' y'))
            (hStep := fun acc y' => addClause_preserves b acc (clauseOf x' y'))
      cases hMem with
      | inl hEq =>
          subst hEq
          have hHead : clauseOf a b_elem ∈ (stepOuter st a).clauses := by
            simpa [stepOuter] using
              foldl_addClause_elem_mem (b := b) (xs := ys) (st := st)
                (clauseOf := clauseOf a) (a := b_elem) (ha := hb)
          have hTail :=
            foldl_step_clauses_subset (b := b) (xs := xs) (st := stepOuter st a)
              (f := stepOuter) (hStep := hStepOuter)
          simpa [stepOuter, List.foldl] using hTail hHead
      | inr hTail =>
          have hMem := ih hTail (stepOuter st x)
          simpa [stepOuter, List.foldl] using hMem

end Encoding
