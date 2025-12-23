import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf

/-!
# Completeness for Equality Formula

The equality formula encodes `v₁ ≃ v₂` (value equality).

## Encoding

```lean
encodeFormula b (Formula.eq v1 v2) w st =
  let (u, st1) := EncState.allocFresh b st
  if v1 = v2 then
    (u, EncState.addClause b st1 [SAT.Lit.pos (FVar.toVar b u)])  -- [u]
  else
    (u, EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u)])  -- [¬u]
```

## Completeness

If `Sat M ... (v₁ ≃ v₂)` holds, then `v1 = v2` by semantics.
The encoding adds `[u]`, so any σ with σ(u) = true satisfies the clause.
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- Completeness for eq: u ↔ (v1 = v2).

    Note: hWF is needed to show that Var.Fresh st.nextFresh cannot appear in st.clauses,
    which is required when extending the assignment. -/
theorem encodeFormula_complete_eq
    (b : Bounds S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    (v1 v2 : S.Value)
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b (Formula.eq v1 v2) w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.eq v1 v2) ↔
       σ_ext (FVar.toVar b (encodeFormula b (Formula.eq v1 v2) w st).1) = true) := by
  -- Get the fresh variable and encoding state
  let freshIdx := st.nextFresh
  let σ₀ := assignmentOf b M hFits

  -- Key: u should match whether v1 = v2
  -- Define σ_ext: set u = (v1 == v2)
  let σ_ext : SAT.Assignment (Var b) := fun v =>
    match v with
    | Var.Fresh n => if n = freshIdx then (v1 == v2) else σ₀ v
    | _ => σ₀ v

  use σ_ext

  refine ⟨?_, ?_, ?_⟩

  · -- Non-fresh variables agree with assignmentOf
    intro v hNotFresh
    cases v with
    | Fresh n =>
        exfalso
        apply hNotFresh
        simp only [isFreshVar, Var.isFresh]
    | _ => rfl

  · -- All clauses satisfied
    simp only [encodeFormula, EncState.addClause, EncState.allocFresh]
    -- Branch on whether v1 = v2
    by_cases hEq : v1 = v2
    · -- v1 = v2: encoding adds [u], and we set u = true
      simp only [beq_iff_eq, hEq, ↓reduceIte]
      simp only [List.all_cons, Bool.and_eq_true]
      constructor
      · -- The new clause [u] is satisfied
        apply SAT.Clause.eval_true_of_pos_mem (v := Var.Fresh st.nextFresh)
        · simp only [FVar.toVar, List.mem_singleton]
        · simp only [σ_ext, freshIdx, ↓reduceIte, beq_iff_eq, hEq]
      · -- Base clauses
        rw [List.all_eq_true] at hBaseClauses ⊢
        intro clause hClause
        have hBase := hBaseClauses clause hClause
        rw [SAT.Clause.eval_eq_any] at hBase ⊢
        rw [List.any_eq_true] at hBase ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hBase
        refine ⟨lit, hLitMem, ?_⟩
        cases lit with
        | pos v =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases v with
            | Fresh n =>
                simp only [σ_ext]
                split
                · next hEq' => simp only [hEq, beq_self_eq_true]
                · exact hLitTrue
            | _ => exact hLitTrue
        | neg v =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases v with
            | Fresh n =>
                simp only [σ_ext]
                split
                · next hEq' =>
                    exfalso
                    have hNotIn := hWF.fresh_not_in_clauses hClause hLitMem
                    simp only [SAT.Lit.getVar] at hNotIn
                    exact hNotIn (congrArg Var.Fresh hEq')
                · exact hLitTrue
            | _ => exact hLitTrue
    · -- v1 ≠ v2: encoding adds [¬u], and we set u = false
      simp only [beq_iff_eq, hEq, ↓reduceIte]
      simp only [List.all_cons, Bool.and_eq_true]
      constructor
      · -- The new clause [¬u] is satisfied
        apply SAT.Clause.eval_true_of_neg_mem (v := Var.Fresh st.nextFresh)
        · simp only [FVar.toVar, List.mem_singleton]
        · simp only [σ_ext, freshIdx, ↓reduceIte]
          -- Goal: !(v1 == v2) = true, but hEq : v1 ≠ v2
          have : (v1 == v2) = false := beq_eq_false_iff_ne.mpr hEq
          simp only [this, Bool.not_false]
      · -- Base clauses
        rw [List.all_eq_true] at hBaseClauses ⊢
        intro clause hClause
        have hBase := hBaseClauses clause hClause
        rw [SAT.Clause.eval_eq_any] at hBase ⊢
        rw [List.any_eq_true] at hBase ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hBase
        refine ⟨lit, hLitMem, ?_⟩
        cases lit with
        | pos v =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases v with
            | Fresh n =>
                simp only [σ_ext]
                split
                · next hEq' =>
                    exfalso
                    have hNotIn := hWF.fresh_not_in_clauses hClause hLitMem
                    simp only [SAT.Lit.getVar] at hNotIn
                    exact hNotIn (congrArg Var.Fresh hEq')
                · exact hLitTrue
            | _ => exact hLitTrue
        | neg v =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases v with
            | Fresh n =>
                simp only [σ_ext]
                split
                · next hEq' =>
                    have : (v1 == v2) = false := beq_eq_false_iff_ne.mpr hEq
                    simp only [this, Bool.not_false]
                · exact hLitTrue
            | _ => exact hLitTrue

  · -- The iff: Sat (eq v1 v2) ↔ u = true
    simp only [encodeFormula, EncState.allocFresh, FVar.toVar]
    change (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.eq v1 v2) ↔
            σ_ext (Var.Fresh freshIdx) = true)
    simp only [σ_ext, ↓reduceIte]
    -- u = (v1 == v2), Sat = (v1 = v2), these are equivalent
    simp only [Sat, beq_iff_eq]

end Encoding
