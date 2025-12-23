import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf

/-!
# Completeness for Seq Formula

The seq formula encodes sequentiality between world timelines.

## Encoding

```lean
encodeFormula b Formula.seq w st =
  let (u, st1) := EncState.allocFresh b st
  -- Tseytin for u ↔ Seq(w.p, w.ti)
  -- Forward: u → Seq  [¬u, Seq]
  -- Backward: Seq → u  [¬Seq, u]
  ...
```

## Completeness Strategy

If `Sat M ... seq` holds, then the semantic sequentiality condition holds.
By assignmentOf construction, `Seq(p, ti) = seqAt ev p ti`.
If sequentiality semantically holds, then seqAt = true.
This satisfies the backward clause, and we set u = true.

The Seq variable is a structural variable (not Fresh), so assignmentOf handles it directly.
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- Completeness for seq: structural Seq variable gives the witness.

    Note: hWF is needed to show that Var.Fresh st.nextFresh cannot appear in st.clauses,
    which is required when extending the assignment. -/
theorem encodeFormula_complete_seq
    (b : Bounds S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b Formula.seq w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) Formula.seq ↔
       σ_ext (FVar.toVar b (encodeFormula b Formula.seq w st).1) = true) := by
  -- Unfold the encoding
  simp only [encodeFormula]

  -- Get fresh variable index
  let freshIdx := st.nextFresh
  let σ₀ := assignmentOf b M hFits

  -- Key lemma: Seq variable matches semantic isSequential
  have hSeqIff : σ₀ (Var.Seq w.ti w.p) = true ↔
      isSequential w.p (prehistoryAt hFits.view w.ti) := by
    classical
    simp only [σ₀, assignmentOf, isSeqAt, prehistoryOfTime]
    exact decide_eq_true_iff

  -- Define σ_ext: set fresh u = Seq variable value, agree with σ₀ on non-fresh
  -- This ensures u ↔ Seq ↔ isSequential
  let σ_ext : SAT.Assignment (Var b) := fun v =>
    match v with
    | Var.Fresh n => if n = freshIdx then σ₀ (Var.Seq w.ti w.p) else σ₀ v
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
    simp only [EncState.addClause, EncState.allocFresh]
    simp only [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_⟩

    · -- Clause [¬Seq, u] is satisfied
      -- u = σ₀(Seq), so either both true or both false
      -- If Seq is true: u is true, clause satisfied by u
      -- If Seq is false: clause satisfied by ¬Seq
      by_cases hSeq : σ₀ (Var.Seq w.ti w.p) = true
      · -- Seq is true, u is true
        apply SAT.Clause.eval_true_of_pos_mem (v := Var.Fresh st.nextFresh)
        · simp only [FVar.toVar]
          exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
        · simp only [σ_ext, freshIdx, ↓reduceIte]
          exact hSeq
      · -- Seq is false, ¬Seq is true
        apply SAT.Clause.eval_true_of_neg_mem (v := Var.Seq w.ti w.p)
        · exact List.mem_cons_self ..
        · simp only [σ_ext]
          simp only [Bool.not_eq_true] at hSeq ⊢
          exact hSeq

    · -- Clause [¬u, Seq] is satisfied
      -- Same logic: u = Seq, so either both true or both false
      by_cases hSeq : σ₀ (Var.Seq w.ti w.p) = true
      · -- Seq is true
        apply SAT.Clause.eval_true_of_pos_mem (v := Var.Seq w.ti w.p)
        · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
        · simp only [σ_ext]
          exact hSeq
      · -- u is false, ¬u is true
        apply SAT.Clause.eval_true_of_neg_mem (v := Var.Fresh st.nextFresh)
        · simp only [FVar.toVar]
          exact List.mem_cons_self ..
        · simp only [σ_ext, freshIdx, ↓reduceIte]
          simp only [Bool.not_eq_true] at hSeq ⊢
          exact hSeq

    · -- Base clauses are satisfied
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
              · next hEq =>
                  exfalso
                  have hNotIn := hWF.fresh_not_in_clauses hClause hLitMem
                  simp only [SAT.Lit.getVar] at hNotIn
                  exact hNotIn (congrArg Var.Fresh hEq)
              · exact hLitTrue
          | _ => exact hLitTrue
      | neg v =>
          simp only [SAT.Lit.eval] at hLitTrue ⊢
          cases v with
          | Fresh n =>
              simp only [σ_ext]
              split
              · next hEq =>
                  exfalso
                  have hNotIn := hWF.fresh_not_in_clauses hClause hLitMem
                  simp only [SAT.Lit.getVar] at hNotIn
                  exact hNotIn (congrArg Var.Fresh hEq)
              · exact hLitTrue
          | _ => exact hLitTrue

  · -- The iff: Sat ↔ u = true
    simp only [EncState.allocFresh, FVar.toVar]
    change (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) Formula.seq ↔
            σ_ext (Var.Fresh freshIdx) = true)
    simp only [σ_ext, ↓reduceIte]
    -- σ_ext (Fresh freshIdx) = σ₀ (Seq w.ti w.p) = isSequential (by hSeqIff)
    -- Sat ... seq = isSequential (by definition)
    simp only [Sat]
    exact hSeqIff.symm

end Encoding
