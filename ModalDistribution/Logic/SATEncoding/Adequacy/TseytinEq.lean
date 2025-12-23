import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.FormulaEncoding

/-!
# Tseytin Correctness for Equality (=)

This file proves that the Tseytin encoding correctly captures the semantics of
equality formulas.

## Main Result

- `encode_eq_correct`: If the encoding produces control variable u for equality v1 = v2,
  then u = true iff the decoded values are equal.

## Strategy

The equality encoding is decidable and uses the decidable equality instance.
-/

open ModalDistribution Encoding

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.Value S)]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-! ## Tseytin Correctness for Equality -/

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Equality encoding for equal values: [u] forces u = true. -/
lemma encode_eq_equal (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u : FVar b) (clauses : List (SAT.Clause (Var b)))
    (hEncoding : clauses = [[SAT.Lit.pos (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true) :
    σ (FVar.toVar b u) = true := by
  -- The encoding produces clause [u]
  -- This forces σ(u) = true
  have hClauseIn : [SAT.Lit.pos (FVar.toVar b u)] ∈ clauses := by
    rw [hEncoding]
    simp

  have hClauseTrue : SAT.Clause.eval σ [SAT.Lit.pos (FVar.toVar b u)] = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Evaluate the clause [u]
  unfold SAT.Clause.eval at hClauseTrue
  simp [SAT.Lit.eval] at hClauseTrue
  exact hClauseTrue

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Equality encoding for unequal values: [¬u] forces u = false. -/
lemma encode_eq_unequal (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u : FVar b) (clauses : List (SAT.Clause (Var b)))
    (hEncoding : clauses = [[SAT.Lit.neg (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true) :
    σ (FVar.toVar b u) = false := by
  -- The encoding produces clause [¬u]
  -- This forces σ(u) = false
  have hClauseIn : [SAT.Lit.neg (FVar.toVar b u)] ∈ clauses := by
    rw [hEncoding]
    simp

  have hClauseTrue : SAT.Clause.eval σ [SAT.Lit.neg (FVar.toVar b u)] = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Proof by contradiction
  by_contra hFalse
  -- If σ(u) ≠ false, then σ(u) = true
  simp at hFalse
  -- But the clause [¬u] = true means σ(u) must be false
  unfold SAT.Clause.eval at hClauseTrue
  simp [SAT.Lit.eval, hFalse] at hClauseTrue

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Main correctness: σ(u) = true ↔ v1 = v2.

    The eq encoding correctly captures decidable equality. -/
lemma encode_eq_correct (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u : FVar b) (clauses : List (SAT.Clause (Var b)))
    (v1 v2 : Signature.Value S)
    (hEncoding : clauses = (if v1 == v2 then [[SAT.Lit.pos (FVar.toVar b u)]]
                             else [[SAT.Lit.neg (FVar.toVar b u)]]))
    (hSat : clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b u) = true) ↔ (v1 = v2) := by
  constructor
  · -- Forward: σ(u) = true → v1 = v2
    intro hU
    by_contra hNe
    -- If v1 ≠ v2, then encoding produces [¬u]
    have hEnc : clauses = [[SAT.Lit.neg (FVar.toVar b u)]] := by
      simp [hEncoding]
      intro heq
      exact hNe heq
    -- By encode_eq_unequal, σ(u) = false
    have hUFalse := encode_eq_unequal b σ u clauses hEnc hSat
    -- Contradiction with hU
    simp [hU] at hUFalse
  · -- Backward: v1 = v2 → σ(u) = true
    intro hEq
    -- If v1 = v2, then encoding produces [u]
    have hEnc : clauses = [[SAT.Lit.pos (FVar.toVar b u)]] := by
      simp [hEncoding, hEq]
    -- By encode_eq_equal, σ(u) = true
    exact encode_eq_equal b σ u clauses hEnc hSat

/-- Adequacy for encodeFormula eq: σ(u) = true ↔ v1 = v2 (↔ Sat M w (.eq v1 v2)). -/
lemma encodeFormula_eq_adequate (b : Bounds S) (w : WId b) (st : EncState b)
    (σ : SAT.Assignment (Var b)) (v1 v2 : Signature.Value S)
    (hClauses : (encodeFormula b (.eq v1 v2) w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b (encodeFormula b (.eq v1 v2) w st).1) = true) ↔ (v1 = v2) := by
  -- Encoding produces: if v1 == v2 then [u] else [¬u]
  -- Use encode_eq_correct which already proves the iff
  simp only [encodeFormula, EncState.allocFresh, EncState.addClause] at hClauses ⊢
  constructor
  · -- Forward: σ(u) = true → v1 = v2
    intro hU
    by_contra hNe
    -- If v1 ≠ v2, the encoding produces [¬u]
    have hBEqFalse : (v1 == v2) = false := by simp [hNe]
    simp only [hBEqFalse] at hClauses hU
    -- The clauses include [¬u] at the head
    have hClause : SAT.Clause.eval σ [SAT.Lit.neg (FVar.toVar b ⟨st.nextFresh⟩)] = true := by
      have hAll := List.all_eq_true.mp hClauses
      exact hAll _ (by simp)
    -- Evaluating [¬u] with σ(u) = true gives false, contradiction
    unfold SAT.Clause.eval SAT.Lit.eval at hClause
    simp [hU] at hClause
  · -- Backward: v1 = v2 → σ(u) = true
    intro hEq
    -- If v1 = v2, the encoding produces [u]
    have hBEqTrue : (v1 == v2) = true := by simp [hEq]
    simp only [hBEqTrue] at hClauses
    -- The clauses include [u] at the head
    have hClause : SAT.Clause.eval σ [SAT.Lit.pos (FVar.toVar b ⟨st.nextFresh⟩)] = true := by
      have hAll := List.all_eq_true.mp hClauses
      exact hAll _ (by simp)
    -- Evaluating [u] = true means σ(u) = true
    unfold SAT.Clause.eval SAT.Lit.eval at hClause
    simp at hClause
    exact hClause

end Encoding
