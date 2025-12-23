import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.Syntax
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.FormulaEncoding

/-!
# Tseytin Correctness for Bot (⊥)

This file proves that the Tseytin encoding correctly captures the semantics of the
bottom formula (⊥).

## Main Result

- `encode_bot_correct`: If the encoding produces control variable u with the bot clause [¬u],
  and that clause is satisfied, then u = false.

## Strategy

The bot encoding simply adds the unit clause [¬u] to enforce u = false.
-/

open ModalDistribution Encoding Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Clause Extraction Helpers -/

/-- For bot encoding, the clause [¬u] is in the result. -/
lemma encodeFormula_bot_has_neg_clause (b : Bounds S) (w : WId b) (st : EncState b) :
    let (u, st') := encodeFormula b Formula.bot w st
    [SAT.Lit.neg (FVar.toVar b u)] ∈ st'.clauses := by
  unfold encodeFormula
  simp [EncState.allocFresh, EncState.addClause]

/-! ## Tseytin Correctness for Bot -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The bot encoding adds a single clause [¬u] which forces u = false.
    If this clause is satisfied and u = true, we have a contradiction.

    This correctly captures the semantics of ⊥, which is never satisfiable. -/
lemma encode_bot_correct (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u : FVar b) (clauses : List (SAT.Clause (Var b)))
    (hEncoding : clauses = [[SAT.Lit.neg (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true)
    (hU : σ (FVar.toVar b u) = true) :
    False := by
  -- The encoding produces a single clause [¬u]
  -- If this clause is satisfied, then σ(u) must be false
  -- But we're given σ(u) = true, so we have a contradiction

  have hClauseIn : [SAT.Lit.neg (FVar.toVar b u)] ∈ clauses := by
    rw [hEncoding]
    simp

  have hClauseTrue : SAT.Clause.eval σ [SAT.Lit.neg (FVar.toVar b u)] = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Evaluate the clause [¬u]
  unfold SAT.Clause.eval at hClauseTrue
  simp [SAT.Lit.eval, hU] at hClauseTrue

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Alternative formulation: The bot encoding correctly captures that ⊥ never holds.

    If the encoding clauses are satisfied, then σ(u) = true is impossible,
    which correctly represents that Sat M w Formula.bot is always False. -/
lemma encode_bot_never_true (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u : FVar b) (clauses : List (SAT.Clause (Var b)))
    (hEncoding : clauses = [[SAT.Lit.neg (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true) :
    σ (FVar.toVar b u) = false := by
  -- Proof by contradiction
  by_contra hFalse
  -- If σ(u) ≠ false, then σ(u) = true (since Bool is decidable)
  simp at hFalse
  -- But then encode_bot_correct gives us a contradiction
  exact encode_bot_correct b σ u clauses hEncoding hSat hFalse

/-- Adequacy for bot encoding: σ(u) = true iff bot is satisfied (which is never).
    The encoding adds [¬u], so σ(u) = true is impossible, correctly representing
    that Sat M w bot ↔ False. -/
lemma encodeFormula_bot_adequate (b : Bounds S) (w : WId b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses : (encodeFormula b Formula.bot w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b (encodeFormula b Formula.bot w st).1) = true) ↔ False := by
  constructor
  · -- Forward: σ(u) = true → False
    intro hU
    -- Extract that [¬u] is in the clauses
    have hNegClause := encodeFormula_bot_has_neg_clause b w st
    -- The clause is the neg clause
    set neg_clause := [SAT.Lit.neg (FVar.toVar b (encodeFormula b Formula.bot w st).1)]
    -- Since all clauses are satisfied, [¬u] evaluates to true
    have hNegSat : SAT.Clause.eval σ neg_clause = true := by
      have hAll := List.all_eq_true.mp hClauses
      exact hAll neg_clause hNegClause
    -- But [¬u] evaluating to true means σ(u) = false
    have : σ (FVar.toVar b (encodeFormula b Formula.bot w st).1) = false := by
      cases hCheck : σ (FVar.toVar b (encodeFormula b Formula.bot w st).1)
      · rfl
      · -- If σ(u) = true, then Lit.eval (neg u) = false, so clause is false
        -- But hNegSat says clause evaluates to true, contradiction
        have hAny := SAT.Clause.eval_eq_any (σ := σ) (C := neg_clause)
        rw [hAny, List.any_eq_true] at hNegSat
        obtain ⟨lit, hMem, hLitTrue⟩ := hNegSat
        have hLitIs : lit = SAT.Lit.neg (FVar.toVar b (encodeFormula b Formula.bot w st).1) :=
          List.mem_singleton.mp hMem
        rw [hLitIs] at hLitTrue
        simp [SAT.Lit.eval, hCheck] at hLitTrue
    rw [this] at hU
    cases hU
  · -- Backward: False → σ(u) = true (vacuous)
    intro hFalse
    exact False.elim hFalse

end Encoding
