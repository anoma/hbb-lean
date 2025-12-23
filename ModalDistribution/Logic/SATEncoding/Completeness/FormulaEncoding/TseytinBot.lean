import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf

/-!
# Completeness for Bot Formula

The bot formula encodes `⊥` (falsity). Since `Sat M ... ⊥ = False` by definition,
the encoding sets u = false, and the iff holds: `False ↔ (u = true)` is `False ↔ False`.

## Encoding

```lean
encodeFormula b Formula.bot w st =
  let (u, st1) := EncState.allocFresh b st
  (u, EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u)])
```

The clause `[¬u]` forces u = false in any satisfying assignment.

## Bidirectional Completeness

We need to show: `Sat M ... ⊥ ↔ σ_ext(u) = true`
- LHS is False (by definition of Sat for ⊥)
- RHS is false (because encoding adds clause [¬u] forcing u = false)
- So the iff holds: False ↔ False
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- Completeness for bot: Sat ⊥ ↔ u = true, both false. -/
theorem encodeFormula_complete_bot
    (b : Bounds S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b Formula.bot w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) Formula.bot ↔
       σ_ext (FVar.toVar b (encodeFormula b Formula.bot w st).1) = true) := by
  -- Unfold encoding for bot
  simp only [encodeFormula]

  let freshIdx := st.nextFresh
  let σ₀ := assignmentOf b M hFits

  -- Define σ_ext: set u = false (to satisfy clause [¬u])
  let σ_ext : SAT.Assignment (Var b) := fun v =>
    match v with
    | Var.Fresh n => if n = freshIdx then false else σ₀ v
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
    constructor
    · -- The new clause [¬u] is satisfied because σ_ext(u) = false
      simp only [SAT.Clause.eval, SAT.Lit.eval, FVar.toVar]
      -- Need to show: (!σ_ext (Fresh freshIdx)) = true
      -- Since σ_ext (Fresh freshIdx) = false by construction
      change (!σ_ext (Var.Fresh st.nextFresh)) = true
      have : st.nextFresh = freshIdx := rfl
      simp only [σ_ext, this, ↓reduceIte, Bool.not_false]
    · -- Base clauses are satisfied (same pattern as other Tseytin proofs)
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
                  -- n = freshIdx = st.nextFresh, impossible by well-formedness
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
                  -- n = freshIdx = st.nextFresh, impossible by well-formedness
                  exfalso
                  have hNotIn := hWF.fresh_not_in_clauses hClause hLitMem
                  simp only [SAT.Lit.getVar] at hNotIn
                  exact hNotIn (congrArg Var.Fresh hEq)
              · exact hLitTrue
          | _ => exact hLitTrue

  · -- The iff: Sat ⊥ ↔ σ_ext(u) = true
    -- LHS is False, RHS is false (since we set u = false)
    constructor
    · -- Forward: Sat ⊥ → u = true (vacuously true since Sat ⊥ = False)
      intro hSat
      unfold Sat at hSat
      exact False.elim hSat
    · -- Backward: u = true → Sat ⊥
      intro hU
      -- But σ_ext(u) = false by construction, contradiction
      simp only [EncState.allocFresh, FVar.toVar] at hU
      have hFresh : st.nextFresh = freshIdx := rfl
      simp only [σ_ext, hFresh, ↓reduceIte] at hU
      exact False.elim (Bool.false_ne_true hU)

end Encoding
