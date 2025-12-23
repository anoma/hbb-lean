import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.FormulaEncodingLemmasAll
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf

/-!
# Completeness for AtEnd Formula

The atEnd formula encodes `↓ φ` (formula holds at end of time).

## Encoding

```lean
encodeFormula b (Formula.atEnd φ) w st =
  let wEnd : WId b := ⟨w.p, ⟨0, _⟩, b.root⟩  -- Same participant, no event, at root
  let (u_body, st1) := encodeFormula b φ wEnd st
  let (u, st2) := EncState.allocFresh b st1
  -- Tseytin clauses for u ↔ u_body
  -- Forward: u → u_body  [¬u, u_body]
  -- Backward: u_body → u  [¬u_body, u]
  ...
```

## Completeness Strategy

If `Sat M ... (↓ φ)` holds, then `Sat M w.p † M.history φ` by semantics.
By IH at wEnd (with time = root = history), u_body can be set to true.
The Tseytin clauses then give u = true.
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- Completeness for atEnd: uses bidirectional IH at the end world.

    The atEnd formula `↓ φ` is true when φ holds at the end of history.
    The encoding creates a biconditional u ↔ u_body where u_body encodes φ
    at the "end world" (participant w.p, event †, time root).

    Key insight: `Sat M ... (↓ φ)` ↔ `Sat M w.p † M.history.val φ`.
    Using `prehistoryAt_root`, this is satisfaction at wEnd, so IH applies.

    The bidirectional property is: u = true ↔ Sat M ... (↓ φ)

    Note: hWF is needed to show well-formedness is preserved through encoding,
    allowing us to know that newly allocated Fresh vars don't appear in prior clauses. -/
theorem encodeFormula_complete_atEnd
    (b : Bounds S) (φ : Formula S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    -- Bidirectional IH: gives witness with u_body ↔ Sat φ
    (ih : ∀ (w : WId b) (st : EncState b),
      st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true →
      EncState.WellFormed st →
      ∃ σ_ext : SAT.Assignment (Var b),
        (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
        (encodeFormula b φ w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
        (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) φ ↔
         σ_ext (FVar.toVar b (encodeFormula b φ w st).1) = true))
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b (Formula.atEnd φ) w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.atEnd φ) ↔
       σ_ext (FVar.toVar b (encodeFormula b (Formula.atEnd φ) w st).1) = true) := by
  -- The bidirectional property: u = true ↔ Sat M ... (↓ φ)

  -- Define the end world
  let wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩

  -- The key connection: prehistoryAt at root = M.history.val
  have hRootPre : prehistoryAt hFits.view b.root = M.history.val :=
    prehistoryAt_root hFits.view

  -- And decodeMaybeEvent at wEnd.ei = † (which is MaybeEvent.none)
  have hEventNone : b.decodeMaybeEvent wEnd.ei = MaybeEvent.none := by
    simp only [wEnd, Bounds.decodeMaybeEvent]

  -- Use bidirectional IH on φ at wEnd to get a witness σ_body with u_body ↔ Sat φ
  have ⟨σ_body, hAgree_body, hClauses_body, hIff_body⟩ :=
    ih wEnd st hBaseClauses hWF

  -- Now we need to extend σ_body with the fresh variable u for atEnd
  -- The encoding creates u ↔ u_body via two clauses

  -- Get the structure of the encoding
  let bodyRes := encodeFormula b φ wEnd st
  let u_body := bodyRes.1
  let st_body := bodyRes.2
  let freshIdx := st_body.nextFresh

  -- Define σ_ext: extends σ_body with the new fresh var u = u_body
  let σ_ext : SAT.Assignment (Var b) := fun v =>
    match v with
    | Var.Fresh n =>
        if n = freshIdx then σ_body (FVar.toVar b u_body)
        else σ_body v
    | _ => σ_body v

  use σ_ext

  refine ⟨?_, ?_, ?_⟩

  · -- Non-fresh variables agree with assignmentOf
    intro v hNotFresh
    cases v with
    | Fresh n =>
        exfalso
        apply hNotFresh
        simp only [isFreshVar, Var.isFresh]
    | _ =>
        simp only [σ_ext]
        exact hAgree_body _ hNotFresh

  · -- All clauses satisfied
    simp only [encodeFormula, EncState.addClause, EncState.allocFresh]
    simp only [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_⟩

    · -- Clause [¬u_body, u] is satisfied
      -- We need: u_body = true → u satisfied by pos u
      -- Or: u_body = false → clause satisfied by neg u_body
      by_cases hU_body : σ_body (FVar.toVar b u_body) = true
      · -- u_body = true, so u = true (by our construction)
        apply SAT.Clause.eval_true_of_pos_mem (v := Var.Fresh st_body.nextFresh)
        · simp only [FVar.toVar]
          exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
        · simp only [σ_ext, freshIdx, ↓reduceIte]
          exact hU_body
      · -- u_body = false, clause satisfied by ¬u_body
        apply SAT.Clause.eval_true_of_neg_mem (v := FVar.toVar b u_body)
        · exact List.mem_cons_self ..
        · simp only [σ_ext, FVar.toVar]
          split
          · next hEq =>
              have hLt := encodeFormula_controlVar_lt_nextFresh b φ wEnd st
              exfalso
              exact Nat.lt_irrefl u_body.id (hEq ▸ hLt)
          · simp only [Bool.not_eq_true] at hU_body ⊢
            exact hU_body

    · -- Clause [¬u, u_body] is satisfied
      by_cases hU_body : σ_body (FVar.toVar b u_body) = true
      · -- u_body = true
        apply SAT.Clause.eval_true_of_pos_mem (v := FVar.toVar b u_body)
        · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
        · simp only [σ_ext, FVar.toVar]
          split
          · next hEq =>
              have hLt := encodeFormula_controlVar_lt_nextFresh b φ wEnd st
              exfalso
              exact Nat.lt_irrefl u_body.id (hEq ▸ hLt)
          · exact hU_body
      · -- u_body = false, so u = false (by our construction), ¬u satisfied
        apply SAT.Clause.eval_true_of_neg_mem (v := Var.Fresh st_body.nextFresh)
        · simp only [FVar.toVar]
          exact List.mem_cons_self ..
        · simp only [σ_ext, freshIdx, ↓reduceIte]
          simp only [Bool.not_eq_true] at hU_body ⊢
          exact hU_body

    · -- Base clauses (st_body.clauses) are satisfied
      have hWF_body : EncState.WellFormed st_body :=
        encodeFormula_preserves_wf b φ wEnd st hWF
      rw [List.all_eq_true] at hClauses_body ⊢
      intro clause hClause
      have hBody := hClauses_body clause hClause
      rw [SAT.Clause.eval_eq_any] at hBody ⊢
      rw [List.any_eq_true] at hBody ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hBody
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
                  have hNotIn := hWF_body.fresh_not_in_clauses hClause hLitMem
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
                  have hNotIn := hWF_body.fresh_not_in_clauses hClause hLitMem
                  simp only [SAT.Lit.getVar] at hNotIn
                  exact hNotIn (congrArg Var.Fresh hEq)
              · exact hLitTrue
          | _ => exact hLitTrue

  · -- The iff: Sat M ... (↓ φ) ↔ σ_ext(u) = true
    simp only [encodeFormula, EncState.allocFresh, FVar.toVar]
    change (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.atEnd φ) ↔
            σ_ext (Var.Fresh freshIdx) = true)
    simp only [σ_ext, ↓reduceIte]
    -- σ_ext(Fresh freshIdx) = σ_body(u_body)
    -- And hIff_body: Sat M wEnd.p ... φ ↔ σ_body(u_body) = true
    -- Sat M ... (↓ φ) ↔ Sat M w.p † M.history.val φ ↔ Sat M wEnd.p ... φ
    simp only [Sat]
    -- Need to show: Sat M w.p † H φ ↔ σ_body(u_body) = true
    -- where H = M.history.val = prehistoryAt hFits.view b.root = prehistoryAt wEnd.ti
    -- hIff_body gives: Sat M wEnd.p (decodeMaybeEvent wEnd.ei) (prehistoryAt wEnd.ti) φ ↔ ...
    -- = Sat M w.p † (prehistoryAt b.root) φ ↔ ...
    -- = Sat M w.p † M.history.val φ ↔ ... (by hRootPre)
    have hWEndP : wEnd.p = w.p := rfl
    have hWEndTi : prehistoryAt hFits.view wEnd.ti = M.history.val := hRootPre
    rw [← hWEndP, ← hEventNone, ← hWEndTi]
    exact hIff_body

end Encoding
