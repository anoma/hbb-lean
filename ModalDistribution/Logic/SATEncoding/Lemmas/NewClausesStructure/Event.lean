import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Common
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.ShiftedAssignment

/-!
# Event Case: Structural Determinism for New Clauses
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- Event case: similar structure to predicate, uses encodeFormulaEvent helper -/
lemma structural_determinism_new_clauses_event (b : Bounds S) (atom : EventAtom S) (w : WId b)
    (st st' : EncState b) (offset : Nat) (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (encodeFormula b (Formula.event atom) w st).2.clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true) :
    let σ' := shiftedAssignment b σ st'.nextFresh offset
    ∀ c ∈ (encodeFormula b (Formula.event atom) w st').2.clauses, c ∉ st'.clauses →
      SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  -- Event encoding has three branches based on decodeMaybeEvent:
  -- 1. Guard match (e = evt): uses encodeFormulaEvent
  -- 2. Guard mismatch (e ≠ evt): just allocFresh + addClause [¬u]
  -- 3. No event (none): just allocFresh + addClause [¬u]

  let evt : Signature.EventType S := ⟨atom.sym, atom.args⟩
  simp only [encodeFormula] at hc hSatNew

  -- Case split on decodeMaybeEvent
  cases hDecode : b.decodeMaybeEvent w.ei with
  | none =>
      -- No event: encoding is just [¬u] where u = Fresh(st.nextFresh)
      -- Same structure at st and st', just u' = Fresh(st'.nextFresh)
      simp only [hDecode, EncState.addClause, EncState.allocFresh] at hc hSatNew
      -- c is either the unit clause [¬(Fresh st'.nextFresh)] or inherited from st'
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hOld
      · -- c = [¬(FVar.toVar b (allocFresh st').1)] (the NEW clause)
        -- The corresponding clause at st is similar
        -- Note: FVar.toVar b x = Var.Fresh x.id, and (allocFresh st).1.id = st.nextFresh
        simp only [FVar.toVar, EncState.allocFresh] at hSatNew ⊢
        have hCorrMem : [SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] ∈
            ([SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] :: st.clauses) := List.Mem.head _
        have hCorrNotOld : [SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] ∉ st.clauses := by
          intro hIn
          have hWFClause := hWF _ hIn
          unfold clauseFreshBelow at hWFClause
          have hLit : SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh) ∈
              [SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] := List.Mem.head _
          have hBound := hWFClause _ hLit
          simp only [litFreshBelow] at hBound
          exact Nat.lt_irrefl _ hBound
        have hSatCorr := hSatNew _ hCorrMem hCorrNotOld
        -- Now show σ' evaluates the st' clause the same way
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hSatCorr
        -- σ'(Fresh st'.nextFresh) = σ(Fresh st.nextFresh) by unshifting
        simp only [σ', shiftedAssignment]
        have hGe : ¬(st'.nextFresh < st'.nextFresh) := Nat.lt_irrefl _
        simp only [hGe, ↓reduceIte, Var.unshift]
        -- st'.nextFresh - offset = st.nextFresh
        have hEqNF : st'.nextFresh - offset = st.nextFresh := by
          rw [hOffset]; omega
        rw [hEqNF]; exact hSatCorr
      · -- c ∈ st'.clauses, but hcNew says c ∉ st'.clauses - contradiction
        exact absurd hOld hcNew
  | some e =>
      simp only [hDecode] at hc hSatNew
      -- Case split on whether e = evt
      by_cases hEqEvt : e = evt
      · -- Guard match: uses encodeFormulaEvent
        -- e = evt, so substitute to simplify
        subst hEqEvt
        -- The dite `if h : evt = evt then ... else ...` reduces to encodeFormulaEvent
        have hOffsetEq : st'.nextFresh = st.nextFresh + offset := by
          rw [hOffset]; omega
        -- evt = { sym := atom.sym, args := atom.args } is definitionally true
        -- The if condition after subst is `evt = { sym := atom.sym, args := atom.args }`
        -- which is definitionally true, so reduce the if
        have hEvtEq : evt = { sym := atom.sym, args := atom.args } := rfl
        -- Split on the if in hc and hSatNew
        split at hc
        · -- True branch: encodeFormulaEvent
          split at hSatNew
          · -- Now apply encodeFormulaEvent_structural_determinism
            have hEventSD := encodeFormulaEvent_structural_determinism b w evt st st' offset
              hOffsetEq hMono hWF σ hSatNew
            -- The σ' from the helper uses same pattern as shiftedAssignment
            have hResult := hEventSD c hc hcNew
            -- Show σ' matches the helper's σ' definition
            convert hResult using 2
            funext v
            -- shiftedAssignment matches on v: for Fresh n, it uses if/else; for others, σ v
            unfold σ' shiftedAssignment
            cases v <;> rfl
          · -- False branch in hSatNew but we're in true branch for hc - contradiction
            rename_i hEvtNeq
            exact absurd hEvtEq hEvtNeq
        · -- False branch: not encodeFormulaEvent - contradiction with hEvtEq
          rename_i hEvtNeq
          exact absurd hEvtEq hEvtNeq
      · -- Guard mismatch: just [¬u] clause (same as none case)
        -- The encoding is: if h : e = evt then encodeFormulaEvent else (u, addClause [¬u])
        -- With hEqEvt : ¬(e = evt), we're in the else branch
        have hEvtEq : { sym := atom.sym, args := atom.args } = evt := rfl
        have hNeq : ¬(e = { sym := atom.sym, args := atom.args }) := by
          intro h; apply hEqEvt; rw [h, hEvtEq]
        -- Split on the if in hc and hSatNew
        split at hc
        · -- True branch: contradiction with hNeq
          rename_i hEvtTrue
          exact absurd hEvtTrue hNeq
        · -- False branch: addClause structure
          split at hSatNew
          · -- True branch in hSatNew: contradiction
            rename_i _ hEvtTrue
            exact absurd hEvtTrue hNeq
          · -- False branch in hSatNew: now continue with the proof
            -- Now in the ¬(e = evt) case with addClause structure
            simp only [EncState.addClause, EncState.allocFresh, List.mem_cons] at hc
            rcases hc with rfl | hOld
            · -- Unfold FVar.toVar to Var.Fresh
              simp only [FVar.toVar, EncState.allocFresh] at hSatNew ⊢
              have hCorrMem : [SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] ∈
                  ([SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] :: st.clauses) := List.Mem.head _
              have hCorrNotOld : [SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] ∉ st.clauses := by
                intro hIn
                have hWFClause := hWF _ hIn
                unfold clauseFreshBelow at hWFClause
                have hLit : SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh) ∈
                    [SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] := List.Mem.head _
                have hBound := hWFClause _ hLit
                simp only [litFreshBelow] at hBound
                exact Nat.lt_irrefl _ hBound
              have hSatCorr := hSatNew _ hCorrMem hCorrNotOld
              simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
              simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hSatCorr
              simp only [σ', shiftedAssignment]
              have hGe : ¬(st'.nextFresh < st'.nextFresh) := Nat.lt_irrefl _
              simp only [hGe, ↓reduceIte, Var.unshift]
              have hEqNF : st'.nextFresh - offset = st.nextFresh := by
                rw [hOffset]; omega
              rw [hEqNF]; exact hSatCorr
            · exact absurd hOld hcNew


end Encoding
