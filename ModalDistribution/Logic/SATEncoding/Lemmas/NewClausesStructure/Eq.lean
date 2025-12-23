import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Common

/-!
# Eq Case: Structural Determinism for New Clauses
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- Eq case: NEW clause is [pos u'] or [neg u'] depending on equality -/
lemma structural_determinism_new_clauses_eq (b : Bounds S) (v1 v2 : S.Value) (w : WId b)
    (st st' : EncState b) (offset : Nat) (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (encodeFormula b (Formula.eq v1 v2) w st).2.clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true) :
    let σ' := shiftedAssignment b σ st'.nextFresh offset
    ∀ c ∈ (encodeFormula b (Formula.eq v1 v2) w st').2.clauses, c ∉ st'.clauses →
      SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  simp only [encodeFormula, EncState.addClause, EncState.allocFresh] at hc
  by_cases hEq : v1 == v2 <;> simp only [hEq, ↓reduceIte] at hc
  · -- v1 = v2: clause is [pos u'] or inherited
    cases hc with
    | head =>
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or, FVar.toVar]
        simp only [σ', shiftedAssignment_at_threshold]
        have hEqIdx : st'.nextFresh - offset = st.nextFresh := by
          rw [hOffset]; exact Nat.sub_sub_self hMono
        simp only [hEqIdx]
        have hNewSt : [SAT.Lit.pos (Var.Fresh st.nextFresh)] ∈
            (encodeFormula b (Formula.eq v1 v2) w st).2.clauses := by
          simp only [encodeFormula, hEq, ↓reduceIte, EncState.addClause, EncState.allocFresh,
            FVar.toVar]
          exact List.Mem.head _
        have hNotInSt : [SAT.Lit.pos (Var.Fresh st.nextFresh)] ∉ st.clauses := by
          intro hIn
          have hWFc := hWF _ hIn
          unfold clauseFreshBelow litFreshBelow at hWFc
          have := hWFc (SAT.Lit.pos (Var.Fresh st.nextFresh)) (List.Mem.head _)
          exact Nat.lt_irrefl _ this
        exact hSatNew _ hNewSt hNotInSt
    | tail _ hTail => exact absurd hTail hcNew
  · -- v1 ≠ v2: clause is [neg u'] or inherited
    cases hc with
    | head =>
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar]
        simp only [σ', shiftedAssignment_at_threshold]
        have hEqIdx : st'.nextFresh - offset = st.nextFresh := by
          rw [hOffset]; exact Nat.sub_sub_self hMono
        simp only [hEqIdx]
        have hNewSt : [SAT.Lit.neg (Var.Fresh st.nextFresh)] ∈
            (encodeFormula b (Formula.eq v1 v2) w st).2.clauses := by
          simp only [encodeFormula, hEq, EncState.addClause, EncState.allocFresh,
            FVar.toVar]
          exact List.Mem.head _
        have hNotInSt : [SAT.Lit.neg (Var.Fresh st.nextFresh)] ∉ st.clauses := by
          intro hIn
          have hWFc := hWF _ hIn
          unfold clauseFreshBelow litFreshBelow at hWFc
          have := hWFc (SAT.Lit.neg (Var.Fresh st.nextFresh)) (List.Mem.head _)
          exact Nat.lt_irrefl _ this
        have hEvalSt := hSatNew _ hNewSt hNotInSt
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hEvalSt
        rw [Bool.not_eq_true'] at hEvalSt
        simp only [hEvalSt, Bool.not_false, Bool.false_or]
    | tail _ hTail => exact absurd hTail hcNew

end Encoding
