import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Common

/-!
# Seq Case: Structural Determinism for New Clauses
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- Seq case: NEW clause is [neg u', Seq ti p] or [pos u', neg (Seq ti p)] -/
lemma structural_determinism_new_clauses_seq (b : Bounds S) (w : WId b)
    (st st' : EncState b) (offset : Nat) (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (encodeFormula b Formula.seq w st).2.clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true) :
    let σ' := shiftedAssignment b σ st'.nextFresh offset
    ∀ c ∈ (encodeFormula b Formula.seq w st').2.clauses, c ∉ st'.clauses →
      SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  simp only [encodeFormula, EncState.addClause, EncState.allocFresh] at hc
  cases hc with
  | head =>
      -- Second clause added: [neg Seq, pos u'] = [SAT.Lit.neg seqVar, SAT.Lit.pos u]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or, FVar.toVar]
      simp only [σ', shiftedAssignment_at_threshold]
      have hEqIdx : st'.nextFresh - offset = st.nextFresh := by
        rw [hOffset]; exact Nat.sub_sub_self hMono
      simp only [hEqIdx]
      have hNewSt : [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (Var.Fresh st.nextFresh)] ∈
          (encodeFormula b Formula.seq w st).2.clauses := by
        simp only [encodeFormula, EncState.addClause, EncState.allocFresh, FVar.toVar]
        exact List.Mem.head _
      have hNotInSt :
          [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (Var.Fresh st.nextFresh)] ∉
            st.clauses := by
        intro hIn
        have hWFc := hWF _ hIn
        unfold clauseFreshBelow litFreshBelow at hWFc
        have := hWFc (SAT.Lit.pos (Var.Fresh st.nextFresh))
          (List.mem_cons_of_mem _ (List.Mem.head _))
        exact Nat.lt_irrefl _ this
      exact hSatNew _ hNewSt hNotInSt
  | tail _ hTail1 =>
      cases hTail1 with
      | head =>
          -- First clause added: [neg u', pos Seq] = [SAT.Lit.neg u, SAT.Lit.pos seqVar]
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or, FVar.toVar]
          simp only [σ', shiftedAssignment_at_threshold]
          have hEqIdx : st'.nextFresh - offset = st.nextFresh := by
            rw [hOffset]; exact Nat.sub_sub_self hMono
          simp only [hEqIdx]
          have hNewSt : [SAT.Lit.neg (Var.Fresh st.nextFresh), SAT.Lit.pos (Var.Seq w.ti w.p)] ∈
              (encodeFormula b Formula.seq w st).2.clauses := by
            simp only [encodeFormula, EncState.addClause, EncState.allocFresh, FVar.toVar]
            exact List.mem_cons_of_mem _ (List.Mem.head _)
          have hNotInSt :
              [SAT.Lit.neg (Var.Fresh st.nextFresh), SAT.Lit.pos (Var.Seq w.ti w.p)] ∉
                st.clauses := by
            intro hIn
            have hWFc := hWF _ hIn
            unfold clauseFreshBelow litFreshBelow at hWFc
            have := hWFc (SAT.Lit.neg (Var.Fresh st.nextFresh)) (List.Mem.head _)
            exact Nat.lt_irrefl _ this
          exact hSatNew _ hNewSt hNotInSt
      | tail _ hTail' => exact absurd hTail' hcNew

end Encoding
