import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Common
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.ShiftedAssignment

/-!
# Imp Case: Structural Determinism for New Clauses
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- Imp case: NEW clauses are 3 Tseytin clauses plus recursive NEW clauses from φ1 and φ2 -/
lemma structural_determinism_new_clauses_imp (b : Bounds S) (φ1 φ2 : Formula S) (w : WId b)
    (st st' : EncState b) (offset : Nat) (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st) (hWF' : EncState.WellFormed st')
    (hNonFreshCompat : nonFreshClausesCompat st st')
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (encodeFormula b (Formula.imp φ1 φ2) w st).2.clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true)
    (ih1 : ∀ (w : WId b) (st st' : EncState b) (offset : Nat),
           offset = st'.nextFresh - st.nextFresh →
           st.nextFresh ≤ st'.nextFresh →
           EncState.WellFormed st → EncState.WellFormed st' →
           nonFreshClausesCompat st st' →
           (∀ c ∈ (encodeFormula b φ1 w st).2.clauses, c ∉ st.clauses → SAT.Clause.eval σ c = true) →
           let σ' := shiftedAssignment b σ st'.nextFresh offset
           ∀ c ∈ (encodeFormula b φ1 w st').2.clauses, c ∉ st'.clauses → SAT.Clause.eval σ' c = true)
    (ih2 : ∀ (w : WId b) (st st' : EncState b) (offset : Nat),
           offset = st'.nextFresh - st.nextFresh →
           st.nextFresh ≤ st'.nextFresh →
           EncState.WellFormed st → EncState.WellFormed st' →
           nonFreshClausesCompat st st' →
           (∀ c ∈ (encodeFormula b φ2 w st).2.clauses, c ∉ st.clauses → SAT.Clause.eval σ c = true) →
           let σ' := shiftedAssignment b σ st'.nextFresh offset
           ∀ c ∈ (encodeFormula b φ2 w st').2.clauses, c ∉ st'.clauses → SAT.Clause.eval σ' c = true) :
    let σ' := shiftedAssignment b σ st'.nextFresh offset
    ∀ c ∈ (encodeFormula b (Formula.imp φ1 φ2) w st').2.clauses, c ∉ st'.clauses →
      SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  simp only [encodeFormula] at hc

  -- Define intermediate states for st-encoding
  let u1 := (encodeFormula b φ1 w st).1
  let st1 := (encodeFormula b φ1 w st).2
  let u2 := (encodeFormula b φ2 w st1).1
  let st2 := (encodeFormula b φ2 w st1).2
  let u := (EncState.allocFresh b st2).1
  let st3 := (EncState.allocFresh b st2).2

  -- Define intermediate states for st'-encoding
  let u1' := (encodeFormula b φ1 w st').1
  let st1' := (encodeFormula b φ1 w st').2
  let u2' := (encodeFormula b φ2 w st1').1
  let st2' := (encodeFormula b φ2 w st1').2
  let u' := (EncState.allocFresh b st2').1
  let st3' := (EncState.allocFresh b st2').2

  -- Offset relationships from helper lemmas
  have hSt1Mono : st.nextFresh ≤ st1.nextFresh := encodeFormula_nextFresh_mono b φ1 w st
  have hSt2Mono : st1.nextFresh ≤ st2.nextFresh := encodeFormula_nextFresh_mono b φ2 w st1
  have hSt1'Mono : st'.nextFresh ≤ st1'.nextFresh := encodeFormula_nextFresh_mono b φ1 w st'
  have hSt2'Mono : st1'.nextFresh ≤ st2'.nextFresh := encodeFormula_nextFresh_mono b φ2 w st1'

  -- From hMono and hOffset, we have st'.nextFresh = st.nextFresh + offset
  have hStEq : st'.nextFresh = st.nextFresh + offset := by rw [hOffset]; omega

  have hOffset1' : st1'.nextFresh = st1.nextFresh + offset := by
    have := encodeFormula_nextFresh_offset b φ1 w st st' offset hStEq
    simp only [st1, st1'] at this ⊢
    exact this
  have hOffset1 : st1'.nextFresh - st1.nextFresh = offset := by
    simp only [hOffset1']; omega
  have hMono1 : st1.nextFresh ≤ st1'.nextFresh := by
    simp only [hOffset1']; omega

  have hSt1Eq : st1'.nextFresh = st1.nextFresh + offset := hOffset1'

  have hOffset2' : st2'.nextFresh = st2.nextFresh + offset := by
    have := encodeFormula_nextFresh_offset b φ2 w st1 st1' offset hSt1Eq
    simp only [st2, st2'] at this ⊢
    exact this
  have hOffset2 : st2'.nextFresh - st2.nextFresh = offset := by
    simp only [hOffset2']; omega
  have hMono2 : st2.nextFresh ≤ st2'.nextFresh := by
    simp only [hOffset2']; omega

  -- Control var shifts
  have hU1Shift : u1'.id = u1.id + offset := by
    have h := encodeFormula_controlVar_shift b φ1 w st st' hMono
    simp only [u1, u1'] at h ⊢
    omega
  have hU2Shift : u2'.id = u2.id + offset := by
    have h := encodeFormula_controlVar_shift b φ2 w st1 st1' hMono1
    simp only [u2, u2'] at h ⊢
    omega

  -- u and u' are allocated at st2/st2' nextFresh
  have hUId : u.id = st2.nextFresh := by simp only [u, EncState.allocFresh]
  have hU'Id : u'.id = st2'.nextFresh := by simp only [u', EncState.allocFresh]
  have hUShift : u'.id = u.id + offset := by
    simp only [hUId, hU'Id]
    omega

  -- The output clauses are: 3 Tseytin + st3'.clauses where st3' includes st2' + u' allocation
  -- st3'.clauses = st2'.clauses (allocFresh doesn't add clauses)
  simp only [EncState.addClause] at hc

  -- Check which clause c is
  cases hc with
  | head =>
      -- c = [neg u', neg u1', pos u2'] (the third Tseytin clause)
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or, FVar.toVar]
      simp only [σ']
      have hU'Ge : ¬(u'.id < st'.nextFresh) := by
        simp only [hUShift]
        have h1 : u.id ≥ st.nextFresh := by
          simp only [hUId]; exact Nat.le_trans hSt1Mono hSt2Mono
        simp only [hStEq]; omega
      have hU1'Ge : ¬(u1'.id < st'.nextFresh) := by
        simp only [hU1Shift]
        have h1 : u1.id ≥ st.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ1 w st
        simp only [hStEq]; omega
      have hU2'Ge : ¬(u2'.id < st'.nextFresh) := by
        simp only [hU2Shift]
        have h1 : u2.id ≥ st1.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ2 w st1
        simp only [hStEq]; omega
      simp only [shiftedAssignment, u1', st1', u2', st2', u',
                 if_neg hU'Ge, if_neg hU1'Ge, if_neg hU2'Ge, Var.unshift]
      have hUEq : u'.id - offset = u.id := by simp only [hUShift]; omega
      have hU1Eq : u1'.id - offset = u1.id := by simp only [hU1Shift]; omega
      have hU2Eq : u2'.id - offset = u2.id := by simp only [hU2Shift]; omega
      rw [hUEq, hU1Eq, hU2Eq]
      have hOrigClause : [SAT.Lit.neg (Var.Fresh u.id), SAT.Lit.neg (Var.Fresh u1.id),
          SAT.Lit.pos (Var.Fresh u2.id)] ∈
            (encodeFormula b (Formula.imp φ1 φ2) w st).2.clauses := by
        simp only [encodeFormula, EncState.addClause, EncState.allocFresh, u1, st1, u2, st2, u]
        exact List.Mem.head _
      have hOrigNotInSt : [SAT.Lit.neg (Var.Fresh u.id), SAT.Lit.neg (Var.Fresh u1.id),
          SAT.Lit.pos (Var.Fresh u2.id)] ∉ st.clauses := by
        intro hIn
        have hWFc := hWF _ hIn
        unfold clauseFreshBelow litFreshBelow at hWFc
        have hLit := hWFc (SAT.Lit.neg (Var.Fresh u.id)) (List.Mem.head _)
        have hUGe : u.id ≥ st.nextFresh := by
          simp only [hUId]; exact Nat.le_trans hSt1Mono hSt2Mono
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLit hUGe)
      have hOrigSat := hSatNew _ hOrigClause hOrigNotInSt
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hOrigSat
      exact hOrigSat

  | tail _ hTail1 =>
      cases hTail1 with
      | head =>
          -- c = [neg u2', pos u'] (second Tseytin clause)
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or, FVar.toVar]
          simp only [σ']
          have hU2'Ge : ¬(u2'.id < st'.nextFresh) := by
            simp only [hU2Shift]
            have h1 : u2.id ≥ st1.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ2 w st1
            have h2 : st1.nextFresh ≥ st.nextFresh := hSt1Mono
            simp only [hStEq]
            omega
          have hU'Ge : ¬(u'.id < st'.nextFresh) := by
            simp only [hUShift]
            have h1 : u.id ≥ st.nextFresh := by
              simp only [hUId]; exact Nat.le_trans hSt1Mono hSt2Mono
            simp only [hStEq]; omega
          simp only [shiftedAssignment, st1', u2', st2', u',
                     if_neg hU2'Ge, if_neg hU'Ge, Var.unshift]
          have hU2Eq : u2'.id - offset = u2.id := by simp only [hU2Shift]; omega
          have hUEq : u'.id - offset = u.id := by simp only [hUShift]; omega
          rw [hU2Eq, hUEq]
          have hOrigClause : [SAT.Lit.neg (Var.Fresh u2.id), SAT.Lit.pos (Var.Fresh u.id)] ∈
              (encodeFormula b (Formula.imp φ1 φ2) w st).2.clauses := by
            simp only [encodeFormula, EncState.addClause, EncState.allocFresh, st1, st2, u]
            exact List.mem_cons_of_mem _ (List.Mem.head _)
          have hOrigNotInSt :
              [SAT.Lit.neg (Var.Fresh u2.id), SAT.Lit.pos (Var.Fresh u.id)] ∉ st.clauses := by
            intro hIn
            have hWFc := hWF _ hIn
            unfold clauseFreshBelow litFreshBelow at hWFc
            have hLit := hWFc (SAT.Lit.neg (Var.Fresh u2.id)) (List.Mem.head _)
            have hU2Ge : u2.id ≥ st1.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ2 w st1
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLit (Nat.le_trans hSt1Mono hU2Ge))
          have hOrigSat := hSatNew _ hOrigClause hOrigNotInSt
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hOrigSat
          exact hOrigSat

      | tail _ hTail2 =>
          cases hTail2 with
          | head =>
              -- c = [pos u1', pos u'] (first Tseytin clause)
              simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or, FVar.toVar]
              simp only [σ']
              have hU1'Ge : ¬(u1'.id < st'.nextFresh) := by
                simp only [hU1Shift]
                have h1 : u1.id ≥ st.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ1 w st
                simp only [hStEq]
                omega
              have hU'Ge : ¬(u'.id < st'.nextFresh) := by
                simp only [hUShift]
                have h1 : u.id ≥ st.nextFresh := by
                  simp only [hUId]
                  have hSt2Ge : st2.nextFresh ≥ st.nextFresh := Nat.le_trans hSt1Mono hSt2Mono
                  omega
                simp only [hStEq]
                omega
              simp only [shiftedAssignment, u1', st1', st2', u',
                         if_neg hU1'Ge, if_neg hU'Ge, Var.unshift]
              have hU1Eq : u1'.id - offset = u1.id := by simp only [hU1Shift]; omega
              have hUEq : u'.id - offset = u.id := by simp only [hUShift]; omega
              rw [hU1Eq, hUEq]
              have hOrigClause : [SAT.Lit.pos (Var.Fresh u1.id), SAT.Lit.pos (Var.Fresh u.id)] ∈
                  (encodeFormula b (Formula.imp φ1 φ2) w st).2.clauses := by
                simp only [encodeFormula, EncState.addClause, EncState.allocFresh,
                  u1, st1, st2, u]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.Mem.head _))
              have hOrigNotInSt :
                  [SAT.Lit.pos (Var.Fresh u1.id), SAT.Lit.pos (Var.Fresh u.id)] ∉ st.clauses := by
                intro hIn
                have hWFc := hWF _ hIn
                unfold clauseFreshBelow litFreshBelow at hWFc
                have hLit := hWFc (SAT.Lit.pos (Var.Fresh u1.id)) (List.Mem.head _)
                have hU1Ge : u1.id ≥ st.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ1 w st
                exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLit hU1Ge)
              have hOrigSat := hSatNew _ hOrigClause hOrigNotInSt
              simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hOrigSat
              exact hOrigSat

          | tail _ hTail3 =>
              -- c is from st3'.clauses (which equals st2'.clauses after allocFresh)
              simp only [EncState.allocFresh] at hTail3

              by_cases hc1 : c ∈ st1'.clauses
              · -- c came from φ1 encoding (or inherited)
                by_cases hcSt' : c ∈ st'.clauses
                · exact absurd hcSt' hcNew
                · -- c ∈ st1'.clauses \ st'.clauses: NEW from φ1
                  have hWF1 : EncState.WellFormed st1 := encodeFormula_preserves_wf b φ1 w st hWF
                  have hSatNew1 : ∀ c ∈ st1.clauses, c ∉ st.clauses → SAT.Clause.eval σ c = true := by
                    intro c' hc' hc'New
                    have hc'InFinal : c' ∈ (encodeFormula b (Formula.imp φ1 φ2) w st).2.clauses := by
                      have hSub1 : st1.clauses ⊆ st2.clauses := encodeFormula_clauses_subset b φ2 w st1
                      have hSub2 : st2.clauses ⊆ st3.clauses := by
                        simp only [st3, EncState.allocFresh]; exact fun _ h => h
                      have hSub3 :
                          st3.clauses ⊆ (encodeFormula b (Formula.imp φ1 φ2) w st).2.clauses := by
                        simp only [encodeFormula, EncState.addClause, EncState.allocFresh,
                          st1, st2, st3]
                        intro x hx
                        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _ hx))
                      exact hSub3 (hSub2 (hSub1 hc'))
                    exact hSatNew c' hc'InFinal hc'New
                  have hSatNew1' : ∀ c ∈ (encodeFormula b φ1 w st).2.clauses, c ∉ st.clauses →
                      SAT.Clause.eval σ c = true := hSatNew1
                  have hih1 := ih1 w st st' offset hOffset hMono hWF hWF' hNonFreshCompat hSatNew1'
                  exact hih1 c hc1 hcSt'

              · -- c ∉ st1'.clauses, so c ∈ st2'.clauses \ st1'.clauses: NEW from φ2
                have hWF1 : EncState.WellFormed st1 := encodeFormula_preserves_wf b φ1 w st hWF
                have hWF1' : EncState.WellFormed st1' := encodeFormula_preserves_wf b φ1 w st' hWF'

                have hSatNew2 :
                    ∀ c ∈ st2.clauses, c ∉ st1.clauses → SAT.Clause.eval σ c = true := by
                  intro c' hc' hc'New
                  have hc'InFinal : c' ∈ (encodeFormula b (Formula.imp φ1 φ2) w st).2.clauses := by
                    have hSub2 : st2.clauses ⊆ st3.clauses := by
                      simp only [st3, EncState.allocFresh]; exact fun _ h => h
                    have hSub3 :
                        st3.clauses ⊆ (encodeFormula b (Formula.imp φ1 φ2) w st).2.clauses := by
                      simp only [encodeFormula, EncState.addClause, EncState.allocFresh,
                        st1, st2, st3]
                      intro x hx
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (List.mem_cons_of_mem _ hx))
                    exact hSub3 (hSub2 hc')
                  have hc'NotInSt : c' ∉ st.clauses := by
                    intro hIn
                    have hSub : st.clauses ⊆ st1.clauses := encodeFormula_clauses_subset b φ1 w st
                    exact hc'New (hSub hIn)
                  exact hSatNew c' hc'InFinal hc'NotInSt

                have hc2' : c ∈ st2'.clauses := hTail3
                have hSatNew2' : ∀ c ∈ (encodeFormula b φ2 w st1).2.clauses, c ∉ st1.clauses →
                    SAT.Clause.eval σ c = true := hSatNew2
                -- For ih2, we need st1.clauses ⊆ st1'.clauses.
                -- This holds for non-Fresh clauses (which is what ih2 actually uses):
                -- - If c ∈ st.clauses: c ∈ st'.clauses (hNonFreshCompat) ⊆ st1'.clauses
                -- - If c ∈ st1.clauses \ st.clauses and non-Fresh: c is deterministic from φ1
                -- Fresh clauses differ between st1 and st1', but ih2 only uses this for non-Fresh.
                -- Derive nonFreshClausesCompat for intermediate states
                have hNonFreshCompat1 : nonFreshClausesCompat st1 st1' :=
                  encodeFormula_preserves_nonFreshCompat b φ1 w st st' hNonFreshCompat
                have hih2 := ih2 w st1 st1' offset hOffset1.symm hMono1 hWF1 hWF1' hNonFreshCompat1 hSatNew2'

                -- ih2 gives us that its local σ'_ih2 (with threshold st1'.nextFresh) satisfies c
                -- But we need our σ' (with threshold st'.nextFresh) to satisfy c
                --
                -- Key: c is a NEW clause from φ2's encoding at st1', so all Fresh vars in c
                -- have indices ≥ st1'.nextFresh (allocated during φ2 encoding).
                -- For such indices n ≥ st1'.nextFresh ≥ st'.nextFresh:
                --   σ'_ih2(n) = σ(unshift n offset)  (since n ≥ st1'.nextFresh)
                --   σ'(n) = σ(unshift n offset)      (since n ≥ st'.nextFresh)
                -- So both assignments agree on all variables in c!

                -- Define ih2's shifted assignment
                let σ'_ih2 := shiftedAssignment b σ st1'.nextFresh offset

                -- ih2 gives: σ'_ih2 satisfies c
                have hih2_sat : SAT.Clause.eval σ'_ih2 c = true := hih2 c hc2' hc1

                -- Show σ' and σ'_ih2 agree on all vars in c
                -- Need: ∀ lit ∈ c, σ' (lit.getVar) = σ'_ih2 (lit.getVar)
                -- For clause_eval_of_agreement with (σ'_ih2, σ'), we need the agreement in
                -- the direction σ' = σ'_ih2 so the result is eval σ' = eval σ'_ih2
                have hAgree : ∀ lit ∈ c, σ' (SAT.Lit.getVar lit) = σ'_ih2 (SAT.Lit.getVar lit) := by
                  intro lit hLitInC
                  -- For non-Fresh vars, both equal σ
                  cases hVar : SAT.Lit.getVar lit with
                  | Fresh n =>
                      -- c is NEW from φ2 at st1', so all Fresh vars have index ≥ st1'.nextFresh
                      have hFreshGe : n ≥ st1'.nextFresh :=
                        encodeFormula_new_clause_fresh_ge_nextFresh b φ2 w st1' hWF1'
                          c hc2' hc1 lit hLitInC n hVar
                      -- σ' and σ'_ih2 agree on Fresh vars ≥ st1'.nextFresh
                      have hThreshLe : st'.nextFresh ≤ st1'.nextFresh := hSt1'Mono
                      exact shiftedAssignment_agree_ge b σ st'.nextFresh st1'.nextFresh offset
                        hThreshLe n hFreshGe
                  | _ =>
                      -- Non-Fresh vars: both assignments equal σ
                      simp only [σ', σ'_ih2, shiftedAssignment]

                -- Conclude by agreement: clause_eval_of_agreement gives
                -- SAT.Clause.eval σ' c = SAT.Clause.eval σ'_ih2 c
                have hEvalEq := clause_eval_of_agreement b σ'_ih2 σ' c hAgree
                rw [hEvalEq]
                exact hih2_sat


end Encoding
