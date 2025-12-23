import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Common
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.ShiftedAssignment

/-!
# AtEnd Case: Structural Determinism for New Clauses
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- AtEnd case: single recursion to wEnd world -/
lemma structural_determinism_new_clauses_atEnd (b : Bounds S) (φ : Formula S) (w : WId b)
    (st st' : EncState b) (offset : Nat) (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st) (hWF' : EncState.WellFormed st')
    (hNonFreshCompat : nonFreshClausesCompat st st')
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (encodeFormula b (Formula.atEnd φ) w st).2.clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true)
    (ih : ∀ (w : WId b) (st st' : EncState b) (offset : Nat),
           offset = st'.nextFresh - st.nextFresh →
           st.nextFresh ≤ st'.nextFresh →
           EncState.WellFormed st → EncState.WellFormed st' →
           nonFreshClausesCompat st st' →
           (∀ c ∈ (encodeFormula b φ w st).2.clauses,
               c ∉ st.clauses → SAT.Clause.eval σ c = true) →
           let σ' := shiftedAssignment b σ st'.nextFresh offset
           ∀ c ∈ (encodeFormula b φ w st').2.clauses,
               c ∉ st'.clauses → SAT.Clause.eval σ' c = true) :
    let σ' := shiftedAssignment b σ st'.nextFresh offset
    ∀ c ∈ (encodeFormula b (Formula.atEnd φ) w st').2.clauses, c ∉ st'.clauses →
      SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  simp only [encodeFormula] at hc

  -- Define wEnd world
  let wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩

  -- Define intermediate states for st-encoding
  let u1 := (encodeFormula b φ wEnd st).1
  let st1 := (encodeFormula b φ wEnd st).2
  let u := (EncState.allocFresh b st1).1
  let st2 := (EncState.allocFresh b st1).2

  -- Define intermediate states for st'-encoding
  let u1' := (encodeFormula b φ wEnd st').1
  let st1' := (encodeFormula b φ wEnd st').2
  let u' := (EncState.allocFresh b st1').1
  let st2' := (EncState.allocFresh b st1').2

  -- Offset relationships
  have hSt1Mono : st.nextFresh ≤ st1.nextFresh := encodeFormula_nextFresh_mono b φ wEnd st
  have hSt1'Mono : st'.nextFresh ≤ st1'.nextFresh := encodeFormula_nextFresh_mono b φ wEnd st'

  have hStEq : st'.nextFresh = st.nextFresh + offset := by rw [hOffset]; omega

  have hOffset1' : st1'.nextFresh = st1.nextFresh + offset := by
    have := encodeFormula_nextFresh_offset b φ wEnd st st' offset hStEq
    simp only [st1, st1'] at this ⊢
    exact this
  have hOffset1 : st1'.nextFresh - st1.nextFresh = offset := by
    simp only [hOffset1']; omega
  have hMono1 : st1.nextFresh ≤ st1'.nextFresh := by
    simp only [hOffset1']; omega

  -- Control var shifts
  have hU1Shift : u1'.id = u1.id + offset := by
    have h := encodeFormula_controlVar_shift b φ wEnd st st' hMono
    simp only [u1, u1'] at h ⊢
    omega

  -- u and u' are allocated at st1/st1' nextFresh
  have hUId : u.id = st1.nextFresh := by simp only [u, EncState.allocFresh]
  have hU'Id : u'.id = st1'.nextFresh := by simp only [u', EncState.allocFresh]
  have hUShift : u'.id = u.id + offset := by
    simp only [hUId, hU'Id, hOffset1']

  -- Output clauses are 2 Tseytin + st2'.clauses
  simp only [EncState.addClause] at hc

  -- Check which clause c is
  cases hc with
  | head =>
      -- c = [¬u', u] (second Tseytin clause)
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or, FVar.toVar]
      simp only [σ']
      have hU1'Ge : ¬(u1'.id < st'.nextFresh) := by
        simp only [hU1Shift]
        have h1 : u1.id ≥ st.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ wEnd st
        simp only [hStEq]; omega
      have hU'Ge : ¬(u'.id < st'.nextFresh) := by
        simp only [hUShift]
        have h1 : u.id ≥ st.nextFresh := by
          simp only [hUId]; exact hSt1Mono
        simp only [hStEq]; omega
      simp only [shiftedAssignment, u1', st1', u', wEnd,
                 if_neg hU1'Ge, if_neg hU'Ge, Var.unshift]
      have hU1Eq : u1'.id - offset = u1.id := by simp only [hU1Shift]; omega
      have hUEq : u'.id - offset = u.id := by simp only [hUShift]; omega
      rw [hU1Eq, hUEq]
      have hOrigClause : [SAT.Lit.neg (Var.Fresh u1.id), SAT.Lit.pos (Var.Fresh u.id)] ∈
          (encodeFormula b (Formula.atEnd φ) w st).2.clauses := by
        simp only [encodeFormula, EncState.addClause, EncState.allocFresh, wEnd, u1, st1, u]
        exact List.Mem.head _
      have hOrigNotInSt :
          [SAT.Lit.neg (Var.Fresh u1.id), SAT.Lit.pos (Var.Fresh u.id)] ∉ st.clauses := by
        intro hIn
        have hWFc := hWF _ hIn
        unfold clauseFreshBelow litFreshBelow at hWFc
        have hLit := hWFc (SAT.Lit.neg (Var.Fresh u1.id)) (List.Mem.head _)
        have hU1Ge : u1.id ≥ st.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ wEnd st
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLit hU1Ge)
      have hOrigSat := hSatNew _ hOrigClause hOrigNotInSt
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hOrigSat
      exact hOrigSat

  | tail _ hTail1 =>
      cases hTail1 with
      | head =>
          -- c = [¬u, u'] (first Tseytin clause)
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or, FVar.toVar]
          simp only [σ']
          have hU'Ge : ¬(u'.id < st'.nextFresh) := by
            simp only [hUShift]
            have h1 : u.id ≥ st.nextFresh := by
              simp only [hUId]; exact hSt1Mono
            simp only [hStEq]; omega
          have hU1'Ge : ¬(u1'.id < st'.nextFresh) := by
            simp only [hU1Shift]
            have h1 : u1.id ≥ st.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ wEnd st
            simp only [hStEq]; omega
          simp only [shiftedAssignment, u1', st1', u', wEnd,
                     if_neg hU'Ge, if_neg hU1'Ge, Var.unshift]
          have hUEq : u'.id - offset = u.id := by simp only [hUShift]; omega
          have hU1Eq : u1'.id - offset = u1.id := by simp only [hU1Shift]; omega
          rw [hUEq, hU1Eq]
          have hOrigClause : [SAT.Lit.neg (Var.Fresh u.id), SAT.Lit.pos (Var.Fresh u1.id)] ∈
              (encodeFormula b (Formula.atEnd φ) w st).2.clauses := by
            simp only [encodeFormula, EncState.addClause, EncState.allocFresh, wEnd, u1]
            exact List.mem_cons_of_mem _ (List.Mem.head _)
          have hOrigNotInSt :
              [SAT.Lit.neg (Var.Fresh u.id), SAT.Lit.pos (Var.Fresh u1.id)] ∉ st.clauses := by
            intro hIn
            have hWFc := hWF _ hIn
            unfold clauseFreshBelow litFreshBelow at hWFc
            have hLit := hWFc (SAT.Lit.neg (Var.Fresh u.id)) (List.Mem.head _)
            have hUGe : u.id ≥ st.nextFresh := by simp only [hUId]; exact hSt1Mono
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLit hUGe)
          have hOrigSat := hSatNew _ hOrigClause hOrigNotInSt
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hOrigSat
          exact hOrigSat

      | tail _ hTail2 =>
          -- c is from st2'.clauses (which equals st1'.clauses after allocFresh)
          simp only [EncState.allocFresh] at hTail2

          -- c must be from φ encoding at wEnd
          by_cases hcSt' : c ∈ st'.clauses
          · exact absurd hcSt' hcNew
          · -- c ∈ st1'.clauses \ st'.clauses: NEW from φ encoding
            have hWF1 : EncState.WellFormed st1 := encodeFormula_preserves_wf b φ wEnd st hWF
            have hWF1' : EncState.WellFormed st1' := encodeFormula_preserves_wf b φ wEnd st' hWF'
            have hSatNew1 : ∀ c ∈ st1.clauses, c ∉ st.clauses → SAT.Clause.eval σ c = true := by
              intro c' hc' hc'New
              have hc'InFinal : c' ∈ (encodeFormula b (Formula.atEnd φ) w st).2.clauses := by
                have hSub1 : st1.clauses ⊆ st2.clauses := by
                  simp only [st2, EncState.allocFresh]; exact fun _ h => h
                have hSub2 : st2.clauses ⊆ (encodeFormula b (Formula.atEnd φ) w st).2.clauses := by
                  simp only [encodeFormula, EncState.addClause, EncState.allocFresh, wEnd, u1, st1, u, st2]
                  intro x hx
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
                exact hSub2 (hSub1 hc')
              exact hSatNew c' hc'InFinal hc'New
            have hSatNew1' : ∀ c ∈ (encodeFormula b φ wEnd st).2.clauses, c ∉ st.clauses →
                SAT.Clause.eval σ c = true := hSatNew1
            have hih1 := ih wEnd st st' offset hOffset hMono hWF hWF' hNonFreshCompat hSatNew1'

            -- ih1 gives us that its local σ'_ih1 (with threshold st'.nextFresh) satisfies c
            -- Since we use the same threshold, our σ' is the same!
            exact hih1 c hTail2 hcSt'


end Encoding
