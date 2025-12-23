import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Common
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.ShiftedAssignment

/-!
# Past Case: Structural Determinism for New Clauses

This file contains:
- `encodeWitnesses_foldl_structural_determinism`: Helper for witnesses fold
- `auxVars_foldl_structural_determinism`: Helper for auxVars fold
- `structural_determinism_new_clauses_past`: Main past case theorem
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- Helper: Two any expressions are equal if the predicates agree on list membership. -/
lemma any_eq_of_pointwise {α : Type*} (c : List α) (p q : α → Bool)
    (h : ∀ x ∈ c, p x = q x) : c.any p = c.any q := by
  induction c with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x (by simp)]
    rw [ih (fun y hy => h y (by simp [hy]))]

/-- Helper: Structural determinism for encodeWitnesses fold.
    For clauses NEW to the fold (not in initial state), if σ satisfies corresponding clauses
    from st-side fold, then σ' satisfies clauses from st'-side fold. -/
lemma encodeWitnesses_foldl_structural_determinism (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hWF : EncState.WellFormed st) (hWF' : EncState.WellFormed st')
    (σ : SAT.Assignment (Var b))
    (hSatFold : ∀ c ∈ (witnesses.foldl (fun (uvars, stCur) w' =>
          let (u', stNext) := encodeFormula b φ w' stCur
          (uvars ++ [u'], stNext)) ([], st)).2.clauses,
        c ∉ st.clauses → SAT.Clause.eval σ c = true)
    (ih : ∀ (w : WId b) (st st' : EncState b) (offset : Nat),
         offset = st'.nextFresh - st.nextFresh →
         st.nextFresh ≤ st'.nextFresh →
         EncState.WellFormed st → EncState.WellFormed st' →
         (∀ c ∈ (encodeFormula b φ w st).2.clauses,
             c ∉ st.clauses → SAT.Clause.eval σ c = true) →
         let σ' := shiftedAssignment b σ st'.nextFresh offset
         ∀ c ∈ (encodeFormula b φ w st').2.clauses,
             c ∉ st'.clauses → SAT.Clause.eval σ' c = true) :
    let σ' := shiftedAssignment b σ st'.nextFresh offset
    ∀ c ∈ (witnesses.foldl (fun (uvars, stCur) w' =>
          let (u', stNext) := encodeFormula b φ w' stCur
          (uvars ++ [u'], stNext)) ([], st')).2.clauses,
      c ∉ st'.clauses → SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  -- We'll prove this by induction on witnesses
  induction witnesses generalizing st st' c with
  | nil =>
    simp only [List.foldl_nil] at hc
    exact absurd hc hcNew
  | cons w' ws ihWs =>
    simp only [List.foldl_cons] at hc
    -- After encoding w', the state is (encodeFormula b φ w' st').2
    -- We need to determine if c came from encoding w' or from the tail
    let st1 := (encodeFormula b φ w' st).2
    let st1' := (encodeFormula b φ w' st').2
    have hOffset1' : st1'.nextFresh = st1.nextFresh + offset := by
      simp only [st1, st1']
      exact encodeFormula_nextFresh_offset b φ w' st st' offset hOffset
    have hOffset1 : offset = st1'.nextFresh - st1.nextFresh := by omega
    have hMono1 : st1.nextFresh ≤ st1'.nextFresh := by omega
    have hWF1 : st1.WellFormed := encodeFormula_preserves_wf b φ w' st hWF
    have hWF1' : st1'.WellFormed := encodeFormula_preserves_wf b φ w' st' hWF'

    -- The clause is in the tail fold starting from some accumulator with .2 = st1'
    -- We convert to using ([], st1') as the accumulator using the clause independence lemma
    have hcConv : c ∈ (ws.foldl (fun (uvars, stCur) w'' =>
        let (u'', stNext) := encodeFormula b φ w'' stCur
        (uvars ++ [u''], stNext)) ([], st1')).2.clauses :=
      encodeWitnesses_foldl_clauses_indep b φ ws
        ([(encodeFormula b φ w' st').1], st1') ([], st1') rfl ▸ hc

    by_cases hcSt1' : c ∈ st1'.clauses
    · -- c is from encoding w' at st'
      by_cases hcSt' : c ∈ st'.clauses
      · exact absurd hcSt' hcNew
      · -- c is NEW from encoding w' at st' (not in st')
        -- Apply ih for encodeFormula at w'
        have hSatW' : ∀ c' ∈ (encodeFormula b φ w' st).2.clauses, c' ∉ st.clauses →
            SAT.Clause.eval σ c' = true := by
          intro c' hc' hc'New
          have hc'InTail : c' ∈ (ws.foldl (fun (uvars, stCur) w'' =>
              let (u'', stNext) := encodeFormula b φ w'' stCur
              (uvars ++ [u''], stNext))
              ([(encodeFormula b φ w' st).1], st1)).2.clauses :=
            encodeWitnesses_foldl_clauses_subset_aux b φ ws
              ([(encodeFormula b φ w' st).1], st1) hc'
          have hc'InFold : c' ∈ ((w' :: ws).foldl (fun (uvars, stCur) w'' =>
              let (u'', stNext) := encodeFormula b φ w'' stCur
              (uvars ++ [u''], stNext)) ([], st)).2.clauses := by
            simp only [List.foldl_cons]
            exact encodeWitnesses_foldl_clauses_indep b φ ws
              ([(encodeFormula b φ w' st).1], st1) ([], st1) rfl ▸ hc'InTail
          exact hSatFold c' hc'InFold hc'New
        have hMono' : st.nextFresh ≤ st'.nextFresh := by omega
        have hOffsetEq : offset = st'.nextFresh - st.nextFresh := by omega
        have hIhW' := ih w' st st' offset hOffsetEq hMono' hWF hWF' hSatW'
        exact hIhW' c hcSt1' hcSt'
    · -- c is NOT from encoding w' at st', so it's from the tail fold
      -- Get satisfaction for tail fold starting from st1
      have hSatFold1 : ∀ c' ∈ (ws.foldl (fun (uvars, stCur) w'' =>
            let (u'', stNext) := encodeFormula b φ w'' stCur
            (uvars ++ [u''], stNext)) ([], st1)).2.clauses,
          c' ∉ st1.clauses → SAT.Clause.eval σ c' = true := by
        intro c' hc' hc'New
        have hc'InTail : c' ∈ (ws.foldl (fun (uvars, stCur) w'' =>
            let (u'', stNext) := encodeFormula b φ w'' stCur
            (uvars ++ [u''], stNext))
            ([(encodeFormula b φ w' st).1], st1)).2.clauses :=
          encodeWitnesses_foldl_clauses_indep b φ ws
            ([], st1) ([(encodeFormula b φ w' st).1], st1) rfl ▸ hc'
        have hc'InFold : c' ∈ ((w' :: ws).foldl (fun (uvars, stCur) w'' =>
            let (u'', stNext) := encodeFormula b φ w'' stCur
            (uvars ++ [u''], stNext)) ([], st)).2.clauses := by
          simp only [List.foldl_cons]
          exact encodeWitnesses_foldl_clauses_indep b φ ws
            ([(encodeFormula b φ w' st).1], st1) ([], st1) rfl ▸ hc'InTail
        have hc'NotInSt : c' ∉ st.clauses :=
          fun h => hc'New (encodeFormula_clauses_subset b φ w' st h)
        exact hSatFold c' hc'InFold hc'NotInSt
      -- Apply IH for witnesses to get result with σ''
      let σ'' := shiftedAssignment b σ st1'.nextFresh offset
      have hcConv1 : c ∈ (ws.foldl (fun (uvars, stCur) w'' =>
            let (u'', stNext) := encodeFormula b φ w'' stCur
            (uvars ++ [u''], stNext)) ([], st1')).2.clauses :=
        encodeWitnesses_foldl_clauses_indep b φ ws
          ([(encodeFormula b φ w' st').1], st1') ([], st1') rfl ▸ hc
      have hIhWs := ihWs st1 st1' hOffset1' hWF1 hWF1' hSatFold1 c hcConv1 hcSt1'
      -- Now show σ'' c = σ' c using threshold agreement
      -- Fresh vars in c have index >= st1'.nextFresh >= st'.nextFresh
      have hThresholdLe : st'.nextFresh ≤ st1'.nextFresh :=
        encodeFormula_nextFresh_mono b φ w' st'
      have hFreshGe : ∀ lit, lit ∈ c → ∀ n, SAT.Lit.getVar lit = Var.Fresh n →
          n ≥ st1'.nextFresh := by
        intro lit hlit n hVarEq
        -- c is a new clause in the tail fold, so its Fresh vars have index >= st1'.nextFresh
        -- Use encodeWitnesses_foldl_newClause_fresh_ge_aux with the encodeFormula IH
        have hIhEnc : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
            c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
            n' >= st'.nextFresh :=
          fun w' st' hWF' c' hc' hc'New lit' hlit' n' hFresh' =>
            encodeFormula_new_clause_fresh_ge_nextFresh b φ w' st' hWF' c' hc' hc'New
              lit' hlit' n' hFresh'
        exact encodeWitnesses_foldl_newClause_fresh_ge_aux b φ ws ([], st1')
          st1'.nextFresh (le_refl _) hWF1' hIhEnc c hcConv1 hcSt1' lit hlit n hVarEq
      have hEvalEq := clause_eval_shiftedAssignment_threshold_agree b σ
        st'.nextFresh st1'.nextFresh offset hThresholdLe c hFreshGe
      simp only [σ', σ''] at hIhWs hEvalEq ⊢
      rw [hEvalEq]
      exact hIhWs

/-- Helper: Every NEW clause from auxVars fold step contains at least one Fresh var.
    The 4 clause types are:
    - [¬Mem, ¬witnessVar, u] - contains u (Fresh)
    - [¬Mem, ¬witnessVar, aux] - contains witnessVar, aux (Fresh)
    - [¬aux, Mem] - contains aux (Fresh)
    - [¬aux, witnessVar] - contains aux, witnessVar (Fresh) -/
lemma auxVars_step_has_fresh (b : Bounds S) (w : WId b) (u uv : FVar b) (wv : WId b)
    (acc : List (FVar b) × EncState b)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (let memVar := Var.Mem w.ti wv
                  let (aux, stCur) := EncState.allocFresh b acc.2
                  let stCur := EncState.addClause b stCur
                    [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
                  let stCur := EncState.addClause b stCur
                    [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv),
                     SAT.Lit.pos (FVar.toVar b aux)]
                  let stCur := EncState.addClause b stCur
                    [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
                  let stCur := EncState.addClause b stCur
                    [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
                  (acc.1 ++ [aux], stCur)).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  simp only [EncState.addClause, EncState.allocFresh_clauses_eq] at hcNew
  cases hcNew with
  | head =>
      -- c = [¬aux, witnessVar]
      use SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1)
      constructor
      · exact List.Mem.head _
      · use (EncState.allocFresh b acc.2).1.id
        simp only [SAT.Lit.getVar, FVar.toVar]
  | tail _ hTail1 =>
    cases hTail1 with
    | head =>
        -- c = [¬aux, Mem]
        use SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1)
        constructor
        · exact List.Mem.head _
        · use (EncState.allocFresh b acc.2).1.id
          simp only [SAT.Lit.getVar, FVar.toVar]
    | tail _ hTail2 =>
      cases hTail2 with
      | head =>
          -- c = [¬Mem, ¬witnessVar, aux]
          use SAT.Lit.neg (FVar.toVar b uv)
          constructor
          · exact List.mem_cons_of_mem _ (List.Mem.head _)
          · use uv.id
            simp only [SAT.Lit.getVar, FVar.toVar]
      | tail _ hTail3 =>
        cases hTail3 with
        | head =>
            -- c = [¬Mem, ¬witnessVar, u]
            use SAT.Lit.pos (FVar.toVar b u)
            constructor
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.Mem.head _))
            · use u.id
              simp only [SAT.Lit.getVar, FVar.toVar]
        | tail _ hOld =>
            -- c ∈ allocFresh.clauses = acc.2.clauses, contradicts hcNotOld
            simp only [EncState.allocFresh_clauses_eq] at hOld
            exact absurd hOld hcNotOld

/-- Helper: Every NEW clause from auxVars fold contains at least one Fresh var. -/
lemma auxVars_foldl_newClause_has_fresh (b : Bounds S) (w : WId b) (u : FVar b)
    (pairs : List (FVar b × WId b)) (acc : List (FVar b) × EncState b)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (pairs.foldl (fun (auxAcc, stCur) (uv, wv) =>
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  induction pairs generalizing acc c with
  | nil =>
      simp only [List.foldl_nil] at hcNew
      exact absurd hcNew hcNotOld
  | cons p ps ihPs =>
      simp only [List.foldl_cons] at hcNew
      -- Define the step result
      let stepResult := (let memVar := Var.Mem w.ti p.2
        let (aux, stCur) := EncState.allocFresh b acc.2
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b u)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b aux)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b p.1)]
        (acc.1 ++ [aux], stCur))
      by_cases hcStep : c ∈ stepResult.2.clauses
      · by_cases hcAcc : c ∈ acc.2.clauses
        · exact absurd hcAcc hcNotOld
        · exact auxVars_step_has_fresh b w u p.1 p.2 acc c hcStep hcAcc
      · exact ihPs stepResult c hcNew hcStep

/-- Helper: For a NEW clause c from auxVars fold at st', the unshifted clause c.map unshiftLit
    is in the auxVars fold at st.
    This requires parallel pairs (same length, witnessVars offset by `offset`). -/
lemma auxVars_foldl_unshift_membership (b : Bounds S) (w : WId b) (u u' : FVar b)
    (pairs pairs' : List (FVar b × WId b)) (acc acc' : List (FVar b) × EncState b)
    (offset : Nat)
    (hAccOff : acc'.2.nextFresh = acc.2.nextFresh + offset)
    (hLen : pairs.length = pairs'.length)
    (hUOff : u'.id = u.id + offset)
    (hPairsOff : ∀ i (hi : i < pairs.length) (hi' : i < pairs'.length),
        (pairs.get ⟨i, hi⟩).1.id + offset = (pairs'.get ⟨i, hi'⟩).1.id ∧
        (pairs.get ⟨i, hi⟩).2 = (pairs'.get ⟨i, hi'⟩).2)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (pairs'.foldl (fun (auxAcc, stCur) (uv, wv) =>
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u')]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) acc').2.clauses)
    (hcNotOld : c ∉ acc'.2.clauses) :
    let unshiftLit : SAT.Lit (Var b) → SAT.Lit (Var b) := fun lit =>
      match lit with
      | SAT.Lit.pos (Var.Fresh n) => SAT.Lit.pos (Var.Fresh (n - offset))
      | SAT.Lit.neg (Var.Fresh n) => SAT.Lit.neg (Var.Fresh (n - offset))
      | other => other
    c.map unshiftLit ∈ (pairs.foldl (fun (auxAcc, stCur) (uv, wv) =>
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) acc).2.clauses := by
  intro unshiftLit
  -- The proof proceeds by induction on pairs/pairs', showing for each step:
  -- - NEW clause c at step i of pairs' fold corresponds to clause c.map unshiftLit at step i of pairs fold
  -- - aux vars and witness vars shift by offset, Mem vars are unchanged
  -- - The fold structures are parallel, so corresponding clauses are added at each step
  --
  -- Key case analysis for each clause type:
  -- C1: [¬Mem, ¬witnessVar', u'] → [¬Mem, ¬witnessVar, u]
  -- C2: [¬Mem, ¬witnessVar', aux'] → [¬Mem, ¬witnessVar, aux]
  -- C3: [¬aux', Mem] → [¬aux, Mem]
  -- C4: [¬aux', witnessVar'] → [¬aux, witnessVar]
  --
  -- All Fresh vars (u', witnessVar', aux') in the st' fold are at offset from st fold vars.
  -- unshiftLit subtracts offset, recovering the st fold clause exactly.
  sorry

/-- Helper: Structural determinism for auxVars fold.
    The auxVars fold adds fixed-pattern clauses with both Fresh and Mem vars.
    For NEW clauses at st', σ' satisfies them if σ satisfies corresponding clauses at st.
    The key insight: each clause at st' corresponds to a clause at st with Fresh indices
    shifted by -offset, and the shifted assignment handles this correctly.

    Note: This lemma requires that the pairs at st and st' are "parallel" - same length,
    with witnessVars/witnessVars' differing by offset in Fresh indices. -/
lemma auxVars_foldl_structural_determinism (b : Bounds S) (w : WId b)
    (u u' : FVar b) (pairs pairs' : List (FVar b × WId b))
    (st st' : EncState b) (offset : Nat) (T : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hTLeSt' : T ≤ st'.nextFresh)
    (hStWF : EncState.WellFormed st)  -- WellFormed for proving clauses are new
    (hStClauseShift : ∀ c ∈ st.clauses, c.map (fun lit =>
        match lit with
        | SAT.Lit.pos (Var.Fresh n) => SAT.Lit.pos (Var.Fresh (n + offset))
        | SAT.Lit.neg (Var.Fresh n) => SAT.Lit.neg (Var.Fresh (n + offset))
        | other => other) ∈ st'.clauses)  -- Clause shift compatibility
    (hULtSt : u.id < st.nextFresh)  -- u was allocated before st
    (hPairsLtSt : ∀ p ∈ pairs, p.1.id < st.nextFresh)  -- pairs' FVars allocated before st
    (hLen : pairs.length = pairs'.length)
    (hUOffset : u'.id = u.id + offset)
    (hU'Ge : u'.id >= T)
    (hPairsOffset : ∀ i (hi : i < pairs.length) (hi' : i < pairs'.length),
        (pairs.get ⟨i, hi⟩).1.id + offset = (pairs'.get ⟨i, hi'⟩).1.id ∧
        (pairs'.get ⟨i, hi'⟩).1.id >= T ∧
        (pairs.get ⟨i, hi⟩).2 = (pairs'.get ⟨i, hi'⟩).2)
    (σ : SAT.Assignment (Var b))
    (hSatFold : ∀ c ∈ (pairs.foldl (fun (auxAcc, stCur) (uv, wv) =>
        let memVar := Var.Mem w.ti wv
        let (aux, stCur) := EncState.allocFresh b stCur
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
        (auxAcc ++ [aux], stCur)) ([], st)).2.clauses,
      c ∉ st.clauses → SAT.Clause.eval σ c = true) :
    let σ' := shiftedAssignment b σ T offset
    ∀ c ∈ (pairs'.foldl (fun (auxAcc, stCur) (uv, wv) =>
        let memVar := Var.Mem w.ti wv
        let (aux, stCur) := EncState.allocFresh b stCur
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u')]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
        (auxAcc ++ [aux], stCur)) ([], st')).2.clauses,
      c ∉ st'.clauses → SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  -- Define step functions for clarity
  let stepU := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
    let (uv, wv) := pair
    let memVar := Var.Mem w.ti wv
    let (aux, stCur) := EncState.allocFresh b acc.2
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
    (acc.1 ++ [aux], stCur)
  let stepU' := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
    let (uv, wv) := pair
    let memVar := Var.Mem w.ti wv
    let (aux, stCur) := EncState.allocFresh b acc.2
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u')]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
    (acc.1 ++ [aux], stCur)
  -- The proof proceeds by induction on pairs/pairs' with parallel structure.
  -- Use suffices to handle the general case with arbitrary accumulators.
  -- CRITICAL: Use FIXED threshold T throughout, not varying acc'.2.nextFresh

  -- Note: Using top-level shiftLitFresh from Common.lean

  -- General induction statement with FIXED threshold T
  -- Add WellFormedness tracking and Fresh bounds to prove stepU preserves WF
  -- Add clause shift compatibility to prove C1 is new
  suffices hSuff : ∀ (ps : List (FVar b × WId b)) (ps' : List (FVar b × WId b))
      (acc : List (FVar b) × EncState b) (acc' : List (FVar b) × EncState b),
      ps.length = ps'.length →
      acc'.2.nextFresh = acc.2.nextFresh + offset →
      acc'.2.nextFresh >= T →  -- Current state is at or past threshold T
      acc.2.WellFormed →  -- WellFormedness for proving clauses are new
      (∀ c ∈ acc.2.clauses, c.map (shiftLitFresh b offset) ∈ acc'.2.clauses) →  -- Clause shift compat
      u.id < acc.2.nextFresh →  -- u was allocated before acc's state
      (∀ p ∈ ps, p.1.id < acc.2.nextFresh) →  -- pairs' FVars allocated before acc's state
      (∀ i (hi : i < ps.length) (hi' : i < ps'.length),
          (ps.get ⟨i, hi⟩).1.id + offset = (ps'.get ⟨i, hi'⟩).1.id ∧
          (ps'.get ⟨i, hi'⟩).1.id >= T ∧  -- pairs' FVars are >= threshold T
          (ps.get ⟨i, hi⟩).2 = (ps'.get ⟨i, hi'⟩).2) →
      (∀ c ∈ (ps.foldl stepU acc).2.clauses, c ∉ acc.2.clauses → SAT.Clause.eval σ c = true) →
      ∀ c ∈ (ps'.foldl stepU' acc').2.clauses, c ∉ acc'.2.clauses →
        SAT.Clause.eval (shiftedAssignment b σ T offset) c = true by
    -- Apply the general statement to our specific case
    have hSt'Ge : st'.nextFresh >= T := hTLeSt'
    have hPairsOff' : ∀ i (hi : i < pairs.length) (hi' : i < pairs'.length),
        (pairs.get ⟨i, hi⟩).1.id + offset = (pairs'.get ⟨i, hi'⟩).1.id ∧
        (pairs'.get ⟨i, hi'⟩).1.id >= T ∧
        (pairs.get ⟨i, hi⟩).2 = (pairs'.get ⟨i, hi'⟩).2 := hPairsOffset
    -- Prove initial clause shift compatibility matches the suffices form
    have hInitClauseShift : ∀ c ∈ st.clauses, c.map (shiftLitFresh b offset) ∈ st'.clauses := by
      intro c' hc'
      exact hStClauseShift c' hc'
    have hResult := hSuff pairs pairs' ([], st) ([], st') hLen hOffset hSt'Ge hStWF hInitClauseShift
        hULtSt hPairsLtSt hPairsOff' hSatFold c hc hcNew
    simp only [σ']
    exact hResult

  -- Prove the suffices by induction on ps
  intro ps
  induction ps with
  | nil =>
    intro ps' acc acc' hLenEq _ _ _ _ _ _ _ _ c hc hcNew
    -- ps' is also empty by hLenEq
    simp only [List.length_nil] at hLenEq
    have hPs'Nil : ps' = [] := List.length_eq_zero.mp hLenEq.symm
    simp only [hPs'Nil, List.foldl_nil] at hc
    exact absurd hc hcNew
  | cons p pTail ihTail =>
    intro ps' acc acc' hLenEq hAccOff hAccGe hAccWF hAccClauseShift hULtAcc hPsLtAcc hPsOff hSatAcc c hc hcNew
    -- ps' = p' :: p'Tail by length
    match ps' with
    | [] => simp only [List.length_nil, List.length_cons, Nat.succ_ne_zero] at hLenEq
    | p' :: p'Tail =>
      simp only [List.length_cons, Nat.succ.injEq] at hLenEq
      simp only [List.foldl_cons] at hc

      -- Compute one step at st and st'
      let accNext := stepU acc p
      let accNext' := stepU' acc' p'

      -- Get correspondence for first element
      have hP0 := hPsOff 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      simp only [List.get_cons_zero] at hP0
      have hUvOff : p.1.id + offset = p'.1.id := hP0.1
      have hP'1Ge : p'.1.id >= T := hP0.2.1
      have hWvEq : p.2 = p'.2 := hP0.2.2

      -- Offset preserved through step
      have hAccNextOff : accNext'.2.nextFresh = accNext.2.nextFresh + offset := by
        simp only [stepU, stepU', accNext, accNext']
        simp only [EncState.addClause, EncState.allocFresh]
        omega

      -- accNext' is still at or past threshold T
      have hAccNextGe : accNext'.2.nextFresh >= T := by
        calc accNext'.2.nextFresh >= acc'.2.nextFresh := by
              simp only [stepU', accNext', EncState.addClause, EncState.allocFresh]
              omega
          _ >= T := hAccGe

      -- WellFormedness preserved through step
      -- Get bounds on u.id and p.1.id BEFORE the simp
      have hPLtAcc : p.1.id < acc.2.nextFresh := by
        have hMem : p ∈ p :: pTail := @List.mem_cons_self _ p pTail
        exact hPsLtAcc p hMem
      have hAccNextWF : accNext.2.WellFormed := by
        simp only [stepU, accNext]
        -- After allocFresh, nextFresh = acc.2.nextFresh + 1
        have hAllocWF : (EncState.allocFresh b acc.2).2.WellFormed :=
          EncState.allocFresh_wf hAccWF
        have hAllocNext : (EncState.allocFresh b acc.2).2.nextFresh = acc.2.nextFresh + 1 := by
          simp only [EncState.allocFresh]
        have hAuxId : (EncState.allocFresh b acc.2).1.id = acc.2.nextFresh :=
          EncState.allocFresh_fst (b := b) acc.2
        -- Helper: prove clauseFreshBelow for each of the 4 clauses
        -- All Fresh vars: u.id, p.1.id, aux.id - all < acc.2.nextFresh + 1
        have hUFB : litFreshBelow (SAT.Lit.pos (FVar.toVar b u)) (acc.2.nextFresh + 1) := by
          show u.id < acc.2.nextFresh + 1
          have : u.id < acc.2.nextFresh := hULtAcc
          omega
        have hUFBNeg : litFreshBelow (SAT.Lit.neg (FVar.toVar b u)) (acc.2.nextFresh + 1) := by
          show u.id < acc.2.nextFresh + 1
          have : u.id < acc.2.nextFresh := hULtAcc
          omega
        have hPFB : litFreshBelow (SAT.Lit.pos (FVar.toVar b p.1)) (acc.2.nextFresh + 1) := by
          show p.1.id < acc.2.nextFresh + 1
          have : p.1.id < acc.2.nextFresh := hPLtAcc
          omega
        have hPFBNeg : litFreshBelow (SAT.Lit.neg (FVar.toVar b p.1)) (acc.2.nextFresh + 1) := by
          show p.1.id < acc.2.nextFresh + 1
          have : p.1.id < acc.2.nextFresh := hPLtAcc
          omega
        have hAuxFB : litFreshBelow (SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b acc.2).1))
            (acc.2.nextFresh + 1) := by
          show (EncState.allocFresh b acc.2).1.id < acc.2.nextFresh + 1
          simp only [EncState.allocFresh]; omega
        have hAuxFBNeg : litFreshBelow (SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1))
            (acc.2.nextFresh + 1) := by
          show (EncState.allocFresh b acc.2).1.id < acc.2.nextFresh + 1
          simp only [EncState.allocFresh]; omega
        have hMemFB : litFreshBelow (SAT.Lit.pos (Var.Mem w.ti p.2)) (acc.2.nextFresh + 1) := by
          simp only [litFreshBelow, SAT.Lit.getVar]; trivial
        have hMemFBNeg : litFreshBelow (SAT.Lit.neg (Var.Mem w.ti p.2)) (acc.2.nextFresh + 1) := by
          simp only [litFreshBelow, SAT.Lit.getVar]; trivial
        -- C1 = [¬Mem, ¬p.1, u]
        have hC1FB : clauseFreshBelow [SAT.Lit.neg (Var.Mem w.ti p.2),
            SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b u)]
            (acc.2.nextFresh + 1) := by
          unfold clauseFreshBelow
          intro lit hLit
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with rfl | rfl | rfl <;> assumption
        -- C2 = [¬Mem, ¬p.1, aux]
        have hC2FB : clauseFreshBelow [SAT.Lit.neg (Var.Mem w.ti p.2),
            SAT.Lit.neg (FVar.toVar b p.1),
            SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b acc.2).1)]
            (acc.2.nextFresh + 1) := by
          unfold clauseFreshBelow
          intro lit hLit
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with rfl | rfl | rfl <;> assumption
        -- C3 = [¬aux, Mem]
        have hC3FB : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1),
            SAT.Lit.pos (Var.Mem w.ti p.2)]
            (acc.2.nextFresh + 1) := by
          unfold clauseFreshBelow
          intro lit hLit
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with rfl | rfl <;> assumption
        -- C4 = [¬aux, p.1]
        have hC4FB : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1),
            SAT.Lit.pos (FVar.toVar b p.1)]
            (acc.2.nextFresh + 1) := by
          unfold clauseFreshBelow
          intro lit hLit
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with rfl | rfl <;> assumption
        -- Chain of addClause_wf
        have hWF1 := EncState.addClause_wf hAllocWF _ hC1FB
        simp only [EncState.addClause, hAllocNext] at hWF1 ⊢
        have hWF2 := EncState.addClause_wf hWF1 _ hC2FB
        simp only [EncState.addClause] at hWF2 ⊢
        have hWF3 := EncState.addClause_wf hWF2 _ hC3FB
        simp only [EncState.addClause] at hWF3 ⊢
        exact EncState.addClause_wf hWF3 _ hC4FB

      -- Pairs offset for tail (including bounds)
      have hTailOff : ∀ i (hi : i < pTail.length) (hi' : i < p'Tail.length),
          (pTail.get ⟨i, hi⟩).1.id + offset = (p'Tail.get ⟨i, hi'⟩).1.id ∧
          (p'Tail.get ⟨i, hi'⟩).1.id >= T ∧
          (pTail.get ⟨i, hi⟩).2 = (p'Tail.get ⟨i, hi'⟩).2 := by
        intro i hi hi'
        have hFull := hPsOff (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi')
        simp only [List.get_cons_succ] at hFull
        exact hFull

      -- Satisfaction for tail at accNext
      have hSatNext : ∀ c ∈ (pTail.foldl stepU accNext).2.clauses,
          c ∉ accNext.2.clauses → SAT.Clause.eval σ c = true := by
        intro c' hc' hc'New
        apply hSatAcc
        · simp only [List.foldl_cons]
          exact hc'
        · intro hc'Acc
          apply hc'New
          -- accNext.2.clauses ⊇ acc.2.clauses
          simp only [stepU, accNext, EncState.addClause]
          simp only [List.mem_cons, List.mem_append] at hc'Acc ⊢
          right; right; right; right; exact hc'Acc

      -- Case analysis: c from this step or from tail fold
      by_cases hcAccNext' : c ∈ accNext'.2.clauses
      · -- c from this step (one of 4 clauses added)
        by_cases hcAcc' : c ∈ acc'.2.clauses
        · exact absurd hcAcc' hcNew
        · -- c is one of the 4 NEW clauses from this step
          -- Show σ' satisfies it by relating to st-side clause
          simp only [stepU', accNext', EncState.addClause, EncState.allocFresh] at hcAccNext'
          simp only [List.mem_cons] at hcAccNext'
          -- hcAccNext' : c = C4 ∨ c = C3 ∨ c = C2 ∨ c = C1 ∨ c ∈ acc'.2.clauses
          -- Eliminate the last disjunct using hcAcc'
          simp only [hcAcc', or_false] at hcAccNext'

          -- The 4 clauses are:
          -- 1. [¬aux', p'.1]
          -- 2. [¬aux', Mem]
          -- 3. [¬Mem, ¬p'.1, aux']
          -- 4. [¬Mem, ¬p'.1, u']

          -- Define aux vars for convenience
          let aux := (EncState.allocFresh b acc.2).1
          let aux' := (EncState.allocFresh b acc'.2).1
          let memVar := Var.Mem w.ti p.2

          -- Key offset properties
          have hAuxOff : aux'.id = aux.id + offset := by
            simp only [aux, aux', EncState.allocFresh]
            omega
          have hAux'Id : aux'.id = acc'.2.nextFresh := EncState.allocFresh_fst (b := b) acc'.2
          have hAuxId : aux.id = acc.2.nextFresh := EncState.allocFresh_fst (b := b) acc.2
          have hAux'Ge : aux'.id >= T := by omega
          have hMemVarEq : Var.Mem w.ti p'.2 = Var.Mem w.ti p.2 := by simp only [hWvEq]

          -- The acc-side step adds corresponding clauses
          let accNextSt := stepU acc p

          -- Show the acc-side clauses are in accNextSt.clauses and in full fold output
          have hC1Acc : [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b u)]
              ∈ accNextSt.2.clauses := by
            simp only [stepU, accNextSt, EncState.addClause, List.mem_cons]
            right; right; right; left; rfl
          have hC2Acc : [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b aux)]
              ∈ accNextSt.2.clauses := by
            simp only [stepU, accNextSt, EncState.addClause, List.mem_cons]
            right; right; left; rfl
          have hC3Acc : [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
              ∈ accNextSt.2.clauses := by
            simp only [stepU, accNextSt, EncState.addClause, List.mem_cons]
            right; left; rfl
          have hC4Acc : [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b p.1)]
              ∈ accNextSt.2.clauses := by
            simp only [stepU, accNextSt, EncState.addClause, List.mem_cons]
            left; rfl

          -- Helper: stepU preserves clause subset
          have hStepUSub : ∀ (st : List (FVar b) × EncState b) (a : FVar b × WId b),
              st.2.clauses ⊆ (stepU st a).2.clauses := by
            intro st' a'
            simp only [stepU, EncState.addClause, EncState.allocFresh]
            intro c' hc'
            simp only [List.mem_cons]
            right; right; right; right; exact hc'

          -- Case analysis on which of the 4 clauses c is
          -- After addClause: [C4, C3, C2, C1, ...] where
          -- C4 = [¬aux', p'.1], C3 = [¬aux', Mem], C2 = [¬Mem, ¬p'.1, aux'], C1 = [¬Mem, ¬p'.1, u']
          rcases hcAccNext' with hC4' | hC3' | hC2' | hC1'
          · -- c = [¬aux', p'.1] (C4 - first in list, last added)
            subst hC4'
            have hC4InFold : [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b p.1)]
                ∈ ((p :: pTail).foldl stepU acc).2.clauses := by
              simp only [List.foldl_cons]
              have hSub := foldl_subset_snd stepU hStepUSub pTail accNextSt
              exact hSub hC4Acc
            have hC4New : [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b p.1)] ∉ acc.2.clauses := by
              intro hContra
              -- This clause contains aux with id = acc.2.nextFresh
              -- By WellFormedness, no clause in acc.2.clauses can contain Var.Fresh acc.2.nextFresh
              have hLit : SAT.Lit.neg (FVar.toVar b aux) ∈
                  [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b p.1)] := by
                simp only [List.mem_cons, true_or]
              have hNotFresh := EncState.WellFormed.fresh_not_in_clauses hAccWF hContra hLit
              simp only [SAT.Lit.getVar, FVar.toVar, hAuxId] at hNotFresh
              exact hNotFresh rfl
            have hSatC4 := hSatAcc _ hC4InFold hC4New
            simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false] at hSatC4 ⊢
            simp only [SAT.Lit.eval]
            -- Work directly with expanded forms (let-bindings get expanded in goal)
            simp only [FVar.toVar, EncState.allocFresh, shiftedAssignment, Var.unshift] at hSatC4 ⊢
            have hNotLtAux : ¬(acc'.2.nextFresh < T) := by omega
            have hNotLtP : ¬(p'.1.id < T) := by omega
            simp only [if_neg hNotLtAux, if_neg hNotLtP]
            have hAuxIdEq : acc'.2.nextFresh - offset = acc.2.nextFresh := by omega
            have hPIdEq : p'.1.id - offset = p.1.id := by simp only [← hUvOff]; omega
            simp only [hAuxIdEq, hPIdEq]
            exact hSatC4
          · -- c = [¬aux', Mem] (C3)
            subst hC3'
            have hC3InFold : [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
                ∈ ((p :: pTail).foldl stepU acc).2.clauses := by
              simp only [List.foldl_cons]
              have hSub := foldl_subset_snd stepU hStepUSub pTail accNextSt
              exact hSub hC3Acc
            have hC3New : [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar] ∉ acc.2.clauses := by
              intro hContra
              have hLit : SAT.Lit.neg (FVar.toVar b aux) ∈
                  [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar] := by
                simp only [List.mem_cons, true_or]
              have hNotFresh := EncState.WellFormed.fresh_not_in_clauses hAccWF hContra hLit
              simp only [SAT.Lit.getVar, FVar.toVar, hAuxId] at hNotFresh
              exact hNotFresh rfl
            have hSatC3 := hSatAcc _ hC3InFold hC3New
            simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false] at hSatC3 ⊢
            simp only [SAT.Lit.eval, hMemVarEq]
            -- Work directly with expanded forms
            simp only [FVar.toVar, EncState.allocFresh, shiftedAssignment, Var.unshift] at hSatC3 ⊢
            have hNotLtAux : ¬(acc'.2.nextFresh < T) := by omega
            simp only [if_neg hNotLtAux]
            have hAuxIdEq : acc'.2.nextFresh - offset = acc.2.nextFresh := by omega
            simp only [hAuxIdEq]
            exact hSatC3
          · -- c = [¬Mem, ¬p'.1, aux'] (C2)
            subst hC2'
            have hC2InFold : [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b aux)]
                ∈ ((p :: pTail).foldl stepU acc).2.clauses := by
              simp only [List.foldl_cons]
              have hSub := foldl_subset_snd stepU hStepUSub pTail accNextSt
              exact hSub hC2Acc
            have hC2New : [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b aux)]
                ∉ acc.2.clauses := by
              intro hContra
              have hLit : SAT.Lit.pos (FVar.toVar b aux) ∈
                  [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b aux)] := by
                simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true]
              have hNotFresh := EncState.WellFormed.fresh_not_in_clauses hAccWF hContra hLit
              simp only [SAT.Lit.getVar, FVar.toVar, hAuxId] at hNotFresh
              exact hNotFresh rfl
            have hSatC2 := hSatAcc _ hC2InFold hC2New
            simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false] at hSatC2 ⊢
            simp only [SAT.Lit.eval, hMemVarEq]
            -- Work directly with expanded forms
            simp only [FVar.toVar, EncState.allocFresh, shiftedAssignment, Var.unshift] at hSatC2 ⊢
            have hNotLtAux : ¬(acc'.2.nextFresh < T) := by omega
            have hNotLtP : ¬(p'.1.id < T) := by omega
            simp only [if_neg hNotLtAux, if_neg hNotLtP]
            have hAuxIdEq : acc'.2.nextFresh - offset = acc.2.nextFresh := by omega
            have hPIdEq : p'.1.id - offset = p.1.id := by simp only [← hUvOff]; omega
            simp only [hAuxIdEq, hPIdEq]
            exact hSatC2
          · -- c = [¬Mem, ¬p'.1, u'] (C1 - last in list, first added)
            subst hC1'
            have hC1InFold : [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b u)]
                ∈ ((p :: pTail).foldl stepU acc).2.clauses := by
              simp only [List.foldl_cons]
              have hSub := foldl_subset_snd stepU hStepUSub pTail accNextSt
              exact hSub hC1Acc
            have hC1New : [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b u)]
                ∉ acc.2.clauses := by
              -- Use clause shift compatibility: if C1 ∈ acc.2, then shift(C1) ∈ acc'.2
              -- But shift(C1) = C1' and hcAcc' says C1' ∉ acc'.2, contradiction
              intro hContra
              apply hcAcc'
              -- Get shifted clause in acc'.2
              have hShifted := hAccClauseShift _ hContra
              -- Transform hShifted to show the shifted clause equals c
              simp only [List.map] at hShifted
              dsimp only [shiftLitFresh] at hShifted
              simp only [FVar.toVar, memVar, hWvEq, hUvOff, ← hUOffset] at hShifted
              exact hShifted
            have hSatC1 := hSatAcc _ hC1InFold hC1New
            simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false] at hSatC1 ⊢
            simp only [SAT.Lit.eval, hMemVarEq]
            -- Work directly with expanded forms
            simp only [FVar.toVar, shiftedAssignment, Var.unshift] at hSatC1 ⊢
            have hNotLtP : ¬(p'.1.id < T) := by omega
            have hNotLtU : ¬(u'.id < T) := by omega
            simp only [if_neg hNotLtP, if_neg hNotLtU]
            have hPIdEq : p'.1.id - offset = p.1.id := by simp only [← hUvOff]; omega
            have hUIdEq : u'.id - offset = u.id := by simp only [hUOffset]; omega
            simp only [hPIdEq, hUIdEq]
            exact hSatC1
      · -- c from tail fold
        -- Define aux vars for the clause shift proof
        let aux := (EncState.allocFresh b acc.2).1
        let aux' := (EncState.allocFresh b acc'.2).1
        have hAuxOff : aux.id + offset = aux'.id := by
          simp only [aux, aux', EncState.allocFresh]
          omega
        -- Need additional hypotheses for IH:
        -- 1. Clause shift compatibility for accNext/accNext'
        have hAccNextClauseShift : ∀ c' ∈ accNext.2.clauses, c'.map (shiftLitFresh b offset) ∈ accNext'.2.clauses := by
          intro c' hc'
          simp only [stepU, accNext, EncState.addClause, EncState.allocFresh] at hc'
          simp only [List.mem_cons] at hc'
          -- c' is either one of the 4 new clauses or from acc.2.clauses
          rcases hc' with hC4 | hC3 | hC2 | hC1 | hOld
          · -- c' = C4 = [¬aux, p.1] -> shifted is [¬aux', p'.1]
            simp only [stepU', accNext', EncState.addClause, EncState.allocFresh, List.mem_cons]
            left
            subst hC4
            simp only [List.map]; dsimp only [shiftLitFresh, aux, aux']
            simp only [FVar.toVar, EncState.allocFresh, hUvOff, ← hAccOff]
          · -- c' = C3 = [¬aux, Mem] -> shifted is [¬aux', Mem]
            simp only [stepU', accNext', EncState.addClause, EncState.allocFresh, List.mem_cons]
            right; left
            subst hC3
            simp only [List.map]; dsimp only [shiftLitFresh, aux, aux']
            simp only [FVar.toVar, EncState.allocFresh, hWvEq, ← hAccOff]
          · -- c' = C2 = [¬Mem, ¬p.1, aux] -> shifted is [¬Mem, ¬p'.1, aux']
            simp only [stepU', accNext', EncState.addClause, EncState.allocFresh, List.mem_cons]
            right; right; left
            subst hC2
            simp only [List.map]; dsimp only [shiftLitFresh, aux, aux']
            simp only [FVar.toVar, EncState.allocFresh, hUvOff, hWvEq, ← hAccOff]
          · -- c' = C1 = [¬Mem, ¬p.1, u] -> shifted is [¬Mem, ¬p'.1, u']
            simp only [stepU', accNext', EncState.addClause, EncState.allocFresh, List.mem_cons]
            right; right; right; left
            subst hC1
            simp only [List.map]; dsimp only [shiftLitFresh]
            simp only [FVar.toVar, hUvOff, hWvEq, ← hUOffset]
          · -- c' from acc.2.clauses - use hAccClauseShift
            have hShifted := hAccClauseShift c' hOld
            simp only [stepU', accNext', EncState.addClause, EncState.allocFresh, List.mem_cons]
            right; right; right; right; exact hShifted
        -- 2. u.id < accNext.2.nextFresh
        have hULtAccNext : u.id < accNext.2.nextFresh := by
          simp only [stepU, accNext, EncState.addClause, EncState.allocFresh]
          omega
        -- 3. ∀ p ∈ pTail, p.1.id < accNext.2.nextFresh
        have hTailLtAccNext : ∀ p' ∈ pTail, p'.1.id < accNext.2.nextFresh := by
          intro p'' hp''
          have hLt := hPsLtAcc p'' (List.mem_cons_of_mem p hp'')
          simp only [stepU, accNext, EncState.addClause, EncState.allocFresh]
          omega
        -- Apply IH - with fixed threshold T, no conversion needed!
        exact ihTail p'Tail accNext accNext' hLenEq hAccNextOff hAccNextGe hAccNextWF hAccNextClauseShift
            hULtAccNext hTailLtAccNext hTailOff hSatNext c hc hcAccNext'

/-- Past case: existential with Mem vars -/
lemma structural_determinism_new_clauses_past (b : Bounds S) (φ : Formula S) (w : WId b)
    (st st' : EncState b) (offset : Nat) (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st) (hWF' : EncState.WellFormed st')
    (hNonFreshCompat : nonFreshClausesCompat st st')
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (encodeFormula b (Formula.past φ) w st).2.clauses, c ∉ st.clauses →
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
    ∀ c ∈ (encodeFormula b (Formula.past φ) w st').2.clauses, c ∉ st'.clauses →
      SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  -- Past encoding structure:
  -- 1. Allocate u fresh
  -- 2. Encode φ at each witness world (multiple recursions)
  -- 3. For each witness: allocate aux fresh, add 4 clauses per witness
  -- 4. Add big-or clause for u → (aux₁ ∨ ... ∨ auxₙ)

  -- Define intermediate states for st side
  let u := (EncState.allocFresh b st).1
  let st1 := (EncState.allocFresh b st).2
  let witnesses := (WId.allWorlds b).filterMap fun w' => if w'.p = w.p then some w' else none
  let encResult := witnesses.foldl (fun (uvars, stCur) w' =>
      let (u', stNext) := encodeFormula b φ w' stCur
      (uvars ++ [u'], stNext)) ([], st1)
  let witnessVars := encResult.1
  let st2 := encResult.2

  -- Define intermediate states for st' side
  let u' := (EncState.allocFresh b st').1
  let st1' := (EncState.allocFresh b st').2
  let encResult' := witnesses.foldl (fun (uvars, stCur) w' =>
      let (u', stNext) := encodeFormula b φ w' stCur
      (uvars ++ [u'], stNext)) ([], st1')
  let witnessVars' := encResult'.1
  let st2' := encResult'.2

  -- Key shift relationships
  have hUId : u.id = st.nextFresh := EncState.allocFresh_fst (b := b) st
  have hU'Id : u'.id = st'.nextFresh := EncState.allocFresh_fst (b := b) st'
  have hUShift : u'.id = u.id + offset := by simp only [hUId, hU'Id, hOffset]; omega
  have hSt1Next : st1.nextFresh = st.nextFresh + 1 := EncState.allocFresh_nextFresh b st
  have hSt1'Next : st1'.nextFresh = st'.nextFresh + 1 := EncState.allocFresh_nextFresh b st'
  have hSt1Offset : st1'.nextFresh - st1.nextFresh = offset := by
    simp only [hSt1Next, hSt1'Next, hOffset]; omega

  -- c is a clause from the past encoding at st'
  simp only [encodeFormula] at hc

  -- Keep hSatNew in original form for flexibility
  -- simp only [encodeFormula] at hSatNew

  -- The past encoding structure at st':
  -- st' → allocFresh → st1' → witnesses fold → st2' → auxVars fold → st3' → addClause → st4'
  -- We already have st1', witnessVars', st2' defined

  -- Define the auxVars fold and final state for st' side
  let auxResult' := witnessVars'.zip witnesses |>.foldl (fun (auxAcc, stCur) (uv, w') =>
    let memVar := Var.Mem w.ti w'
    let (aux, stCur) := EncState.allocFresh b stCur
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u')]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
    (auxAcc ++ [aux], stCur)) ([], st2')
  let auxVars' := auxResult'.1
  let st3' := auxResult'.2
  let auxLits' := auxVars'.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))
  let st4' := EncState.addClause b st3' ([SAT.Lit.neg (FVar.toVar b u')] ++ auxLits')

  -- The proof follows the pattern from atEnd case:
  -- All Fresh vars in new clauses have index >= st'.nextFresh
  -- The shiftedAssignment translates them correctly

  -- Key approach: trace where c came from and apply appropriate argument
  -- c is in (EncState.addClause ...).clauses, so either:
  -- 1. c is the final clause [¬u', aux₁', ..., auxₙ']
  -- 2. c is from st3'.clauses (auxVars fold output)

  -- We use encodeFormula_new_clause_fresh_ge_nextFresh for Fresh var bounds
  -- which shows all Fresh vars in NEW clauses have index >= initial nextFresh

  -- The key is: the final encoding is a composition of:
  -- allocFresh → witnesses fold → auxVars fold → addClause
  -- All Fresh vars introduced are >= st'.nextFresh, so σ' handles them correctly

  -- For this proof, we use that all NEW clauses have Fresh vars >= st'.nextFresh
  -- and the corresponding clause structure exists at st with vars shifted by -offset
  have hFreshGe : ∀ lit, lit ∈ c → ∀ n, SAT.Lit.getVar lit = Var.Fresh n → n ≥ st'.nextFresh := by
    intro lit hLitInC n hLitFresh
    have hcMem : c ∈ (encodeFormula b (Formula.past φ) w st').2.clauses := by
      simp only [encodeFormula] at hc ⊢
      exact hc
    have hWF' : EncState.WellFormed st' := hWF'
    exact encodeFormula_new_clause_fresh_ge_nextFresh b (Formula.past φ) w st' hWF'
      c hcMem hcNew lit hLitInC n hLitFresh

  -- Now use the fact that σ' agrees with σ on shifted Fresh vars >= threshold
  -- We need to show there's a corresponding clause at st that σ satisfies
  -- This follows from the structural symmetry of the encoding

  -- Strategy: use encodeFormula_structural_determinism at the full formula level
  -- via the existing IH and structure

  -- The past case is complex due to:
  -- 1. Witnesses fold: encodes φ at each witness world
  -- 2. AuxVars fold: adds 4 gadget clauses per witness
  -- 3. Final clause: big-or connecting control var to aux vars
  --
  -- The proof structure:
  -- - For clauses from witnesses fold: use encodeWitnesses_foldl_structural_determinism
  --   with threshold conversion (st1'.nextFresh → st'.nextFresh)
  -- - For clauses from auxVars fold / final: use clause shifting correspondence
  --   (each clause at st' has a corresponding clause at st with Fresh IDs - offset)
  --
  -- Key insight: all Fresh vars in NEW clauses have index >= st'.nextFresh (hFreshGe),
  -- so σ' correctly maps them via unshift: σ'(Fresh n) = σ(Fresh (n-offset))
  --
  -- The shifted clause at st is in the encoding and is new (Fresh vars >= st.nextFresh),
  -- so σ satisfies it, which means σ' satisfies the original clause c.

  -- We need nonFreshClausesCompat st1 st1' to use ih
  have hCompat1 : nonFreshClausesCompat st1 st1' := by
    intro c' hc' hNoFresh
    have hc'St : c' ∈ st.clauses := (EncState.allocFresh_clauses_eq b st) ▸ hc'
    have hIn' := hNonFreshCompat c' hc'St hNoFresh
    exact (EncState.allocFresh_clauses_eq b st') ▸ hIn'

  -- WF for intermediate states
  have hWF1 : st1.WellFormed := EncState.allocFresh_wf hWF
  have hWF1' : st1'.WellFormed := EncState.allocFresh_wf hWF'

  -- Offset for st1/st1'
  have hOffset1' : st1'.nextFresh = st1.nextFresh + offset := by
    simp only [hSt1Next, hSt1'Next, hOffset]; omega
  have hOffset1 : offset = st1'.nextFresh - st1.nextFresh := by omega
  have hMono1 : st1.nextFresh ≤ st1'.nextFresh := by omega

  -- Direct induction approach for witnesses fold instead of using a helper
  -- This avoids the signature mismatch problem with ihWrap

  -- First, establish that σ satisfies new clauses from the witnesses fold at st
  have hSatFold1 : ∀ c ∈ (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) ([], st1)).2.clauses,
      c ∉ st1.clauses → SAT.Clause.eval σ c = true := by
    intro c' hc' hc'New
    -- c' is in the witnesses fold result at st1
    -- We need to show σ satisfies it
    -- c' is also in the full past encoding at st
    have hc'InFull : c' ∈ (encodeFormula b (Formula.past φ) w st).2.clauses := by
      simp only [encodeFormula, EncState.addClause, List.mem_cons]
      right
      -- c' is in the auxVars fold result, which contains witnesses fold clauses
      have hAuxPreserve : ∀ (pairs : List (FVar b × WId b)) (acc : List (FVar b) × EncState b),
          acc.2.clauses ⊆ (pairs.foldl (fun (auxAcc, stCur) (u', w') =>
            let memVar := Var.Mem w.ti w'
            let (aux, stCur) := EncState.allocFresh b stCur
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                SAT.Lit.pos (FVar.toVar b u)]
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                SAT.Lit.pos (FVar.toVar b aux)]
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
            (auxAcc ++ [aux], stCur)) acc).2.clauses := by
        intro pairs
        induction pairs with
        | nil => intro acc; exact fun x hx => hx
        | cons hd tl ihPairs =>
            intro acc y hy
            simp only [List.foldl_cons]
            apply ihPairs
            simp only [EncState.addClause, EncState.allocFresh, List.mem_cons]
            right; right; right; right
            exact hy
      exact hAuxPreserve (witnessVars.zip witnesses) ([], st2) hc'
    have hc'NotSt : c' ∉ st.clauses := by
      intro hIn
      apply hc'New
      exact (EncState.allocFresh_clauses_eq b st) ▸ hIn
    exact hSatNew c' hc'InFull hc'NotSt

  -- Case split on where c came from
  by_cases hcSt2' : c ∈ st2'.clauses
  · -- Case 1: c is from witnesses fold (st2')
    by_cases hcSt1' : c ∈ st1'.clauses
    · -- c is from st1' = allocFresh st', so c ∈ st'.clauses
      have hcSt' : c ∈ st'.clauses := (EncState.allocFresh_clauses_eq b st') ▸ hcSt1'
      exact absurd hcSt' hcNew
    · -- c is NEW from witnesses fold at st1'
      -- Use direct induction on witnesses instead of a helper
      -- Key: we maintain nonFreshClausesCompat through the fold

      -- Prove by induction that σ' satisfies new clauses from st1' witnesses fold
      -- The induction tracks: (stCur, stCur') pairs maintain nonFreshClausesCompat
      suffices hWitSD : ∀ (ws : List (WId b)) (stCur stCur' : EncState b),
          stCur'.nextFresh = stCur.nextFresh + offset →
          stCur.WellFormed → stCur'.WellFormed →
          nonFreshClausesCompat stCur stCur' →
          (∀ c' ∈ (ws.foldl (fun (uvars, st) w' =>
              let (u', stNext) := encodeFormula b φ w' st
              (uvars ++ [u'], stNext)) ([], stCur)).2.clauses,
            c' ∉ stCur.clauses → SAT.Clause.eval σ c' = true) →
          let σ'Cur := shiftedAssignment b σ stCur'.nextFresh offset
          ∀ c' ∈ (ws.foldl (fun (uvars, st) w' =>
              let (u', stNext) := encodeFormula b φ w' st
              (uvars ++ [u'], stNext)) ([], stCur')).2.clauses,
            c' ∉ stCur'.clauses → SAT.Clause.eval σ'Cur c' = true by
        -- Apply the suffices to witnesses at st1/st1'
        have hWitResult := hWitSD witnesses st1 st1' hOffset1' hWF1 hWF1' hCompat1 hSatFold1
        -- Convert threshold from st1'.nextFresh to st'.nextFresh
        have hThreshLe : st'.nextFresh ≤ st1'.nextFresh := by simp only [hSt1'Next]; omega
        have hFreshGeC : ∀ lit, lit ∈ c → ∀ n, SAT.Lit.getVar lit = Var.Fresh n →
            n ≥ st1'.nextFresh := by
          intro lit hLit n hFreshLit
          have hIhEnc : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
              c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
              n' >= st'.nextFresh :=
            fun w' st' hWF' c' hc' hc'New lit' hlit' n' hFresh' =>
              encodeFormula_new_clause_fresh_ge_nextFresh b φ w' st' hWF' c' hc' hc'New
                lit' hlit' n' hFresh'
          exact encodeWitnesses_foldl_newClause_fresh_ge_aux b φ witnesses ([], st1')
            st1'.nextFresh (le_refl _) hWF1' hIhEnc c hcSt2' hcSt1' lit hLit n hFreshLit
        have hEvalEq := clause_eval_shiftedAssignment_threshold_agree b σ
          st'.nextFresh st1'.nextFresh offset hThreshLe c hFreshGeC
        simp only [σ'] at hEvalEq ⊢
        rw [hEvalEq]
        exact hWitResult c hcSt2' hcSt1'
      -- Prove the suffices by induction on ws
      intro ws
      induction ws with
      | nil =>
        intro stCur stCur' _ _ _ _ _
        simp only [List.foldl_nil]
        intro c' hc' hc'New
        exact absurd hc' hc'New
      | cons w' wsTail ihWsTail =>
        intro stCur stCur' hOffCur hWFCur hWFCur' hCompatCur hSatCur
        simp only [List.foldl_cons]
        intro c' hc' hc'New
        -- After encoding w', states are (encodeFormula ... stCur).2 and (encodeFormula ... stCur').2
        let stNext := (encodeFormula b φ w' stCur).2
        let stNext' := (encodeFormula b φ w' stCur').2
        -- Offset preserved
        have hOffNext : stNext'.nextFresh = stNext.nextFresh + offset :=
          encodeFormula_nextFresh_offset b φ w' stCur stCur' offset hOffCur
        -- WF preserved
        have hWFNext : stNext.WellFormed := encodeFormula_preserves_wf b φ w' stCur hWFCur
        have hWFNext' : stNext'.WellFormed := encodeFormula_preserves_wf b φ w' stCur' hWFCur'
        -- nonFreshClausesCompat preserved
        have hCompatNext : nonFreshClausesCompat stNext stNext' :=
          encodeFormula_preserves_nonFreshCompat b φ w' stCur stCur' hCompatCur
        -- hSatCur for tail fold at stNext
        have hSatNext : ∀ c'' ∈ (wsTail.foldl (fun (uvars, st) w'' =>
            let (u'', stN) := encodeFormula b φ w'' st
            (uvars ++ [u''], stN)) ([], stNext)).2.clauses,
          c'' ∉ stNext.clauses → SAT.Clause.eval σ c'' = true := by
          intro c'' hc'' hc''New
          -- c'' is in wsTail fold at stNext (with empty var list)
          -- Show c'' is in (w' :: wsTail) fold at stCur
          -- Key: clauses don't depend on var list, use independence
          have hc''InFull : c'' ∈ ((w' :: wsTail).foldl (fun (uvars, st) w'' =>
              let (u'', stN) := encodeFormula b φ w'' st
              (uvars ++ [u''], stN)) ([], stCur)).2.clauses := by
            simp only [List.foldl_cons, List.nil_append]
            -- (w' :: wsTail).foldl ... ([], stCur) = wsTail.foldl ... ([u'], stNext)
            -- Clauses are same as wsTail.foldl ... ([], stNext) by independence
            have hIndep := encodeWitnesses_foldl_clauses_indep b φ wsTail
              ([], stNext) ([(encodeFormula b φ w' stCur).1], stNext) rfl
            rw [← hIndep]
            exact hc''
          have hc''NotCur : c'' ∉ stCur.clauses := by
            intro h
            apply hc''New
            exact encodeFormula_clauses_subset b φ w' stCur h
          exact hSatCur c'' hc''InFull hc''NotCur
        -- Convert clause accumulator using independence
        have hc'Conv : c' ∈ (wsTail.foldl (fun (uvars, st) w'' =>
            let (u'', stN) := encodeFormula b φ w'' st
            (uvars ++ [u''], stN)) ([], stNext')).2.clauses :=
          encodeWitnesses_foldl_clauses_indep b φ wsTail
            ([(encodeFormula b φ w' stCur').1], stNext') ([], stNext') rfl ▸ hc'
        -- Case: c' from encodeFormula w' at stCur', or from tail fold
        by_cases hc'Next' : c' ∈ stNext'.clauses
        · -- c' from encoding w' at stCur'
          by_cases hc'Cur' : c' ∈ stCur'.clauses
          · exact absurd hc'Cur' hc'New
          · -- c' is NEW from encodeFormula w' at stCur'
            -- Use ih directly!
            have hSatW' : ∀ c'' ∈ (encodeFormula b φ w' stCur).2.clauses,
                c'' ∉ stCur.clauses → SAT.Clause.eval σ c'' = true := by
              intro c'' hc'' hc''New
              have hc''InFull : c'' ∈ ((w' :: wsTail).foldl (fun (uvars, st) w'' =>
                  let (u'', stN) := encodeFormula b φ w'' st
                  (uvars ++ [u''], stN)) ([], stCur)).2.clauses := by
                simp only [List.foldl_cons]
                exact encodeWitnesses_foldl_clauses_subset_aux b φ wsTail
                  ([(encodeFormula b φ w' stCur).1], stNext) hc''
              exact hSatCur c'' hc''InFull hc''New
            have hOffCurEq : offset = stCur'.nextFresh - stCur.nextFresh := by omega
            have hMonoCur : stCur.nextFresh ≤ stCur'.nextFresh := by omega
            have hIhW' := ih w' stCur stCur' offset hOffCurEq hMonoCur hWFCur hWFCur' hCompatCur hSatW'
            exact hIhW' c' hc'Next' hc'Cur'
        · -- c' from tail fold at stNext'
          -- IH gives result with threshold stNext'.nextFresh, we need stCur'.nextFresh
          have hIhResult := ihWsTail stNext stNext' hOffNext hWFNext hWFNext' hCompatNext hSatNext
            c' hc'Conv hc'Next'
          -- Convert threshold using agreement lemma
          have hThreshLe : stCur'.nextFresh ≤ stNext'.nextFresh :=
            encodeFormula_nextFresh_mono b φ w' stCur'
          -- c' has Fresh vars >= stNext'.nextFresh (from tail fold, not in stNext'.clauses)
          have hFreshGeC' : ∀ lit, lit ∈ c' → ∀ n, SAT.Lit.getVar lit = Var.Fresh n →
              n ≥ stNext'.nextFresh := by
            intro lit hLit n hFreshLit
            have hIhEnc : ∀ w'' st'', st''.WellFormed → ∀ c'', c'' ∈ (encodeFormula b φ w'' st'').2.clauses →
                c'' ∉ st''.clauses → ∀ lit', lit' ∈ c'' → ∀ n', lit'.getVar = Var.Fresh n' →
                n' >= st''.nextFresh :=
              fun w'' st'' hWF'' c'' hc'' hc''New lit' hlit' n' hFresh' =>
                encodeFormula_new_clause_fresh_ge_nextFresh b φ w'' st'' hWF'' c'' hc'' hc''New
                  lit' hlit' n' hFresh'
            exact encodeWitnesses_foldl_newClause_fresh_ge_aux b φ wsTail ([], stNext')
              stNext'.nextFresh (le_refl _) hWFNext' hIhEnc c' hc'Conv hc'Next' lit hLit n hFreshLit
          have hEvalEq := clause_eval_shiftedAssignment_threshold_agree b σ
            stCur'.nextFresh stNext'.nextFresh offset hThreshLe c' hFreshGeC'
          rw [hEvalEq]
          exact hIhResult
  · -- Case 2 & 3: c is from auxVars fold or final clause
    -- All such clauses have Fresh vars >= st'.nextFresh
    -- Use the existing hFreshGe and show correspondence with st-side clause
    -- For clauses with only Fresh vars >= threshold, shifted assignment gives same eval
    -- as the unshifted clause evaluated by σ

    -- The key insight: σ' maps Fresh n to σ (Fresh (n - offset))
    -- The st-side encoding has the same clause structure with Fresh vars at (n - offset)
    -- σ satisfies the st-side clause, so σ' satisfies the st'-side clause

    -- For now, we use that all Fresh vars in c satisfy hFreshGe
    -- and show σ' c = true by showing the unshifted clause is in st-encoding and satisfied

    -- The clause c is either from auxVars fold (st3' \ st2') or the final clause
    -- In both cases, c has Fresh vars >= st'.nextFresh

    -- Define st-side auxVars fold and final state
    let auxResult := witnessVars.zip witnesses |>.foldl (fun (auxAcc, stCur) (uv, w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) ([], st2)
    let auxVars := auxResult.1
    let st3 := auxResult.2
    let auxLits := auxVars.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))
    let st4 := EncState.addClause b st3 ([SAT.Lit.neg (FVar.toVar b u)] ++ auxLits)

    -- All Fresh vars in c have index >= st'.nextFresh (from hFreshGe)
    -- The shiftedAssignment σ' maps Fresh n to σ (Fresh (n - offset))
    -- We need to show σ' c = true

    -- Since c has only Fresh vars >= st'.nextFresh, and the corresponding
    -- clause at st has Fresh vars >= st.nextFresh = st'.nextFresh - offset,
    -- σ satisfies the st-clause, so σ' satisfies c.

    -- Use clause_eval_shiftedAssignment for this
    -- The clause c evaluates to the same under σ' as the unshifted clause under σ
    have hcInFull' : c ∈ (encodeFormula b (Formula.past φ) w st').2.clauses := by
      simp only [encodeFormula] at hc ⊢
      exact hc

    -- For new clauses from auxVars fold or final clause, all have Fresh vars
    -- and the shifted assignment correctly evaluates them.
    -- Key: all Fresh vars in c have index >= st'.nextFresh.
    -- The corresponding clause at st (with Fresh indices shifted by -offset) is satisfied by σ.
    -- Since σ' maps Fresh n to σ(Fresh(n-offset)) for n >= st'.nextFresh, σ' satisfies c.

    -- First establish Fresh bounds for c
    have hcNotSt' : c ∉ st'.clauses := hcNew
    have hcNotSt1' : c ∉ st1'.clauses := by
      intro h
      exact hcSt2' (encodeWitnesses_foldl_clauses_subset_aux b φ witnesses ([], st1') h)
    have hcNotSt2' : c ∉ st2'.clauses := hcSt2'

    -- c is from auxVars fold or final clause
    -- Show Fresh vars in c have index >= st'.nextFresh using hFreshGe

    -- The key insight: for the auxVars fold and final clause, all clauses have
    -- a corresponding clause in the st-encoding with Fresh indices shifted by -offset.
    -- The shifted assignment σ' correctly evaluates c to match σ on the st-clause.

    -- Use the existing hSatNew which applies to ALL new clauses from the full encoding.
    -- The full encoding at st includes auxVars fold and final clause.

    -- For c with all Fresh vars >= st'.nextFresh:
    -- σ'(Fresh n) = σ(Fresh(n - offset)) for n >= st'.nextFresh
    -- The st-side clause has Fresh(n - offset) where c has Fresh(n).
    -- So σ'(c) = σ(st-side clause).

    -- Since st-side clause is new at st, σ satisfies it by hSatNew.

    -- Define the corresponding clause at st by computing what the st-encoding produces
    -- at the same position. For now, use that the full formula encoding satisfies SD.

    -- This requires showing clause-level correspondence, which is complex.
    -- The cleanest approach would be a helper lemma for auxVars fold SD.
    -- For now, we note that hFreshGe ensures the shifted assignment evaluates correctly,
    -- and the structural correspondence guarantees the st-side clause exists and is new.

    -- Use hFreshGe directly with clause_eval_shiftedAssignment logic
    -- The clause c at st' corresponds structurally to some c0 at st
    -- where c0 = shiftClause(c, -offset) for Fresh vars.

    -- Since hSatNew covers all new clauses from (encodeFormula ... st),
    -- including the auxVars fold clauses with shifted indices,
    -- and σ' evaluates c the same as σ evaluates c0, we get σ' c = true.

    -- Key insight: All literals in c are either:
    -- 1. Non-Fresh (Mem vars): σ'(v) = σ(v) since shiftedAssignment preserves non-Fresh
    -- 2. Fresh with index n >= st'.nextFresh: σ'(Fresh n) = σ(Fresh(n - offset))
    --
    -- The st-side encoding produces the same clause structure with Fresh(n - offset).
    -- That clause is new at st (Fresh vars >= st.nextFresh), so σ satisfies it.
    -- Therefore σ' satisfies c.

    -- Direct evaluation approach: prove σ' satisfies c by showing correspondence with st-side clause
    --
    -- Key insight: All clauses from auxVars fold and final clause contain u (control var).
    -- u.id = st.nextFresh, so by WellFormed(st), none of these clauses are in st.clauses.
    -- Therefore hSatNew applies to all of them.
    --
    -- For the st'-side clause c with Fresh vars >= st'.nextFresh:
    -- - σ' maps Fresh(n) to σ(Fresh(n - offset)) for n >= st'.nextFresh
    -- - The st-side clause has Fresh(n - offset) where c has Fresh(n)
    -- - σ satisfies the st-side clause, so σ' satisfies c

    -- Establish key identities for u and u'
    have hU'IdEq : u'.id = st'.nextFresh := hU'Id
    have hUIdEq : u.id = st.nextFresh := hUId
    have hU'MinusOffset : u'.id - offset = u.id := by
      simp only [hU'IdEq, hUIdEq, hOffset]; omega

    -- All clauses containing u (Fresh st.nextFresh) are NOT in st.clauses by WellFormed
    have hUNotInSt : ∀ c', c' ∈ (encodeFormula b (Formula.past φ) w st).2.clauses →
        (SAT.Lit.pos (FVar.toVar b u) ∈ c' ∨ SAT.Lit.neg (FVar.toVar b u) ∈ c') →
        c' ∉ st.clauses := by
      intro c' _ hUInC' hContra
      have hWFClause := hWF c' hContra
      unfold clauseFreshBelow at hWFClause
      cases hUInC' with
      | inl hPos =>
          have hLitFB := hWFClause (SAT.Lit.pos (FVar.toVar b u)) hPos
          simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hUIdEq] at hLitFB
          exact Nat.lt_irrefl _ hLitFB
      | inr hNeg =>
          have hLitFB := hWFClause (SAT.Lit.neg (FVar.toVar b u)) hNeg
          simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hUIdEq] at hLitFB
          exact Nat.lt_irrefl _ hLitFB

    -- Get offset relationships for witnessVars (needed in both branches)
    have hOffset2 : st2'.nextFresh = st2.nextFresh + offset :=
      encodeWitnesses_foldl_nextFresh_offset b φ witnesses st1 st1' offset
        (by simp only [hSt1Next, hSt1'Next, hOffset]; omega)

    -- Get witnessVars offset info
    have hMono1 : st1.nextFresh ≤ st1'.nextFresh := by omega
    have hNextFreshIH : ∀ w' stX stX', stX'.nextFresh = stX.nextFresh + offset →
        stX.nextFresh ≤ stX'.nextFresh →
        (encodeFormula b φ w' stX').2.nextFresh = (encodeFormula b φ w' stX).2.nextFresh + offset :=
      fun w' stX stX' hOff _ => encodeFormula_nextFresh_offset b φ w' stX stX' offset hOff
    have hVarsInfo := encodeWitnesses_foldl_vars_offset b φ witnesses st1 st1' offset
      (by simp only [hSt1Next, hSt1'Next, hOffset]; omega) hMono1 hNextFreshIH
    have hVarsLen : witnessVars.length = witnessVars'.length := hVarsInfo.1

    -- Define pairs for auxVars fold
    let pairs := witnessVars.zip witnesses
    let pairs' := witnessVars'.zip witnesses

    have hPairsLen : pairs.length = pairs'.length := by
      simp only [pairs, pairs', List.length_zip, hVarsLen, min_self]

    have hPairsOff : ∀ i (hi : i < pairs.length) (hi' : i < pairs'.length),
        (pairs.get ⟨i, hi⟩).1.id + offset = (pairs'.get ⟨i, hi'⟩).1.id ∧
        (pairs.get ⟨i, hi⟩).2 = (pairs'.get ⟨i, hi'⟩).2 := by
      intro i hi hi'
      simp only [pairs, pairs'] at hi hi' ⊢
      simp only [List.get_eq_getElem, List.getElem_zip]
      have hiLen : i < witnessVars.length := by
        simp only [List.length_zip] at hi
        have hMin : min witnessVars.length witnesses.length ≤ witnessVars.length := Nat.min_le_left _ _
        omega
      have hiLen' : i < witnessVars'.length := by
        simp only [List.length_zip] at hi'
        have hMin : min witnessVars'.length witnesses.length ≤ witnessVars'.length := Nat.min_le_left _ _
        omega
      have hiWit : i < witnesses.length := by
        simp only [List.length_zip] at hi
        have hMin : min witnessVars.length witnesses.length ≤ witnesses.length := Nat.min_le_right _ _
        omega
      constructor
      · -- Fresh var offset
        exact hVarsInfo.2 i hiLen hiLen'
      · -- World equality: both are witnesses[i]
        simp only [hiWit]

    -- WellFormedness for st2
    have hWF2 : st2.WellFormed :=
      encodeWitnesses_foldl_wf b φ witnesses st1 hWF1
        (fun w' st'' hWF'' => encodeFormula_preserves_wf b φ w' st'' hWF'')

    -- Case analysis: c from auxVars fold (st3') or final clause
    by_cases hcSt3' : c ∈ st3'.clauses
    · -- c is from auxVars fold (st3' \ st2')
      -- The clause c is from auxVars fold at st'
      -- Use direct evaluation: find corresponding clause at st, show it's new, apply hSatNew

      -- Helper: all Fresh vars in auxVars fold NEW clauses at st' have id >= st'.nextFresh
      have hFreshGeAux : ∀ lit, lit ∈ c → ∀ n, SAT.Lit.getVar lit = Var.Fresh n → n ≥ st'.nextFresh :=
        hFreshGe

      -- The auxVars fold at st' produces clauses with Fresh vars from:
      -- - u' (id = st'.nextFresh)
      -- - witnessVars' (ids >= st'.nextFresh + 1)
      -- - auxVars' (ids >= st2'.nextFresh)
      -- All are >= st'.nextFresh

      -- For each NEW clause from auxVars fold at st', the corresponding st-side clause:
      -- 1. Has u instead of u' (u.id = st.nextFresh = u'.id - offset)
      -- 2. Has witnessVars[i] instead of witnessVars'[i]
      -- 3. Has auxVars[i] instead of auxVars'[i]
      -- 4. Same Mem vars

      -- The st-side clause contains u, so it's not in st.clauses by hUNotInSt

      -- Establish σ' evaluates c to same value as σ evaluates the st-side clause
      -- Using shiftedAssignment: for n >= st'.nextFresh, σ'(Fresh n) = σ(Fresh(n - offset))

      -- Since c ∈ st3'.clauses \ st2'.clauses, it's one of the 4 clause types from auxVars fold
      -- or it was inherited from st2'.clauses (but we know c ∉ st2'.clauses)

      -- Define unshift function for clauses
      let unshiftLit : SAT.Lit (Var b) → SAT.Lit (Var b) := fun lit =>
        match lit with
        | SAT.Lit.pos (Var.Fresh n) => SAT.Lit.pos (Var.Fresh (n - offset))
        | SAT.Lit.neg (Var.Fresh n) => SAT.Lit.neg (Var.Fresh (n - offset))
        | other => other

      -- Key property: for lit with Fresh n >= st'.nextFresh, σ'(lit) = σ(unshiftLit(lit))
      have hLitEval : ∀ lit, (∀ n, SAT.Lit.getVar lit = Var.Fresh n → n ≥ st'.nextFresh) →
          SAT.Lit.eval σ' lit = SAT.Lit.eval σ (unshiftLit lit) := by
        intro lit hLitFreshGe
        cases lit with
        | pos v =>
            cases v with
            | Fresh n =>
                have hGe := hLitFreshGe n rfl
                simp only [SAT.Lit.eval, σ', shiftedAssignment, Var.unshift, unshiftLit]
                have hNotLt : ¬(n < st'.nextFresh) := Nat.not_lt.mpr hGe
                simp only [if_neg hNotLt]
            | Mem ti wid =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Level ti j =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Pred p ti k =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | MinQ v Q =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | ReachT ti =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Edge ti ti' =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Exists ti p ti' =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | PreEq ti ti' =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Seq ti p =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Rep v =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Incomp ti p w1 w2 =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Acc w1 w2 w3 =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
        | neg v =>
            cases v with
            | Fresh n =>
                have hGe := hLitFreshGe n rfl
                simp only [SAT.Lit.eval, σ', shiftedAssignment, Var.unshift, unshiftLit]
                have hNotLt : ¬(n < st'.nextFresh) := Nat.not_lt.mpr hGe
                simp only [if_neg hNotLt]
            | Mem ti wid =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Level ti j =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Pred p ti k =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | MinQ v Q =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | ReachT ti =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Edge ti ti' =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Exists ti p ti' =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | PreEq ti ti' =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Seq ti p =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Rep v =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Incomp ti p w1 w2 =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]
            | Acc w1 w2 w3 =>
                simp only [SAT.Lit.eval, σ', shiftedAssignment, unshiftLit]

      -- The unshifted clause c.map unshiftLit is in (encodeFormula ... st).2.clauses
      -- and contains u, so it's not in st.clauses

      -- For clause evaluation: c evaluates to true under σ' iff c.map unshiftLit evaluates to true under σ
      have hClauseEvalCorr : SAT.Clause.eval σ' c = SAT.Clause.eval σ (c.map unshiftLit) := by
        simp only [SAT.Clause.eval_eq_any, List.any_map]
        apply any_eq_of_pointwise
        intro lit hLit
        have hLitFresh := hFreshGeAux lit hLit
        exact hLitEval lit hLitFresh

      -- Now show c.map unshiftLit is in st encoding and is new
      -- This requires showing the clause structure correspondence

      -- The auxVars fold at st' produces clauses with structure:
      -- Type 1: [¬Mem, ¬witnessVar', u']
      -- Type 2: [¬Mem, ¬witnessVar', aux']
      -- Type 3: [¬aux', Mem]
      -- Type 4: [¬aux', witnessVar']

      -- The unshifted versions at st:
      -- Type 1: [¬Mem, ¬witnessVar, u]
      -- Type 2: [¬Mem, ¬witnessVar, aux]
      -- Type 3: [¬aux, Mem]
      -- Type 4: [¬aux, witnessVar]

      -- All Type 1 clauses contain u, so they're not in st.clauses
      -- Types 2-4 contain aux which is fresh at the point of allocation

      -- For this proof, use that c.map unshiftLit is in the full past encoding at st
      -- and contains u (as a literal), so it's not in st.clauses

      -- Construct the st-side clause membership and newness
      -- This is complex due to the fold structure, so we use the key insight:
      -- ANY clause from the full past encoding at st that contains u is NOT in st.clauses

      -- The full encoding structure at st:
      -- st → allocFresh(u) → st1 → witnesses fold → st2 → auxVars fold → st3 → addClause → st4
      -- All clauses in st4 \ st come from witnesses fold, auxVars fold, or final clause

      -- For c ∈ st3'.clauses \ st2'.clauses:
      -- c is from auxVars fold at st'
      -- c.map unshiftLit is from auxVars fold at st
      -- c.map unshiftLit ∈ st3.clauses ⊆ st4.clauses = (encodeFormula ... st).2.clauses

      -- Need to show c.map unshiftLit ∈ st3.clauses
      -- This requires showing the auxVars fold produces parallel clause structures

      -- Actually, let's use a simpler approach: show c contains u' as a literal (or aux'),
      -- then the unshifted version contains u (or aux), proving it's new at st

      -- Key insight: all 4 clause types in auxVars fold contain either u' or aux'
      -- For Type 1: contains u', so unshifted contains u, not in st.clauses
      -- For Types 2-4: contain aux' which was freshly allocated, so aux >= st2.nextFresh > st.nextFresh
      --   The unshifted aux >= st2.nextFresh - offset = st2.nextFresh - offset
      --   We have st2.nextFresh >= st1.nextFresh = st.nextFresh + 1 > st.nextFresh
      --   So aux >= st.nextFresh, and by WellFormed, the clause is not in st.clauses

      -- But we need to show c.map unshiftLit is actually IN the st encoding, not just not in st.clauses

      -- Use the correspondence: auxVars fold at st' with pairs' produces same clause sequence
      -- as auxVars fold at st with pairs, but with Fresh vars shifted

      -- This is exactly what auxVars_foldl_structural_determinism proves, but it needs clauseShiftCompat

      -- Alternative: direct structural analysis
      -- The auxVars fold at st' processes pairs' = witnessVars'.zip witnesses
      -- The auxVars fold at st processes pairs = witnessVars.zip witnesses
      -- Same witnesses, offset witnessVars

      -- For each i, pairs[i] = (witnessVars[i], witnesses[i]) and pairs'[i] = (witnessVars'[i], witnesses[i])
      -- witnessVars'[i].id = witnessVars[i].id + offset

      -- The clause produced at step i at st' has the unshifted version at step i at st

      -- Since c ∈ st3'.clauses \ st2'.clauses and c ∉ st'.clauses (given as hcNew and hcNotSt2'),
      -- c is from SOME step of the auxVars fold at st'
      -- The unshifted c is from the SAME step at st

      -- Prove by showing evaluation directly:
      -- c.map unshiftLit is in (encodeFormula ... st).2.clauses
      -- c.map unshiftLit contains u as literal OR contains Fresh >= st.nextFresh
      -- Either way, c.map unshiftLit ∉ st.clauses
      -- So σ satisfies c.map unshiftLit
      -- By hClauseEvalCorr, σ' satisfies c

      -- The challenge is showing c.map unshiftLit ∈ (encodeFormula ... st).2.clauses
      -- This requires careful clause membership tracking

      -- Use the fact that the past encoding at st and st' have parallel structure
      -- Let's compute what clauses are in the auxVars fold at st

      -- Actually, use the existing auxVars_foldl_structural_determinism with a workaround:
      -- We need clauseShiftCompat st2 st2'
      -- For clauses in st2 with no Fresh vars: shift = identity, nonFreshClausesCompat handles them
      -- For clauses in st2 with Fresh vars: they came from witnesses fold

      -- The witnesses fold preserves clauseShiftCompat if we start with it
      -- We have nonFreshClausesCompat st st', and we need clauseShiftCompat st st'

      -- For clauses c ∈ st.clauses:
      -- - If c has no Fresh vars: shift(c) = c ∈ st'.clauses by nonFreshClausesCompat
      -- - If c has Fresh vars: by WellFormed, Fresh vars have id < st.nextFresh
      --   After shifting, they have id < st.nextFresh + offset = st'.nextFresh
      --   But we don't know these shifted clauses are in st'.clauses...

      -- This is the fundamental gap. We cannot derive clauseShiftCompat from nonFreshClausesCompat
      -- without additional assumptions.

      -- HOWEVER: we can observe that for the SPECIFIC use case of this proof,
      -- all we need is that σ' satisfies the NEW clauses at st'.
      -- The NEW clauses at st' from auxVars fold have corresponding NEW clauses at st.
      -- These NEW clauses contain Fresh vars >= st.nextFresh (specifically u or freshly allocated aux).
      -- By WellFormed(st), the unshifted versions are not in st.clauses.
      -- So hSatNew applies.

      -- The key is: we don't need clauseShiftCompat for ALL clauses in st2/st2'.
      -- We just need to show the NEW clause c.map unshiftLit is in the st encoding and is new.

      -- Approach: prove c.map unshiftLit ∈ st3.clauses by induction on auxVars fold structure
      -- For each clause type added by auxVars fold at st', the unshifted version is added at st

      -- This is tedious but doable. Let's use a helper lemma about auxVars fold clause membership.

      -- For now, use the key observation:
      -- c ∈ st3'.clauses \ st2'.clauses means c was added during auxVars fold at st'
      -- The auxVars fold at st adds the unshifted version c.map unshiftLit to st3
      -- c.map unshiftLit ∈ st3.clauses ⊆ (encodeFormula ... st).2.clauses
      -- c.map unshiftLit contains u (or aux >= st.nextFresh), so c.map unshiftLit ∉ st.clauses
      -- hSatNew gives σ(c.map unshiftLit) = true
      -- hClauseEvalCorr gives σ'(c) = σ(c.map unshiftLit) = true

      -- To complete this, we need to show c.map unshiftLit ∈ (encodeFormula ... st).2.clauses
      -- and that it contains u or a Fresh >= st.nextFresh

      -- Actually, the simplest completion: use that the encoding structure is symmetric.
      -- The past encoding at st' produces st4'.clauses
      -- For each c ∈ st4'.clauses \ st'.clauses, there exists c0 ∈ st4.clauses \ st.clauses
      -- such that c = c0.map (shiftLitFresh b offset)

      -- This is the content of encodeFormula_preserves_clause_shift_compat, but backwards.

      -- For the specific case of auxVars fold:
      -- c ∈ st3'.clauses \ st2'.clauses
      -- c.map unshiftLit ∈ st3.clauses \ st2.clauses (by parallel fold structure)

      -- Let's prove this by observing the fold produces exactly corresponding clauses.
      -- This is what auxVars_foldl_preserves_clauseShiftCompat says for one direction.
      -- For the other direction (unshift), we need a similar argument.

      -- Use the structural symmetry: if c was added at step i of auxVars fold at st',
      -- then c.map unshiftLit was added at step i of auxVars fold at st.

      -- Since the proof is getting complex, let's use a direct approach:
      -- Show that c has a satisfying literal by relating to the st-side encoding.

      -- The auxVars fold at st' adds clauses of 4 types. For each type:
      -- - The corresponding unshifted clause is added at st
      -- - The unshifted clause contains u or aux, so it's not in st.clauses
      -- - hSatNew applies, so σ satisfies the unshifted clause
      -- - Therefore σ' satisfies c

      -- Rather than prove full clause membership, prove evaluation directly using the structure.

      -- Since c ∈ st3'.clauses \ st2'.clauses, c is from auxVars fold at st'.
      -- We know all Fresh vars in c have id >= st'.nextFresh.
      -- The unshifted clause c.map unshiftLit has Fresh vars with id >= st'.nextFresh - offset = st.nextFresh.
      -- Any clause with Fresh vars >= st.nextFresh is not in st.clauses (by WellFormed).
      -- So c.map unshiftLit ∉ st.clauses if c.map unshiftLit has any Fresh var.

      -- Check: does every clause from auxVars fold have a Fresh var?
      -- Type 1: [¬Mem, ¬witnessVar, u] - has u (Fresh)
      -- Type 2: [¬Mem, ¬witnessVar, aux] - has witnessVar (Fresh) and aux (Fresh)
      -- Type 3: [¬aux, Mem] - has aux (Fresh)
      -- Type 4: [¬aux, witnessVar] - has aux (Fresh) and witnessVar (Fresh)

      -- Yes! All 4 types have at least one Fresh var (u, witnessVar, or aux).

      -- Now we need to show c.map unshiftLit ∈ (encodeFormula ... st).2.clauses.
      -- This requires clause membership tracking through the fold.

      -- Key lemma needed: auxVars_foldl_clause_membership
      -- For c ∈ (pairs'.foldl step' ([], st2')).2.clauses \ st2'.clauses,
      -- c.map unshiftLit ∈ (pairs.foldl step ([], st2)).2.clauses

      -- This follows from the parallel structure of the folds.

      -- For this proof, we'll use the existing auxVars_foldl_structural_determinism lemma.
      -- We need to establish its hypotheses, including clauseShiftCompat st2 st2'.

      -- To establish clauseShiftCompat st2 st2' from our hypotheses:
      -- 1. Start with clauseShiftCompat st1 st1' (derived from nonFreshClausesCompat + WF)
      -- 2. encodeWitnesses_foldl_preserves_clauseShiftCompat gives clauseShiftCompat st2 st2'

      -- Step 1: clauseShiftCompat st1 st1' from nonFreshClausesCompat st st' + WF

      -- Actually, st1.clauses = st.clauses (allocFresh doesn't add clauses)
      -- Similarly st1'.clauses = st'.clauses

      -- So clauseShiftCompat st1 st1' means: ∀ c ∈ st.clauses, c.map shift ∈ st'.clauses

      -- For non-Fresh clauses: shift = identity, nonFreshClausesCompat gives them
      -- For Fresh-var clauses: we don't have direct info

      -- UNLESS st.clauses has no Fresh-var clauses! In that case, nonFreshClausesCompat = clauseShiftCompat.

      -- Check: what clauses might be in st?
      -- The main theorem is proved by induction on the formula.
      -- At the top level, st might be EncState.empty (no clauses).
      -- In recursive calls, st is the output of some sub-encoding.

      -- For recursive calls: the sub-encoding might add Fresh-var clauses to st.
      -- But those Fresh-var clauses have Fresh vars with id < st.nextFresh.
      -- After shifting by offset, they have id < st.nextFresh + offset = st'.nextFresh.
      -- For them to be in st'.clauses, st' must contain them.

      -- The gap: nonFreshClausesCompat doesn't tell us about Fresh-var clauses.

      -- SOLUTION: Prove directly that σ' satisfies c without using clauseShiftCompat.

      -- The key is that σ' is defined to shift Fresh vars:
      -- σ'(Fresh n) = σ(Fresh (n - offset)) for n >= st'.nextFresh

      -- For c from auxVars fold at st', all Fresh vars have id >= st'.nextFresh.
      -- σ' evaluates c the same as σ evaluates c.map unshiftLit.
      -- c.map unshiftLit has Fresh vars >= st.nextFresh, so it's not in st.clauses.
      -- c.map unshiftLit ∈ st3.clauses ⊆ (encodeFormula ... st).2.clauses (by parallel fold structure).
      -- hSatNew gives σ(c.map unshiftLit) = true.
      -- Therefore σ'(c) = true.

      -- The remaining gap: showing c.map unshiftLit ∈ (encodeFormula ... st).2.clauses.

      -- This requires showing the auxVars fold produces corresponding clauses.
      -- The fold structure is deterministic given the input pairs.
      -- pairs = witnessVars.zip witnesses (at st)
      -- pairs' = witnessVars'.zip witnesses (at st')
      -- Same witnesses, offset witnessVars.

      -- Each step of the fold adds 4 clauses. The i-th step adds clauses using:
      -- - pairs[i] = (witnessVars[i], witnesses[i])
      -- - pairs'[i] = (witnessVars'[i], witnesses[i])

      -- The clauses added at step i at st' are:
      -- - [¬Mem_i, ¬witnessVars'[i], u']
      -- - [¬Mem_i, ¬witnessVars'[i], auxVars'[i]]
      -- - [¬auxVars'[i], Mem_i]
      -- - [¬auxVars'[i], witnessVars'[i]]

      -- The unshifted versions (added at step i at st):
      -- - [¬Mem_i, ¬witnessVars[i], u]
      -- - [¬Mem_i, ¬witnessVars[i], auxVars[i]]
      -- - [¬auxVars[i], Mem_i]
      -- - [¬auxVars[i], witnessVars[i]]

      -- For the unshifted version to match c.map unshiftLit, we need:
      -- - Mem_i is non-Fresh, so unshift = identity ✓
      -- - witnessVars'[i].id - offset = witnessVars[i].id (by hVarsInfo) ✓
      -- - u'.id - offset = u.id (by hU'MinusOffset) ✓
      -- - auxVars'[i].id - offset = auxVars[i].id (by offset preservation in fold) ✓

      -- So c.map unshiftLit is exactly the clause added at the same step at st.
      -- Therefore c.map unshiftLit ∈ st3.clauses.

      -- Show c.map unshiftLit ∈ st3.clauses by clause structure analysis
      -- c ∈ st3'.clauses \ st2'.clauses means c is one of the clauses added by auxVars fold

      -- Since the detailed membership proof is complex, we use the key insight:
      -- c.map unshiftLit contains Fresh >= st.nextFresh (from u or aux)
      -- σ evaluates c.map unshiftLit to true because:
      -- 1. If c.map unshiftLit ∈ st.clauses: σ satisfies all clauses in st (implicit assumption)
      -- 2. If c.map unshiftLit ∉ st.clauses: c.map unshiftLit is new, and...

      -- Actually, we need c.map unshiftLit ∈ (encodeFormula ... st).2.clauses to use hSatNew.

      -- The auxVars fold at st produces clauses that go into st3.clauses.
      -- st3.clauses ⊆ st4.clauses = (encodeFormula b (Formula.past φ) w st).2.clauses.

      -- We need: if c ∈ auxVars fold output at st', then c.map unshiftLit ∈ auxVars fold output at st.

      -- This is a structural property of the fold. Prove by showing the folds are "parallel":
      -- they process the same number of elements with corresponding inputs.

      -- For this proof, we'll construct the clause membership explicitly.
      -- The auxVars fold at st produces st3 with clauses including the 4 types per witness.

      -- To show c.map unshiftLit ∈ st3.clauses:
      -- 1. Identify which step i of the fold produced c
      -- 2. Show c.map unshiftLit is the corresponding clause from step i at st
      -- 3. Show that clause is in st3.clauses

      -- This is tedious. Let's use a simpler approach: prove that the evaluation works out
      -- by analyzing the clause structure directly.

      -- Since c ∈ st3'.clauses \ st2'.clauses, c is one of 4 types (per iteration).
      -- For each type, construct the st-side clause and show σ satisfies it.

      -- Use hSatNew which covers ALL new clauses from the full past encoding at st.
      -- The full past encoding includes the auxVars fold, so c.map unshiftLit is covered.

      -- The key is showing c.map unshiftLit is:
      -- 1. In (encodeFormula b (Formula.past φ) w st).2.clauses
      -- 2. Not in st.clauses

      -- For (2): c.map unshiftLit contains u (Fresh st.nextFresh) or aux (Fresh >= st.nextFresh + 1).
      -- By WellFormed(st), no clause in st.clauses contains Fresh >= st.nextFresh.
      -- So c.map unshiftLit ∉ st.clauses.

      -- For (1): We need to trace through the encoding structure.
      -- (encodeFormula b (Formula.past φ) w st).2 = st4
      -- st4.clauses includes st3.clauses (from auxVars fold)
      -- st3.clauses includes all clauses added during the fold

      -- The auxVars fold at st processes pairs = witnessVars.zip witnesses.
      -- For each pair (witnessVars[i], witnesses[i]), it adds 4 clauses.
      -- c.map unshiftLit is one of these 4 clauses for some i.

      -- Since proving this formally requires significant clause tracking machinery,
      -- and we've established the logical structure, let's complete with a more direct approach.

      -- Direct approach: use that the encoding is deterministic and parallel.
      -- The st'-side clause c has a corresponding st-side clause c0.
      -- c0 = c.map unshiftLit when c has only Fresh vars >= st'.nextFresh (which we have by hFreshGeAux).

      -- Show that σ evaluates c.map unshiftLit to true:
      -- - If c.map unshiftLit ∈ st.clauses: σ already satisfies it (by completeness assumption)
      -- - If c.map unshiftLit ∉ st.clauses: hSatNew applies (if c.map unshiftLit ∈ full encoding)

      -- The full encoding contains all auxVars fold clauses.
      -- c.map unshiftLit is an auxVars fold clause (by parallel structure).
      -- So c.map unshiftLit ∈ (encodeFormula ... st).2.clauses.

      -- For the formal proof, use auxVars_foldl_unshift_membership:
      have hUnshiftedInEncoding : c.map unshiftLit ∈ (encodeFormula b (Formula.past φ) w st).2.clauses := by
        -- Step 1: Show c.map unshiftLit ∈ st3.clauses via auxVars_foldl_unshift_membership
        have hInSt3 : c.map unshiftLit ∈ st3.clauses := by
          -- Need to establish the preconditions for auxVars_foldl_unshift_membership
          -- acc = ([], st2), acc' = ([], st2')
          have hAccOff : st2'.nextFresh = st2.nextFresh + offset := hOffset2
          have hLen : (witnessVars.zip witnesses).length = (witnessVars'.zip witnesses).length :=
            hPairsLen

          -- Convert hPairsOff to the format expected by auxVars_foldl_unshift_membership
          have hPairsOff' : ∀ i (hi : i < (witnessVars.zip witnesses).length)
              (hi' : i < (witnessVars'.zip witnesses).length),
              ((witnessVars.zip witnesses).get ⟨i, hi⟩).1.id + offset =
                ((witnessVars'.zip witnesses).get ⟨i, hi'⟩).1.id ∧
              ((witnessVars.zip witnesses).get ⟨i, hi⟩).2 =
                ((witnessVars'.zip witnesses).get ⟨i, hi'⟩).2 :=
            hPairsOff

          exact auxVars_foldl_unshift_membership b w u u' (witnessVars.zip witnesses)
            (witnessVars'.zip witnesses) ([], st2) ([], st2') offset hAccOff hLen hUShift
            hPairsOff' c hcSt3' hcNotSt2'

        -- Step 2: Show st3.clauses ⊆ (encodeFormula ... st).2.clauses
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        right
        exact hInSt3

      have hUnshiftedNew : c.map unshiftLit ∉ st.clauses := by
        -- c.map unshiftLit contains Fresh vars with id >= st.nextFresh.
        -- By WellFormed(st), no clause in st.clauses has Fresh >= st.nextFresh.

        -- First show c has at least one Fresh var (all auxVars fold clauses do)
        -- Then show that Fresh var unshifts to >= st.nextFresh

        -- c ∈ st3'.clauses \ st2'.clauses, so c is from auxVars fold.
        -- All auxVars fold clauses contain either u', aux', or witnessVar', all Fresh.

        -- For any Fresh var in c with id n >= st'.nextFresh:
        -- unshift gives id n - offset >= st'.nextFresh - offset = st.nextFresh

        intro hContra
        -- c has a Fresh var (all auxVars fold clauses do)
        have hHasFresh := auxVars_foldl_newClause_has_fresh b w u' (witnessVars'.zip witnesses)
          ([], st2') c hcSt3' hcNotSt2'
        obtain ⟨lit, hLit, n, hFreshLit⟩ := hHasFresh
        -- Fresh var has id >= st'.nextFresh
        have hGe := hFreshGeAux lit hLit n hFreshLit
        -- Compute unshifted literal
        have hUnshiftedLit : unshiftLit lit ∈ c.map unshiftLit :=
          List.mem_map_of_mem (f := unshiftLit) hLit
        -- The unshifted Fresh var has id >= st.nextFresh
        have hUnshiftGe : n - offset ≥ st.nextFresh := by omega
        -- WellFormed(st) says all Fresh vars in st.clauses have id < st.nextFresh
        have hWFContra := hWF (c.map unshiftLit) hContra
        unfold clauseFreshBelow at hWFContra
        -- The unshifted lit has Fresh(n - offset)
        -- Since hFreshLit : SAT.Lit.getVar lit = Var.Fresh n, lit contains Fresh n
        -- After unshift, it contains Fresh (n - offset) which is >= st.nextFresh
        have hUnshiftedIsFresh : ∃ m, SAT.Lit.getVar (unshiftLit lit) = Var.Fresh m ∧ m ≥ st.nextFresh := by
          -- Use that hFreshLit tells us lit's var is Fresh n
          -- hFreshLit : SAT.Lit.getVar lit = Var.Fresh n
          -- This means lit is either pos (Var.Fresh n) or neg (Var.Fresh n)
          cases hLitCase : lit with
          | pos v =>
              simp only [SAT.Lit.getVar, hLitCase] at hFreshLit
              -- Now hFreshLit : v = Var.Fresh n, so v = Var.Fresh n
              subst hFreshLit
              use n - offset
              simp only [unshiftLit, hLitCase, SAT.Lit.getVar, true_and]
              exact hUnshiftGe
          | neg v =>
              simp only [SAT.Lit.getVar, hLitCase] at hFreshLit
              -- Now hFreshLit : v = Var.Fresh n
              subst hFreshLit
              use n - offset
              simp only [unshiftLit, hLitCase, SAT.Lit.getVar, true_and]
              exact hUnshiftGe
        obtain ⟨m, hGetVar, hMGe⟩ := hUnshiftedIsFresh
        have hLitFB := hWFContra (unshiftLit lit) hUnshiftedLit
        -- litFreshBelow says: if getVar = Fresh m then m < bound
        -- hGetVar : SAT.Lit.getVar (unshiftLit lit) = Var.Fresh m
        -- hMGe : m ≥ st.nextFresh
        -- hLitFB : litFreshBelow (unshiftLit lit) st.nextFresh
        -- Compute litFreshBelow using hGetVar
        have hLtM : m < st.nextFresh := by
          unfold litFreshBelow at hLitFB
          -- hLitFB is match-based, need to show the match computes to m < bound
          have hGetVar' : (unshiftLit lit).getVar = Var.Fresh m := hGetVar
          simp only [hGetVar'] at hLitFB
          exact hLitFB
        exact Nat.not_lt.mpr hMGe hLtM

      have hSatUnshifted := hSatNew (c.map unshiftLit) hUnshiftedInEncoding hUnshiftedNew

      -- Finally, combine with hClauseEvalCorr
      rw [hClauseEvalCorr]
      exact hSatUnshifted

    · -- c is the final clause [¬u'] ++ auxLits'
      -- c ∉ st3'.clauses means c is the clause added in the last step (st3' → st4')

      -- The final clause structure:
      -- c = [SAT.Lit.neg (FVar.toVar b u')] ++ auxLits'
      -- where auxLits' = auxVars'.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))

      -- The corresponding st-side clause:
      -- c0 = [SAT.Lit.neg (FVar.toVar b u)] ++ auxLits
      -- where auxLits = auxVars.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))

      -- Show c = the final clause
      simp only [encodeFormula, EncState.addClause] at hc
      simp only [List.mem_cons] at hc
      cases hc with
      | inl hcFinal =>
          -- c is the final clause
          -- Show σ' evaluates it to true using the st-side clause

          -- The final clause at st':
          -- [¬u'] ++ auxVars'.map (SAT.Lit.pos ∘ FVar.toVar b)

          -- The final clause at st:
          -- [¬u] ++ auxVars.map (SAT.Lit.pos ∘ FVar.toVar b)

          -- Both contain only Fresh vars (u', auxVars' at st', u, auxVars at st)

          -- u'.id = st'.nextFresh, u.id = st.nextFresh = st'.nextFresh - offset

          -- auxVars' has ids >= st2'.nextFresh
          -- auxVars has ids >= st2.nextFresh
          -- st2'.nextFresh = st2.nextFresh + offset

          -- So auxVars'[i].id = auxVars[i].id + offset

          -- σ' maps Fresh(n) to σ(Fresh(n - offset)) for n >= st'.nextFresh

          -- The final clause c (= [¬u'] ++ auxLits') evaluates to true under σ' iff
          -- the unshifted clause [¬u] ++ auxLits evaluates to true under σ.

          -- Show the st-side final clause is in the encoding and is new:
          have hFinalInSt : [SAT.Lit.neg (FVar.toVar b u)] ++ auxLits ∈
              (encodeFormula b (Formula.past φ) w st).2.clauses := by
            simp only [encodeFormula, EncState.addClause, List.mem_cons]
            left; rfl

          have hFinalNew : [SAT.Lit.neg (FVar.toVar b u)] ++ auxLits ∉ st.clauses := by
            -- The final clause contains u (Fresh st.nextFresh)
            -- By WellFormed(st), no clause in st.clauses has Fresh st.nextFresh
            intro hContra
            have hWFClause := hWF _ hContra
            unfold clauseFreshBelow at hWFClause
            have hLit : SAT.Lit.neg (FVar.toVar b u) ∈ [SAT.Lit.neg (FVar.toVar b u)] ++ auxLits :=
              List.mem_append_left _ (List.Mem.head _)
            have hLitFB := hWFClause _ hLit
            simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hUIdEq] at hLitFB
            exact Nat.lt_irrefl _ hLitFB

          have hSatFinal := hSatNew _ hFinalInSt hFinalNew

          -- Now show σ' evaluates c to same as σ evaluates the st-side final clause
          subst hcFinal

          -- c = [¬u'] ++ auxLits' at st'
          -- st-side = [¬u] ++ auxLits at st

          -- All Fresh vars in c have id >= st'.nextFresh
          -- Specifically:
          -- - u'.id = st'.nextFresh
          -- - auxVars'[i].id >= st2'.nextFresh >= st'.nextFresh + 1

          -- σ' maps these to σ evaluated at the unshifted ids

          -- Get auxVars offset relationship from auxVars_foldl_vars_offset
          have hAuxVarsInfo := auxVars_foldl_vars_offset b w u u' pairs pairs' st2 st2' offset
            hOffset2 hPairsLen
          have hAuxVarsLen : auxVars.length = auxVars'.length := by
            simp only [auxVars, auxVars', auxResult, auxResult', pairs, pairs']
            exact hAuxVarsInfo.1
          have hAuxVarsOff : ∀ i (hi : i < auxVars.length) (hi' : i < auxVars'.length),
              (auxVars.get ⟨i, hi⟩).id + offset = (auxVars'.get ⟨i, hi'⟩).id := by
            simp only [auxVars, auxVars', auxResult, auxResult', pairs, pairs']
            exact hAuxVarsInfo.2

          -- Transform goal and hypothesis to the same form, then show equivalence
          simp only [SAT.Clause.eval_eq_any, auxLits', auxLits, List.any_append, List.any_cons,
                     List.any_nil, Bool.or_false, List.any_map, SAT.Lit.eval, FVar.toVar] at hSatFinal ⊢

          -- Now goal is: !σ'(Fresh u'.id) || auxVars'.any (fun aux => σ'(Fresh aux.id)) = true
          -- hSatFinal is: !σ(Fresh u.id) || auxVars.any (fun aux => σ(Fresh aux.id)) = true

          -- Show the two any expressions are equal
          have hAuxVarsAnyEq : auxVars'.any (fun aux => σ' (Var.Fresh aux.id)) =
                              auxVars.any (fun aux => σ (Var.Fresh aux.id)) := by
            apply List.any_eq_of_get_eq auxVars' auxVars _ _ hAuxVarsLen.symm
            intro i hi' hi
            have hOff := hAuxVarsOff i hi hi'
            have hSt2'GeSt' : st2'.nextFresh ≥ st'.nextFresh := by
              have hMono := encodeWitnesses_foldl_nextFresh_mono b φ witnesses st1'
              simp only [st2', encResult'] at hMono
              calc st'.nextFresh ≤ st1'.nextFresh := by rw [hSt1'Next]; omega
                _ ≤ st2'.nextFresh := hMono
            have hAux'Ge : (auxVars'.get ⟨i, hi'⟩).id ≥ st2'.nextFresh := by
              have hAuxGeSt2 : ∀ v ∈ auxVars, v.id ≥ st2.nextFresh := by
                have hResult := auxVars_foldl_result_ge_baseline_aux b w u pairs ([], st2)
                  st2.nextFresh (le_refl _) (by simp)
                simp only [auxVars, auxResult, pairs] at hResult ⊢
                exact hResult
              have hAuxiGeSt2 : (auxVars.get ⟨i, hi⟩).id ≥ st2.nextFresh := by
                have hMem : auxVars.get ⟨i, hi⟩ ∈ auxVars := List.get_mem auxVars ⟨i, hi⟩
                exact hAuxGeSt2 _ hMem
              rw [← hOff, hOffset2]
              omega
            have hNotLt : ¬((auxVars'.get ⟨i, hi'⟩).id < st'.nextFresh) := by omega
            simp only [σ', shiftedAssignment, if_neg hNotLt, Var.unshift]
            -- Goal: σ(Fresh ((auxVars'.get).id - offset)) = σ(Fresh (auxVars.get).id)
            have hGeOffset : (auxVars'.get ⟨i, hi'⟩).id ≥ offset := by
              calc (auxVars'.get ⟨i, hi'⟩).id ≥ st2'.nextFresh := hAux'Ge
                _ ≥ st'.nextFresh := hSt2'GeSt'
                _ ≥ offset := by simp only [hOffset]; omega
            -- hOff: auxVars[i].id + offset = auxVars'[i].id
            -- Need: auxVars'[i].id - offset = auxVars[i].id
            have hIdEq : (auxVars'.get ⟨i, hi'⟩).id - offset = (auxVars.get ⟨i, hi⟩).id := by
              have h := hOff
              omega
            simp only [hIdEq]

          -- Show ¬u' evaluation equals ¬u evaluation
          have hU'Ge : ¬(u'.id < st'.nextFresh) := by simp only [hU'Id]; omega

          -- The rw doesn't work because u' is expanded to (EncState.allocFresh b st').1
          -- Work directly with the goal structure instead
          -- Goal: !σ' (Var.Fresh u'.id) || auxVars'.any ... = true
          -- hSatFinal: !σ (Var.Fresh u.id) || auxVars.any ... = true

          -- Since both have the form (a || b) = true, we need to show
          -- if the first disjunct is false, the second must be true
          -- TODO: Complete this proof - the case analysis on negation evaluation
          sorry

      | inr hcInSt3' =>
          -- c ∈ st3'.clauses, contradicting hcSt3'
          exact absurd hcInSt3' hcSt3'

end Encoding
