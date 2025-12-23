import ModalDistribution.Logic.SATEncoding.Lemmas.WellFormedness

/-!
# Fresh Variable Bounds Lemmas

This file contains lemmas proving that fresh variables in NEW clauses (clauses added
during encoding but not present in the input state) have indices >= the input state's
nextFresh counter.

Main result: `encodeFormula_new_clause_fresh_ge_nextFresh`

This property is essential for completeness proofs: it guarantees that newly allocated
variables don't appear in prior clauses, allowing us to extend assignments safely.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-! ## Helper lemmas for encodeFormula_new_clause_fresh_ge_nextFresh -/

/-- Bot case: Fresh vars in NEW clauses have index >= st.nextFresh. -/
lemma encodeFormula_bot_fresh_ge_nextFresh (b : Bounds S) (w : WId b)
    (st : EncState b)
    (c : SAT.Clause (Var b)) (hcNew : c ∈ (encodeFormula b Formula.bot w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n >= st.nextFresh := by
  simp only [encodeFormula, EncState.addClause, EncState.allocFresh] at hcNew
  cases hcNew with
  | head =>
      simp only [List.mem_singleton] at hLit
      rw [hLit] at hFresh
      simp only [SAT.Lit.getVar] at hFresh
      have hn : st.nextFresh = n := Var.Fresh.inj hFresh
      omega
  | tail _ hTail =>
      exact absurd hTail hcNotOld

/-- Eq case: Fresh vars in NEW clauses have index >= st.nextFresh. -/
lemma encodeFormula_eq_fresh_ge_nextFresh (b : Bounds S) (v1 v2 : S.Value) (w : WId b)
    (st : EncState b)
    (c : SAT.Clause (Var b)) (hcNew : c ∈ (encodeFormula b (Formula.eq v1 v2) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n >= st.nextFresh := by
  simp only [encodeFormula, EncState.addClause, EncState.allocFresh] at hcNew
  split at hcNew
  · -- v1 == v2: clause is [pos u]
    cases hcNew with
    | head =>
        simp only [List.mem_singleton] at hLit
        rw [hLit] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : st.nextFresh = n := Var.Fresh.inj hFresh
        omega
    | tail _ hTail => exact absurd hTail hcNotOld
  · -- v1 ≠ v2: clause is [neg u]
    cases hcNew with
    | head =>
        simp only [List.mem_singleton] at hLit
        rw [hLit] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : st.nextFresh = n := Var.Fresh.inj hFresh
        omega
    | tail _ hTail => exact absurd hTail hcNotOld

/-- Seq case: Fresh vars in NEW clauses have index >= st.nextFresh. -/
lemma encodeFormula_seq_fresh_ge_nextFresh (b : Bounds S) (w : WId b)
    (st : EncState b)
    (c : SAT.Clause (Var b)) (hcNew : c ∈ (encodeFormula b Formula.seq w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n >= st.nextFresh := by
  simp only [encodeFormula, EncState.addClause, EncState.allocFresh] at hcNew
  cases hcNew with
  | head =>
      -- Second clause: [neg Seq, pos u]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      rcases hLit with h1 | h2
      · rw [h1] at hFresh
        simp only [SAT.Lit.getVar] at hFresh
        cases hFresh
      · rw [h2] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : st.nextFresh = n := Var.Fresh.inj hFresh
        omega
  | tail _ hTail1 =>
      cases hTail1 with
      | head =>
          -- First clause: [neg u, pos Seq]
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with h1 | h2
          · rw [h1] at hFresh
            simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : st.nextFresh = n := Var.Fresh.inj hFresh
            omega
          · rw [h2] at hFresh
            simp only [SAT.Lit.getVar] at hFresh
            cases hFresh
      | tail _ hTail2 => exact absurd hTail2 hcNotOld

/-- Imp case: Fresh vars in NEW clauses have index >= st.nextFresh. -/
lemma encodeFormula_imp_fresh_ge_nextFresh (b : Bounds S) (φ1 φ2 : Formula S) (w : WId b)
    (st : EncState b) (hWF : EncState.WellFormed st)
    (c : SAT.Clause (Var b)) (hcNew : c ∈ (encodeFormula b (Formula.imp φ1 φ2) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n)
    (ih1 : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ1 w' st').2.clauses →
           c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
           n' >= st'.nextFresh)
    (ih2 : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ2 w' st').2.clauses →
           c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
           n' >= st'.nextFresh) :
    n >= st.nextFresh := by
  simp only [encodeFormula] at hcNew
  simp only [EncState.addClause, EncState.allocFresh] at hcNew

  -- Define intermediate states
  let st1 := (encodeFormula b φ1 w st).2
  let u1 := (encodeFormula b φ1 w st).1
  let st2 := (encodeFormula b φ2 w st1).2
  let u2 := (encodeFormula b φ2 w st1).1
  let u := st2.nextFresh

  -- Monotonicity facts
  have hSt1Mono : st.nextFresh <= st1.nextFresh := encodeFormula_nextFresh_mono b φ1 w st
  have hSt2Mono : st1.nextFresh <= st2.nextFresh := encodeFormula_nextFresh_mono b φ2 w st1

  -- Control variable bounds
  have hU1Ge : u1.id >= st.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ1 w st
  have hU2Ge : u2.id >= st1.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ2 w st1

  -- WellFormed states propagate through encoding
  have hWF1 : EncState.WellFormed st1 := encodeFormula_preserves_wf b φ1 w st hWF
  have hWF2 : EncState.WellFormed st2 := encodeFormula_preserves_wf b φ2 w st1 hWF1

  -- Case analysis: c is one of the 3 Tseytin clauses or from recursive encoding
  cases hcNew with
  | head =>
      -- c = [neg u, neg u1, pos u2] (third Tseytin clause)
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      rcases hLit with h1 | h2 | h3
      · -- lit = neg (Fresh u) where u = st2.nextFresh
        rw [h1] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : st2.nextFresh = n := Var.Fresh.inj hFresh
        omega
      · -- lit = neg (Fresh u1.id) where u1 is from encodeFormula φ1
        rw [h2] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : u1.id = n := Var.Fresh.inj hFresh
        omega
      · -- lit = pos (Fresh u2.id) where u2 is from encodeFormula φ2
        rw [h3] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : u2.id = n := Var.Fresh.inj hFresh
        omega
  | tail _ hTail1 =>
      cases hTail1 with
      | head =>
          -- c = [neg u2, pos u] (second Tseytin clause)
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with h1 | h2
          · -- lit = neg (Fresh u2.id)
            rw [h1] at hFresh
            simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : u2.id = n := Var.Fresh.inj hFresh
            omega
          · -- lit = pos (Fresh u) where u = st2.nextFresh
            rw [h2] at hFresh
            simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : st2.nextFresh = n := Var.Fresh.inj hFresh
            omega
      | tail _ hTail2 =>
          cases hTail2 with
          | head =>
              -- c = [pos u1, pos u] (first Tseytin clause)
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
              rcases hLit with h1 | h2
              · -- lit = pos (Fresh u1.id)
                rw [h1] at hFresh
                simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
                have hn : u1.id = n := Var.Fresh.inj hFresh
                omega
              · -- lit = pos (Fresh u) where u = st2.nextFresh
                rw [h2] at hFresh
                simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
                have hn : st2.nextFresh = n := Var.Fresh.inj hFresh
                omega
          | tail _ hRest =>
              -- c ∈ st2.clauses (from recursive encodings)
              by_cases hcSt1 : c ∈ (encodeFormula b φ1 w st).2.clauses
              · -- c ∈ st1.clauses
                by_cases hcSt : c ∈ st.clauses
                · exact absurd hcSt hcNotOld
                · -- c is from φ1 encoding (NEW in st1, not in st)
                  exact ih1 w st hWF c hcSt1 hcSt lit hLit n hFresh
              · -- c ∉ st1.clauses, so c is from φ2 encoding
                have hc2 : c ∈ (encodeFormula b φ2 w (encodeFormula b φ1 w st).2).2.clauses :=
                  hRest
                exact Nat.le_trans hSt1Mono (ih2 w (encodeFormula b φ1 w st).2 hWF1 c hc2
                  hcSt1 lit hLit n hFresh)

/-- AtEnd case: Fresh vars in NEW clauses have index >= st.nextFresh. -/
lemma encodeFormula_atEnd_fresh_ge_nextFresh (b : Bounds S) (φ : Formula S) (w : WId b)
    (st : EncState b) (hWF : EncState.WellFormed st)
    (c : SAT.Clause (Var b)) (hcNew : c ∈ (encodeFormula b (Formula.atEnd φ) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n)
    (ih : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh) :
    n >= st.nextFresh := by
  simp only [encodeFormula] at hcNew
  simp only [EncState.addClause, EncState.allocFresh] at hcNew

  -- Define intermediate state and control var
  let wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
  let st1 := (encodeFormula b φ wEnd st).2
  let u' := (encodeFormula b φ wEnd st).1
  let u := st1.nextFresh

  -- Monotonicity and control var bounds
  have hSt1Mono : st.nextFresh <= st1.nextFresh := encodeFormula_nextFresh_mono b φ wEnd st
  have hU'Ge : u'.id >= st.nextFresh := encodeFormula_controlVar_ge_nextFresh b φ wEnd st

  -- WellFormed propagation
  have hWF1 : EncState.WellFormed st1 := encodeFormula_preserves_wf b φ wEnd st hWF

  -- Case analysis on which clause c is
  cases hcNew with
  | head =>
      -- c = [neg u', pos u] (second Tseytin clause)
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      rcases hLit with h1 | h2
      · -- lit = neg (Fresh u'.id)
        rw [h1] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : u'.id = n := Var.Fresh.inj hFresh
        omega
      · -- lit = pos (Fresh u) where u = st1.nextFresh
        rw [h2] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : st1.nextFresh = n := Var.Fresh.inj hFresh
        omega
  | tail _ hTail1 =>
      cases hTail1 with
      | head =>
          -- c = [neg u, pos u'] (first Tseytin clause)
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with h1 | h2
          · -- lit = neg (Fresh u) where u = st1.nextFresh
            rw [h1] at hFresh
            simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : st1.nextFresh = n := Var.Fresh.inj hFresh
            omega
          · -- lit = pos (Fresh u'.id)
            rw [h2] at hFresh
            simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : u'.id = n := Var.Fresh.inj hFresh
            omega
      | tail _ hRest =>
          -- c ∈ st1.clauses (from recursive encoding of φ)
          by_cases hcSt : c ∈ st.clauses
          · exact absurd hcSt hcNotOld
          · -- c is from φ encoding (NEW in st1, not in st)
            exact ih wEnd st hWF c hRest hcSt lit hLit n hFresh

/-- Predicate case: Fresh vars in NEW clauses have index >= st.nextFresh. -/
lemma encodeFormula_predicate_fresh_ge_nextFresh (b : Bounds S) (atom : PredicateAtom S) (w : WId b)
    (st : EncState b)
    (c : SAT.Clause (Var b)) (hcNew : c ∈ (encodeFormula b (Formula.predicate atom) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n >= st.nextFresh := by
  simp only [encodeFormula] at hcNew

  let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
  let idxs := predIxList b pred
  let literals := idxs.map (fun k => Var.Pred w.p w.ti k)
  let st1 := (mkBigOrIff b literals st).2
  -- Control var id fact
  have hFVarEq : FVar.toVar b (mkBigOrIff b literals st).1 = Var.Fresh st.nextFresh := by
    have h := mkBigOrIff_fst b literals st
    simp only [h, FVar.toVar]

  split at hcNew
  · -- idxs = []: output is just st1
    have hVarsOpt := mkBigOrIff_newClause_vars b literals st c hcNew hcNotOld lit hLit
    rcases hVarsOpt with hIsU | hInLiterals
    · have hEq : Var.Fresh (b := b) st.nextFresh = Var.Fresh n :=
        hFVarEq.symm.trans (hIsU.symm.trans hFresh)
      have hn : st.nextFresh = n := Var.Fresh.inj hEq
      omega
    · have hLitInMap : SAT.Lit.getVar lit ∈ idxs.map (fun k => Var.Pred w.p w.ti k) :=
        hInLiterals
      rw [List.mem_map] at hLitInMap
      obtain ⟨k, _, hLitEq⟩ := hLitInMap
      rw [← hLitEq] at hFresh
      cases hFresh

  · -- idxs ≠ []: additional folds after mkBigOrIff
    by_cases hcSt1 : c ∈ (mkBigOrIff b literals st).2.clauses
    · -- c ∈ st1.clauses (from mkBigOrIff)
      by_cases hcSt : c ∈ st.clauses
      · exact absurd hcSt hcNotOld
      · -- c is a NEW mkBigOrIff clause
        have hVarsOpt := mkBigOrIff_newClause_vars b literals st c hcSt1 hcSt lit hLit
        rcases hVarsOpt with hIsU | hInLiterals
        · have hEq : Var.Fresh (b := b) st.nextFresh = Var.Fresh n :=
            hFVarEq.symm.trans (hIsU.symm.trans hFresh)
          have hn : st.nextFresh = n := Var.Fresh.inj hEq
          omega
        · have hLitInMap : SAT.Lit.getVar lit ∈ idxs.map (fun k => Var.Pred w.p w.ti k) :=
            hInLiterals
          rw [List.mem_map] at hLitInMap
          obtain ⟨k, _, hLitEq⟩ := hLitInMap
          rw [← hLitEq] at hFresh
          cases hFresh
    · -- c ∉ st1.clauses (from one of the folds: addPreEqFrom → addPreEqReflAll → st4)
      -- We show n >= st1.nextFresh >= st.nextFresh by analyzing each fold
      have hSt1Mono : st.nextFresh <= st1.nextFresh := by
        simp only [st1, mkBigOrIff_nextFresh b literals st]; omega
      -- Define intermediate states
      let st2 := addPreEqFrom b w.ti st1
      let st3 := addPreEqReflAll b st2
      -- backward/forward clauses for the nested fold
      let backward (H' : b.times) (k : b.predIx) : SAT.Clause (Var b) :=
        [SAT.Lit.neg (Var.PreEq w.ti H'), SAT.Lit.neg (Var.Pred w.p H' k),
         SAT.Lit.pos (Var.Pred w.p w.ti k)]
      let forward (H' : b.times) (k : b.predIx) : SAT.Clause (Var b) :=
        [SAT.Lit.neg (Var.PreEq w.ti H'), SAT.Lit.neg (Var.Pred w.p w.ti k),
         SAT.Lit.pos (Var.Pred w.p H' k)]
      let st4 := (Bounds.timesL b).foldl (fun stCur H' =>
          idxs.foldl (fun stAcc k =>
            let stAcc' := EncState.addClause b stAcc (backward H' k)
            EncState.addClause b stAcc' (forward H' k)) stCur) st3

      -- Helper: backward/forward clauses have no Fresh vars
      have hNoFreshBF : ∀ H' k lit, lit ∈ backward H' k ∨ lit ∈ forward H' k →
          ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n := by
        intro H' k lit hLit n hEq
        rcases hLit with hB | hF
        · simp only [backward, List.mem_cons, List.mem_nil_iff, or_false] at hB
          rcases hB with rfl | rfl | rfl <;> simp only [SAT.Lit.getVar] at hEq <;> cases hEq
        · simp only [forward, List.mem_cons, List.mem_nil_iff, or_false] at hF
          rcases hF with rfl | rfl | rfl <;> simp only [SAT.Lit.getVar] at hEq <;> cases hEq

      -- Clause subset chain
      have hSt1St2 : st1.clauses ⊆ st2.clauses := addPreEqFrom_clauses_subset b w.ti st1
      have hSt2St3 : st2.clauses ⊆ st3.clauses := addPreEqReflAll_clauses_subset b st2
      have hSt3St4 : st3.clauses ⊆ st4.clauses := by
        simp only [st4]
        apply foldl_subset_state (b := b) (f := fun stCur H' =>
          idxs.foldl (fun stAcc k =>
            EncState.addClause b (EncState.addClause b stAcc (backward H' k)) (forward H' k)) stCur)
        intro stCur H'
        apply foldl_subset_state (b := b) (f := fun stAcc k =>
          EncState.addClause b (EncState.addClause b stAcc (backward H' k)) (forward H' k))
        intro stAcc k
        let stAcc' := EncState.addClause b stAcc (backward H' k)
        calc stAcc.clauses
            ⊆ stAcc'.clauses := EncState.addClause_subset_clauses b stAcc (backward H' k)
          _ ⊆ (EncState.addClause b stAcc' (forward H' k)).clauses :=
              EncState.addClause_subset_clauses b stAcc' (forward H' k)

      -- Check if c is from st3 (before the nested fold)
      by_cases hcSt3 : c ∈ st3.clauses
      · -- c ∈ st3.clauses
        -- Either c ∈ st2.clauses, or c is from addPreEqReflAll (no Fresh vars)
        by_cases hcSt2 : c ∈ st2.clauses
        · -- c ∈ st2.clauses ∧ c ∉ st1.clauses
          -- c is from addPreEqFrom. Fresh vars in addPreEqFrom new clauses have id >= st1.nextFresh
          have hFreshGeSt1 := addPreEqFrom_newClause_fresh_ge b w.ti st1 c hcSt2 hcSt1
            lit hLit n hFresh
          omega
        · -- c ∈ st3.clauses ∧ c ∉ st2.clauses
          -- c is from addPreEqReflAll, which only adds [pos (PreEq t t)] - no Fresh vars
          have hNoFresh := addPreEqReflAll_clauses_nonFresh b st2 c hcSt3 hcSt2
          exact absurd hFresh (hNoFresh lit hLit n)
      · -- c ∉ st3.clauses, so c is from the nested fold (backward/forward clauses)
        -- These clauses only have PreEq/Pred vars, no Fresh vars
        exfalso
        -- Use nested_foldl_addClause2_mem to classify c
        have hMem :=
          nested_foldl_addClause2_mem b (Bounds.timesL b) idxs st3 backward forward c hcNew
        rcases hMem with hcSt3' | ⟨H', _, k', _, hBackOrFwd⟩
        · exact hcSt3 hcSt3'
        · -- c = backward H' k' or c = forward H' k', both have no Fresh vars
          rcases hBackOrFwd with hBack | hFwd
          · exact hNoFreshBF H' k' lit (Or.inl (hBack ▸ hLit)) n hFresh
          · exact hNoFreshBF H' k' lit (Or.inr (hFwd ▸ hLit)) n hFresh

/-- Event case: Fresh vars in NEW clauses have index >= st.nextFresh. -/
lemma encodeFormula_event_fresh_ge_nextFresh (b : Bounds S) (atom : EventAtom S) (w : WId b)
    (st : EncState b)
    (c : SAT.Clause (Var b)) (hcNew : c ∈ (encodeFormula b (Formula.event atom) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n >= st.nextFresh := by
  simp only [encodeFormula] at hcNew
  let evt : Signature.EventType S := ⟨atom.sym, atom.args⟩
  split at hcNew
  · -- MaybeEvent.some e
    rename_i e hDecode
    split at hcNew
    · -- e = evt: encodeFormulaEvent case
      simp only [encodeFormulaEvent] at hcNew
      let witnessPairs := eventWitnessPairs b w evt
      let stFold := (witnessPairs.foldl (eventWitnessStep b) ([], st)).2
      let witnessVars := (witnessPairs.foldl (eventWitnessStep b) ([], st)).1
      have hFoldMono : st.nextFresh <= stFold.nextFresh :=
        foldl_eventWitnessStep_nextFresh_mono b witnessPairs ([], st)
      have hFVarEq :
          FVar.toVar b (mkBigOrIff b witnessVars stFold).1 = Var.Fresh stFold.nextFresh := by
        simp only [mkBigOrIff_fst, FVar.toVar]
      -- Check if c is from mkBigOrIff or from eventWitnessStep fold
      by_cases hcFold : c ∈ stFold.clauses
      · -- c is from eventWitnessStep fold
        by_cases hcSt : c ∈ st.clauses
        · exact absurd hcSt hcNotOld
        · -- c is NEW in eventWitnessStep fold
          have hPairsNF : ∀ p ∈ witnessPairs, Var.notFresh b p.1 ∧ Var.notFresh b p.2 :=
            fun p hp => eventWitnessPairs_notFresh b w evt p hp
          exact foldl_eventWitnessStep_newClause_fresh_ge b witnessPairs hPairsNF ([], st)
            c hcFold hcSt lit hLit n hFresh
      · -- c ∉ stFold.clauses, so c is from mkBigOrIff
        have hVarsOpt := mkBigOrIff_newClause_vars b witnessVars stFold c hcNew hcFold lit hLit
        rcases hVarsOpt with hIsU | hInWitness
        · -- lit.getVar = control var from mkBigOrIff
          have hEq : Var.Fresh (b := b) stFold.nextFresh = Var.Fresh n :=
            hFVarEq.symm.trans (hIsU.symm.trans hFresh)
          have hn : stFold.nextFresh = n := Var.Fresh.inj hEq
          omega
        · -- lit.getVar ∈ witnessVars (which are Fresh vars from eventWitnessStep)
          exact foldl_eventWitnessStep_witnessVars_fresh_ge_empty b witnessPairs st
            lit.getVar hInWitness n hFresh
    · -- e ≠ evt: guard fails, allocFresh + addClause [neg u]
      simp only [EncState.addClause, EncState.allocFresh] at hcNew
      cases hcNew with
      | head =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rw [hLit] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : st.nextFresh = n := Var.Fresh.inj hFresh
          omega
      | tail _ hTail => exact absurd hTail hcNotOld
  · -- MaybeEvent.none: guard fails, allocFresh + addClause [neg u]
    simp only [EncState.addClause, EncState.allocFresh] at hcNew
    cases hcNew with
    | head =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
        rw [hLit] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : st.nextFresh = n := Var.Fresh.inj hFresh
        omega
    | tail _ hTail => exact absurd hTail hcNotOld

/-- Helper: encodeWitnesses fold output vars have ids ≥ input state's nextFresh (baseline). -/
lemma encodeWitnesses_foldl_vars_ge_baseline_aux (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (acc : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh)
    (hAccGe : ∀ v ∈ acc.1, v.id ≥ baseline) :
    let result := witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) acc
    ∀ v ∈ result.1, v.id ≥ baseline := by
  induction witnesses generalizing acc with
  | nil =>
    simp only [List.foldl_nil]
    exact hAccGe
  | cons w' ws ih =>
    simp only [List.foldl_cons]
    apply ih
    · -- baseline ≤ step.2.nextFresh
      have hMono := encodeFormula_nextFresh_mono b φ w' acc.2
      exact Nat.le_trans hBaseline hMono
    · -- ∀ v ∈ step.1, v.id ≥ baseline
      intro v hv
      simp only [List.mem_append, List.mem_singleton] at hv
      cases hv with
      | inl hOld => exact hAccGe v hOld
      | inr hNew =>
        subst hNew
        have hGeNF := encodeFormula_controlVar_ge_nextFresh b φ w' acc.2
        exact Nat.le_trans hBaseline hGeNF

/-- Helper: encodeWitnesses fold output vars have ids ≥ input state's nextFresh. -/
lemma encodeWitnesses_foldl_vars_ge_baseline (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (st : EncState b) :
    let result := witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) ([], st)
    ∀ v ∈ result.1, v.id ≥ st.nextFresh := by
  apply encodeWitnesses_foldl_vars_ge_baseline_aux
  · exact Nat.le_refl _
  · intro v hv; simp only [List.not_mem_nil] at hv

/-- Helper: encodeWitnesses fold clauses subset for tracking NEW clauses. -/
lemma encodeWitnesses_foldl_clauses_subset_aux (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (acc : List (FVar b) × EncState b) :
    acc.2.clauses ⊆ (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) acc).2.clauses := by
  induction witnesses generalizing acc with
  | nil => simp only [List.foldl_nil]; exact List.Subset.refl _
  | cons w' ws ih =>
    simp only [List.foldl_cons]
    let acc' := (acc.1 ++ [(encodeFormula b φ w' acc.2).1], (encodeFormula b φ w' acc.2).2)
    have hStep : acc.2.clauses ⊆ acc'.2.clauses := encodeFormula_clauses_subset b φ w' acc.2
    exact List.Subset.trans hStep (ih acc')

/-- Helper: Fresh vars in NEW clauses from encodeWitnesses fold have index ≥ input nextFresh. -/
lemma encodeWitnesses_foldl_newClause_fresh_ge_aux (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (acc : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh)
    (hWF : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline := by
  induction witnesses generalizing acc c lit n with
  | nil =>
    simp only [List.foldl_nil] at hcNew
    exact absurd hcNew hcNotOld
  | cons w' ws ihWs =>
    simp only [List.foldl_cons] at hcNew
    by_cases hcStep : c ∈ (encodeFormula b φ w' acc.2).2.clauses
    · by_cases hcAcc : c ∈ acc.2.clauses
      · exact absurd hcAcc hcNotOld
      · -- c is NEW from encodeFormula φ w' acc.2
        have hFreshGeAcc := ih w' acc.2 hWF c hcStep hcAcc lit hLit n hFresh
        exact Nat.le_trans hBaseline hFreshGeAcc
    · -- c is from the tail fold
      have hMono := encodeFormula_nextFresh_mono b φ w' acc.2
      have hWFStep := encodeFormula_preserves_wf b φ w' acc.2 hWF
      exact ihWs (acc.1 ++ [(encodeFormula b φ w' acc.2).1], (encodeFormula b φ w' acc.2).2)
        (Nat.le_trans hBaseline hMono) hWFStep c hcNew hcStep lit hLit n hFresh

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: auxVars fold step adds 4 clauses that only contain Fresh vars with id ≥ baseline
    if the input vars (u, u') have id ≥ baseline and baseline ≤ acc.2.nextFresh. -/
lemma auxVars_step_newClause_fresh_ge (b : Bounds S) (w : WId b) (u : FVar b)
    (uv : FVar b) (w' : WId b) (acc : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh)
    (hUGe : u.id ≥ baseline) (hUvGe : uv.id ≥ baseline)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (let memVar := Var.Mem w.ti w'
                  let (aux, stCur) := EncState.allocFresh b acc.2
                  let clause1 := [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv),
                                  SAT.Lit.pos (FVar.toVar b u)]
                  let stCur := EncState.addClause b stCur clause1
                  let clause2 := [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv),
                                  SAT.Lit.pos (FVar.toVar b aux)]
                  let stCur := EncState.addClause b stCur clause2
                  let clause3 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
                  let stCur := EncState.addClause b stCur clause3
                  let clause4 := [SAT.Lit.neg (FVar.toVar b aux),
                                  SAT.Lit.pos (FVar.toVar b uv)]
                  let stCur := EncState.addClause b stCur clause4
                  (acc.1 ++ [aux], stCur)).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline := by
  -- aux.id = acc.2.nextFresh ≥ baseline
  have hAuxId : (EncState.allocFresh b acc.2).1.id = acc.2.nextFresh :=
    EncState.allocFresh_fst (b := b) acc.2
  have hAuxGe : (EncState.allocFresh b acc.2).1.id ≥ baseline := by rw [hAuxId]; exact hBaseline
  -- Trace through clauses
  simp only [EncState.addClause, EncState.allocFresh_clauses_eq] at hcNew
  cases hcNew with
  | head =>
      -- c = [neg aux, pos uv] (4th clause)
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      rcases hLit with h1 | h2
      · rw [h1] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : (EncState.allocFresh b acc.2).1.id = n := Var.Fresh.inj hFresh
        rw [← hn]; exact hAuxGe
      · rw [h2] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : uv.id = n := Var.Fresh.inj hFresh
        rw [← hn]; exact hUvGe
  | tail _ hTail1 =>
    cases hTail1 with
    | head =>
        -- c = [neg aux, pos Mem] (3rd clause)
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
        rcases hLit with h1 | h2
        · rw [h1] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : (EncState.allocFresh b acc.2).1.id = n := Var.Fresh.inj hFresh
          rw [← hn]; exact hAuxGe
        · rw [h2] at hFresh; simp only [SAT.Lit.getVar] at hFresh
          exact Var.noConfusion hFresh -- Mem is not Fresh
    | tail _ hTail2 =>
      cases hTail2 with
      | head =>
          -- c = [neg Mem, neg uv, pos aux] (2nd clause)
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with h1 | h2 | h3
          · rw [h1] at hFresh; simp only [SAT.Lit.getVar] at hFresh
            exact Var.noConfusion hFresh -- Mem is not Fresh
          · rw [h2] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : uv.id = n := Var.Fresh.inj hFresh
            rw [← hn]; exact hUvGe
          · rw [h3] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : (EncState.allocFresh b acc.2).1.id = n := Var.Fresh.inj hFresh
            rw [← hn]; exact hAuxGe
      | tail _ hTail3 =>
        cases hTail3 with
        | head =>
            -- c = [neg Mem, neg uv, pos u] (1st clause)
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
            rcases hLit with h1 | h2 | h3
            · rw [h1] at hFresh; simp only [SAT.Lit.getVar] at hFresh
              exact Var.noConfusion hFresh -- Mem is not Fresh
            · rw [h2] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
              have hn : uv.id = n := Var.Fresh.inj hFresh
              rw [← hn]; exact hUvGe
            · rw [h3] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
              have hn : u.id = n := Var.Fresh.inj hFresh
              rw [← hn]; exact hUGe
        | tail _ hOld =>
            -- c ∈ allocFresh.clauses = acc.2.clauses
            exact absurd hOld hcNotOld

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: auxVars fold allocates aux vars with ids ≥ baseline. -/
lemma auxVars_foldl_result_ge_baseline_aux (b : Bounds S) (w : WId b) (u : FVar b)
    (pairs : List (FVar b × WId b)) (acc : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh)
    (hAccGe : ∀ v ∈ acc.1, v.id ≥ baseline) :
    let result := pairs.foldl (fun (auxAcc, stCur) (uv, w') =>
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
      (auxAcc ++ [aux], stCur)) acc
    ∀ v ∈ result.1, v.id ≥ baseline := by
  induction pairs generalizing acc with
  | nil =>
    simp only [List.foldl_nil]
    exact hAccGe
  | cons p ps ih =>
    simp only [List.foldl_cons]
    apply ih
    · -- baseline ≤ step.2.nextFresh
      have hAllocNext := EncState.allocFresh_nextFresh b acc.2
      simp only [EncState.addClause]
      omega
    · -- ∀ v ∈ step.1, v.id ≥ baseline
      intro v hv
      simp only [List.mem_append, List.mem_singleton] at hv
      cases hv with
      | inl hOld => exact hAccGe v hOld
      | inr hNew =>
        subst hNew
        have hAuxId := EncState.allocFresh_fst (b := b) acc.2
        rw [hAuxId]
        exact hBaseline

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Fresh vars in NEW clauses from auxVars fold have index ≥ baseline. -/
lemma auxVars_foldl_newClause_fresh_ge_aux (b : Bounds S) (w : WId b) (u : FVar b)
    (pairs : List (FVar b × WId b)) (acc : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh)
    (hUGe : u.id ≥ baseline)
    (hPairsGe : ∀ p ∈ pairs, p.1.id ≥ baseline)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (pairs.foldl (fun (auxAcc, stCur) (uv, w') =>
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
      (auxAcc ++ [aux], stCur)) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline := by
  induction pairs generalizing acc c lit n with
  | nil =>
    simp only [List.foldl_nil] at hcNew
    exact absurd hcNew hcNotOld
  | cons p ps ihPs =>
    simp only [List.foldl_cons] at hcNew
    have hpGe := hPairsGe p (List.mem_cons_self (a := p) (l := ps))
    -- Define step explicitly matching the fold structure
    let memVar := Var.Mem w.ti p.2
    let allocRes := EncState.allocFresh b acc.2
    let aux := allocRes.1
    let st0 := allocRes.2
    let st1 := EncState.addClause b st0
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b u)]
    let st2 := EncState.addClause b st1
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b aux)]
    let clause3 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
    let st3 := EncState.addClause b st2 clause3
    let clause4 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b p.1)]
    let stFinal := EncState.addClause b st3 clause4
    let acc' : List (FVar b) × EncState b := (acc.1 ++ [aux], stFinal)
    by_cases hcStep : c ∈ acc'.2.clauses
    · by_cases hcAcc : c ∈ acc.2.clauses
      · exact absurd hcAcc hcNotOld
      · -- c is NEW from this step
        exact auxVars_step_newClause_fresh_ge b w u p.1 p.2 acc baseline hBaseline hUGe hpGe
          c hcStep hcAcc lit hLit n hFresh
    · -- c is from the tail fold
      have hMono : acc.2.nextFresh + 1 = acc'.2.nextFresh := by
        simp only [acc', stFinal, st3, st2, st1, st0, allocRes, clause3, clause4,
          EncState.addClause, EncState.allocFresh_nextFresh]
      have hBaseline' : baseline ≤ acc'.2.nextFresh := by
        have h : baseline < acc'.2.nextFresh := calc baseline
          _ ≤ acc.2.nextFresh := hBaseline
          _ < acc.2.nextFresh + 1 := Nat.lt_succ_self _
          _ = acc'.2.nextFresh := hMono
        exact Nat.le_of_lt h
      have hPsGe : ∀ p' ∈ ps, p'.1.id ≥ baseline := fun p' hp' =>
        hPairsGe p' (List.mem_cons_of_mem p hp')
      exact ihPs acc' hBaseline' hPsGe c hcNew hcStep lit hLit n hFresh

/-- Past case: Fresh vars in NEW clauses have index >= st.nextFresh. -/
lemma encodeFormula_past_fresh_ge_nextFresh (b : Bounds S) (φ : Formula S) (w : WId b)
    (st : EncState b) (hWF : EncState.WellFormed st)
    (c : SAT.Clause (Var b)) (hcNew : c ∈ (encodeFormula b (Formula.past φ) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n)
    (ih : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh) :
    n >= st.nextFresh := by
  simp only [encodeFormula] at hcNew
  -- Define intermediate states
  let u := (EncState.allocFresh b st).1
  let st1 := (EncState.allocFresh b st).2
  let witnesses := (WId.allWorlds b).filterMap fun w' => if w'.p = w.p then some w' else none
  let encResult := witnesses.foldl (fun (uvars, stCur) w' =>
      let (u', stNext) := encodeFormula b φ w' stCur
      (uvars ++ [u'], stNext)) ([], st1)
  let witnessVars := encResult.1
  let st2 := encResult.2
  let auxResult := (witnessVars.zip witnesses).foldl (fun (auxAcc, stCur) (u', w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
      (auxAcc ++ [aux], stCur)) ([], st2)
  let auxVars := auxResult.1
  let st3 := auxResult.2
  let auxLits := auxVars.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))
  let st4 := EncState.addClause b st3 ([SAT.Lit.neg (FVar.toVar b u)] ++ auxLits)

  -- Key facts
  have hUId : u.id = st.nextFresh := EncState.allocFresh_fst (b := b) st
  have hSt1Next : st1.nextFresh = st.nextFresh + 1 := EncState.allocFresh_nextFresh b st
  have hSt1WF : st1.WellFormed := EncState.allocFresh_wf hWF
  have hSt1Sub : st.clauses ⊆ st1.clauses := by
    rw [EncState.allocFresh_clauses_eq]; exact List.Subset.refl _
  have hSt1St2Mono : st1.nextFresh ≤ st2.nextFresh :=
    encodeWitnesses_foldl_nextFresh_mono b φ witnesses st1
  have hSt2Sub : st1.clauses ⊆ st2.clauses :=
    encodeWitnesses_foldl_clauses_subset_aux b φ witnesses ([], st1)
  have hSt2St3Mono : st2.nextFresh ≤ st3.nextFresh :=
    auxVars_foldl_nextFresh_mono b w u witnessVars witnesses st2

  -- witnessVars have ids ≥ st1.nextFresh
  have hWitnessVarsGe : ∀ v ∈ witnessVars, v.id ≥ st1.nextFresh :=
    encodeWitnesses_foldl_vars_ge_baseline b φ witnesses st1
  -- auxVars have ids ≥ st2.nextFresh
  have hAuxVarsGe : ∀ v ∈ auxVars, v.id ≥ st2.nextFresh := by
    apply auxVars_foldl_result_ge_baseline_aux b w u (witnessVars.zip witnesses)
      ([], st2) st2.nextFresh
    · exact Nat.le_refl _
    · intro v hv; simp only [List.not_mem_nil] at hv

  -- Case analysis on where c comes from
  simp only [EncState.addClause] at hcNew
  cases hcNew with
  | head =>
      -- c is the final clause [neg u, pos aux1, ...]
      simp only [List.mem_append] at hLit
      cases hLit with
      | inl hNegU =>
          simp only [List.mem_singleton] at hNegU
          rw [hNegU] at hFresh
          simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : u.id = n := Var.Fresh.inj hFresh
          rw [hUId] at hn; omega
      | inr hAuxLit =>
          simp only [List.mem_map] at hAuxLit
          obtain ⟨aux, hAuxMem, hLitEq⟩ := hAuxLit
          rw [← hLitEq] at hFresh
          simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : aux.id = n := Var.Fresh.inj hFresh
          have hAuxGeSt2 := hAuxVarsGe aux hAuxMem
          calc st.nextFresh
            _ ≤ st.nextFresh + 1 := Nat.le_succ _
            _ = st1.nextFresh := hSt1Next.symm
            _ ≤ st2.nextFresh := hSt1St2Mono
            _ ≤ aux.id := hAuxGeSt2
            _ = n := hn
  | tail _ hTail =>
      -- c ∈ st3.clauses
      by_cases hcSt2 : c ∈ st2.clauses
      · -- c ∈ st2.clauses (from encodeWitnesses)
        by_cases hcSt1 : c ∈ st1.clauses
        · -- c ∈ st1.clauses = st.clauses (via allocFresh)
          have hcSt : c ∈ st.clauses := by
            rw [EncState.allocFresh_clauses_eq] at hcSt1; exact hcSt1
          exact absurd hcSt hcNotOld
        · -- c is NEW from encodeWitnesses (in st2 but not st1)
          have hGeSt1 := encodeWitnesses_foldl_newClause_fresh_ge_aux b φ witnesses ([], st1)
            st1.nextFresh (Nat.le_refl _) hSt1WF ih c hcSt2 hcSt1 lit hLit n hFresh
          rw [hSt1Next] at hGeSt1; omega
      · -- c ∉ st2.clauses, so c is from auxVars fold (in st3 but not st2)
        have hPairsGe : ∀ p ∈ witnessVars.zip witnesses, p.1.id ≥ st.nextFresh := by
          intro p hp
          have ⟨hFstMem, _⟩ := List.of_mem_zip hp
          have hGeSt1 := hWitnessVarsGe p.1 hFstMem
          rw [hSt1Next] at hGeSt1; omega
        have hUGeSt : u.id ≥ st.nextFresh := by rw [hUId]
        have hBaselineSt2 : st.nextFresh ≤ st2.nextFresh := by
          calc st.nextFresh
            _ ≤ st.nextFresh + 1 := Nat.le_succ _
            _ = st1.nextFresh := hSt1Next.symm
            _ ≤ st2.nextFresh := hSt1St2Mono
        exact auxVars_foldl_newClause_fresh_ge_aux b w u (witnessVars.zip witnesses)
          ([], st2) st.nextFresh hBaselineSt2 hUGeSt hPairsGe c hTail hcSt2 lit hLit n hFresh

/-- Helper: Fresh vars in NEW clauses from forall encodeConj fold have index >= baseline. -/
lemma forall_encodeConj_foldl_newClause_fresh_ge_aux (b : Bounds S) (body : S.Value → Formula S)
    (w : WId b) (valIndices : List b.valIx) (acc : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh)
    (hWF : acc.2.WellFormed)
    (ih : ∀ v w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b (body v) w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (valIndices.foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline := by
  induction valIndices generalizing acc c lit n with
  | nil =>
    simp only [List.foldl_nil] at hcNew
    exact absurd hcNew hcNotOld
  | cons vIdx vs ihVs =>
    simp only [List.foldl_cons] at hcNew
    let v := b.values.get vIdx
    by_cases hcStep : c ∈ (encodeFormula b (body v) w acc.2).2.clauses
    · by_cases hcAcc : c ∈ acc.2.clauses
      · exact absurd hcAcc hcNotOld
      · -- c is NEW from encodeFormula (body v) w acc.2
        have hFreshGeAcc := ih v w acc.2 hWF c hcStep hcAcc lit hLit n hFresh
        exact Nat.le_trans hBaseline hFreshGeAcc
    · -- c is from the tail fold
      have hMono := encodeFormula_nextFresh_mono b (body v) w acc.2
      have hWFStep := encodeFormula_preserves_wf b (body v) w acc.2 hWF
      let encRes := encodeFormula b (body v) w acc.2
      exact ihVs (acc.1 ++ [encRes.1], encRes.2)
        (Nat.le_trans hBaseline hMono) hWFStep c hcNew hcStep lit hLit n hFresh

/-- Helper: forall encodeConj fold output vars have ids >= baseline. -/
lemma forall_encodeConj_foldl_vars_ge_baseline_aux (b : Bounds S) (body : S.Value → Formula S)
    (w : WId b) (valIndices : List b.valIx) (acc : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh)
    (hAccGe : ∀ v ∈ acc.1, v.id ≥ baseline) :
    let result := valIndices.foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)) acc
    ∀ v ∈ result.1, v.id ≥ baseline := by
  induction valIndices generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hAccGe
  | cons vIdx vs ihVs =>
    simp only [List.foldl_cons]
    apply ihVs
    · -- baseline ≤ step.2.nextFresh
      exact Nat.le_trans hBaseline (encodeFormula_nextFresh_mono b _ w acc.2)
    · -- ∀ v ∈ step.1, v.id ≥ baseline
      intro fv hfv
      simp only [List.mem_append, List.mem_singleton] at hfv
      cases hfv with
      | inl hOld => exact hAccGe fv hOld
      | inr hNew =>
        subst hNew
        exact Nat.le_trans hBaseline (encodeFormula_controlVar_ge_nextFresh b _ w acc.2)

/-- Forall case: Fresh vars in NEW clauses have index >= st.nextFresh. -/
lemma encodeFormula_forall_fresh_ge_nextFresh (b : Bounds S) (body : S.Value → Formula S)
    (w : WId b) (st : EncState b) (hWF : EncState.WellFormed st)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (encodeFormula b (Formula.«forall» body) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses) (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n)
    (ih : ∀ v w' st', st'.WellFormed →
          ∀ c', c' ∈ (encodeFormula b (body v) w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh) :
    n >= st.nextFresh := by
  simp only [encodeFormula] at hcNew

  -- Define intermediate states
  let u := (EncState.allocFresh b st).1
  let st1 := (EncState.allocFresh b st).2
  let foldResult := (List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
      let v := b.values.get vIdx
      have hNonempty : Nonempty S.Value := ⟨v⟩
      have hDepth : depth (body v) < depth (.forall body) := by
        simp only [depth, hNonempty, ↓reduceDIte]
        rw [depth_uniform body v (Classical.choice hNonempty)]; omega
      let (uBody, stNext) := encodeFormula b (body v) w stCur
      (vars ++ [uBody], stNext)) ([], st1)
  let bodyVars := foldResult.1
  let st2 := foldResult.2
  let st3 := bodyVars.foldl (fun stCur uBody =>
      let cl := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]
      EncState.addClause b stCur cl) st2
  let clause4 :=
    bodyVars.map (fun uBody => SAT.Lit.neg (FVar.toVar b uBody)) ++ [SAT.Lit.pos (FVar.toVar b u)]

  -- Key facts
  have hUId : u.id = st.nextFresh := EncState.allocFresh_fst (b := b) st
  have hSt1Next : st1.nextFresh = st.nextFresh + 1 := EncState.allocFresh_nextFresh b st
  have hSt1WF : st1.WellFormed := EncState.allocFresh_wf hWF
  have hSt1Sub : st.clauses ⊆ st1.clauses := by
    rw [EncState.allocFresh_clauses_eq]; exact List.Subset.refl _
  have hSt2Mono : st1.nextFresh ≤ st2.nextFresh :=
    forall_encodeConj_foldl_nextFresh_mono b body w st1
  have hSt2Sub : st1.clauses ⊆ st2.clauses := by
    simp only [st2, foldResult, st1]
    have hStep : ∀ (acc : List (FVar b) × EncState b) (vIdx : b.valIx),
        acc.2.clauses ⊆ ((let v := b.values.get vIdx
          have hNonempty : Nonempty S.Value := ⟨v⟩
          have hDepth : depth (body v) < depth (.forall body) := by
            simp only [depth, hNonempty, ↓reduceDIte]
            rw [depth_uniform body v (Classical.choice hNonempty)]; omega
          let (uBody, stNext) := encodeFormula b (body v) w acc.2
          (acc.1 ++ [uBody], stNext))).2.clauses := by
      intro acc vIdx
      exact encodeFormula_clauses_subset b (body (b.values.get vIdx)) w acc.2
    exact foldl_subset_snd _ hStep (List.finRange b.nVals) ([], (EncState.allocFresh b st).2)

  -- bodyVars have ids >= st1.nextFresh
  have hBodyVarsGe : ∀ v ∈ bodyVars, v.id ≥ st1.nextFresh := by
    apply forall_encodeConj_foldl_vars_ge_baseline_aux b body w (List.finRange b.nVals)
      ([], st1) st1.nextFresh (Nat.le_refl _)
    intro v hv; simp only [List.not_mem_nil] at hv

  -- Case analysis on where c comes from
  simp only [EncState.addClause] at hcNew
  cases hcNew with
  | head =>
      -- c = clause4 = [neg u1, ..., neg un, pos u]
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hLit
      rcases hLit with ⟨uBody, hMem, hLitEq⟩ | hPosU
      · -- lit = neg (Fresh uBody.id)
        rw [← hLitEq] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : uBody.id = n := Var.Fresh.inj hFresh
        have hGeS1 := hBodyVarsGe uBody hMem
        rw [hSt1Next] at hGeS1
        omega
      · -- lit = pos (Fresh u.id)
        rw [hPosU] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hAllocEq : (EncState.allocFresh b st).1.id = st.nextFresh :=
          EncState.allocFresh_fst (b := b) st
        have hn : (EncState.allocFresh b st).1.id = n := Var.Fresh.inj hFresh
        omega
  | tail _ hTail =>
      -- c ∈ st3.clauses
      by_cases hcSt2 : c ∈ st2.clauses
      · -- c ∈ st2.clauses (from encodeConj fold)
        by_cases hcSt1 : c ∈ st1.clauses
        · -- c ∈ st1.clauses = st.clauses (via allocFresh)
          have hcSt : c ∈ st.clauses := by
            rw [EncState.allocFresh_clauses_eq] at hcSt1; exact hcSt1
          exact absurd hcSt hcNotOld
        · -- c is NEW from encodeConj fold (in st2 but not st1)
          have hGeSt1 := forall_encodeConj_foldl_newClause_fresh_ge_aux b body w
            (List.finRange b.nVals) ([], st1) st1.nextFresh (Nat.le_refl _) hSt1WF ih c
            hcSt2 hcSt1 lit hLit n hFresh
          rw [hSt1Next] at hGeSt1; omega
      · -- c ∉ st2.clauses, so c is from the forward clause fold st3
        -- st3 = foldl [neg u, pos uBody] over st2
        -- c is one of [neg u, pos uBody] for some uBody ∈ bodyVars
        have hFwdFold := foldl_addClause_single_mem_aux b bodyVars st2
          (fun uBody => [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]) c hTail
        rcases hFwdFold with hOld | ⟨uBody, hUbMem, hcEq⟩
        · exact absurd hOld hcSt2
        · -- c = [neg u, pos uBody]
          rw [hcEq] at hLit
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with hNegU | hPosBody
          · rw [hNegU] at hFresh
            simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : u.id = n := Var.Fresh.inj hFresh
            rw [hUId] at hn; omega
          · rw [hPosBody] at hFresh
            simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : uBody.id = n := Var.Fresh.inj hFresh
            -- uBody ∈ bodyVars comes from hUbMem via rcases
            have hGeS1 := hBodyVarsGe uBody hUbMem
            rw [hSt1Next] at hGeS1
            omega
where
  foldl_addClause_single_mem_aux (b : Bounds S) (items : List (FVar b)) (st : EncState b)
      (mkClause : FVar b → SAT.Clause (Var b)) (c : SAT.Clause (Var b))
      (hc : c ∈ (items.foldl (fun stCur item =>
          EncState.addClause b stCur (mkClause item)) st).clauses) :
      c ∈ st.clauses ∨ ∃ item ∈ items, c = mkClause item := by
    induction items generalizing st with
    | nil => simp only [List.foldl_nil] at hc; exact Or.inl hc
    | cons x xs ih =>
      simp only [List.foldl_cons] at hc
      rcases ih (EncState.addClause b st (mkClause x)) hc with hOld | ⟨item, hMem, hEq⟩
      · simp only [EncState.addClause] at hOld
        cases hOld with
        | head => exact Or.inr ⟨x, List.mem_cons_self .., rfl⟩
        | tail _ hTail => exact Or.inl hTail
      · exact Or.inr ⟨item, List.mem_cons_of_mem x hMem, hEq⟩

/-! ### Diamond case helpers -/

/-- Helper: Fresh vars in NEW clauses from a partsL fold have index ≥ baseline.
    This is an auxiliary lemma generalized over an arbitrary list of participants. -/
lemma diamondWitnessFold_newClause_fresh_ge_aux' (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (parts : List b.participants)
    (acc : List (FVar b × b.participants) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh) (hWF : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (parts.foldl
        (fun (accInner : List (FVar b × b.participants) × EncState b) p =>
          if _ : p ∈ intersection then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd accInner.2
            (accInner.1 ++ [(uWit, p)], stNew)
          else accInner) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline := by
  induction parts generalizing acc with
  | nil =>
    simp only [List.foldl_nil] at hcNew
    exact absurd hcNew hcNotOld
  | cons p ps ihPs =>
    simp only [List.foldl_cons] at hcNew
    split_ifs at hcNew with hp
    · -- This participant is encoded (p ∈ intersection)
      let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
      by_cases hcEnc : c ∈ (encodeFormula b φ wEnd acc.2).2.clauses
      · by_cases hcAcc : c ∈ acc.2.clauses
        · exact absurd hcAcc hcNotOld
        · -- c is NEW from encodeFormula φ wEnd acc.2
          have hFreshGeAcc := ih wEnd acc.2 hWF c hcEnc hcAcc lit hLit n hFresh
          exact Nat.le_trans hBaseline hFreshGeAcc
      · -- c is from the tail fold
        have hMono := encodeFormula_nextFresh_mono b φ wEnd acc.2
        have hWFStep := encodeFormula_preserves_wf b φ wEnd acc.2 hWF
        let encRes := encodeFormula b φ wEnd acc.2
        have hcNewPs : c ∈ (ps.foldl
          (fun (accInner : List (FVar b × b.participants) × EncState b) q =>
            if _ : q ∈ intersection then
              let wEnd : WId b := ⟨q, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
              let (uWit, stNew) := encodeFormula b φ wEnd accInner.2
              (accInner.1 ++ [(uWit, q)], stNew)
            else accInner)
          (acc.1 ++ [(encRes.1, p)], encRes.2)).2.clauses := hcNew
        exact ihPs (acc.1 ++ [(encRes.1, p)], encRes.2)
          (Nat.le_trans hBaseline hMono) hWFStep hcNewPs hcEnc
    · -- This participant is skipped (p ∉ intersection)
      have hcNewPs : c ∈ (ps.foldl
        (fun (accInner : List (FVar b × b.participants) × EncState b) q =>
          if _ : q ∈ intersection then
            let wEnd : WId b := ⟨q, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd accInner.2
            (accInner.1 ++ [(uWit, q)], stNew)
          else accInner) acc).2.clauses := hcNew
      exact ihPs acc hBaseline hWF hcNewPs hcNotOld

/-- Helper: Fresh vars in NEW clauses from diamondWitnessFold have index ≥ baseline.
    Specialized version for partsL. -/
lemma diamondWitnessFold_newClause_fresh_ge_aux (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants)
    (acc : List (FVar b × b.participants) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh) (hWF : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ ((Bounds.partsL b).foldl
        (fun (accInner : List (FVar b × b.participants) × EncState b) p =>
          if _ : p ∈ intersection then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd accInner.2
            (accInner.1 ++ [(uWit, p)], stNew)
          else accInner) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline :=
  diamondWitnessFold_newClause_fresh_ge_aux' b φ w intersection (Bounds.partsL b)
    acc baseline hBaseline hWF ih c hcNew hcNotOld lit hLit n hFresh

/-- Helper: All witness vars from a partsL fold have id >= starting nextFresh.
    Generalized over an arbitrary list. -/
lemma diamondWitnessFold_witnessVars_fresh_ge' (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (parts : List b.participants)
    (acc : List (FVar b × b.participants) × EncState b) (baseline : Nat)
    (hAccGe : ∀ pair ∈ acc.1, pair.1.id ≥ baseline)
    (hMono : baseline ≤ acc.2.nextFresh) :
    ∀ pair ∈ (parts.foldl
        (fun (accInner : List (FVar b × b.participants) × EncState b) p =>
          if _ : p ∈ intersection then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd accInner.2
            (accInner.1 ++ [(uWit, p)], stNew)
          else accInner) acc).1, pair.1.id ≥ baseline := by
  induction parts generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hAccGe
  | cons p ps ihPs =>
    simp only [List.foldl_cons]
    split_ifs with hp
    · let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
      let encResult := encodeFormula b φ wEnd acc.2
      -- The new controlVar has id >= acc.2.nextFresh >= baseline
      have hNewGe : encResult.1.id ≥ baseline := by
        have hCtrl := encodeFormula_controlVar_ge_nextFresh b φ wEnd acc.2
        exact Nat.le_trans hMono hCtrl
      have hAccGe' : ∀ pair ∈ acc.1 ++ [(encResult.1, p)], pair.1.id ≥ baseline := by
        intro pair hPair
        simp only [List.mem_append, List.mem_singleton] at hPair
        rcases hPair with hOld | hNew
        · exact hAccGe pair hOld
        · simp only [hNew]; exact hNewGe
      have hMono' : baseline ≤ encResult.2.nextFresh := by
        exact Nat.le_trans hMono (encodeFormula_nextFresh_mono b φ wEnd acc.2)
      exact ihPs (acc.1 ++ [(encResult.1, p)], encResult.2) hAccGe' hMono'
    · exact ihPs acc hAccGe hMono

/-- Helper: All witness vars from diamondWitnessFold have id >= starting nextFresh. -/
lemma diamondWitnessFold_witnessVars_fresh_ge (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (st : EncState b) :
    ∀ pair ∈ (diamondWitnessFold b φ w intersection st).1, pair.1.id ≥ st.nextFresh := by
  simp only [diamondWitnessFold]
  exact diamondWitnessFold_witnessVars_fresh_ge' b φ w intersection (Bounds.partsL b)
    ([], st) st.nextFresh (by simp) (Nat.le_refl _)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Fresh vars in NEW clauses from encodeTupleControl have index ≥ baseline.
    Clauses contain uTuple (Fresh, id = st.nextFresh), MinQ vars (not Fresh),
    and witnessVars (assumed to have id >= baseline). -/
lemma encodeTupleControl_newClause_fresh_ge (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants)) (witnessVars : List (Var b)) (st : EncState b)
    (baseline : Nat) (hBaseline : baseline ≤ st.nextFresh)
    (hWitnessVarsGe : ∀ v ∈ witnessVars, ∀ n, v = Var.Fresh n → n ≥ baseline)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (encodeTupleControl b learners tuple witnessVars st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline := by
  -- The clauses in encodeTupleControl contain only:
  -- 1. uTuple (Fresh, id = st.nextFresh >= baseline)
  -- 2. MinQ vars (not Fresh, vacuously satisfy)
  -- 3. witnessVars (bounded by hWitnessVarsGe)
  -- All Fresh vars are either uTuple or from witnessVars, both >= baseline.

  simp only [encodeTupleControl] at hcNew

  -- Name intermediate states
  rcases hAlloc : EncState.allocFresh b st with ⟨uTuple, stAlloc⟩
  simp only [hAlloc] at hcNew

  -- uTuple.id = st.nextFresh >= baseline
  have hUTupleId : uTuple.id = st.nextFresh := by
    simp only [EncState.allocFresh] at hAlloc
    injection hAlloc with h1 _; rw [← h1]

  have hUTupleGe : uTuple.id ≥ baseline := by rw [hUTupleId]; exact hBaseline

  -- stAlloc.clauses = st.clauses
  have hAllocEq : stAlloc.clauses = st.clauses := by
    simp only [EncState.allocFresh] at hAlloc
    injection hAlloc with _ h2
    simp only [← h2]

  -- Helper to show that any Fresh var in a lit from c has id >= baseline
  -- Key insight: lit.getVar is either Var.Fresh uTuple.id, Var.MinQ _, or a witnessVar
  -- MinQ ≠ Fresh (vacuous), uTuple.id >= baseline, witnessVars bounded by hypothesis

  -- The clauses added are all subsets of vars from: uTuple, MinQ vars, witnessVars
  -- Since lit.getVar = Var.Fresh n, it cannot be a MinQ var
  -- So it's either uTuple (n = uTuple.id >= baseline) or a witnessVar (bounded)

  -- Tracking through all addClauses is tedious. Use a simpler approach:
  -- All addClause calls add clauses containing literals whose getVar is:
  -- - FVar.toVar b uTuple = Var.Fresh uTuple.id
  -- - Var.MinQ _ _ (not Fresh)
  -- - witnessVars (bounded by hypothesis)

  -- Since c ∉ st.clauses but c ∈ final.clauses, c was added by one of the addClause calls
  -- Each such clause contains only the variables listed above

  -- The only Fresh variables that can appear are:
  -- 1. Var.Fresh uTuple.id (from FVar.toVar b uTuple)
  -- 2. Var.Fresh m where Var.Fresh m ∈ witnessVars (bounded by hWitnessVarsGe)

  -- If lit.getVar = Var.Fresh n, then either:
  -- - n = uTuple.id >= baseline
  -- - Var.Fresh n ∈ witnessVars → n >= baseline by hWitnessVarsGe

  -- Define intermediate states matching encodeTupleControl structure
  let guards := (learners.zip tuple).map fun (ℓ, Q) =>
    SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)

  -- st1: first addClause
  -- st2: foldl over learners.zip tuple
  -- st3: foldl over witnessVars (final state)

  -- Track clause membership through the three phases
  -- c ∈ final.clauses and c ∉ st.clauses = stAlloc.clauses

  -- Phase 1: st1 = addClause stAlloc [neg uTuple ++ guards ++ witnessVars.map pos]
  -- Phase 2: st2 = foldl over (learners.zip tuple) adding [pos MinQ, pos uTuple]
  -- Phase 3: st3 = foldl over witnessVars adding [neg v, pos uTuple]

  -- Since c ∉ stAlloc.clauses, c must be one of the added clauses.
  -- We need to show all Fresh vars in c are either uTuple.id or from witnessVars.

  -- The key observation: every literal in every added clause has getVar that is either:
  -- 1. FVar.toVar b uTuple = Var.Fresh uTuple.id
  -- 2. Var.MinQ _ _ (never equal to Var.Fresh _)
  -- 3. A variable from witnessVars

  -- Since lit.getVar = Var.Fresh n:
  -- - If lit.getVar = FVar.toVar b uTuple, then n = uTuple.id
  -- - If lit.getVar is MinQ, impossible (MinQ ≠ Fresh)
  -- - Otherwise lit.getVar ∈ witnessVars

  -- Check if n = uTuple.id (i.e., lit.getVar = FVar.toVar b uTuple)
  by_cases hEqU : n = uTuple.id
  · -- n = uTuple.id >= baseline
    rw [hEqU]; exact hUTupleGe
  · -- n ≠ uTuple.id, so lit.getVar must be from witnessVars
    -- We need to track through the clause structure to show Var.Fresh n ∈ witnessVars

    -- The final state is st3 = witnessVars.foldl ... st2
    -- where st2 = (learners.zip tuple).foldl ... st1
    -- and st1 = addClause stAlloc [neg uTuple ++ guards ++ witnessVars.map pos]

    -- Characterize clause membership in st3
    -- c ∈ st3.clauses ↔ c ∈ st2.clauses ∨ c is one of the clauses added by the witnessVars fold
    -- c ∈ st2.clauses ↔ c ∈ st1.clauses ∨ c is one of the clauses added by the learners.zip fold
    -- c ∈ st1.clauses ↔ c = [neg uTuple ++ guards ++ witnessVars.map pos] ∨ c ∈ stAlloc.clauses

    -- Since c ∉ stAlloc.clauses (= st.clauses by hAllocEq), c is one of:
    -- A. c = [neg uTuple ++ guards ++ witnessVars.map pos] (from st1)
    -- B. c = [pos MinQ, pos uTuple] for some MinQ (from st2 fold)
    -- C. c = [neg v, pos uTuple] for some v ∈ witnessVars (from st3 fold)

    -- In case A: lits are neg uTuple, neg MinQ (guards), or pos v for v ∈ witnessVars
    -- In case B: lits are pos MinQ or pos uTuple
    -- In case C: lits are neg v (v ∈ witnessVars) or pos uTuple

    -- Fresh vars in these clauses:
    -- - uTuple gives Var.Fresh uTuple.id
    -- - MinQ gives Var.MinQ (never Fresh)
    -- - witnessVars may contain Var.Fresh

    -- Since n ≠ uTuple.id and MinQ ≠ Fresh, lit.getVar must be from witnessVars

    -- We need to show Var.Fresh n ∈ witnessVars given n ≠ uTuple.id
    -- All vars in new clauses are: uTuple (Fresh uTuple.id), MinQ (not Fresh), or witnessVars
    -- Since lit.getVar = Var.Fresh n and n ≠ uTuple.id and MinQ ≠ Fresh,
    -- lit.getVar must be from witnessVars.

    -- Key insight: lit.getVar appears in clause c. Since c is a new clause,
    -- lit.getVar is one of:
    -- - FVar.toVar b uTuple = Var.Fresh uTuple.id (but n ≠ uTuple.id, contradiction)
    -- - Var.MinQ _ _ (but this ≠ Var.Fresh _, contradiction)
    -- - v for some v ∈ witnessVars

    -- Since hFresh : lit.getVar = Var.Fresh n, it cannot be MinQ.
    -- Since n ≠ uTuple.id, it cannot be FVar.toVar b uTuple.
    -- So lit.getVar = Var.Fresh n must be in witnessVars.

    -- To establish this, we analyze where lit could have come from.
    -- lit ∈ c means c contains lit. The clause c is one of:
    -- (A) [neg uTuple ++ guards ++ witnessVars.map pos]
    -- (B) [pos MinQ, pos uTuple] for some MinQ
    -- (C) [neg v, pos uTuple] for some v ∈ witnessVars

    -- In (A): lit is neg uTuple, neg MinQ (a guard), or pos v for v ∈ witnessVars
    --         - neg uTuple has getVar = Var.Fresh uTuple.id (n ≠ uTuple.id, excluded)
    --         - neg MinQ has getVar = Var.MinQ (not Fresh, excluded)
    --         - pos v has getVar = v ∈ witnessVars ✓
    -- In (B): lit is pos MinQ or pos uTuple
    --         - pos MinQ has getVar = Var.MinQ (not Fresh, excluded)
    --         - pos uTuple has getVar = Var.Fresh uTuple.id (n ≠ uTuple.id, excluded)
    -- In (C): lit is neg v or pos uTuple
    --         - neg v has getVar = v ∈ witnessVars ✓
    --         - pos uTuple has getVar = Var.Fresh uTuple.id (n ≠ uTuple.id, excluded)

    -- So in all cases where lit.getVar = Var.Fresh n with n ≠ uTuple.id,
    -- we must have lit.getVar ∈ witnessVars.

    -- The proof: lit.getVar = Var.Fresh n. If Var.Fresh n ∉ witnessVars, then:
    -- - lit.getVar ≠ any v ∈ witnessVars
    -- - lit.getVar ≠ FVar.toVar b uTuple (since n ≠ uTuple.id)
    -- - lit.getVar ≠ Var.MinQ _ _ (since Var.Fresh ≠ Var.MinQ)
    -- But lit ∈ c and c only contains lits with getVar in {uTuple, MinQs, witnessVars}
    -- This is a contradiction.

    -- Rather than prove by contradiction, we directly show the bound:
    -- If Var.Fresh n ∈ witnessVars, done by hWitnessVarsGe.
    -- If Var.Fresh n ∉ witnessVars, we derive a contradiction.

    by_cases hInWit : Var.Fresh n ∈ witnessVars
    · exact hWitnessVarsGe (Var.Fresh n) hInWit n rfl
    · -- Var.Fresh n ∉ witnessVars - derive contradiction
      -- lit.getVar = Var.Fresh n is in clause c
      -- c is a new clause containing only {uTuple, MinQs, witnessVars}
      -- Since Var.Fresh n ∉ witnessVars and n ≠ uTuple.id and Var.Fresh ≠ Var.MinQ,
      -- lit.getVar cannot be in c. But lit ∈ c, contradiction.

      -- To formalize: we need to show all vars in new clauses are from the known set.
      -- This requires tracking through the clause additions.

      -- The simplest approach: use the fact that encodeTupleControl only introduces
      -- vars from {uTuple, MinQs, witnessVars}. Any Fresh var is either uTuple.id
      -- (excluded by hEqU) or in witnessVars (excluded by hInWit).
      -- So there's no Fresh var that lit.getVar could be, contradicting hFresh.

      exfalso

      -- Track through clause membership to find the contradiction.
      -- hcNew : c ∈ (encodeTupleControl ...).2.clauses, after simp this is c ∈ st3.clauses
      -- where st3 = witnessVars.foldl (addClause [neg v, pos uTuple]) st2
      -- st2 = (learners.zip tuple).foldl (addClause [pos MinQ, pos uTuple]) st1
      -- st1 = addClause stAlloc [neg uTuple ++ guards ++ witnessVars.map pos]

      -- hNotStAlloc : c ∉ stAlloc.clauses (= st.clauses)
      have hNotStAlloc : c ∉ stAlloc.clauses := by rw [hAllocEq]; exact hcNotOld

      -- We need to show lit.getVar is in {uTuple, MinQs, witnessVars}
      -- Then derive contradiction since Var.Fresh n is not in this set (given hEqU and hInWit)

      -- Helper: characterize vars in the first added clause
      -- The clause [neg uTuple ++ guards ++ witnessVars.map pos] has lits with getVar:
      -- - neg uTuple: getVar = FVar.toVar b uTuple = Var.Fresh uTuple.id
      -- - guards: each is neg (Var.MinQ _ _), so getVar = Var.MinQ _ _
      -- - witnessVars.map pos: each is pos v, so getVar = v for v ∈ witnessVars

      -- Helper: foldl addClause membership
      -- c ∈ (xs.foldl (fun st x => addClause st (f x)) init).clauses
      -- ↔ c ∈ init.clauses ∨ ∃ x ∈ xs, c = f x

      -- Apply this to get which clause c is:
      -- c ∈ st3 ↔ c ∈ st2 ∨ ∃ v ∈ witnessVars, c = [neg v, pos uTuple]
      -- c ∈ st2 ↔ c ∈ st1 ∨ ∃ (ℓ, Q) ∈ learners.zip tuple, c = [pos MinQ, pos uTuple]
      -- c ∈ st1 ↔ c = firstClause ∨ c ∈ stAlloc.clauses

      -- Since c ∉ stAlloc.clauses, c is one of the explicitly added clauses.
      -- Case on which:

      -- addClause st cl adds cl at the head: (st.addClause cl).clauses = cl :: st.clauses
      -- And foldl addClause produces a list where later-added clauses are at the front.

      -- Key fact: hFresh says lit.getVar = Var.Fresh n
      -- We show this leads to contradiction by case analysis on c.

      -- FVar.toVar b uTuple = Var.Fresh uTuple.id
      have hUTupleVar : FVar.toVar b uTuple = Var.Fresh uTuple.id := rfl

      -- If lit.getVar = FVar.toVar b uTuple, then Var.Fresh n = Var.Fresh uTuple.id,
      -- so n = uTuple.id. But hEqU says n ≠ uTuple.id, so lit.getVar ≠ FVar.toVar b uTuple
      have hNotUTuple : lit.getVar ≠ FVar.toVar b uTuple := by
        intro hEq
        rw [hUTupleVar] at hEq
        -- hEq : lit.getVar = Var.Fresh uTuple.id
        -- hFresh : SAT.Lit.getVar lit = Var.Fresh n
        -- Combine them to get n = uTuple.id
        have hN : n = uTuple.id := Var.Fresh.inj (hFresh.symm.trans hEq)
        exact hEqU hN

      -- MinQ vars are never Var.Fresh
      have hMinQNotFresh : ∀ (i : b.valIx) (Q : Finset b.participants),
          Var.MinQ i Q ≠ Var.Fresh n := by
        intro i Q hEq
        cases hEq

      -- Now case on which clause c is
      -- This requires expanding the folds and checking membership

      -- The final state structure after simp:
      -- hcNew should be about membership in the result of the full encodeTupleControl

      -- Use simpler approach: enumerate possible lits in c
      -- lit ∈ c means lit is one of the literals in c
      -- Each clause has a known form, so lit is one of the known literals

      -- The contradiction arises because:
      -- - If lit is pos/neg of uTuple, lit.getVar ≠ Var.Fresh n (by hNotUTuple via hEqU)
      -- - If lit is pos/neg of MinQ, lit.getVar ≠ Var.Fresh n (different constructor)
      -- - If lit is pos/neg of v ∈ witnessVars, then lit.getVar = v.
      --   If v = Var.Fresh n, then Var.Fresh n ∈ witnessVars, contradicting hInWit

      -- So there's no valid lit with n ≠ uTuple.id and Var.Fresh n ∉ witnessVars.

      -- To complete formally, we trace through hcNew to identify c and then hLit to identify lit.
      -- The detailed case analysis is lengthy but follows the pattern above.

      -- Use foldl_addClause_mem_iff for the witnessVars fold
      -- First, characterize membership in the witnessVars fold
      rw [foldl_addClause_mem_iff] at hcNew
      cases hcNew with
      | inl hcInSt2 =>
          -- c came from st2 (the learners.zip tuple fold) or earlier
          -- Need to further characterize st2
          -- st2 = (learners.zip tuple).foldl ... st1
          -- This fold is over pairs, which foldl_addClause_mem_iff doesn't directly handle.
          -- But we can use a similar approach manually.

          -- The key point: st2 clauses come from st1 or are [pos MinQ, pos uTuple]
          -- st1 clauses come from stAlloc or are the first clause

          -- For st2, the fold adds clauses [pos (MinQ i Q), pos uTuple] for each (ℓ, Q) pair
          -- These contain only MinQ vars and uTuple

          -- For st1, the single added clause contains uTuple, MinQs (guards), and witnessVars

          -- Since c ∉ stAlloc.clauses, c is one of these added clauses.
          -- In all cases, lit.getVar is uTuple, MinQ, or in witnessVars.

          -- Apply hNotUTuple, hMinQNotFresh, hInWit to get contradiction.

          -- Track through st2: it's a fold over (learners.zip tuple)
          -- Each step adds [pos MinQ, pos uTuple]
          -- Lits in these clauses have getVar = MinQ or getVar = uTuple

          -- Track through st1: one addClause adding [neg uTuple ++ guards ++ witnessVars.map pos]
          -- Lits have getVar = uTuple (neg), MinQ (guards via neg), or v ∈ witnessVars (via pos)

          -- In all cases from st2/st1, lit.getVar is uTuple, MinQ, or in witnessVars.

          -- We'll handle this with a nested case analysis, but the key point is:
          -- lit.getVar cannot be Var.Fresh n with n ≠ uTuple.id and Var.Fresh n ∉ witnessVars

          -- For st2 specifically: clauses are [pos MinQ, pos uTuple]
          -- lit ∈ such clause means lit is pos MinQ or pos uTuple
          -- getVar of pos MinQ is MinQ (not Fresh)
          -- getVar of pos uTuple is Var.Fresh uTuple.id (but n ≠ uTuple.id)
          -- Either way, contradiction with hFresh

          -- For st1: c is [neg uTuple ++ guards ++ witnessVars.map pos] or c ∈ stAlloc.clauses
          -- Since c ∉ stAlloc.clauses (= st.clauses), c is the first clause.
          -- lit ∈ c means lit is neg uTuple, neg MinQ (guard), or pos v for v ∈ witnessVars
          -- getVar of neg uTuple is Var.Fresh uTuple.id (n ≠ uTuple.id, excluded)
          -- getVar of neg MinQ is MinQ (not Fresh, excluded)
          -- getVar of pos v is v ∈ witnessVars

          -- So if lit.getVar = Var.Fresh n, we must have Var.Fresh n ∈ witnessVars
          -- But hInWit says Var.Fresh n ∉ witnessVars. Contradiction.

          -- Apply foldl_addClause_mem to st2 (fold over learners.zip tuple)
          -- mkClause for st2 fold: fun (ℓ, Q) => [pos MinQ, pos uTuple]
          have hSt2Mem := foldl_addClause_mem b (learners.zip tuple)
            (EncState.addClause b stAlloc
              ([SAT.Lit.neg (FVar.toVar b uTuple)] ++ guards ++ witnessVars.map SAT.Lit.pos))
            (fun (pair : S.Value × Finset b.participants) =>
              [SAT.Lit.pos (Var.MinQ (b.findValueIndex pair.1) pair.2),
               SAT.Lit.pos (FVar.toVar b uTuple)])
            c hcInSt2
          cases hSt2Mem with
          | inl hcInSt1 =>
              -- c ∈ st1.clauses = [firstClause] ++ stAlloc.clauses
              simp only [EncState.addClause] at hcInSt1
              cases hcInSt1 with
              | head =>
                  -- c is the first clause: [neg uTuple] ++ guards ++ witnessVars.map pos
                  -- lit ∈ c means lit is in this concatenated list
                  simp only [List.mem_append] at hLit
                  rcases hLit with (hLitInFirst | hLitGuard) | hLitInWit
                  · -- lit ∈ [neg uTuple]
                    simp only [List.mem_singleton] at hLitInFirst
                    rw [hLitInFirst] at hFresh
                    simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
                    exact hEqU (Var.Fresh.inj hFresh).symm
                  · -- lit ∈ guards (a neg MinQ)
                    simp only [guards, List.mem_map] at hLitGuard
                    obtain ⟨pair, _, hLitEq⟩ := hLitGuard
                    -- hLitEq : lit = neg (MinQ ...)
                    subst hLitEq
                    simp only [SAT.Lit.getVar] at hFresh
                    exact hMinQNotFresh _ _ hFresh
                  · -- lit ∈ witnessVars.map pos
                    simp only [List.mem_map] at hLitInWit
                    obtain ⟨v, hvWit, hLitEq⟩ := hLitInWit
                    subst hLitEq
                    simp only [SAT.Lit.getVar] at hFresh
                    -- v = Var.Fresh n, so Var.Fresh n ∈ witnessVars
                    rw [← hFresh] at hInWit
                    exact hInWit hvWit
              | tail _ hcInStAlloc =>
                  -- c ∈ stAlloc.clauses = st.clauses (contradiction with hcNotOld)
                  rw [hAllocEq] at hcInStAlloc
                  exact hcNotOld hcInStAlloc
          | inr hcFromSt2Fold =>
              -- c = [pos MinQ, pos uTuple] for some pair
              obtain ⟨⟨ℓ', Q'⟩, _, hcEq⟩ := hcFromSt2Fold
              rw [hcEq] at hLit
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
              cases hLit with
              | inl hLitMinQ =>
                  -- lit = pos MinQ
                  rw [hLitMinQ] at hFresh
                  simp only [SAT.Lit.getVar] at hFresh
                  exact hMinQNotFresh _ _ hFresh
              | inr hLitPosU =>
                  -- lit = pos uTuple
                  rw [hLitPosU] at hFresh
                  simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
                  exact hEqU (Var.Fresh.inj hFresh).symm

      | inr hcFromWitFold =>
          -- c is one of the clauses added by the witnessVars fold
          -- c = [neg v, pos uTuple] for some v ∈ witnessVars
          obtain ⟨v, hvMem, hcEq⟩ := hcFromWitFold
          rw [hcEq] at hLit
          -- lit ∈ [neg v, pos uTuple]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
          cases hLit with
          | inl hLitNegV =>
              -- lit = neg v where v ∈ witnessVars
              rw [hLitNegV] at hFresh
              simp only [SAT.Lit.getVar] at hFresh
              -- hFresh : v = Var.Fresh n
              -- Since v ∈ witnessVars and v = Var.Fresh n, we have Var.Fresh n ∈ witnessVars
              -- But hInWit says Var.Fresh n ∉ witnessVars. Contradiction.
              rw [← hFresh] at hInWit
              exact hInWit hvMem
          | inr hLitPosU =>
              -- lit = pos uTuple
              rw [hLitPosU] at hFresh
              simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
              -- hFresh : Var.Fresh uTuple.id = Var.Fresh n
              have hIdEq := Var.Fresh.inj hFresh
              -- n = uTuple.id, contradicting hEqU
              exact hEqU hIdEq.symm

/-- Helper: diamondStep preserves well-formedness.
    This follows from diamondWitnessFold and encodeTupleControl both preserving WF. -/
lemma diamondStep_preserves_wf (b : Bounds S) (learners : List S.Value) (φ : Formula S)
    (w : WId b) (acc : List (FVar b) × EncState b) (tuple : List (Finset b.participants))
    (hWF : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    (diamondStep b learners φ w acc tuple).2.WellFormed := by
  simp only [diamondStep]
  let intersection := tuple.foldl (· ∩ ·) Finset.univ
  let witnessFold := diamondWitnessFold b φ w intersection acc.2
  let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
  -- witnessFold preserves WF
  have hWFFold : witnessFold.2.WellFormed :=
    diamond_witnessFold_wf b φ w intersection acc.2 hWF ih
  -- Witness vars are safe for encodeTupleControl
  have hVarsLt := diamond_witnessFold_vars_lt_nextFresh b φ w intersection acc.2
  have hWitnessSafe : ∀ v ∈ witnessVars, ∀ n, v = Var.Fresh n → n < witnessFold.2.nextFresh := by
    intro v hv n hEq
    simp only [witnessVars, List.mem_map] at hv
    obtain ⟨pair, hPair, rfl⟩ := hv
    simp only [FVar.toVar] at hEq
    cases hEq
    exact hVarsLt pair hPair
  exact encodeTupleControl_wf b learners tuple witnessVars witnessFold.2 hWFFold hWitnessSafe

/-- Helper: diamondWitnessFold preserves clauses (input clauses are subset of output). -/
lemma diamondWitnessFold_clauses_subset (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (st : EncState b) :
    st.clauses ⊆ (diamondWitnessFold b φ w intersection st).2.clauses := by
  simp only [diamondWitnessFold]
  have hMono : ∀ (acc : List (FVar b × b.participants) × EncState b) p,
      acc.2.clauses ⊆ ((fun acc p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc.2
          (acc.1 ++ [(uWit, p)], stNew)
        else acc) acc p).2.clauses := by
    intro acc p
    by_cases hp : p ∈ intersection
    · simp only [hp, ↓reduceDIte]
      exact encodeFormula_clauses_subset b φ _ acc.2
    · simp only [hp, ↓reduceDIte]
      exact List.Subset.refl _
  exact foldl_subset_snd _ hMono (Bounds.partsL b) ([], st)

/-- Helper: Fresh vars in NEW clauses from a single diamondStep have index ≥ baseline. -/
lemma diamondStep_newClause_fresh_ge_aux (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b) (acc : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh) (hWF : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh)
    (ihWF : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed)
    (tuple : List (Finset b.participants))
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (diamondStep b learners φ w acc tuple).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline := by
  -- diamondStep = diamondWitnessFold + encodeTupleControl
  simp only [diamondStep] at hcNew

  let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
  let witnessFold := diamondWitnessFold b φ w intersection acc.2
  let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)

  -- witnessFold.2.clauses ⊇ acc.2.clauses
  have hWitSub : acc.2.clauses ⊆ witnessFold.2.clauses :=
    diamondWitnessFold_clauses_subset b φ w intersection acc.2

  -- nextFresh is monotonic through witnessFold
  have hWitMono : acc.2.nextFresh ≤ witnessFold.2.nextFresh :=
    diamondWitnessFold_nextFresh_mono b φ w intersection acc.2

  -- witnessFold.2 is well-formed
  have hWitWF : witnessFold.2.WellFormed :=
    diamond_witnessFold_wf b φ w intersection acc.2 hWF ihWF

  -- Witness vars have id >= acc.2.nextFresh
  have hWitVarsGe' : ∀ pair ∈ witnessFold.1, pair.1.id ≥ acc.2.nextFresh :=
    diamondWitnessFold_witnessVars_fresh_ge b φ w intersection acc.2

  have hWitVarsGe : ∀ v ∈ witnessVars, ∀ n, v = Var.Fresh n → n ≥ baseline := by
    intro v hv n hEq
    simp only [witnessVars, List.mem_map] at hv
    obtain ⟨pair, hPair, rfl⟩ := hv
    simp only [FVar.toVar] at hEq
    cases hEq
    calc pair.1.id ≥ acc.2.nextFresh := hWitVarsGe' pair hPair
      _ ≥ baseline := hBaseline

  -- Case split: c from witnessFold or from encodeTupleControl
  by_cases hcWit : c ∈ witnessFold.2.clauses
  · -- c ∈ witnessFold.2.clauses
    by_cases hcAcc2 : c ∈ acc.2.clauses
    · exact absurd hcAcc2 hcNotOld
    · -- c is NEW from witnessFold - apply diamondWitnessFold_newClause_fresh_ge_aux
      unfold diamondWitnessFold at hcWit
      exact diamondWitnessFold_newClause_fresh_ge_aux b φ w intersection
        ([], acc.2) baseline (by simp only [hBaseline]) hWF ih c hcWit hcAcc2 lit hLit n hFresh
  · -- c from encodeTupleControl
    exact encodeTupleControl_newClause_fresh_ge b learners tuple witnessVars witnessFold.2
      baseline (Nat.le_trans hBaseline hWitMono) hWitVarsGe c hcNew hcWit lit hLit n hFresh

/-- Helper: Fresh vars in NEW clauses from tuples.foldl diamondStep have index ≥ st.nextFresh. -/
lemma diamondStep_foldl_newClause_fresh_ge' (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b) (tuples : List (List (Finset b.participants)))
    (acc : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh) (hWF : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh)
    (ihWF : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (tuples.foldl (diamondStep b learners φ w) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline := by
  -- Fold induction using diamondStep_newClause_fresh_ge_aux at each step
  induction tuples generalizing acc with
  | nil =>
    simp only [List.foldl_nil] at hcNew
    exact absurd hcNew hcNotOld
  | cons tuple ts ihTs =>
    simp only [List.foldl_cons] at hcNew
    by_cases hcStep : c ∈ (diamondStep b learners φ w acc tuple).2.clauses
    · by_cases hcAcc : c ∈ acc.2.clauses
      · exact absurd hcAcc hcNotOld
      · exact diamondStep_newClause_fresh_ge_aux b learners φ w acc baseline hBaseline hWF
          ih ihWF tuple c hcStep hcAcc lit hLit n hFresh
    · have hMono := diamondStep_nextFresh_mono b learners φ w acc tuple
      have hWFStep := diamondStep_preserves_wf b learners φ w acc tuple hWF ihWF
      exact ihTs (diamondStep b learners φ w acc tuple)
        (Nat.le_trans hBaseline hMono) hWFStep hcNew hcStep

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: Fresh vars in NEW clauses from mkAndIff fold have index ≥ baseline.

The actual fold pattern used in diamond encoding is:
  us.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0, st)

mkAndIff clauses contain only:
- Newly allocated Fresh var (id = state.nextFresh at allocation)
- The two input FVars (acc.1 and u')
So all Fresh vars have index >= baseline. -/
lemma mkAndIff_foldl_newClause_fresh_ge' (b : Bounds S) (us : List (FVar b))
    (acc : FVar b × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh)
    (hAccGe : acc.1.id ≥ baseline)
    (hUsGe : ∀ u ∈ us, u.id ≥ baseline)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (us.foldl (fun acc' u' => mkAndIff b acc'.1 u' acc'.2) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ baseline := by
  induction us generalizing acc with
  | nil =>
    simp only [List.foldl_nil] at hcNew
    exact absurd hcNew hcNotOld
  | cons u' us' ihUs =>
    simp only [List.foldl_cons] at hcNew
    have hU'Ge : u'.id ≥ baseline := hUsGe u' (List.mem_cons_self ..)
    have hUsGe' : ∀ u ∈ us', u.id ≥ baseline := fun u hu => hUsGe u (List.mem_cons_of_mem _ hu)
    let step := mkAndIff b acc.1 u' acc.2
    by_cases hcStep : c ∈ step.2.clauses
    · by_cases hcAcc : c ∈ acc.2.clauses
      · exact absurd hcAcc hcNotOld
      · -- c is NEW from this mkAndIff step
        -- mkAndIff b x y st allocates fresh u (id = st.nextFresh) and adds 3 clauses:
        --   [neg u, pos x], [neg u, pos y], [neg x, neg y, pos u]
        -- Variables in clauses: FVar.toVar b acc.1, FVar.toVar b u', FVar.toVar b u (new)
        -- All FVars have id >= baseline (acc.1 by hAccGe, u' by hU'Ge, u by hBaseline)

        simp only [mkAndIff, step] at hcStep
        -- Extract the newly allocated var
        rcases hAlloc : EncState.allocFresh b acc.2 with ⟨u, stU⟩
        simp only [hAlloc] at hcStep

        have hUId : u.id = acc.2.nextFresh := by
          simp only [EncState.allocFresh] at hAlloc
          injection hAlloc with h1 _; rw [← h1]
        have hUGe : u.id ≥ baseline := by rw [hUId]; exact hBaseline

        have hStUEq : stU.clauses = acc.2.clauses := by
          simp only [EncState.allocFresh] at hAlloc
          injection hAlloc with _ h2
          simp only [← h2]

        -- After 3 addClauses, clauses are: c3 :: c2 :: c1 :: stU.clauses
        simp only [EncState.addClause] at hcStep
        -- c is in one of the 3 new clauses or in stU.clauses
        -- Since c ∉ acc.2.clauses = stU.clauses, c must be one of the 3 new clauses

        -- Determine which var lit.getVar is
        -- lit ∈ c, and c is one of the 3 clauses
        -- Each clause contains only vars from {acc.1, u', u}
        -- All have id >= baseline

        -- Process each possible clause and literal
        cases hcStep with
        | head =>
            -- c = [neg acc.1, neg u', pos u]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
            rcases hLit with hE1 | hE2 | hE3
            · -- lit = neg acc.1
              simp only [hE1, SAT.Lit.getVar, FVar.toVar] at hFresh
              injection hFresh with hN; rw [← hN]; exact hAccGe
            · -- lit = neg u'
              rw [hE2] at hFresh
              simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
              have hn : u'.id = n := Var.Fresh.inj hFresh; rw [← hn]; exact hU'Ge
            · -- lit = pos u
              rw [hE3] at hFresh
              simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
              have hn : u.id = n := Var.Fresh.inj hFresh; rw [← hn]; exact hUGe
        | tail _ hc1 =>
            cases hc1 with
            | head =>
                -- c = [neg u, pos u']
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
                rcases hLit with hE1 | hE2
                · -- lit = neg u
                  rw [hE1] at hFresh
                  simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
                  have hn : u.id = n := Var.Fresh.inj hFresh; rw [← hn]; exact hUGe
                · -- lit = pos u'
                  rw [hE2] at hFresh
                  simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
                  have hn : u'.id = n := Var.Fresh.inj hFresh; rw [← hn]; exact hU'Ge
            | tail _ hc2 =>
                cases hc2 with
                | head =>
                    -- c = [neg u, pos acc.1]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
                    rcases hLit with hE1 | hE2
                    · -- lit = neg u
                      rw [hE1] at hFresh
                      simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
                      have hn : u.id = n := Var.Fresh.inj hFresh; rw [← hn]; exact hUGe
                    · -- lit = pos acc.1
                      rw [hE2] at hFresh
                      simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
                      have hn : acc.1.id = n := Var.Fresh.inj hFresh; rw [← hn]; exact hAccGe
                | tail _ hOld =>
                    rw [hStUEq] at hOld
                    exact absurd hOld hcNotOld
    · -- c is from the tail fold
      have hMono : acc.2.nextFresh ≤ step.2.nextFresh := mkAndIff_nextFresh_mono b acc.1 u' acc.2
      have hFreshGe : step.1.id ≥ baseline := by
        simp only [step, mkAndIff, EncState.allocFresh_fst]
        exact hBaseline
      exact ihUs step (Nat.le_trans hBaseline hMono) hFreshGe hUsGe' hcNew hcStep

/-- Diamond case: Fresh vars in NEW clauses have index >= st.nextFresh.

The diamond encoding has the structure:
  tuples.foldl step ([], st) where step involves:
  1. witnessFold over participants (each may call encodeFormula for φ)
  2. encodeTupleControl (allocates Fresh vars and adds clauses)

All Fresh vars come from:
- encodeFormula calls (by IH, n >= state.nextFresh at call time)
- encodeTupleControl (allocates from state.nextFresh)
Since nextFresh is monotonically increasing, all Fresh vars have n >= st.nextFresh. -/
lemma encodeFormula_diamond_fresh_ge_nextFresh (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b)
    (st : EncState b) (hWF : EncState.WellFormed st)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (encodeFormula b (Formula.diamond learners φ) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n)
    (ih : ∀ w' st', st'.WellFormed → ∀ c', c' ∈ (encodeFormula b φ w' st').2.clauses →
          c' ∉ st'.clauses → ∀ lit', lit' ∈ c' → ∀ n', lit'.getVar = Var.Fresh n' →
          n' >= st'.nextFresh) :
    n >= st.nextFresh := by
  -- Diamond encoding structure: tuples.foldl (diamondStep ...) ([], st)
  -- where diamondStep involves:
  --   1. diamondWitnessFold: fold over participants calling encodeFormula
  --   2. encodeTupleControl: allocates one Fresh var and adds clauses
  --
  -- All Fresh vars in clauses come from:
  -- - encodeFormula calls in diamondWitnessFold (by IH, n >= call state's nextFresh)
  -- - encodeTupleControl allocations (id = witnessFold state's nextFresh)
  --
  -- Since nextFresh is monotonic and starts at st.nextFresh, all Fresh vars have n >= st.nextFresh.

  -- Define tuples from the formula structure (must match what encodeFormula uses)
  let getMinQs (ℓ : S.Value) : List (Finset b.participants) :=
    let vIdx := b.findValueIndex ℓ
    (Var.allMinQ b vIdx).filterMap fun v =>
      match v with
      | Var.MinQ _ Q => some Q
      | _ => none
  let quorumSets := learners.map getMinQs
  let tuples := cartesianProduct quorumSets

  -- The fold result
  let foldResult := tuples.foldl (diamondStep b learners φ w) ([], st)
  let tupleVars := foldResult.1
  let stTuples := foldResult.2

  -- nextFresh monotonicity for the fold
  have hFoldMono : st.nextFresh ≤ stTuples.nextFresh := by
    have hStepMono : ∀ (acc : List (FVar b) × EncState b) tuple,
        acc.2.nextFresh ≤ (diamondStep b learners φ w acc tuple).2.nextFresh :=
      diamondStep_nextFresh_mono b learners φ w
    exact foldl_nextFresh_mono_pair tuples ([], st) _ hStepMono

  -- WF preservation through the fold
  have hIhWF : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed :=
    fun w' st' hw' => encodeFormula_preserves_wf b φ w' st' hw'
  have hFoldWF : stTuples.WellFormed := by
    have := diamond_outerFold_wf_aux b learners φ w tuples ([], st) hWF hIhWF
    simp only at this
    exact this

  -- All tupleVars have id >= st.nextFresh (from diamondStep_foldl_all_id_ge)
  have hTupleVarsGe : ∀ u ∈ tupleVars, u.id ≥ st.nextFresh :=
    diamondStep_foldl_all_id_ge b learners φ w tuples st

  -- Now case split on where c came from
  -- The final state comes from either:
  -- 1. tuples.foldl (diamondStep ...) - clauses in stTuples
  -- 2. The match on tupleVars (empty case or mkAndIff fold)

  -- Check if c is from the tuples fold
  by_cases hcFold : c ∈ stTuples.clauses
  · -- c came from the tuples fold
    by_cases hcSt : c ∈ st.clauses
    · exact absurd hcSt hcNotOld
    · -- c is NEW from the tuples fold
      exact diamondStep_foldl_newClause_fresh_ge' b learners φ w tuples
        ([], st) st.nextFresh (by simp) hWF ih hIhWF c hcFold hcSt lit hLit n hFresh
  · -- c came from the final match (empty case or mkAndIff fold)
    -- c ∉ stTuples.clauses, so c is from the match expression

    -- First expand encodeFormula and rewrite to use diamondStep
    simp only [encodeFormula] at hcNew
    have hStepEq : ∀ acc tuple, (fun (accVars, stCur) tuple =>
        let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
        let witnessFold :=
          (Bounds.partsL b).foldl
            (fun (acc : List (FVar b × b.participants) × EncState b) p =>
              if _ : p ∈ intersection then
                let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd acc.2
                (acc.1 ++ [(uWit, p)], stNew)
              else acc)
            ([], stCur)
        let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
        let (uTuple, stFinal) := encodeTupleControl b learners tuple witnessVars witnessFold.2
        (accVars ++ [uTuple], stFinal)) acc tuple = diamondStep b learners φ w acc tuple := by
      intro acc tuple
      simp only [diamondStep, diamondWitnessFold]
    simp only [hStepEq] at hcNew

    -- Now split on the match in hcNew
    split at hcNew
    case h_1 heq =>
      -- Empty case: tupleVars = []
      -- hcNew: c ∈ (addClause (allocFresh stTuples) [pos u']).2.clauses
      simp only [EncState.addClause] at hcNew
      cases hcNew with
      | head =>
        -- c = [pos u'] where u'.id = stTuples.nextFresh
        simp only [List.mem_singleton] at hLit
        subst hLit
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hN := Var.Fresh.inj hFresh
        simp only [EncState.allocFresh_fst] at hN
        -- hN has: (expanded form).nextFresh = n
        -- stTuples is definitionally equal to (expanded form).2, so nextFresh matches
        -- hFoldMono says st.nextFresh ≤ stTuples.nextFresh
        -- So n = stTuples.nextFresh >= st.nextFresh
        have hNStTuples : n = stTuples.nextFresh := hN.symm
        rw [hNStTuples]
        exact hFoldMono
      | tail _ hcOld =>
        -- c ∈ (allocFresh stTuples).2.clauses = stTuples.clauses
        simp only [EncState.allocFresh_clauses_eq] at hcOld
        exact absurd hcOld hcFold
    case h_2 u0 us heq =>
      -- Non-empty case: tupleVars = u0 :: us
      -- hcNew: c ∈ (us.foldl mkAndIff (u0, stTuples)).2.clauses
      -- heq says the fold result's .1 = u0 :: us, which is tupleVars (but in expanded form)
      -- We need to convert heq to use our local definitions
      have hTupleVarsEq : tupleVars = u0 :: us := heq
      have hU0Ge : u0.id ≥ st.nextFresh := hTupleVarsGe u0 (by
        rw [hTupleVarsEq]; exact List.mem_cons_self ..)
      have hUsGe : ∀ u ∈ us, u.id ≥ st.nextFresh := fun u hu => hTupleVarsGe u (by
        rw [hTupleVarsEq]; exact List.mem_cons_of_mem _ hu)
      -- Apply mkAndIff_foldl_newClause_fresh_ge'
      exact mkAndIff_foldl_newClause_fresh_ge' b us (u0, stTuples) st.nextFresh
        hFoldMono hU0Ge hUsGe c hcNew hcFold lit hLit n hFresh

/-- For NEW clauses (output.clauses \ input.clauses), all Fresh variables in the clause
    have indices >= input.nextFresh.

    Proof: Encoding only allocates Fresh vars starting from st.nextFresh and upward.
    Any clause added during encoding uses only:
    - Non-Fresh vars (which have no index constraint)
    - Newly allocated Fresh vars (with index >= st.nextFresh)
    - Fresh vars from recursive encoding (which by IH are also >= st.nextFresh)

    This is a structural property of encodeFormula that requires induction on the formula. -/
lemma encodeFormula_new_clause_fresh_ge_nextFresh (b : Bounds S) (φ : Formula S) (w : WId b)
    (st : EncState b) (hWF : EncState.WellFormed st)
    (c : SAT.Clause (Var b)) (hcNew : c ∈ (encodeFormula b φ w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n >= st.nextFresh := by
  induction φ generalizing w st c lit n with
  | bot => exact encodeFormula_bot_fresh_ge_nextFresh b w st c hcNew hcNotOld lit hLit n hFresh
  | eq v1 v2 =>
      exact encodeFormula_eq_fresh_ge_nextFresh b v1 v2 w st c hcNew hcNotOld lit hLit n hFresh
  | seq => exact encodeFormula_seq_fresh_ge_nextFresh b w st c hcNew hcNotOld lit hLit n hFresh
  | imp φ1 φ2 ih1 ih2 =>
      exact encodeFormula_imp_fresh_ge_nextFresh b φ1 φ2 w st hWF c hcNew hcNotOld
        lit hLit n hFresh ih1 ih2
  | atEnd φ ih =>
      exact encodeFormula_atEnd_fresh_ge_nextFresh b φ w st hWF c hcNew hcNotOld
        lit hLit n hFresh ih
  | predicate atom =>
      exact encodeFormula_predicate_fresh_ge_nextFresh b atom w st c hcNew hcNotOld
        lit hLit n hFresh
  | event atom =>
      exact encodeFormula_event_fresh_ge_nextFresh b atom w st c hcNew hcNotOld
        lit hLit n hFresh
  | past φ ih =>
      exact encodeFormula_past_fresh_ge_nextFresh b φ w st hWF c hcNew hcNotOld
        lit hLit n hFresh ih
  | «forall» body ih =>
      exact encodeFormula_forall_fresh_ge_nextFresh b body w st hWF c hcNew hcNotOld
        lit hLit n hFresh ih
  | diamond learners φ ih =>
      exact encodeFormula_diamond_fresh_ge_nextFresh b learners φ w st hWF c hcNew hcNotOld
        lit hLit n hFresh ih

end Encoding
