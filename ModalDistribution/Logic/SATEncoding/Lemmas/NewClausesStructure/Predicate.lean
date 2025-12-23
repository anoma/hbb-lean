import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Common
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.ShiftedAssignment

/-!
# Predicate Case: Structural Determinism for New Clauses
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- Predicate case: NEW clauses are mkBigOrIff clauses plus PreEq and transfer guard clauses -/
lemma structural_determinism_new_clauses_predicate (b : Bounds S) (atom : PredicateAtom S) (w : WId b)
    (st st' : EncState b) (offset : Nat) (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st)
    (hNonFreshCompat : nonFreshClausesCompat st st')
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (encodeFormula b (Formula.predicate atom) w st).2.clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true) :
    let σ' := shiftedAssignment b σ st'.nextFresh offset
    ∀ c ∈ (encodeFormula b (Formula.predicate atom) w st').2.clauses, c ∉ st'.clauses →
      SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  simp only [encodeFormula] at hc hSatNew

  -- Define the intermediate encoding structure
  let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
  let idxs := predIxList b pred
  let literals := idxs.map (fun k => Var.Pred w.p w.ti k)

  -- mkBigOrIff is applied at both st and st'
  let ⟨u, st1⟩ := mkBigOrIff b literals st
  let ⟨u', st1'⟩ := mkBigOrIff b literals st'

  -- Case split on whether idxs is empty (using split since the if has a proof)
  split at hc
  · -- Empty case for hc: only mkBigOrIff clauses
    rename_i hEmpty
    split at hSatNew
    · -- Both are in empty case
      -- c is from mkBigOrIff at st', which is NEW (c ∉ st'.clauses)
      -- The corresponding clause at st is in mkBigOrIff at st
      -- Since the only difference is Fresh var index, and all Fresh vars in mkBigOrIff
      -- are at the st/st' nextFresh position, we can directly map:
      -- - Pred vars are unchanged (σ' = σ for non-Fresh)
      -- - The Fresh var at st'.nextFresh maps to st.nextFresh via unshift

      -- c is NEW from mkBigOrIff at st'
      -- Use mkBigOrIff_clause_mem_iff to characterize c
      have hMem := (mkBigOrIff_clause_mem_iff b literals st' c).mp hc
      -- hMem : c ∈ st'.clauses ∨ (∃ v ∈ literals, short clause) ∨ (backward clause)
      rcases hMem with hcSt' | ⟨v, hv, hFwd⟩ | hBack
      · -- c ∈ st'.clauses - contradiction
        exact absurd hcSt' hcNew
      · -- c is a short clause [¬v, u'] where v ∈ literals
        -- The corresponding clause at st is [¬v, u] where u = Fresh st.nextFresh
        have hU' : (mkBigOrIff b literals st').1 = ⟨st'.nextFresh⟩ := by
          simp only [mkBigOrIff, EncState.allocFresh]
        have hU : (mkBigOrIff b literals st).1 = ⟨st.nextFresh⟩ := by
          simp only [mkBigOrIff, EncState.allocFresh]
        -- c = [¬v, u']
        rw [hFwd]
        simp only [hU', FVar.toVar]
        -- The corresponding clause at st is [¬v, u]
        have hCStMem : [SAT.Lit.neg v, SAT.Lit.pos (Var.Fresh st.nextFresh)] ∈
            (mkBigOrIff b literals st).2.clauses := by
          rw [mkBigOrIff_clause_mem_iff]
          right; left
          refine ⟨v, hv, ?_⟩
          simp only [hU, FVar.toVar]
        have hCStNew : [SAT.Lit.neg v, SAT.Lit.pos (Var.Fresh st.nextFresh)] ∉ st.clauses := by
          intro hIn
          have hWFClause := hWF _ hIn
          unfold clauseFreshBelow at hWFClause
          have hLit : SAT.Lit.pos (Var.Fresh (b := b) st.nextFresh) ∈
              [SAT.Lit.neg v, SAT.Lit.pos (Var.Fresh (b := b) st.nextFresh)] := by
            simp
          have hBound := hWFClause _ hLit
          simp only [litFreshBelow] at hBound
          exact Nat.lt_irrefl _ hBound
        have hSatCSt := hSatNew _ hCStMem hCStNew
        -- Now show σ' satisfies [¬v, u']
        simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false, SAT.Lit.eval]
        simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false,
                   SAT.Lit.eval] at hSatCSt
        -- σ'(v) = σ(v) for non-Fresh v (literals are Pred vars)
        have hVPred : ∃ p ti k, v = Var.Pred p ti k := by
          simp only [literals, List.mem_map] at hv
          obtain ⟨k, _, rfl⟩ := hv
          exact ⟨w.p, w.ti, k, rfl⟩
        obtain ⟨p, ti, k, hvEq⟩ := hVPred
        subst hvEq
        simp only [σ', shiftedAssignment]
        -- σ'(Fresh st'.nextFresh) = σ(Fresh (st'.nextFresh - offset))
        --                        = σ(Fresh st.nextFresh) since offset = st'.nextFresh - st.nextFresh
        have hUnshift : st'.nextFresh - offset = st.nextFresh := by
          rw [hOffset]; omega
        have hNotLt : ¬(st'.nextFresh < st'.nextFresh) := Nat.lt_irrefl _
        simp only [hNotLt, ↓reduceIte, Var.unshift, hUnshift]
        exact hSatCSt
      · -- c is the backward clause [¬u', v₁, ..., vₙ]
        have hU' : (mkBigOrIff b literals st').1 = ⟨st'.nextFresh⟩ := by
          simp only [mkBigOrIff, EncState.allocFresh]
        have hU : (mkBigOrIff b literals st).1 = ⟨st.nextFresh⟩ := by
          simp only [mkBigOrIff, EncState.allocFresh]
        -- c = [¬u'] ++ literals.map pos
        rw [hBack]
        simp only [hU', FVar.toVar]
        -- The corresponding clause at st is [¬u] ++ literals.map pos
        have hCStMem : SAT.Lit.neg (Var.Fresh st.nextFresh) :: literals.map SAT.Lit.pos ∈
            (mkBigOrIff b literals st).2.clauses := by
          rw [mkBigOrIff_clause_mem_iff]
          right; right
          simp only [hU, FVar.toVar]
        have hCStNew : SAT.Lit.neg (Var.Fresh st.nextFresh) :: literals.map SAT.Lit.pos ∉
            st.clauses := by
          intro hIn
          have hWFClause := hWF _ hIn
          unfold clauseFreshBelow at hWFClause
          have hLit : SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh) ∈
              (SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh) :: literals.map SAT.Lit.pos) := by
            simp
          have hBound := hWFClause _ hLit
          simp only [litFreshBelow] at hBound
          exact Nat.lt_irrefl _ hBound
        have hSatCSt := hSatNew _ hCStMem hCStNew
        -- Show σ' satisfies [¬u', v₁, ..., vₙ]
        simp only [SAT.Clause.eval_eq_any, List.any_cons, SAT.Lit.eval] at hSatCSt ⊢
        -- σ'(¬(Fresh st'.nextFresh)) = σ(¬(Fresh st.nextFresh))
        have hFreshEq : σ' (Var.Fresh st'.nextFresh) = σ (Var.Fresh st.nextFresh) := by
          simp only [σ', shiftedAssignment]
          have hUnshift : st'.nextFresh - offset = st.nextFresh := by rw [hOffset]; omega
          have hNotLt : ¬(st'.nextFresh < st'.nextFresh) := Nat.lt_irrefl _
          simp only [hNotLt, ↓reduceIte, Var.unshift, hUnshift]
        -- The literals are Pred vars, so σ' = σ on them
        have hLitsPred : ∀ v ∈ literals, ∃ p ti k, v = Var.Pred p ti k := by
          intro v hv
          simp only [literals, List.mem_map] at hv
          obtain ⟨k, _, rfl⟩ := hv
          exact ⟨w.p, w.ti, k, rfl⟩
        -- In the empty case, literals = idxs.map ... = [].map ... = []
        -- So the backward clause is just [¬u'] and [¬u], and any on [] is trivially false = false
        have hIdxsEmpty : idxs = [] := hEmpty
        have hLitsEmpty : literals = [] := by simp only [literals, hIdxsEmpty, List.map_nil]
        simp only [hLitsEmpty, List.map_nil, List.any_nil, Bool.or_false] at hSatCSt ⊢
        rw [hFreshEq]
        exact hSatCSt
    · -- Contradiction: idxs = [] at st' but ¬(idxs = []) at st
      rename_i hNotEmpty
      exact absurd hEmpty hNotEmpty
  · -- Non-empty case for hc
    rename_i hNonEmpty
    split at hSatNew
    · -- Contradiction: idxs ≠ [] at st' but idxs = [] at st
      rename_i hEmpty
      exact absurd hEmpty hNonEmpty
    · -- Both are in non-empty case: full predicate encoding structure
      rename_i hNonEmpty'
      -- Define intermediate states for st-encoding
      let st1 := (mkBigOrIff b literals st).2
      let st2 := addPreEqFrom b w.ti st1
      let st3 := addPreEqReflAll b st2
      -- st4 is the final fold adding backward/forward predicateFold clauses

      -- Define intermediate states for st'-encoding
      let st1' := (mkBigOrIff b literals st').2
      let st2' := addPreEqFrom b w.ti st1'
      let st3' := addPreEqReflAll b st2'

      -- Define the nested foldl step function (same for st and st')
      let predicateFoldStep := fun stCur (H' : b.times) =>
        idxs.foldl (fun stAcc k =>
          let backward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                           SAT.Lit.neg (Var.Pred w.p H' k),
                           SAT.Lit.pos (Var.Pred w.p w.ti k)]
          let forward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                          SAT.Lit.neg (Var.Pred w.p w.ti k),
                          SAT.Lit.pos (Var.Pred w.p H' k)]
          EncState.addClause b (EncState.addClause b stAcc backward) forward) stCur

      -- Check where c comes from in the st'-encoding
      -- The encoding adds clauses in order: mkBigOrIff, addPreEqFrom, addPreEqReflAll, predicateFold
      -- c could be from any of these stages or inherited from st'

      -- First check if c is in st1' (mkBigOrIff stage)
      match Decidable.em (c ∈ st1'.clauses) with
      | Or.inl hcSt1' => -- c is from mkBigOrIff at st'
        by_cases hcSt' : c ∈ st'.clauses
        · exact absurd hcSt' hcNew
        · -- c is NEW from mkBigOrIff at st'
          -- Use the same argument as the empty case (mkBigOrIff SD)
          have hMem := (mkBigOrIff_clause_mem_iff b literals st' c).mp hcSt1'
          rcases hMem with hcSt'Bad | ⟨v, hv, hFwd⟩ | hBack
          · exact absurd hcSt'Bad hcNew
          · -- c is a forward clause [¬v, u'] - same as empty case
            have hU' : (mkBigOrIff b literals st').1 = ⟨st'.nextFresh⟩ := by
              simp only [mkBigOrIff, EncState.allocFresh]
            have hU : (mkBigOrIff b literals st).1 = ⟨st.nextFresh⟩ := by
              simp only [mkBigOrIff, EncState.allocFresh]
            rw [hFwd]
            simp only [hU', FVar.toVar]
            have hCStMem : [SAT.Lit.neg v, SAT.Lit.pos (Var.Fresh st.nextFresh)] ∈
                (mkBigOrIff b literals st).2.clauses := by
              rw [mkBigOrIff_clause_mem_iff]
              right; left
              refine ⟨v, hv, ?_⟩
              simp only [hU, FVar.toVar]
            have hCStNew : [SAT.Lit.neg v, SAT.Lit.pos (Var.Fresh st.nextFresh)] ∉ st.clauses := by
              intro hIn
              have hWFClause := hWF _ hIn
              unfold clauseFreshBelow at hWFClause
              have hLit : SAT.Lit.pos (Var.Fresh (b := b) st.nextFresh) ∈
                  [SAT.Lit.neg v, SAT.Lit.pos (Var.Fresh (b := b) st.nextFresh)] := by simp
              have hBound := hWFClause _ hLit
              simp only [litFreshBelow] at hBound
              exact Nat.lt_irrefl _ hBound
            -- hSatNew has been unfolded by simp, so we need the internal form
            -- Chain: mkBigOrIff ⊆ addPreEqFrom ⊆ addPreEqReflAll ⊆ nested predicateFold
            -- All subsequent stages preserve clauses (monotonicity property)
            have hCStInInternal := addPreEqFrom_clauses_subset b w.ti (mkBigOrIff b literals st).2 hCStMem
            have hCStInInternal2 := addPreEqReflAll_clauses_subset b _ hCStInInternal
            -- Show the clause survives through the nested foldl
            have hCStInFinal : [SAT.Lit.neg v, SAT.Lit.pos (Var.Fresh st.nextFresh)] ∈
                ((Bounds.timesL b).foldl predicateFoldStep
                  (addPreEqReflAll b (addPreEqFrom b w.ti (mkBigOrIff b literals st).2))).clauses := by
              apply foldl_subset_state (f := predicateFoldStep)
              · intro stCur H'
                apply foldl_subset_state (f := fun stAcc k =>
                    let backward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                     SAT.Lit.neg (Var.Pred w.p H' k),
                                     SAT.Lit.pos (Var.Pred w.p w.ti k)]
                    let forward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                    SAT.Lit.neg (Var.Pred w.p w.ti k),
                                    SAT.Lit.pos (Var.Pred w.p H' k)]
                    EncState.addClause b (EncState.addClause b stAcc backward) forward)
                intro stAcc k
                calc stAcc.clauses
                    ⊆ (EncState.addClause b stAcc _).clauses :=
                        EncState.addClause_subset_clauses b stAcc _
                  _ ⊆ (EncState.addClause b (EncState.addClause b stAcc _) _).clauses :=
                        EncState.addClause_subset_clauses b _ _
              · exact hCStInInternal2
            have hSatCSt := hSatNew _ hCStInFinal hCStNew
            simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false, SAT.Lit.eval]
            simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false,
                       SAT.Lit.eval] at hSatCSt
            have hVPred : ∃ p ti k, v = Var.Pred p ti k := by
              simp only [literals, List.mem_map] at hv
              obtain ⟨k, _, rfl⟩ := hv
              exact ⟨w.p, w.ti, k, rfl⟩
            obtain ⟨p, ti, k, hvEq⟩ := hVPred
            subst hvEq
            simp only [σ', shiftedAssignment]
            have hUnshift : st'.nextFresh - offset = st.nextFresh := by rw [hOffset]; omega
            have hNotLt : ¬(st'.nextFresh < st'.nextFresh) := Nat.lt_irrefl _
            simp only [hNotLt, ↓reduceIte, Var.unshift, hUnshift]
            exact hSatCSt
          · -- c is the backward clause [¬u', v₁, ..., vₙ] - same as empty case
            have hU' : (mkBigOrIff b literals st').1 = ⟨st'.nextFresh⟩ := by
              simp only [mkBigOrIff, EncState.allocFresh]
            have hU : (mkBigOrIff b literals st).1 = ⟨st.nextFresh⟩ := by
              simp only [mkBigOrIff, EncState.allocFresh]
            rw [hBack]
            simp only [hU', FVar.toVar]
            have hCStMem : SAT.Lit.neg (Var.Fresh st.nextFresh) :: literals.map SAT.Lit.pos ∈
                (mkBigOrIff b literals st).2.clauses := by
              rw [mkBigOrIff_clause_mem_iff]
              right; right
              simp only [hU, FVar.toVar]
            have hCStNew : SAT.Lit.neg (Var.Fresh st.nextFresh) :: literals.map SAT.Lit.pos ∉
                st.clauses := by
              intro hIn
              have hWFClause := hWF _ hIn
              unfold clauseFreshBelow at hWFClause
              have hLit : SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh) ∈
                  (SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh) :: literals.map SAT.Lit.pos) := by simp
              have hBound := hWFClause _ hLit
              simp only [litFreshBelow] at hBound
              exact Nat.lt_irrefl _ hBound
            -- Show the corresponding clause at st is in the final encoding (unfolded form)
            have hCStInInternal := addPreEqFrom_clauses_subset b w.ti (mkBigOrIff b literals st).2 hCStMem
            have hCStInInternal2 := addPreEqReflAll_clauses_subset b _ hCStInInternal
            have hCStInFinal : SAT.Lit.neg (Var.Fresh st.nextFresh) :: literals.map SAT.Lit.pos ∈
                ((Bounds.timesL b).foldl predicateFoldStep
                  (addPreEqReflAll b (addPreEqFrom b w.ti (mkBigOrIff b literals st).2))).clauses := by
              apply foldl_subset_state (f := predicateFoldStep)
              · intro stCur H'
                apply foldl_subset_state (f := fun stAcc k =>
                    let backward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                     SAT.Lit.neg (Var.Pred w.p H' k),
                                     SAT.Lit.pos (Var.Pred w.p w.ti k)]
                    let forward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                    SAT.Lit.neg (Var.Pred w.p w.ti k),
                                    SAT.Lit.pos (Var.Pred w.p H' k)]
                    EncState.addClause b (EncState.addClause b stAcc backward) forward)
                intro stAcc k
                calc stAcc.clauses
                    ⊆ (EncState.addClause b stAcc _).clauses :=
                        EncState.addClause_subset_clauses b stAcc _
                  _ ⊆ (EncState.addClause b (EncState.addClause b stAcc _) _).clauses :=
                        EncState.addClause_subset_clauses b _ _
              · exact hCStInInternal2
            have hSatCSt := hSatNew _ hCStInFinal hCStNew
            simp only [SAT.Clause.eval_eq_any, List.any_cons, SAT.Lit.eval] at hSatCSt ⊢
            -- σ'(Fresh st'.nextFresh) = σ(Fresh st.nextFresh)
            have hFreshEq : σ' (Var.Fresh st'.nextFresh) = σ (Var.Fresh st.nextFresh) := by
              simp only [σ', shiftedAssignment]
              have hUnshift : st'.nextFresh - offset = st.nextFresh := by rw [hOffset]; omega
              have hNotLt : ¬(st'.nextFresh < st'.nextFresh) := Nat.lt_irrefl _
              simp only [hNotLt, ↓reduceIte, Var.unshift, hUnshift]
            -- The literals are Pred vars - shiftedAssignment preserves non-Fresh vars
            have hLitsEq : (literals.map SAT.Lit.pos).any (SAT.Lit.eval σ') =
                (literals.map SAT.Lit.pos).any (SAT.Lit.eval σ) := by
              simp only [literals, List.map_map]
              induction idxs with
              | nil => rfl
              | cons hd tl ih =>
                simp only [List.map_cons, List.any_cons, Function.comp_apply, SAT.Lit.eval]
                -- σ' on Var.Pred is the same as σ (non-Fresh var)
                have hPred : σ' (Var.Pred w.p w.ti hd) = σ (Var.Pred w.p w.ti hd) := rfl
                simp only [hPred, ih]
            -- Goal: (¬σ'(Fresh st'.nextFresh) || lits.any(σ')) = true
            -- hSatCSt: (¬σ(Fresh st.nextFresh) || lits.any(σ)) = true
            -- hFreshEq: σ'(Fresh st'.nextFresh) = σ(Fresh st.nextFresh)
            -- hLitsEq: lits.any(σ') = lits.any(σ)
            simp only [hFreshEq]
            -- Use convert to handle SAT.Lit.eval expansion
            convert hSatCSt using 2
      | Or.inr hcNotSt1' => -- c is not in st1'.clauses, so c came from addPreEqFrom, addPreEqReflAll, or predicateFold

        -- Show clause chain: st.clauses ⊆ st1.clauses ⊆ st2.clauses ⊆ st3.clauses ⊆ final.clauses
        have hStSt1 : st.clauses ⊆ st1.clauses := mkBigOrIff_clauses_subset b literals st
        have hSt1St2 : st1.clauses ⊆ st2.clauses := addPreEqFrom_clauses_subset b w.ti st1
        have hSt2St3 : st2.clauses ⊆ st3.clauses := addPreEqReflAll_clauses_subset b st2
        have hSt3Final : st3.clauses ⊆
            ((Bounds.timesL b).foldl predicateFoldStep st3).clauses := by
          apply foldl_subset_state (f := predicateFoldStep)
          intro stCur H'
          apply foldl_subset_state
          intro stAcc k
          let backward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                           SAT.Lit.neg (Var.Pred w.p H' k),
                           SAT.Lit.pos (Var.Pred w.p w.ti k)]
          let forward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                          SAT.Lit.neg (Var.Pred w.p w.ti k),
                          SAT.Lit.pos (Var.Pred w.p H' k)]
          have h1 : stAcc.clauses ⊆ (EncState.addClause b stAcc backward).clauses :=
            EncState.addClause_subset_clauses b stAcc backward
          have h2 : (EncState.addClause b stAcc backward).clauses ⊆
              (EncState.addClause b (EncState.addClause b stAcc backward) forward).clauses :=
            EncState.addClause_subset_clauses b (EncState.addClause b stAcc backward) forward
          exact fun c hc => h2 (h1 hc)

        -- Similarly for st' path
        have hSt1'St2' : st1'.clauses ⊆ st2'.clauses := addPreEqFrom_clauses_subset b w.ti st1'
        have hSt2'St3' : st2'.clauses ⊆ st3'.clauses := addPreEqReflAll_clauses_subset b st2'

        -- Split into three sub-cases based on which stage added c
        by_cases hcSt2' : c ∈ st2'.clauses
        · -- Case: c is from addPreEqFrom (st1' → st2'), c ∉ st1'
          -- Check if c has any Fresh vars
          by_cases hHasFresh : ∃ lit ∈ c, ∃ n, lit.getVar = Var.Fresh n
          · -- c has Fresh vars: use addPreEqFrom_structural_determinism
            -- Step 1: Derive offset = st1'.nextFresh - st1.nextFresh (same as original offset)
            have hOffset1 : offset = st1'.nextFresh - st1.nextFresh := by
              simp only [st1, st1', mkBigOrIff_nextFresh]
              omega
            -- Step 2: Derive monotonicity for st1/st1'
            have hMono1 : st1.nextFresh ≤ st1'.nextFresh := by
              simp only [st1, st1', mkBigOrIff_nextFresh]
              omega
            -- Step 3: Get st1.WellFormed
            have hWF1 : st1.WellFormed := by
              apply mkBigOrIff_wf b literals st hWF
              -- All literals are non-Fresh (Pred vars)
              intro v hv
              simp only [literals, List.mem_map] at hv
              obtain ⟨k, _, rfl⟩ := hv
              intro n hContra
              exact Var.noConfusion hContra
            -- Step 4: Derive satisfaction for addPreEqFrom at st1
            have hSat2 : ∀ c ∈ (addPreEqFrom b w.ti st1).clauses, c ∉ st1.clauses →
                SAT.Clause.eval σ c = true := by
              intro c' hc' hc'NotSt1
              have hc'InSt3 := hSt2St3 hc'
              have hc'InFinal := hSt3Final hc'InSt3
              have hc'NotSt : c' ∉ st.clauses := by
                intro hIn
                exact hc'NotSt1 (hStSt1 hIn)
              exact hSatNew c' hc'InFinal hc'NotSt
            -- Step 5: Apply addPreEqFrom_structural_determinism at st1/st1'
            have hResult := addPreEqFrom_structural_determinism b w.ti st1 st1' offset
                hOffset1 hMono1 hWF1 σ hSat2 c hcSt2' hcNotSt1' hHasFresh
            -- hResult : SAT.Clause.eval (shiftedAssignment b σ st1'.nextFresh offset) c = true
            -- Goal: SAT.Clause.eval σ' c = true where σ' = shiftedAssignment b σ st'.nextFresh offset
            -- Step 6: Convert threshold using clause_eval_shiftedAssignment_threshold_agree
            have hThreshLe : st'.nextFresh ≤ st1'.nextFresh := by
              simp only [st1', mkBigOrIff_nextFresh]; omega
            -- Fresh vars in c have index >= st1'.nextFresh
            have hFreshGe : ∀ lit, lit ∈ c → ∀ n, SAT.Lit.getVar lit = Var.Fresh n →
                n ≥ st1'.nextFresh :=
              addPreEqFrom_newClause_fresh_ge b w.ti st1' c hcSt2' hcNotSt1'
            have hEvalEq := clause_eval_shiftedAssignment_threshold_agree b σ
                st'.nextFresh st1'.nextFresh offset hThreshLe c hFreshGe
            rw [hEvalEq]
            exact hResult
          · -- c has no Fresh vars: c = [pos (PreEq ti ti)] by addPreEqFrom_newClause_nonFresh_eq_refl
            push_neg at hHasFresh
            have hNoFreshAlt : ∀ lit ∈ c, ∀ n, lit.getVar ≠ Var.Fresh n := by
              intro lit hLit n; exact hHasFresh lit hLit n
            have hcEq := addPreEqFrom_newClause_nonFresh_eq_refl b w.ti st1' c hcSt2' hcNotSt1' hNoFreshAlt
            -- c = [pos (PreEq ti ti)] is deterministic - added at both st1 and st1'
            rw [hcEq]
            -- σ' = σ on non-Fresh vars (PreEq vars are not Fresh)
            simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false, SAT.Lit.eval]
            simp only [σ', shiftedAssignment]
            -- The same clause is added at st1, so σ satisfies it
            have hReflInSt2 : [SAT.Lit.pos (Var.PreEq w.ti w.ti)] ∈ st2.clauses :=
              addPreEqFrom_refl_unit_mem b w.ti st1
            have hReflInSt3 := hSt2St3 hReflInSt2
            have hReflInFinal := hSt3Final hReflInSt3
            have hReflNotSt : [SAT.Lit.pos (Var.PreEq w.ti w.ti)] ∉ st.clauses := by
              intro hIn
              -- This clause would be in st'.clauses by hNonFreshCompat (it has no Fresh vars)
              have hNoFreshClause : clauseHasNoFresh [SAT.Lit.pos (Var.PreEq w.ti w.ti)] := by
                intro lit hLit n hEq
                simp only [List.mem_singleton] at hLit
                subst hLit
                simp only [SAT.Lit.getVar] at hEq
                -- Var.PreEq ≠ Var.Fresh - different constructors
                exact Var.noConfusion hEq
              have hInSt' := hNonFreshCompat [SAT.Lit.pos (Var.PreEq w.ti w.ti)] hIn hNoFreshClause
              have hInSt1' := mkBigOrIff_clauses_subset b literals st' hInSt'
              -- If [pos (PreEq ...)] ∈ st1'.clauses, we show c ∈ st1'.clauses to contradict hcNotSt1'
              -- Note: hcEq : c = [pos (PreEq w.ti w.ti)]
              rw [hcEq] at hcNotSt1'
              exact hcNotSt1' hInSt1'
            have hSat := hSatNew _ hReflInFinal hReflNotSt
            simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, Bool.or_false,
                       SAT.Lit.eval] at hSat
            exact hSat
        · -- c ∉ st2'.clauses, so c is from addPreEqReflAll or predicateFold
          by_cases hcSt3' : c ∈ st3'.clauses
          · -- Case: c is from addPreEqReflAll (st2' → st3'), c ∉ st2'
            -- addPreEqReflAll only adds [pos (PreEq t t)] - no Fresh vars
            have hNoFresh := addPreEqReflAll_clauses_nonFresh b st2' c hcSt3' hcSt2'
            have hEvalEq : SAT.Clause.eval σ' c = SAT.Clause.eval σ c :=
              nonFresh_clause_eval b st' σ offset c hNoFresh
            -- Same clause added at st path (addPreEqReflAll is deterministic)
            have hcInSt3 : c ∈ st3.clauses := by
              -- addPreEqReflAll adds [pos (PreEq t t)] for each t in Bounds.timesL b
              -- This is independent of input state's clauses
              have hRefl := addPreEqReflAll_clauses_nonFresh b st2' c hcSt3' hcSt2'
              -- c = [pos (PreEq t t)] for some t
              rcases foldl_addClause_mem b (Bounds.timesL b) st2'
                  (fun t => [SAT.Lit.pos (Var.PreEq t t)]) c hcSt3' with hBase | ⟨t, hT, hEq⟩
              · exact absurd hBase hcSt2'
              · -- c = [pos (PreEq t t)], same clause added at st2
                rw [hEq]
                exact foldl_addClause_elem_mem b (Bounds.timesL b) st2
                  (fun t => [SAT.Lit.pos (Var.PreEq t t)]) t hT
            have hcInFinal : c ∈ ((Bounds.timesL b).foldl predicateFoldStep st3).clauses :=
              hSt3Final hcInSt3
            have hcNotSt : c ∉ st.clauses := by
              intro hInSt
              have hInSt1 := hStSt1 hInSt
              have hInSt2 := hSt1St2 hInSt1
              have hInSt2' : c ∈ st2'.clauses := by
                -- c ∈ st.clauses → c ∈ st'.clauses (hNonFreshCompat, using hNoFresh)
                --               → c ∈ st1'.clauses (mkBigOrIff preserves)
                --               → c ∈ st2'.clauses (addPreEqFrom preserves)
                have hInSt' := hNonFreshCompat c hInSt hNoFresh
                have hSt'St1' := mkBigOrIff_clauses_subset b literals st'
                have hSt1'St2' := addPreEqFrom_clauses_subset b w.ti st1'
                exact hSt1'St2' (hSt'St1' hInSt')
              exact hcSt2' hInSt2'
            have hSat := hSatNew c hcInFinal hcNotSt
            rw [hEvalEq]
            exact hSat
          · -- Case: c is from predicateFold (st3' → final'), c ∉ st3'
            -- predicateFold only adds [neg PreEq, neg Pred, pos Pred] clauses - no Fresh vars
            have hNoFresh : ∀ lit ∈ c, ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n := by
              intro lit hLit n hFreshEq
              -- c is from predicateFold, which only adds clauses with PreEq and Pred vars
              simp only [encodeFormula, hNonEmpty] at hc
              -- Use nested_foldl_addClause2_mem to characterize clauses in fold result
              let mkBackward := fun (H' : b.times) (k : b.predIx) =>
                [SAT.Lit.neg (Var.PreEq w.ti H'),
                 SAT.Lit.neg (Var.Pred w.p H' k),
                 SAT.Lit.pos (Var.Pred w.p w.ti k)]
              let mkForward := fun (H' : b.times) (k : b.predIx) =>
                [SAT.Lit.neg (Var.PreEq w.ti H'),
                 SAT.Lit.neg (Var.Pred w.p w.ti k),
                 SAT.Lit.pos (Var.Pred w.p H' k)]
              have hFoldEq : ((Bounds.timesL b).foldl predicateFoldStep st3').clauses =
                  ((Bounds.timesL b).foldl (fun stAcc H' =>
                    idxs.foldl (fun stAcc' k =>
                      let stAcc' := EncState.addClause b stAcc' (mkBackward H' k)
                      EncState.addClause b stAcc' (mkForward H' k)) stAcc) st3').clauses := rfl
              rw [hFoldEq] at hc
              rcases nested_foldl_addClause2_mem b (Bounds.timesL b) idxs st3'
                  mkBackward mkForward c hc with hBase | ⟨H', _, k, _, hEq⟩
              · -- c ∈ st3'.clauses contradicts hcSt3'
                exact absurd hBase hcSt3'
              · -- c = backward or c = forward for some H', k
                rcases hEq with hBack | hFwd
                · -- c = backward, which has only PreEq and Pred vars
                  simp only [mkBackward] at hBack
                  rw [hBack] at hLit
                  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff,
                    or_false] at hLit
                  rcases hLit with rfl | rfl | rfl <;>
                    simp only [SAT.Lit.getVar] at hFreshEq <;>
                    cases hFreshEq
                · -- c = forward, which has only PreEq and Pred vars
                  simp only [mkForward] at hFwd
                  rw [hFwd] at hLit
                  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff,
                    or_false] at hLit
                  rcases hLit with rfl | rfl | rfl <;>
                    simp only [SAT.Lit.getVar] at hFreshEq <;>
                    cases hFreshEq
            have hEvalEq : SAT.Clause.eval σ' c = SAT.Clause.eval σ c :=
              nonFresh_clause_eval b st' σ offset c hNoFresh
            -- Same clause added at st path (predicateFold is deterministic)
            have hcInFinal : c ∈ ((Bounds.timesL b).foldl predicateFoldStep st3).clauses := by
              -- Re-derive that c is a backward/forward clause using nested_foldl_addClause2_mem
              simp only [encodeFormula, hNonEmpty] at hc
              let mkBackward := fun (H' : b.times) (k : b.predIx) =>
                [SAT.Lit.neg (Var.PreEq w.ti H'),
                 SAT.Lit.neg (Var.Pred w.p H' k),
                 SAT.Lit.pos (Var.Pred w.p w.ti k)]
              let mkForward := fun (H' : b.times) (k : b.predIx) =>
                [SAT.Lit.neg (Var.PreEq w.ti H'),
                 SAT.Lit.neg (Var.Pred w.p w.ti k),
                 SAT.Lit.pos (Var.Pred w.p H' k)]
              have hFoldEq : ((Bounds.timesL b).foldl predicateFoldStep st3').clauses =
                  ((Bounds.timesL b).foldl (fun stAcc H' =>
                    idxs.foldl (fun stAcc' k =>
                      let stAcc' := EncState.addClause b stAcc' (mkBackward H' k)
                      EncState.addClause b stAcc' (mkForward H' k)) stAcc) st3').clauses := rfl
              rw [hFoldEq] at hc
              rcases nested_foldl_addClause2_mem b (Bounds.timesL b) idxs st3'
                  mkBackward mkForward c hc with hBase | ⟨H', hH', k, hk, hEq⟩
              · exact absurd hBase hcSt3'
              · -- c = backward H' k or c = forward H' k
                have hFoldEq' : ((Bounds.timesL b).foldl predicateFoldStep st3).clauses =
                    ((Bounds.timesL b).foldl (fun stAcc H' =>
                      idxs.foldl (fun stAcc' k =>
                        let stAcc' := EncState.addClause b stAcc' (mkBackward H' k)
                        EncState.addClause b stAcc' (mkForward H' k)) stAcc) st3).clauses := rfl
                rw [hFoldEq']
                rcases hEq with hBack | hFwd
                · -- c = backward H' k
                  rw [hBack]
                  exact nested_foldl_addClause2_elem_mem1 b (Bounds.timesL b) idxs st3
                    mkBackward mkForward H' hH' k hk
                · -- c = forward H' k
                  rw [hFwd]
                  exact nested_foldl_addClause2_elem_mem2 b (Bounds.timesL b) idxs st3
                    mkBackward mkForward H' hH' k hk
            have hcNotSt : c ∉ st.clauses := by
              intro hInSt
              have hInSt' : c ∈ st'.clauses := hNonFreshCompat c hInSt hNoFresh
              exact hcNew hInSt'
            have hSat := hSatNew c hcInFinal hcNotSt
            rw [hEvalEq]
            exact hSat


end Encoding
