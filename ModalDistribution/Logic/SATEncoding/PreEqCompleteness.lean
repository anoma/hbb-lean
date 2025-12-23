import ModalDistribution.Logic.SATEncoding.PreEqEncoding
import ModalDistribution.Logic.SATEncoding.PreEqSoundness

open ModalDistribution
open ModalDistribution.Logic
open PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkBigOrIff_complete (b : Bounds S) (vs : List (Var b)) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses : (mkBigOrIff b vs st).2.clauses.all (SAT.Clause.eval σ) = true)
    {v : Var b} (hv : v ∈ vs) (hVal : σ v = true) :
    σ (FVar.toVar b (mkBigOrIff b vs st).1) = true := by
  classical
  have hUnit := mkBigOrIff_unit_clause_mem b vs st hv
  have hEval := (List.all_eq_true.mp hClauses) _ hUnit
  simp [SAT.Clause.eval, SAT.Lit.eval, hVal, Bool.not_true, Bool.false_or] at hEval
  exact hEval

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkY_complete (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t' : b.times) (w w' : WId b) (st : EncState b)
    (hClauses : (mkY b t' w w' st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hMem : σ (Var.Mem t' w') = true)
    (hPreEq : σ (Var.PreEq w.ti w'.ti) = true) :
    σ (FVar.toVar b (mkY b t' w w' st).1) = true := by
  classical
  unfold mkY at hClauses
  cases hAlloc : EncState.allocFresh b st with
  | mk y st1 =>
    have hAll := (List.all_eq_true.mp hClauses)
    let clause := [SAT.Lit.neg (Var.Mem t' w')
                  , SAT.Lit.neg (Var.PreEq w.ti w'.ti)
                  , SAT.Lit.pos (FVar.toVar b y)]
    have hMemClause : clause ∈ (mkY b t' w w' st).2.clauses := by
      unfold mkY
      rw [hAlloc]
      simp [EncState.addClause, clause]
    have hEval := hAll clause hMemClause
    -- Unfold the clause evaluation manually
    simp [SAT.Clause.eval, SAT.Lit.eval, clause] at hEval
    -- The clause is [neg (Mem t' w'), neg (PreEq w.ti w'.ti), pos (FVar.toVar b y)]
    -- At least one literal must be true: ¬(Mem t' w') ∨ ¬(PreEq w.ti w'.ti) ∨ (FVar.toVar b y)
    simp only [hMem, hPreEq] at hEval
    have hEq : (mkY b t' w w' st).1 = y := by
      unfold mkY; rw [hAlloc]
    rw [hEq]
    cases hEval with
    | inl h => cases h with
      | inl h => cases h
      | inr h => cases h
    | inr h => exact h

-- Auxiliary lemma for mkDw_complete_from_preds
omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkDwStepPair_completeness (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st : EncState b)
    (w' : WId b) (hMem : w' ∈ cands) :
    ∃ triple ∈ ((cands.foldl (mkDwStepPair b t' w) ([], st)).1), triple.2.2 = w' := by
  induction cands generalizing st with
  | nil => cases hMem
  | cons w0 ws ih =>
    simp only [mkDwStepPair, List.foldl_cons]
    cases hMk : mkY b t' w w0 st with
    | mk y st' =>
      if hEq : w' = w0 then
        subst hEq
        exists (y, st, w')
        constructor
        · apply mkDwStepPair_fold_preserves_acc
          simp
        · rfl
      else
        have hInWs : w' ∈ ws := List.mem_of_ne_of_mem hEq hMem
        obtain ⟨triple, hTri, hEqTri⟩ := ih st' hInWs
        exists triple
        constructor
        · apply mkDwStepPair_fold_mem_monotone b t' w ws [] [(y, st, w0)] st' hTri
        · exact hEqTri

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_complete_from_preds (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t' : b.times) (w : WId b) (st : EncState b)
    (hClauses : (mkDw b t' w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (w' : WId b) (hSig : sameSig b w w' = true)
    (hMem : σ (Var.Mem t' w') = true)
    (hPreEq : σ (Var.PreEq w.ti w'.ti) = true) :
    σ (FVar.toVar b (mkDw b t' w st).1) = true := by
  classical
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  have hMemCands : w' ∈ cands := by
    simp [cands, WId.mem_allWorlds, hSig]
  -- Save original hClauses before unfolding
  have hClausesOrig := hClauses
  unfold mkDw at hClauses
  rw [← (show cands = (WId.allWorlds b).filter (fun w' => sameSig b w w') from rfl)] at hClauses
  cases hCands : cands with
  | nil =>
    rw [hCands] at hMemCands
    cases hMemCands
  | cons w0 ws =>
    have hFilterEq : (WId.allWorlds b).filter (fun x => sameSig b w x) = w0 :: ws := by
      rw [← hCands]
    -- Destructure the fold result
    cases hFold :
        ((w0 :: ws).foldl
          (fun (acc : List (Var b) × EncState b) w' =>
            let (vs, st') := acc
            let (y, st'') := mkY b t' w w' st'
            (FVar.toVar b y :: vs, st''))
          ([], st)) with
    | mk ys st1 =>
      have hMkDw : mkDw b t' w st = mkBigOrIff b ys st1 := by
        unfold mkDw; simp [hFilterEq, hFold]
      rw [hCands] at hMemCands
      have hPairMem :
          ∃ triple ∈ ((w0 :: ws).foldl (mkDwStepPair b t' w) ([], st)).1,
            triple.2.2 = w' :=
        mkDwStepPair_completeness b t' w (w0 :: ws) st w' hMemCands
      obtain ⟨triple, hTriMem, hTriEq⟩ := hPairMem
      -- Use hClausesOrig for mkDw_satisfies_mkY_clauses
      have hYClauses := mkDw_satisfies_mkY_clauses b σ t' w st w0 ws hFilterEq hClausesOrig hTriMem
      rw [hTriEq] at hYClauses
      have hYTrue : σ (FVar.toVar b triple.1) = true := by
        rw [mkDwStepPair_fst_eq_mkY_fst b t' w (w0 :: ws) st hTriMem]
        apply mkY_complete b σ t' w w' triple.2.1 hYClauses hMem hPreEq
      obtain ⟨hVarsEq, _⟩ := mkDw_fold_pairs b t' w (w0 :: ws) st
      have hYinYs : FVar.toVar b triple.1 ∈ ys := by
        have hVarEq :
            ys = ((w0 :: ws).foldl (mkDwStepPair b t' w) ([], st)).1.map
              (fun triple => FVar.toVar b triple.1) := by
          conv_lhs => rw [← (show (ys, st1).1 = ys from rfl)]
          rw [← hFold]
          exact hVarsEq
        rw [hVarEq]
        exact List.mem_map.mpr ⟨triple, hTriMem, rfl⟩
      -- Rewrite goal and hClausesOrig to mkBigOrIff for the final step
      rw [hMkDw] at hClausesOrig ⊢
      apply mkBigOrIff_complete b ys st1 σ hClausesOrig hYinYs hYTrue

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOw_complete (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t : b.times) (w : WId b) (d : FVar b) (st : EncState b)
    (hClauses : (mkOw b t w d st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hMem : σ (Var.Mem t w) = true → σ (FVar.toVar b d) = true) :
    σ (FVar.toVar b (mkOw b t w d st).1) = true := by
  classical
  unfold mkOw at hClauses
  cases hAlloc : EncState.allocFresh b st with
  | mk o st1 =>
    have hEq : (mkOw b t w d st).1 = o := by
      unfold mkOw; rw [hAlloc]
    rw [hEq]
    have hAll := List.all_eq_true.mp hClauses
    by_cases hMemVal : σ (Var.Mem t w) = true
    · have hD := hMem hMemVal
      let clause := [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)]
      have hIn : clause ∈ (mkOw b t w d st).2.clauses := by
        unfold mkOw; rw [hAlloc]; simp [EncState.addClause, clause]
      have hEval := hAll clause hIn
      simp [clause, SAT.Clause.eval, SAT.Lit.eval] at hEval
      simp [hD] at hEval
      exact hEval
    · have hMemFalse : σ (Var.Mem t w) = false := by
        cases h : σ (Var.Mem t w); rfl; contradiction
      let clause := [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)]
      have hIn : clause ∈ (mkOw b t w d st).2.clauses := by
        unfold mkOw; rw [hAlloc]; simp [EncState.addClause, clause]
      have hEval := hAll clause hIn
      simp [clause, SAT.Clause.eval, SAT.Lit.eval] at hEval
      simp [hMemFalse] at hEval
      exact hEval

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma and_accumulator_complete
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (os : List (FVar b))
    (base : FVar b) (stBase : EncState b)
    (final : FVar b × EncState b)
    (hResult : final = os.foldl (preEqAccStep b) (base, stBase))
    (hClauses : final.2.clauses.all (SAT.Clause.eval σ) = true)
    (hOsTrue : ∀ o ∈ os, σ (FVar.toVar b o) = true)
    (hBaseTrue : σ (FVar.toVar b base) = true) :
    σ (FVar.toVar b final.1) = true := by
  classical
  induction os generalizing base stBase final with
  | nil =>
      simp [List.foldl] at hResult
      rw [hResult]
      simp
      exact hBaseTrue
  | cons x xs ih =>
      simp [List.foldl_cons] at hResult
      cases hAlloc : EncState.allocFresh b stBase with | mk n stNext =>
      have hNext : (n, addAccStep b base n x stNext) = preEqAccStep b (base, stBase) x := by
        simp [preEqAccStep, hAlloc]
      rw [← hNext] at hResult

      have hXTrue : σ (FVar.toVar b x) = true := hOsTrue x List.mem_cons_self
      have hNextTrue : σ (FVar.toVar b n) = true := by
        have hNextClauses :
            (addAccStep b base n x stNext).clauses.all (SAT.Clause.eval σ) = true := by
          apply all_true_of_subset _ hClauses
          exact preEqAcc_fold_clauses_subset b xs hResult
        have hXTrue : σ (FVar.toVar b x) = true := hOsTrue x List.mem_cons_self
        apply addAccStep_backward b σ base n x stNext hNextClauses hBaseTrue hXTrue

      apply ih n (addAccStep b base n x stNext) final hResult hClauses
      · intro o hMem
        exact hOsTrue o (List.mem_cons_of_mem x hMem)
      · exact hNextTrue


omit [DecidableEq S.AtomicPredType] in
lemma preEq_obligation_complete
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) (w : WId b) (st : EncState b)
    (d : FVar b) (stDw : EncState b) (o : FVar b) (stOw : EncState b)
    (hMkDw : mkDw b t' w st = (d, stDw))
    (hMkOw : mkOw b t w d stDw = (o, stOw))
    (hClauses : stOw.clauses.all (SAT.Clause.eval σ) = true)
    (hDecode : histEq (decodePre b σ hWF t) (decodePre b σ hWF t'))
    (IH : ∀ ⦃t₁ t₂ : b.times⦄,
        fuelOf b σ t₁ + fuelOf b σ t₂ < fuelOf b σ t + fuelOf b σ t' →
        histEq (decodePre b σ hWF t₁) (decodePre b σ hWF t₂) →
        σ (Var.PreEq t₁ t₂) = true) :
    σ (FVar.toVar b o) = true := by
  classical
  have hO : o = (mkOw b t w d stDw).1 := by rw [hMkOw]
  rw [hO]
  apply mkOw_complete b σ t w d stDw
  · rw [show (mkOw b t w d stDw).2 = stOw from (congrArg Prod.snd hMkOw)]
    exact hClauses
  · intro hMemW
    -- Witness matching logic
    let worldW := (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti)
    have hInT : worldW ∈ decodePre b σ hWF t :=
      mem_decodePre_of_memVar b σ hWF t w hMemW
    have hInT' : ∃ world' ∈ decodePre b σ hWF t', worldEq worldW world' :=
      ((histEq_spec _ _).mp hDecode).1 worldW hInT
    obtain ⟨world', hInT'Mem, hWorldEq⟩ := hInT'
    obtain ⟨w', hw'Eq, hMem'⟩ := exists_memVar_of_mem_decodePre b σ hWF t' hInT'Mem
    let worldW' := (w'.p, b.decodeMaybeEvent w'.ei, decodePre b σ hWF w'.ti)
    have hWEqW' : worldEq worldW worldW' := by
      have : worldW' = world' := hw'Eq
      rw [this]
      exact hWorldEq
    have hSig : sameSig b w w' = true := by
      have : w'.p = w.p ∧ b.decodeMaybeEvent w'.ei = b.decodeMaybeEvent w.ei := by
        rw [worldEq_spec] at hWEqW'
        simp [worldW, worldW'] at hWEqW'
        exact ⟨hWEqW'.1.symm, hWEqW'.2.1.symm⟩
      unfold sameSig
      simp only [this.1, this.2]
      cases b.decodeMaybeEvent w.ei <;> simp
    have hPre : σ (Var.PreEq w.ti w'.ti) = true := by
      apply IH
      · have h1 : fuelOf b σ w.ti < fuelOf b σ t :=
          fuelOf_strict_decrease_mem b σ hWF t w hMemW (fuel_pos_of_mem b σ hWF hMemW)
        have h2 : fuelOf b σ w'.ti < fuelOf b σ t' :=
          fuelOf_strict_decrease_mem b σ hWF t' w' hMem' (fuel_pos_of_mem b σ hWF hMem')
        omega
      · rw [worldEq_spec] at hWEqW'
        simp [worldW, worldW'] at hWEqW'
        exact hWEqW'.2.2

    have hD : d = (mkDw b t' w st).1 := (congrArg Prod.fst hMkDw).symm
    have hD2 : (mkDw b t' w st).2 = stDw := (congrArg Prod.snd hMkDw)
    rw [hD]
    apply mkDw_complete_from_preds b σ t' w st _ w' hSig hMem' hPre
    rw [hD2]
    have hSub : stDw.clauses ⊆ stOw.clauses := by
      have := mkOw_clauses_subset b t w d stDw
      simp [hMkOw] at this
      exact this
    apply all_true_of_subset hSub hClauses



omit [DecidableEq S.AtomicPredType] in
lemma preEqObligation_fold_sound
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) (ws : List (WId b)) (acc : List (FVar b) × EncState b)
    (stFinal : EncState b)
    (hExtends : (ws.foldl (preEqObligationStep b t t') acc).2.clauses ⊆ stFinal.clauses)
    (hClausesFinal : stFinal.clauses.all (SAT.Clause.eval σ) = true)
    (hDecode : histEq (decodePre b σ hWF t) (decodePre b σ hWF t'))
    (IH : ∀ ⦃t₁ t₂ : b.times⦄,
        fuelOf b σ t₁ + fuelOf b σ t₂ < fuelOf b σ t + fuelOf b σ t' →
        histEq (decodePre b σ hWF t₁) (decodePre b σ hWF t₂) →
        σ (Var.PreEq t₁ t₂) = true)
    (hAccTrue : ∀ o ∈ acc.1, σ (FVar.toVar b o) = true) :
    ∀ o ∈ (ws.foldl (preEqObligationStep b t t') acc).1, σ (FVar.toVar b o) = true := by
  classical
  induction ws generalizing acc with
  | nil => exact hAccTrue
  | cons w ws ih =>
      apply ih
      · -- hExtends applies to the result of the *whole* fold, which is the same
        exact hExtends
      · -- Show hAccTrue for next step
        rcases acc with ⟨lst, stc⟩
        dsimp [preEqObligationStep]
        cases hDw : mkDw b t' w stc with | mk d stc1 =>
        cases hOw : mkOw b t w d stc1 with | mk o_val stc2 =>
        intro v hv
        simp [List.mem_cons] at hv
        cases hv with
        | inl hEq =>
           rw [hEq]
           have : o_val = (mkOw b t w d stc1).1 := (congrArg Prod.fst hOw).symm
           apply preEq_obligation_complete b σ hWF t t' w stc d stc1 o_val stc2 hDw hOw _ hDecode IH
           apply all_true_of_subset _ hClausesFinal
           -- Chain subsets
           have hSub :
             (o_val :: lst, stc2).2.clauses
               ⊆ (List.foldl (preEqObligationStep b t t') (o_val :: lst, stc2) ws).2.clauses :=
             preEqObligation_fold_clauses_subset b t t' ws (init := (o_val :: lst, stc2)) rfl
           apply List.Subset.trans hSub
           -- Rewrite hExtends: (w::ws).foldl step (lst,stc) = ws.foldl step (step (lst,stc) w)
           have hFoldEq :
             (w :: ws).foldl (preEqObligationStep b t t') (lst, stc) =
               ws.foldl (preEqObligationStep b t t') (preEqObligationStep b t t' (lst, stc) w) := by
             simp [List.foldl_cons]
           have hStepEq : preEqObligationStep b t t' (lst, stc) w = (o_val :: lst, stc2) := by
             simp [preEqObligationStep, hDw, hOw]
           rw [hFoldEq, hStepEq] at hExtends
           exact hExtends
        | inr hTail => exact hAccTrue v hTail

omit [DecidableEq S.AtomicPredType] in

omit [DecidableEq S.AtomicPredType] in
/-- Completeness for a single `(t, t')` encoding: if the clauses are satisfied and
    the decoded prehistories are equal, then `PreEq t t'` is true. -/
lemma preEq_pair_complete
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) (st : EncState b)
    (hClauses : (addPreEqPair b t t' st).clauses.all (SAT.Clause.eval σ) = true)
    (hDecode : histEq (decodePre b σ hWF t) (decodePre b σ hWF t'))
    (IH : ∀ ⦃t₁ t₂ : b.times⦄,
        fuelOf b σ t₁ + fuelOf b σ t₂ < fuelOf b σ t + fuelOf b σ t' →
        histEq (decodePre b σ hWF t₁) (decodePre b σ hWF t₂) →
        σ (Var.PreEq t₁ t₂) = true) :
    σ (Var.PreEq t t') = true := by
  classical
  by_cases hEq : t = t'
  { -- Reflexive case
    rw [addPreEqPair] at hClauses
    simp only [hEq, if_true] at hClauses
    have hAll := List.all_eq_true.mp hClauses
    rw [hEq]
    have hUnit : [SAT.Lit.pos (Var.PreEq t' t')] ∈
        (EncState.addClause b (addPreEqPair_core b t' t' st)
          [SAT.Lit.pos (Var.PreEq t' t')]).clauses := by
      dsimp [addPreEqPair, EncState.addClause]
      simp
    have hEval := hAll _ hUnit
    simp [SAT.Clause.eval, SAT.Lit.eval] at hEval
    exact hEval
  }
  { -- Inductive case
    rw [addPreEqPair] at hClauses
    simp only [hEq, if_false] at hClauses

    -- Unpack the state construction
    set foldOs := (WId.allWorlds b).foldl (preEqObligationStep b t t') ([], st)
    let os := foldOs.1
    let stOs := foldOs.2
    set foldOs' := (WId.allWorlds b).foldl (preEqObligationStep b t' t) ([], stOs)
    let os' := foldOs'.1
    let stOs' := foldOs'.2

    cases hAllocBase : EncState.allocFresh b stOs' with | mk base stBase =>
    set stBasePos := EncState.addClause b stBase [SAT.Lit.pos (FVar.toVar b base)]

    set foldAcc := List.foldl (preEqAccStep b) (base, stBasePos) os
    let eqA := foldAcc.1
    let stAcc := foldAcc.2
    set foldAcc' := List.foldl (preEqAccStep b) (eqA, stAcc) os'
    let eqFinal := foldAcc'.1
    let stFinal := foldAcc'.2

    set stExpose := addPreEqExpose b t t' eqFinal stFinal
    have hClausesExpose :
        stExpose.clauses.all (SAT.Clause.eval σ) = true := by
      -- Non-reflexive branch: addPreEqPair_core is definitionally stExpose.
      -- hClauses already has addPreEqPair_core (from lines 370-371)
      have : addPreEqPair_core b t t' st = stExpose := by
        unfold addPreEqPair_core
        -- Match the fold structure
        have h1 :
            (WId.allWorlds b).foldl (preEqObligationStep b t t') ([], st) = foldOs := rfl
        have h2 :
            (WId.allWorlds b).foldl (preEqObligationStep b t' t) ([], foldOs.2) = foldOs' := rfl
        have h3 : EncState.allocFresh b foldOs'.2 = (base, stBase) := hAllocBase
        simp [h1, h2, h3]
        rfl
      rw [this] at hClauses
      exact hClauses
    have hAll := List.all_eq_true.mp hClausesExpose

    -- Clause subsets
    have hSub1 : st.clauses ⊆ stOs.clauses :=
      preEqObligation_fold_clauses_subset b t t' (WId.allWorlds b) (init := ([], st)) rfl
    have hSub2 : stOs.clauses ⊆ stOs'.clauses :=
      preEqObligation_fold_clauses_subset b t' t (WId.allWorlds b) (init := ([], stOs)) rfl
    have hSub3 : stOs'.clauses ⊆ stBase.clauses := by
      have heq : (EncState.allocFresh b stOs').2.clauses = stOs'.clauses :=
        EncState.allocFresh_clauses_eq (b := b) (st := stOs')
      have : stBase = (EncState.allocFresh b stOs').2 := by
        cases hAllocBase; rfl
      rw [this, heq]
      apply List.Subset.refl
    have hSub4 : stBase.clauses ⊆ stBasePos.clauses :=
      EncState.addClause_subset_clauses b stBase [SAT.Lit.pos (FVar.toVar b base)]
    have hSub5 : stBasePos.clauses ⊆ stAcc.clauses :=
      preEqAcc_fold_clauses_subset b os (init := (base, stBasePos)) rfl
    have hSub6 : stAcc.clauses ⊆ stFinal.clauses :=
      preEqAcc_fold_clauses_subset b os' (init := (eqA, stAcc)) rfl
    have hSubExpose : stFinal.clauses ⊆ stExpose.clauses :=
      addPreEqExpose_clauses_subset b t t' eqFinal stFinal

    -- Base is true
    have hBaseTrue : σ (FVar.toVar b base) = true := by
      have hUnit : [SAT.Lit.pos (FVar.toVar b base)] ∈ stBasePos.clauses := by
         simp [stBasePos, EncState.addClause]
      have hInFinal : [SAT.Lit.pos (FVar.toVar b base)] ∈ stFinal.clauses :=
        hSub6 (hSub5 hUnit)
      have hInExpose : [SAT.Lit.pos (FVar.toVar b base)] ∈ stExpose.clauses :=
        hSubExpose hInFinal
      have hEval := hAll _ hInExpose
      simp [SAT.Clause.eval, SAT.Lit.eval] at hEval
      exact hEval

    have hClausesFinal : stFinal.clauses.all (SAT.Clause.eval σ) = true :=
      all_true_of_subset hSubExpose hClausesExpose

    -- Helper for os True
    have hOsTrue : ∀ o ∈ os, σ (FVar.toVar b o) = true := by
      apply preEqObligation_fold_sound b σ hWF t t' (WId.allWorlds b) ([], st) stFinal
      · exact List.Subset.trans hSub2
          (List.Subset.trans hSub3 (List.Subset.trans hSub4 (List.Subset.trans hSub5 hSub6)))
      · exact hClausesFinal
      · exact hDecode
      · exact IH
      · simp

    -- Helper for os' True (Symmetric)
    have hOs'True : ∀ o ∈ os', σ (FVar.toVar b o) = true := by
      apply preEqObligation_fold_sound b σ hWF t' t (WId.allWorlds b) ([], stOs) stFinal
      · exact List.Subset.trans hSub3
          (List.Subset.trans hSub4 (List.Subset.trans hSub5 hSub6))
      · exact hClausesFinal
      · exact histEq_symm hDecode
      · -- IH'
        intro t₁ t₂ hFuel hHist
        apply IH
        · omega
        · exact hHist
      · simp

    have hEqATrue : σ (FVar.toVar b eqA) = true := by
      apply and_accumulator_complete b σ os base stBasePos (eqA, stAcc) rfl
      · apply all_true_of_subset hSub6 hClausesFinal
      · exact hOsTrue
      · exact hBaseTrue

    have hEqFinalTrue : σ (FVar.toVar b eqFinal) = true := by
      apply and_accumulator_complete b σ os' eqA stAcc (eqFinal, stFinal) rfl hClausesFinal
        hOs'True hEqATrue

    have hClause :
        [SAT.Lit.neg (FVar.toVar b eqFinal), SAT.Lit.pos (Var.PreEq t t')] ∈
          stExpose.clauses := by
      dsimp [stExpose]
      unfold addPreEqExpose
      simp [EncState.addClause]
    have hEval := hAll _ hClause
    simp [SAT.Clause.eval, SAT.Lit.eval, hEqFinalTrue, Bool.not_true, Bool.false_or] at hEval
    exact hEval
  }

omit [DecidableEq S.AtomicPredType] in
lemma preEq_complete_from
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t : b.times) (st0 : EncState b)
    (hClauses : (addPreEqFrom b t st0).clauses.all (SAT.Clause.eval σ) = true)
    (t' : b.times)
    (hDecode : histEq (decodePre b σ hWF t) (decodePre b σ hWF t'))
    (IH : ∀ ⦃t₁ t₂ : b.times⦄,
        fuelOf b σ t₁ + fuelOf b σ t₂ < fuelOf b σ t + fuelOf b σ t' →
        histEq (decodePre b σ hWF t₁) (decodePre b σ hWF t₂) →
        σ (Var.PreEq t₁ t₂) = true) :
    σ (Var.PreEq t t') = true := by
  classical
  let step := fun stCur (u : b.times) => addPreEqPair b t u stCur
  have hMem : t' ∈ Bounds.timesL b := by simp [Bounds.timesL]
  obtain ⟨before, after, hSplit⟩ := exists_split_of_mem (a := t') (l := Bounds.timesL b) hMem
  have hSplitEq :
      addPreEqFrom b t st0 = after.foldl step (addPreEqPair b t t' (before.foldl step st0)) :=
    addPreEqFrom_split b t st0 t' before after hSplit
  set stBefore := before.foldl step st0
  set stPair := addPreEqPair b t t' stBefore
  set stAfter := after.foldl step stPair
  have hClausesAfter : stAfter.clauses.all (SAT.Clause.eval σ) = true := by
    simpa [stAfter, stPair, stBefore, step, hSplitEq] using hClauses
  have hClausesPairRaw := preEq_pair_clauses_true b σ t t' st0 before after hSplit hClauses
  have hClausesPair : stPair.clauses.all (SAT.Clause.eval σ) = true := by
    simpa [step, stBefore, stPair] using hClausesPairRaw
  exact preEq_pair_complete b σ hWF t t' stBefore hClausesPair hDecode IH

omit [DecidableEq S.AtomicPredType] in
lemma preEq_complete
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) (st : EncState b)
    (hClauses : (addPreEqAll b st).clauses.all (SAT.Clause.eval σ) = true)
    (hDecode : histEq (decodePre b σ hWF t) (decodePre b σ hWF t')) :
    σ (Var.PreEq t t') = true := by
  revert hDecode hClauses st
  generalize hN : fuelOf b σ t + fuelOf b σ t' = n
  induction n using Nat.strong_induction_on generalizing t t' with
  | h n IH =>
    intro st hClauses hDecode
    let step := fun stCur (u : b.times) => addPreEqFrom b u stCur
    have hMem : t ∈ Bounds.timesL b := by simp [Bounds.timesL]
    obtain ⟨before, after, hSplit⟩ := exists_split_of_mem (a := t) (l := Bounds.timesL b) hMem

    -- Unfold the outer fold to isolate the iteration for `t`.
    have hSplitEq :
        addPreEqAll b st =
          after.foldl step (addPreEqFrom b t (before.foldl step st)) := by
      classical
      simp [addPreEqAll, step, hSplit, List.foldl_append]

    set stBefore := before.foldl step st
    set stAtT := addPreEqFrom b t stBefore
    set stAfter := after.foldl step stAtT

    have hClausesAfter : stAfter.clauses.all (SAT.Clause.eval σ) = true := by
      simpa [stAfter, stAtT, stBefore, step, hSplitEq] using hClauses

    -- Every step of the outer fold only adds clauses.
    have hStepSubset :
        ∀ stCur u, stCur.clauses ⊆ (step stCur u).clauses := by
      intro stCur u
      exact addPreEqFrom_clauses_subset (b := b) (H0 := u) (st := stCur)

    -- Subset chain from the initial state to the final state.
    have hSubAtT : stAtT.clauses ⊆ stAfter.clauses := by
      have h := foldl_subset_state (b := b) (f := step) (hStep := hStepSubset)
          (xs := after) (init := stAtT)
      have hFold : after.foldl step stAtT = stAfter := by
        simp [stAfter]
      simpa [hFold] using h

    have hClausesAtT : stAtT.clauses.all (SAT.Clause.eval σ) = true :=
      all_true_of_subset hSubAtT hClausesAfter

    -- Fuel IH for smaller pairs.
    have hFuelIH :
        ∀ ⦃t₁ t₂ : b.times⦄,
          fuelOf b σ t₁ + fuelOf b σ t₂ < fuelOf b σ t + fuelOf b σ t' →
          histEq (decodePre b σ hWF t₁) (decodePre b σ hWF t₂) →
          σ (Var.PreEq t₁ t₂) = true := by
      intro t₁ t₂ hLt hEq
      have hLtN : fuelOf b σ t₁ + fuelOf b σ t₂ < n := by
        rw [← hN]; exact hLt
      exact IH _ hLtN t₁ t₂ rfl st hClauses hEq

    -- Complete the isolated iteration at `t`.
    exact
      preEq_complete_from b σ hWF t stBefore hClausesAtT t' hDecode hFuelIH

end Encoding
