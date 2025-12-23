import ModalDistribution.Core.Prehistory
import ModalDistribution.Logic.SATEncoding.PreEqGadgets
import ModalDistribution.Logic.SATEncoding.AddAccumulators
import ModalDistribution.Logic.SATEncoding.Decoder

/-!
# PreEq Encoding

This file implements the PreEq encoding mechanism for witnessing prehistory equality
in the SAT-based model checker. The encoding uses obligation-based matching to ensure
that PreEq(t,t') holds iff the decoded prehistories are equal.

## Main Components

- `sameSig`/`mkY`/`mkDw`/`mkOw`: gadget definitions (see `PreEqGadgets`)
- `addPreEqPair_core`: Core PreEq encoding using bidirectional obligations
- `addPreEqPair`: Wrapper that adds reflexivity unit clauses
- `addPreEqFrom`: Encode all PreEq pairs from a fixed time index
- `preEq_sound`: PreEq(t,t') = true implies decoded prehistories equal
- `preEq_complete`: decoded prehistories equal implies PreEq(t,t') = true

## Key Properties

The obligations-based encoding avoids relying on decodePre injectivity.
Instead, it directly encodes "decoded prehistory equality" by checking that
every world in one prehistory has a matching counterpart in the other.

## References

See CLAUDE.md and the user's specification for the obligations-based approach.
-/

open ModalDistribution
open ModalDistribution.Logic
open PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Membership implies positive fuel (otherwise the decoder would return empty). -/
lemma fuel_pos_of_mem
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    {H : b.times} {w : WId b} (hMem : σ (Var.Mem H w) = true) :
    0 < fuelOf b σ H := by
  classical
  have hCNF := mem_requires_fuel_from_wf b σ hWF
  let clause :=
    [ SAT.Lit.neg (Var.Mem H w)
    , SAT.Lit.pos (Var.Level H ⟨1, Nat.succ_lt_succ b.posTimes⟩) ]
  have hAll :
      ∀ cl ∈ (cnfMemRequiresFuel b).clauses,
        SAT.Clause.eval σ cl = true := by
    have : (cnfMemRequiresFuel b).clauses.all (SAT.Clause.eval σ) = true := by
      simpa [SAT.CNF.eval] using hCNF
    exact List.all_eq_true.mp this
  have hClauseMem :
      clause ∈ (cnfMemRequiresFuel b).clauses := by
    unfold cnfMemRequiresFuel
    refine List.mem_flatMap.mpr ?_
    refine ⟨H, ?_⟩
    constructor
    · unfold Bounds.timesL
      exact List.mem_finRange H
    · refine List.mem_map.mpr ?_
      exact ⟨w, WId.mem_allWorlds b w, rfl⟩
  have hClauseEval : SAT.Clause.eval σ clause = true :=
    hAll clause hClauseMem
  have hLevel :
      σ (Var.Level H ⟨1, Nat.succ_lt_succ b.posTimes⟩) = true := by
    simpa [clause, SAT.Clause.eval, SAT.Lit.eval, List.foldl,
           hMem, Bool.not_true, Bool.false_or, Bool.or_false] using hClauseEval
  have hLe :
      1 ≤ fuelOf b σ H :=
    level_true_le_fuelOf
      (b := b)
      (σ := σ)
      (ti := H)
      (k := ⟨1, Nat.succ_lt_succ b.posTimes⟩)
      hLevel
  exact Nat.lt_of_lt_of_le (Nat.succ_pos _) hLe

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Extract process and event equality from sameSig being true. -/
lemma sameSig_eq_true_iff (b : Bounds S) (w w' : WId b) :
    sameSig b w w' = true ↔
      w'.p = w.p ∧ b.decodeMaybeEvent w'.ei = b.decodeMaybeEvent w.ei := by
  unfold sameSig
  split
  · next hp =>
    simp only [beq_iff_eq] at hp
    cases hDecode : b.decodeMaybeEvent w'.ei <;>
    cases hDecode' : b.decodeMaybeEvent w.ei <;>
    simp [hp, MaybeEvent.some.injEq]
  · next hp =>
    simp only [beq_iff_eq] at hp
    simp [hp]

/-- Helper step for folding the `(t,t')` obligations list. -/
def preEqObligationStep
    (b : Bounds S) (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b) :
    List (FVar b) × EncState b :=
  let (lst, stc) := acc
  let (d, stc) := mkDw b t' w stc
  let (o, stc) := mkOw b t w d stc
  (o :: lst, stc)

/-- Helper step for the accumulator in pre-equivalence encoding. -/
def preEqAccStep (b : Bounds S)
    (acc : FVar b × EncState b) (o : FVar b) :
    FVar b × EncState b :=
  let (cur, stc) := acc
  let (next, stc) := EncState.allocFresh b stc
  (next, addAccStep b cur next o stc)

/-- Core logic for addPreEqPair without the reflexivity unit clause.

    Encodes PreEq(t,t') as decoded prehistory equality using local obligations:
    - For each world w in t, obligation o_w checks if there's a matching w' in t'
    - For each world w' in t', obligation o'_w' checks if there's a matching w in t
    - PreEq(t,t') holds iff all obligations are satisfied -/
def addPreEqPair_core (b : Bounds S) (H0 H' : b.times) (st : EncState b) : EncState b :=
  -- Always emit the PreEq obligations; caching is disabled.
  -- Obligations for children of H0
  let (os, st1) := (WId.allWorlds b).foldl
    (preEqObligationStep b H0 H')
    ([], st)
  -- Obligations for children of H'
  let (os', st2) := (WId.allWorlds b).foldl
    (preEqObligationStep b H' H0)
    ([], st1)
  -- Chain all obligations into eqFinal
  let (base, st3) := EncState.allocFresh b st2
  let st3 := EncState.addClause b st3 [SAT.Lit.pos (FVar.toVar b base)]
  let (eqA, st4) := os.foldl
    (preEqAccStep b)
    (base, st3)
  let (eqFinal, st5) := os'.foldl
    (preEqAccStep b)
    (eqA, st4)
  -- Expose ↔ with no memoization
  addPreEqExpose b H0 H' eqFinal st5

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Helper lemma: mkDw in the non-empty case returns mkBigOrIff of the foldl result -/
lemma mkDw_cons_eq (b : Bounds S)
    (t' : b.times) (w : WId b) (st : EncState b)
    (cand : WId b) (cands : List (WId b))
    (hCands : (WId.allWorlds b).filter (fun w' => sameSig b w w') = cand :: cands) :
    mkDw b t' w st =
      let (ys, st1) := (cand :: cands).foldl
        (fun (acc : List (Var b) × EncState b) w' =>
          let (vs, st') := acc
          let (y, st'') := mkY b t' w w' st'
          (FVar.toVar b y :: vs, st''))
        ([], st)
      mkBigOrIff b ys st1 := by
  unfold mkDw
  simp [hCands]

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_clauses_subset (b : Bounds S)
    (t' : b.times) (w : WId b) (st : EncState b) :
    st.clauses ⊆ (mkDw b t' w st).2.clauses := by
  classical
  intro clause hClause
  cases hCands :
      (WId.allWorlds b).filter (fun w' => sameSig b w w') with
  | nil =>
      -- Empty filter case: mkDw allocates d and adds [¬d]
      unfold mkDw
      simp only [hCands]
      cases hAlloc : EncState.allocFresh b st with
      | mk d st1 =>
          have hAllocEq :
              st1.clauses = st.clauses := by
            simpa [hAlloc] using
              (EncState.allocFresh_clauses_eq (b := b) (st := st))
          have hClause' : clause ∈ st1.clauses := by
            simpa [hAllocEq] using hClause
          have hSubset :=
            EncState.addClause_subset_clauses
              (b := b)
              (st := st1)
              (clause := [SAT.Lit.neg (FVar.toVar b d)])
          have hRes := hSubset hClause'
          simpa [hAlloc] using hRes
  | cons cand cands =>
      -- Non-empty case: use helper lemma
      have hEq := mkDw_cons_eq (b := b) (t' := t') (w := w) (st := st)
        (cand := cand) (cands := cands) hCands
      rw [hEq]
      -- Now we need to show clause ∈ (mkBigOrIff b ys st1).2.clauses
      -- where (ys, st1) = foldl ...
      let step :
          List (Var b) × EncState b → WId b →
            List (Var b) × EncState b :=
        fun acc w' =>
          let (vs, st') := acc
          let (y, st'') := mkY b t' w w' st'
          (FVar.toVar b y :: vs, st'')
      have hStep :
          ∀ acc w', acc.2.clauses ⊆ (step acc w').2.clauses := by
        intro acc w'
        rcases acc with ⟨vs, st'⟩
        change st'.clauses ⊆ (mkY b t' w w' st').2.clauses
        exact mkY_clauses_subset (t' := t') (w := w) (w' := w') (st := st')
      cases hFold :
          (cand :: cands).foldl step ([], st) with
      | mk ys st1 =>
          have hFoldSubset :
              st.clauses ⊆ st1.clauses := by
            have hResult :=
              foldl_subset_snd
                (b := b)
                (f := step)
                (hStep := hStep)
                (xs := cand :: cands)
                (init := ([], st))
            simpa [step, hFold] using hResult
          have hFinal :=
            mkBigOrIff_clauses_subset (b := b) (vs := ys) (st := st1)
          have hClause₁ := hFoldSubset hClause
          exact hFinal hClause₁

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
def mkDwStepVar (b : Bounds S) (t' : b.times) (w : WId b)
    (acc : List (Var b) × EncState b) (w' : WId b) :
    List (Var b) × EncState b :=
  let (vs, st') := acc
  let (y, st'') := mkY b t' w w' st'
  (FVar.toVar b y :: vs, st'')

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
def mkDwStepPair (b : Bounds S) (t' : b.times) (w : WId b)
    (acc : List (FVar b × EncState b × WId b) × EncState b) (w' : WId b) :
    List (FVar b × EncState b × WId b) × EncState b :=
  let (lst, st') := acc
  let (y, st'') := mkY b t' w w' st'
  ((y, st', w') :: lst, st'')

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkDwStepVar_subset (b : Bounds S) (t' : b.times) (w : WId b)
    (acc : List (Var b) × EncState b) (cand : WId b) :
    acc.2.clauses ⊆ (mkDwStepVar b t' w acc cand).2.clauses := by
  classical
  rcases acc with ⟨vs, st⟩
  unfold mkDwStepVar
  cases hMk : mkY b t' w cand st with
  | mk y st' =>
      simpa [hMk]
        using mkY_clauses_subset (b := b) (t' := t') (w := w) (w' := cand) (st := st)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Auxiliary fold lemma: starting from aligned accumulators, folding over the candidate
    list preserves the alignment between the Tseytin variable list and the recorded
    `(FVar, state, world)` triples. -/
lemma mkDw_fold_pairs_aux
    (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b))
    (vsAcc : List (Var b))
    (pairsAcc : List (FVar b × EncState b × WId b))
    (st : EncState b)
    (hAcc :
      vsAcc = pairsAcc.map (fun triple => FVar.toVar b triple.1)) :
    (cands.foldl (mkDwStepVar b t' w) (vsAcc, st)).1 =
        (cands.foldl (mkDwStepPair b t' w) (pairsAcc, st)).1.map
          (fun triple => FVar.toVar b triple.1) ∧
    (cands.foldl (mkDwStepVar b t' w) (vsAcc, st)).2 =
        (cands.foldl (mkDwStepPair b t' w) (pairsAcc, st)).2 := by
  classical
  revert vsAcc pairsAcc st hAcc
  refine List.recOn cands ?base ?step
  · intro vsAcc pairsAcc st hAcc
    simp [hAcc]
  · intro wHead cands ih vsAcc pairsAcc st hAcc
    cases hMk : mkY b t' w wHead st with
    | mk y st' =>
        have hAcc' :
            FVar.toVar b y :: vsAcc =
              ((y, st, wHead) :: pairsAcc).map
                (fun triple => FVar.toVar b triple.1) := by
          simp [hAcc]
        have hIH :=
          ih (FVar.toVar b y :: vsAcc) ((y, st, wHead) :: pairsAcc) st' hAcc'
        rcases hIH with ⟨hVars, hState⟩
        constructor
        · simp [List.foldl_cons, mkDwStepVar, mkDwStepPair, hMk, hVars]
        · simp [List.foldl_cons, mkDwStepVar, mkDwStepPair, hMk, hState]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Auxiliary fold that records, for every candidate world, the fresh Tseytin variable
    allocated by `mkY` together with the state at which it was introduced.  Its first
    component maps to the list of witness variables used by `mkDw`. -/
lemma mkDw_fold_pairs
    (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b))
    (st : EncState b) :
    (cands.foldl (mkDwStepVar b t' w) ([], st)).1 =
        (cands.foldl (mkDwStepPair b t' w) ([], st)).1.map
          (fun triple => FVar.toVar b triple.1) ∧
    (cands.foldl (mkDwStepVar b t' w) ([], st)).2 =
        (cands.foldl (mkDwStepPair b t' w) ([], st)).2 := by
  simpa using
    (mkDw_fold_pairs_aux
      (b := b) (t' := t') (w := w)
      (cands := cands)
      (vsAcc := []) (pairsAcc := []) (st := st)
      (hAcc := rfl))

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Every triple tracked by `mkDwStepPair` originates from one of the processed worlds. -/
lemma mkDwStepPair_mem_world_aux
    (b : Bounds S) (t' : b.times) (w : WId b) :
    ∀ (cands : List (WId b)) (accWorlds : List (WId b))
      (accPairs : List (FVar b × EncState b × WId b)) (st : EncState b),
      (∀ triple ∈ accPairs, triple.2.2 ∈ accWorlds) →
      ∀ {triple},
        triple ∈ (cands.foldl (mkDwStepPair b t' w) (accPairs, st)).1 →
        triple.2.2 ∈ accWorlds ++ cands := by
  classical
  intro cands
  induction cands with
  | nil =>
      intro accWorlds accPairs st hAcc triple hMem
      simpa [mkDwStepPair] using hAcc triple hMem
  | cons wHead cands ih =>
      intro accWorlds accPairs st hAcc triple hMem
      unfold List.foldl at hMem
      cases hMk : mkY b t' w wHead st with
      | mk y st' =>
          have hMem' :
              triple ∈
                (cands.foldl (mkDwStepPair b t' w)
                  ((y, st, wHead) :: accPairs, st')).1 := by
            simpa [mkDwStepPair, hMk] using hMem
          have hAcc' :
              ∀ triple ∈ (y, st, wHead) :: accPairs,
                triple.2.2 ∈ accWorlds ++ [wHead] := by
            intro triple hTriple
            have hSplit :
                triple = (y, st, wHead) ∨ triple ∈ accPairs := by
              simpa [List.mem_cons] using hTriple
            cases hSplit with
            | inl hEq =>
                cases hEq
                exact (List.mem_append).2 (Or.inr (by simp))
            | inr hTail =>
                have hOld := hAcc triple hTail
                exact (List.mem_append).2 (Or.inl hOld)
          have hResult :=
            ih (accWorlds ++ [wHead]) ((y, st, wHead) :: accPairs) st' hAcc'
              (triple := triple) hMem'
          simpa [List.append_assoc] using hResult

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkDwStepPair_mem_world (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st : EncState b)
    {triple : FVar b × EncState b × WId b}
    (hMem : triple ∈ (cands.foldl (mkDwStepPair b t' w) ([], st)).1) :
    triple.2.2 ∈ cands := by
  have h :=
    mkDwStepPair_mem_world_aux
      (b := b) (t' := t') (w := w)
      cands
      ([] : List (WId b))
      ([] : List (FVar b × EncState b × WId b)) st
      (by intro triple h; cases h)
      (triple := triple) hMem
  simpa using h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The fold operation preserves accumulator elements: any element in the initial
    accumulator will remain in the final accumulator after folding. -/
lemma mkDwStepPair_fold_preserves_acc
    (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (acc : List (FVar b × EncState b × WId b)) (st : EncState b)
    {triple : FVar b × EncState b × WId b}
    (hMem : triple ∈ acc) :
    triple ∈ (cands.foldl (mkDwStepPair b t' w) (acc, st)).1 := by
  classical
  revert acc st
  induction cands with
  | nil =>
      intro acc st hMem
      simp [List.foldl]
      exact hMem
  | cons wHead cands ih =>
      intro acc st hMem
      simp only [List.foldl_cons]
      cases hMk : mkY b t' w wHead st with
      | mk y stNew =>
          have hMemExt : triple ∈ (y, st, wHead) :: acc := by
            simp [hMem]
          have hStep : mkDwStepPair b t' w (acc, st) wHead = ((y, st, wHead) :: acc, stNew) := by
            simp [mkDwStepPair, hMk]
          rw [hStep]
          exact ih ((y, st, wHead) :: acc) stNew hMemExt

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Elements produced during folding are independent of the starting accumulator:
    if an element appears when folding from a given accumulator, it also appears
    when folding from an extended accumulator. -/
lemma mkDwStepPair_fold_mem_monotone
    (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (acc1 acc2 : List (FVar b × EncState b × WId b)) (st : EncState b)
    {triple : FVar b × EncState b × WId b}
    (hMem : triple ∈ (cands.foldl (mkDwStepPair b t' w) (acc1, st)).1) :
    triple ∈ (cands.foldl (mkDwStepPair b t' w) (acc1 ++ acc2, st)).1 := by
  classical
  revert acc1 acc2 st triple
  induction cands with
  | nil =>
      intro acc1 acc2 st triple hMem
      simp [List.foldl, List.mem_append] at hMem ⊢
      exact Or.inl hMem
  | cons wHead cands ih =>
      intro acc1 acc2 st triple hMem
      simp only [List.foldl_cons] at hMem ⊢
      cases hMk : mkY b t' w wHead st with
      | mk y stNew =>
          have hStep1 : mkDwStepPair b t' w (acc1, st) wHead = ((y, st, wHead) :: acc1, stNew) := by
            simp [mkDwStepPair, hMk]
          have hStep2 : mkDwStepPair b t' w (acc1 ++ acc2, st) wHead =
              ((y, st, wHead) :: (acc1 ++ acc2), stNew) := by
            simp [mkDwStepPair, hMk]
          rw [hStep1] at hMem
          rw [hStep2]
          -- Apply IH: since triple ∈ fold from ((y, st, wHead) :: acc1),
          -- it's also in fold from ((y, st, wHead) :: acc1 ++ acc2)
          exact @ih ((y, st, wHead) :: acc1) acc2 stNew triple hMem

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: if an element is in the fold result but not in the initial accumulator,
    then it must be in the fold result starting from empty accumulator. -/
lemma mkDwStepPair_fold_mem_split
    (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (acc : List (FVar b × EncState b × WId b)) (st : EncState b)
    {triple : FVar b × EncState b × WId b}
    (hMem : triple ∈ (cands.foldl (mkDwStepPair b t' w) (acc, st)).1)
    (hNotAcc : triple ∉ acc) :
    triple ∈ (cands.foldl (mkDwStepPair b t' w) ([], st)).1 := by
  classical
  revert acc st triple
  induction cands with
  | nil =>
      intro acc st triple hMem hNotAcc
      simp [List.foldl] at hMem
      exact absurd hMem hNotAcc
  | cons wHead cands ih =>
      intro acc st triple hMem hNotAcc
      simp only [List.foldl_cons] at hMem ⊢
      cases hMk : mkY b t' w wHead st with
      | mk y stNew =>
          have hStep : mkDwStepPair b t' w (acc, st) wHead = ((y, st, wHead) :: acc, stNew) := by
            simp [mkDwStepPair, hMk]
          rw [hStep] at hMem
          have hMem' :
              triple ∈
                (cands.foldl (mkDwStepPair b t' w) ((y, st, wHead) :: acc, stNew)).1 :=
            hMem
          by_cases hHead : triple = (y, st, wHead)
          · -- triple is the newly added element
            cases hHead
            -- Show (y, st, wHead) is in fold from empty starting with this element
            have hEmptyStep : mkDwStepPair b t' w ([], st) wHead = ([(y, st, wHead)], stNew) := by
              simp [mkDwStepPair, hMk]
            rw [hEmptyStep]
            apply mkDwStepPair_fold_preserves_acc
            simp
          · -- triple is not the newly added element, so apply IH
            have hNotExtended : triple ∉ (y, st, wHead) :: acc := by
              simp [hHead, hNotAcc]
            have hFromEmpty : triple ∈ (cands.foldl (mkDwStepPair b t' w) ([], stNew)).1 :=
              ih ((y, st, wHead) :: acc) stNew hMem' hNotExtended
            -- Use monotonicity to lift from empty to singleton accumulator
            have hEmptyStep : mkDwStepPair b t' w ([], st) wHead = ([(y, st, wHead)], stNew) := by
              simp [mkDwStepPair, hMk]
            rw [hEmptyStep]
            have hSing : [(y, st, wHead)] = [] ++ [(y, st, wHead)] := by simp
            rw [hSing]
            exact mkDwStepPair_fold_mem_monotone b t' w cands [] [(y, st, wHead)] stNew hFromEmpty

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- For any triple produced by mkDwStepPair fold, the first component equals
    the Y variable that would be produced by calling mkY with the corresponding
    world and state from the triple. This is true by construction of mkDwStepPair. -/
lemma mkDwStepPair_fst_eq_mkY_fst
    (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st : EncState b)
    {triple : FVar b × EncState b × WId b}
    (hMem : triple ∈ (cands.foldl (mkDwStepPair b t' w) ([], st)).1) :
    triple.1 = (mkY b t' w triple.2.2 triple.2.1).1 := by
  classical
  revert triple
  induction cands generalizing st with
  | nil =>
      intro triple hMem
      simp [List.foldl] at hMem
  | cons wHead cands ih =>
      intro triple hMem
      simp only [List.foldl_cons] at hMem
      cases hMk : mkY b t' w wHead st with
      | mk y stAfterY =>
          have hMem' :
              triple ∈
                (cands.foldl (mkDwStepPair b t' w)
                  ([(y, st, wHead)], stAfterY)).1 := by
            simpa [mkDwStepPair, hMk] using hMem
          -- The fold with accumulator [(y, st, wHead)] means triple is either:
          -- 1. From the initial accumulator: triple = (y, st, wHead)
          -- 2. From processing cands: triple ∈ (fold on cands from [])
          by_cases hEq : triple = (y, st, wHead)
          · -- Case 1: triple is the head element
            cases hEq
            -- Need to show y = (mkY b t' w wHead st).1
            simp [hMk]
          · -- Case 2: triple is from the recursive fold
            have hTail :
                triple ∈ (cands.foldl (mkDwStepPair b t' w) ([], stAfterY)).1 := by
              exact mkDwStepPair_fold_mem_split b t' w cands [(y, st, wHead)]
                stAfterY hMem' (by simp [hEq])
            exact @ih stAfterY triple hTail

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkDwStepPair_preserves_mkY_clauses_aux
    (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b))
    (pairsAcc : List (FVar b × EncState b × WId b))
    (st : EncState b)
    (hAcc :
      ∀ triple ∈ pairsAcc,
        (mkY b t' w triple.2.2 triple.2.1).2.clauses ⊆ st.clauses)
    {triple : FVar b × EncState b × WId b}
    (hMem :
      triple ∈ (cands.foldl (mkDwStepPair b t' w) (pairsAcc, st)).1) :
    (mkY b t' w triple.2.2 triple.2.1).2.clauses ⊆
      (cands.foldl (mkDwStepPair b t' w) (pairsAcc, st)).2.clauses := by
  classical
  revert pairsAcc st hAcc triple hMem
  refine List.recOn cands ?base ?step
  · -- Base case: empty candidate list
    intro pairsAcc st hAcc triple hMem
    simp [List.foldl] at hMem
    have hSubset := hAcc triple hMem
    simp [List.foldl]
    exact hSubset
  · -- Inductive case: wHead :: cands
    intro wHead cands ih pairsAcc st hAcc triple hTripleMem
    -- Unfold one step of the fold
    simp only [List.foldl_cons] at hTripleMem
    cases hMk : mkY b t' w wHead st with
    | mk y stAfterY =>
        -- Show st.clauses ⊆ stAfterY.clauses (by mkY_clauses_subset)
        have hStep : st.clauses ⊆ stAfterY.clauses := by
          simpa [hMk] using
            mkY_clauses_subset (b := b) (t' := t') (w := w) (w' := wHead) (st := st)
        -- Build the updated accumulator invariant
        have hAcc' :
            ∀ triple' ∈ (y, st, wHead) :: pairsAcc,
              (mkY b t' w triple'.2.2 triple'.2.1).2.clauses ⊆ stAfterY.clauses := by
          intro triple' hTriple'
          cases hTriple' with
          | head =>
              -- triple' = (y, st, wHead), so its mkY clauses are in stAfterY
              simp [hMk]
          | tail _ hTail =>
              -- triple' ∈ pairsAcc, use old invariant and transitivity
              have hOld := hAcc triple' hTail
              exact List.Subset.trans hOld hStep
        -- After mkDwStepPair, we fold with the extended accumulator
        have hMem' :
            triple ∈
              (cands.foldl (mkDwStepPair b t' w)
                ((y, st, wHead) :: pairsAcc, stAfterY)).1 := by
          simpa [mkDwStepPair, hMk] using hTripleMem
        -- Apply IH with explicit triple argument
        have hIH := @ih ((y, st, wHead) :: pairsAcc) stAfterY hAcc' triple hMem'
        -- The result state is also updated
        simp only [List.foldl_cons, mkDwStepPair, hMk]
        exact hIH

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- For any triple in the fold result, the clauses from the corresponding mkY call
    are preserved in the final fold state.

    **Proof strategy**: Induction on the candidate list:
    - Base case: vacuous (empty fold has no triples)
    - Inductive case: Show clauses from `mkY b t' w wHead st` are preserved
      by using `mkY_clauses_subset` for monotonicity and applying IH -/
lemma mkDwStepPair_preserves_mkY_clauses
    (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st : EncState b)
    {triple : FVar b × EncState b × WId b}
    (hMem : triple ∈ (cands.foldl (mkDwStepPair b t' w) ([], st)).1) :
    (mkY b t' w triple.2.2 triple.2.1).2.clauses ⊆
      (cands.foldl (mkDwStepPair b t' w) ([], st)).2.clauses := by
  classical
  have hAcc :
      ∀ triple ∈ ([] : List (FVar b × EncState b × WId b)),
        (mkY b t' w triple.2.2 triple.2.1).2.clauses ⊆ st.clauses := by
    intro triple hTriple
    cases hTriple
  have hSubset :=
    mkDwStepPair_preserves_mkY_clauses_aux
      (b := b) (t' := t') (w := w)
      (cands := cands)
      (pairsAcc := []) (st := st) hAcc
      (triple := triple) hMem
  simpa using hSubset

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- High-level lemma combining clause preservation and satisfaction for mkDw.

    If a triple is in the fold result and all final mkDw clauses are satisfied,
    then the mkY clauses for that triple are also satisfied. This directly
    supports applying `mkY_adequate_forward`.

    **Proof strategy**: Chain together:
    1. `mkDwStepPair_preserves_mkY_clauses`: mkY clauses in fold result
    2. Relate fold result to mkBigOrIff via `mkDw_fold_pairs`
    3. `mkBigOrIff_clauses_subset`: fold clauses in final state
    4. Use `hClauses` to show all final clauses satisfied -/
lemma mkDw_satisfies_mkY_clauses
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t' : b.times) (w : WId b) (st : EncState b)
    (w0 : WId b) (ws : List (WId b))
    (hFilterEq : (WId.allWorlds b).filter (fun w' => sameSig b w w') = w0 :: ws)
    (hClauses : (mkDw b t' w st).2.clauses.all (SAT.Clause.eval σ) = true)
    {triple : FVar b × EncState b × WId b}
    (hTriMem : triple ∈ ((w0 :: ws).foldl (mkDwStepPair b t' w) ([], st)).1) :
    (mkY b t' w triple.2.2 triple.2.1).2.clauses.all (SAT.Clause.eval σ) = true := by
  classical
  cases hFold :
      ((w0 :: ws).foldl (mkDwStepVar b t' w) ([], st)) with
  | mk ys st1 =>
      -- Extract that the mkDwStepVar fold produces st1
      have hVarState :
          ((w0 :: ws).foldl (mkDwStepVar b t' w) ([], st)).2 = st1 := by
        simpa using congrArg Prod.snd hFold
      -- Get the relationship between mkDwStepVar and mkDwStepPair folds
      obtain ⟨_, hStateEq⟩ :=
        mkDw_fold_pairs
          (b := b) (t' := t') (w := w)
          (cands := w0 :: ws) (st := st)
      -- Combine to show mkDwStepPair fold also produces st1
      have hPairState :
          ((w0 :: ws).foldl (mkDwStepPair b t' w) ([], st)).2 = st1 := by
        rw [← hVarState]
        exact hStateEq.symm
      -- mkY clauses are in the fold result (by mkDwStepPair_preserves_mkY_clauses)
      have hSubsetFold :
          (mkY b t' w triple.2.2 triple.2.1).2.clauses ⊆ st1.clauses := by
        have h :=
          mkDwStepPair_preserves_mkY_clauses
            (b := b) (t' := t') (w := w)
            (cands := w0 :: ws) (st := st)
            (triple := triple) hTriMem
        rw [hPairState] at h
        exact h
      -- st1 clauses are in mkBigOrIff result
      have hSubsetFinal :
          (mkY b t' w triple.2.2 triple.2.1).2.clauses ⊆
            (mkBigOrIff b ys st1).2.clauses := by
        refine List.Subset.trans hSubsetFold ?_
        exact mkBigOrIff_clauses_subset (b := b) (vs := ys) (st := st1)
      -- mkBigOrIff b ys st1 is what mkDw returns (by definition with filter equation)
      have hClausesFinal :
          (mkBigOrIff b ys st1).2.clauses.all (SAT.Clause.eval σ) = true := by
        -- mkDw expands to mkBigOrIff when the filter is non-empty
        -- and the fold produces (ys, st1)
        have hMkDwEq : (mkDw b t' w st).2 = (mkBigOrIff b ys st1).2 := by
          show (mkDw b t' w st).2 = (mkBigOrIff b ys st1).2
          -- Unfold mkDw and substitute the filter equation
          have : mkDw b t' w st =
              (let cands := w0 :: ws
               let (ys', st1') := cands.foldl (mkDwStepVar b t' w) ([], st)
               mkBigOrIff b ys' st1') := by
            simp only [mkDw, hFilterEq]
            rfl
          rw [this]
          -- The fold produces (ys, st1)
          simp only [hFold]
        rw [← hMkDwEq]
        exact hClauses
      exact all_true_of_subset hSubsetFinal hClausesFinal

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- If `mkDw` returns a true witness variable, then the candidate list cannot be
    empty (otherwise `[¬d]` would force the variable to be false). -/
lemma mkDw_candidates_nonempty_of_true (b : Bounds S)
    (σ : SAT.Assignment (Var b)) (t' : b.times) (w : WId b) (st : EncState b)
    (hClauses : (mkDw b t' w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hDw : σ (FVar.toVar b (mkDw b t' w st).1) = true) :
    (WId.allWorlds b).filter (fun w' => sameSig b w w') ≠ [] := by
  classical
  intro hEmpty
  unfold mkDw at hClauses hDw
  cases hAlloc : EncState.allocFresh b st with
  | mk d st1 =>
      -- When the candidate list is empty, mkDw adds the clause [¬d]
      simp [hEmpty, hAlloc] at hDw hClauses
      have hAll := hClauses
      have hClauseMem : [SAT.Lit.neg (FVar.toVar b d)] ∈
          (EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b d)]).clauses := by
        simp [EncState.addClause]
      have hClauseEval := hAll _ hClauseMem
      -- The clause `[¬d]` forces `σ d = false`, contradicting hDw
      have : False := by
        simp [List.foldl, hDw, Bool.not_true] at hClauseEval
      exact this.elim

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Forward direction for `mkDw`: if the disjunction variable is true, then some witness
    world produced by the candidate list satisfies both the `Mem` and `PreEq` literals
    guarded by the corresponding `mkY` gadget.  This isolates the purely disjunctive
    reasoning needed later for PreEq correctness. -/
lemma mkDw_adequate_forward (b : Bounds S)
    (σ : SAT.Assignment (Var b)) (t' : b.times) (w : WId b) (st : EncState b)
    (hClauses : (mkDw b t' w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hDw : σ (FVar.toVar b (mkDw b t' w st).1) = true) :
    ∃ w' : WId b,
      w' ∈ WId.allWorlds b ∧
        sameSig b w w' = true ∧
        σ (Var.Mem t' w') = true ∧
        σ (Var.PreEq w.ti w'.ti) = true := by
  classical
  set cands :=
      (WId.allWorlds b).filter (fun w' => sameSig b w w') with hCands
  have hNonEmpty :
      cands ≠ [] := by
    have h :=
      mkDw_candidates_nonempty_of_true
        (b := b) (σ := σ) (t' := t') (w := w) (st := st)
        (hClauses := hClauses) (hDw := hDw)
    simpa [hCands] using h
  -- Save the original hClauses for mkDw_satisfies_mkY_clauses
  have hClausesOrig : (mkDw b t' w st).2.clauses.all (SAT.Clause.eval σ) = true := hClauses
  unfold mkDw at hClauses hDw
  cases hCandsList : cands with
  | nil =>
      exact False.elim (hNonEmpty hCandsList)
  | cons w0 ws =>
      have hCandsEq : cands = w0 :: ws := hCandsList
      -- Rewrite using the filter equation
      have hFilterEq : (WId.allWorlds b).filter (fun w' => sameSig b w w') = w0 :: ws := by
        rw [← hCands, hCandsEq]
      -- mkDw in the cons case returns mkBigOrIff of the fold result
      rw [hFilterEq] at hClauses hDw
      cases hFold :
          (List.foldl
            (fun (acc : List (Var b) × EncState b) w' =>
              let (vs, st') := acc
              let (y, st'') := mkY b t' w w' st'
              (FVar.toVar b y :: vs, st''))
            ([], st) (w0 :: ws)) with
      | mk ys st1 =>
          -- Now hClauses and hDw are about mkBigOrIff since mkDw = mkBigOrIff in this case
          simp only [hFold] at hClauses hDw
          obtain ⟨v, hvMem, hvTrue⟩ :=
            mkBigOrIff_exists_true
              (b := b) (vs := ys) (st := st1)
              (σ := σ) hClauses hDw
          obtain ⟨hVarsEq₀, _⟩ :=
            mkDw_fold_pairs
              (b := b) (t' := t') (w := w)
              (cands := w0 :: ws) (st := st)
          have hVarsEq :
              ys =
                ((w0 :: ws).foldl (mkDwStepPair b t' w) ([], st)).1.map
                  (fun triple => FVar.toVar b triple.1) := by
            -- Extract the equation that ys equals the first component of the fold
            -- by using congruence on hFold
            conv_lhs => rw [← (show (ys, st1).1 = ys from rfl)]
            rw [← hFold]
            exact hVarsEq₀
          have hMemMap :
              v ∈ ((w0 :: ws).foldl (mkDwStepPair b t' w) ([], st)).1.map
                (fun triple => FVar.toVar b triple.1) := by
            rw [← hVarsEq]
            exact hvMem
          obtain ⟨triple, hTripleMem, hVarEq⟩ :=
            List.mem_map.1 hMemMap
          have hTriMem :
              triple ∈
                ((w0 :: ws).foldl (mkDwStepPair b t' w) ([], st)).1 := by
            exact hTripleMem
          have hWorldMem :
              triple.2.2 ∈ w0 :: ws := by
            exact
              (mkDwStepPair_mem_world
                (b := b) (t' := t') (w := w)
                (cands := w0 :: ws) (st := st)
                (triple := triple) hTriMem)
          have hFilterMem :
              triple.2.2 ∈
                (WId.allWorlds b).filter
                  (fun w' => sameSig b w w') := by
            -- w0 :: ws is the filtered list
            rw [hFilterEq]
            exact hWorldMem
          have hInAllWorlds :
              triple.2.2 ∈ WId.allWorlds b := by
            exact (List.mem_filter.mp hFilterMem).1
          have hSameSig :
              sameSig b w triple.2.2 = true := by
            exact (List.mem_filter.mp hFilterMem).2
          have hYTrue :
              σ (FVar.toVar b triple.1) = true := by
            simpa [hVarEq] using hvTrue
          -- Use the high-level clause tracking lemma to get mkY clauses satisfied
          have hMkYClauses : (mkY b t' w triple.2.2 triple.2.1).2.clauses.all
              (SAT.Clause.eval σ) = true :=
            mkDw_satisfies_mkY_clauses b σ t' w st w0 ws hFilterEq hClausesOrig hTriMem
          -- Now apply mkY_adequate_forward to extract both Mem and PreEq
          -- We need to show (mkY ...).1 equals triple.1
          -- This holds by mkDwStepPair_fst_eq_mkY_fst
          have hYEq : triple.1 = (mkY b t' w triple.2.2 triple.2.1).1 := by
            exact mkDwStepPair_fst_eq_mkY_fst
              (b := b) (t' := t') (w := w)
              (cands := w0 :: ws) (st := st)
              (hMem := hTriMem)
          have hMemPreEq := mkY_adequate_forward
            (b := b) (σ := σ) (t' := t') (w := w) (w' := triple.2.2) (st := triple.2.1)
            (hClauses := hMkYClauses)
            (hY := by
              rw [← hYEq]
              exact hYTrue)
          refine ⟨triple.2.2, hInAllWorlds, hSameSig, hMemPreEq.1, hMemPreEq.2⟩

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Combine the truth of an `mkOw` literal with the corresponding `mkDw`
    clauses to obtain a matching witness world. -/
lemma mkOw_mkDw_match
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t t' : b.times) (w : WId b) (st : EncState b)
    (hDwClauses :
      (mkDw b t' w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hOwClauses :
      (mkOw b t w (mkDw b t' w st).1 (mkDw b t' w st).2).2.clauses.all
        (SAT.Clause.eval σ) = true)
    (hOwTrue :
      σ
        (FVar.toVar b
          (mkOw b t w (mkDw b t' w st).1 (mkDw b t' w st).2).1) = true)
    (hMem : σ (Var.Mem t w) = true) :
    ∃ w' : WId b,
      w'.p = w.p ∧
        b.decodeMaybeEvent w'.ei = b.decodeMaybeEvent w.ei ∧
        σ (Var.Mem t' w') = true ∧
        σ (Var.PreEq w.ti w'.ti) = true := by
  classical
  cases hDw : mkDw b t' w st with
  | mk d stDw =>
      have hDwClauses' :
          stDw.clauses.all (SAT.Clause.eval σ) = true := by
        have : (mkDw b t' w st).2 = stDw := by rw [hDw]
        rw [← this]
        exact hDwClauses
      cases hOw : mkOw b t w d stDw with
      | mk o stOw =>
          have hOwClauses' :
              stOw.clauses.all (SAT.Clause.eval σ) = true := by
            have h1 : (mkDw b t' w st).1 = d := by rw [hDw]
            have h2 : (mkDw b t' w st).2 = stDw := by rw [hDw]
            have : (mkOw b t w (mkDw b t' w st).1 (mkDw b t' w st).2).2 = stOw := by
              rw [h1, h2, hOw]
            rw [← this]
            exact hOwClauses
          have hOwTrue' :
              σ (FVar.toVar b o) = true := by
            have h1 : (mkDw b t' w st).1 = d := by rw [hDw]
            have h2 : (mkDw b t' w st).2 = stDw := by rw [hDw]
            have : (mkOw b t w (mkDw b t' w st).1 (mkDw b t' w st).2).1 = o := by
              rw [h1, h2, hOw]
            rw [← this]
            exact hOwTrue
          have hDwTrue :
              σ (FVar.toVar b d) = true :=
            mkOw_adequate_forward
              (b := b) (σ := σ) (t := t) (w := w) (d := d) (st := stDw)
              (hClauses := by
                have : (mkOw b t w d stDw).2 = stOw := by rw [hOw]
                rw [this]
                exact hOwClauses')
              (hOw := by
                have : (mkOw b t w d stDw).1 = o := by rw [hOw]
                rw [this]
                exact hOwTrue')
              (hMem := hMem)
          obtain ⟨w', hMemAll, hSig, hMem', hPreEq⟩ :=
            mkDw_adequate_forward
              (b := b) (σ := σ) (t' := t') (w := w) (st := st)
              (hClauses := by
                have : (mkDw b t' w st).2 = stDw := by rw [hDw]
                rw [this]
                exact hDwClauses')
              (hDw := by
                have : (mkDw b t' w st).1 = d := by rw [hDw]
                rw [this]
                exact hDwTrue)
          obtain ⟨hp, heq⟩ := sameSig_true_iff (b := b) (w := w) (w' := w') hSig
          exact ⟨w', hp, heq, hMem', hPreEq⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in

/-- Add PreEq pair with reflexivity unit clause for self-pairs -/
def addPreEqPair (b : Bounds S) (H0 H' : b.times) (st : EncState b) : EncState b :=
  let stCore := addPreEqPair_core b H0 H' st
  if H0 = H' then
    EncState.addClause b stCore [SAT.Lit.pos (Var.PreEq H0 H')]
  else
    stCore

/-- Ensure all pairs `(H0, H')` with fixed `H0` have their PreEq clauses emitted. -/
def addPreEqFrom (b : Bounds S) (H0 : b.times) (st : EncState b) : EncState b :=
  (Bounds.timesL b).foldl (fun acc H' => addPreEqPair b H0 H' acc) st

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma preEqObligationStep_clauses_subset
    (b : Bounds S) (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b) :
    acc.2.clauses ⊆ (preEqObligationStep b t t' acc w).2.clauses := by
  classical
  rcases acc with ⟨lst, stc⟩
  unfold preEqObligationStep
  cases hDw : mkDw b t' w stc with
  | mk d stDw =>
      cases hOw : mkOw b t w d stDw with
      | mk o stOw =>
          simp only [hDw, hOw]
          intro clause hClause
          have hSubsetDw :
              stc.clauses ⊆ stDw.clauses := by
            simpa [hDw] using
              (mkDw_clauses_subset (b := b) (t' := t') (w := w) (st := stc))
          have hSubsetOw :
              stDw.clauses ⊆ stOw.clauses := by
            simpa [hOw] using
              (mkOw_clauses_subset (b := b) (t := t) (w := w) (d := d) (st := stDw))
          exact hSubsetOw (hSubsetDw hClause)

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma addPreEqPair_core_clauses_subset (b : Bounds S) (H0 H' : b.times)
    (st : EncState b) :
    st.clauses ⊆ (addPreEqPair_core b H0 H' st).clauses := by
  classical
  intro clause hClause
  simp [addPreEqPair_core]
  -- New obligations branch
  let step₁ := preEqObligationStep b H0 H'
  have hStep₁ :
      ∀ acc w, acc.2.clauses ⊆ (step₁ acc w).2.clauses := by
    intro acc w
    exact preEqObligationStep_clauses_subset b H0 H' acc w
  cases hFold1 :
      (WId.allWorlds b).foldl step₁ ([], st) with
  | mk os st1 =>
    let step₂ := preEqObligationStep b H' H0
    have hStep₂ :
        ∀ acc w', acc.2.clauses ⊆ (step₂ acc w').2.clauses := by
      intro acc w'
      exact preEqObligationStep_clauses_subset b H' H0 acc w'
    cases hFold2 :
        (WId.allWorlds b).foldl step₂ ([], st1) with
    | mk os' st2 =>
      cases hAllocBase : EncState.allocFresh b st2 with
      | mk base st3₀ =>
        let st3 :=
          EncState.addClause b st3₀ [SAT.Lit.pos (FVar.toVar b base)]
        let chainStep := preEqAccStep b
        have hChainStep :
            ∀ acc o, acc.2.clauses ⊆ (chainStep acc o).2.clauses := by
          intro acc o
          rcases acc with ⟨cur, stc⟩
          cases hAlloc' : EncState.allocFresh b stc with
          | mk next stc' =>
            have hAllocEq :
                stc'.clauses = stc.clauses := by
              simpa [hAlloc'] using
                (EncState.allocFresh_clauses_eq (b := b) (st := stc))
            intro clause hClauseAcc
            have hClauseAlloc : clause ∈ stc'.clauses := by
              simpa [hAllocEq] using hClauseAcc
            have hAdd :=
              addAccStep_clauses_subset
                (b := b)
                (cur := cur)
                (next := next)
                (eqb := o)
                (st := stc')
            have hClauseAdd := hAdd hClauseAlloc
            simpa [chainStep, preEqAccStep, hAlloc'] using hClauseAdd
        cases hFoldA :
            os.foldl chainStep (base, st3) with
        | mk eqA st4 =>
          cases hFoldB :
              os'.foldl chainStep (eqA, st4) with
          | mk eqFinal st5 =>
            let st6 := addPreEqExpose b H0 H' eqFinal st5
            have hFold1Subset :
                st.clauses ⊆ st1.clauses := by
              have hResult :=
                foldl_subset_snd
                  (b := b)
                  (f := step₁)
                  (hStep := hStep₁)
                  (xs := WId.allWorlds b)
                  (init := ([], st))
              simpa [step₁, hFold1] using hResult
            have hFold2Subset :
                st1.clauses ⊆ st2.clauses := by
              have hResult :=
                foldl_subset_snd
                  (b := b)
                  (f := step₂)
                  (hStep := hStep₂)
                  (xs := WId.allWorlds b)
                  (init := ([], st1))
              simpa [step₂, hFold2] using hResult
            have hAllocEq :
                st3₀.clauses = st2.clauses := by
              simpa [hAllocBase] using
                (EncState.allocFresh_clauses_eq (b := b) (st := st2))
            have hAllocSubset :
                st2.clauses ⊆ st3₀.clauses := by
              intro clause hSt2
              simpa [hAllocEq] using hSt2
            have hBaseSubset :
                st3₀.clauses ⊆ st3.clauses := by
              exact
                EncState.addClause_subset_clauses
                  (b := b)
                  (st := st3₀)
                  (clause := [SAT.Lit.pos (FVar.toVar b base)])
            have hChainSubset :
                st3.clauses ⊆ st4.clauses := by
              have hResult :=
                foldl_subset_snd
                  (b := b)
                  (f := chainStep)
                  (hStep := hChainStep)
                  (xs := os)
                  (init := (base, st3))
              simpa [chainStep, hFoldA] using hResult
            have hChain2Subset :
                st4.clauses ⊆ st5.clauses := by
              have hResult :=
                foldl_subset_snd
                  (b := b)
                  (f := chainStep)
                  (hStep := hChainStep)
                  (xs := os')
                  (init := (eqA, st4))
              simpa [chainStep, hFoldB] using hResult
            have hExposeSubset :
                st5.clauses ⊆ st6.clauses := by
              exact
                addPreEqExpose_clauses_subset
                  (b := b)
                  (H0 := H0)
                  (H' := H')
                  (v := eqFinal)
                  (st := st5)
            have h1 := hFold1Subset hClause
            have h2 := hFold2Subset h1
            have h3 := hAllocSubset h2
            have h4 := hBaseSubset h3
            have h5 := hChainSubset h4
            have h6 := hChain2Subset h5
            have h7 := hExposeSubset h6
            simpa [addPreEqPair_core, step₁, step₂,
                    hFold1, hFold2, hAllocBase, st3, chainStep,
                    hFoldA, hFoldB, st6]
              using h7

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma addPreEqPair_clauses_subset (b : Bounds S) (H0 H' : b.times)
    (st : EncState b) :
    st.clauses ⊆ (addPreEqPair b H0 H' st).clauses := by
  classical
  intro clause hClause
  have hCore :=
    (addPreEqPair_core_clauses_subset
      (b := b) (H0 := H0) (H' := H') (st := st)) hClause
  by_cases hEq : H0 = H'
  · have hAdd :=
      EncState.addClause_subset_clauses
        (b := b)
        (st := addPreEqPair_core b H0 H' st)
        (clause := [SAT.Lit.pos (Var.PreEq H0 H')])
    have hFinal := hAdd hCore
    simpa [addPreEqPair, hEq]
      using hFinal
  · simpa [addPreEqPair, hEq] using hCore

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma addPreEqFrom_clauses_subset (b : Bounds S) (H0 : b.times)
    (st : EncState b) :
    st.clauses ⊆ (addPreEqFrom b H0 st).clauses := by
  classical
  unfold addPreEqFrom
  refine
    foldl_subset_state
      (b := b)
      (f := fun stCur H' => addPreEqPair b H0 H' stCur)
      (hStep := ?_)
      (xs := Bounds.timesL b)
      (init := st)
  intro stCur H'
  exact addPreEqPair_clauses_subset (b := b) (H0 := H0) (H' := H') (st := stCur)

/-- Add PreEq constraints for all pairs of time indices. -/
def addPreEqAll (b : Bounds S) (st : EncState b) : EncState b :=
  (Bounds.timesL b).foldl (fun acc t => addPreEqFrom b t acc) st

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma addPreEqAll_clauses_subset (b : Bounds S) (st : EncState b) :
    st.clauses ⊆ (addPreEqAll b st).clauses := by
  classical
  unfold addPreEqAll
  exact
    foldl_subset_state
      (b := b)
      (f := fun stCur t => addPreEqFrom b t stCur)
      (hStep := fun stCur t => addPreEqFrom_clauses_subset (b := b) (H0 := t) (st := stCur))
      (xs := Bounds.timesL b)
      (init := st)



omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma preEqObligationStep_clauses_eq_append
    (b : Bounds S) (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b) :
    ∃ newClauses,
      (preEqObligationStep b t t' acc w).2.clauses = newClauses ++ acc.2.clauses := by
  classical
  rcases acc with ⟨lst, stc⟩
  unfold preEqObligationStep
  set dwPair := mkDw b t' w stc with hDw
  rcases dwPair with ⟨d, stDw⟩
  rcases mkDw_clauses_eq_append (b := b) (t' := t') (w := w) (st := stc) with ⟨newDw, hDwAppend⟩
  rw [← hDw] at hDwAppend
  set owPair := mkOw b t w d stDw with hOw
  rcases owPair with ⟨o, stOw⟩
  have hOwAppend := mkOw_clauses_eq_append (b := b) (t := t) (w := w) (d := d) (st := stDw)
  refine ⟨[ [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)]
          , [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)]
          , [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w), SAT.Lit.pos (FVar.toVar b d)]
          ] ++ newDw, ?_⟩
  calc (mkOw b t w (mkDw b t' w stc).1 (mkDw b t' w stc).2).2.clauses
      = (mkOw b t w d stDw).2.clauses := by rw [← hDw]
    _ = [[SAT.Lit.pos (FVar.toVar b (mkOw b t w d stDw).1), SAT.Lit.neg (FVar.toVar b d)],
          [SAT.Lit.pos (FVar.toVar b (mkOw b t w d stDw).1), SAT.Lit.pos (Var.Mem t w)],
          [SAT.Lit.neg (FVar.toVar b (mkOw b t w d stDw).1), SAT.Lit.neg (Var.Mem t w),
            SAT.Lit.pos (FVar.toVar b d)]] ++ stDw.clauses := hOwAppend
    _ = [[SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)],
          [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)],
          [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
            SAT.Lit.pos (FVar.toVar b d)]] ++
        (newDw ++ stc.clauses) := by rw [← hOw, hDwAppend]
    _ = [[SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)],
          [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)],
          [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
            SAT.Lit.pos (FVar.toVar b d)]] ++
        newDw ++ stc.clauses := by simp

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma preEqAccStep_clauses_eq_append_aux (b : Bounds S)
    (cur next eqb : FVar b) :
    addAccStep_clauses b cur next eqb =
      [ [SAT.Lit.neg (FVar.toVar b cur), SAT.Lit.neg (FVar.toVar b eqb),
          SAT.Lit.pos (FVar.toVar b next)]
      , [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)]
      , [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)] ] := by
  rfl

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma preEqAccStep_clauses_eq_append (b : Bounds S)
    (acc : FVar b × EncState b) (o : FVar b) :
    ∃ newClauses,
      (preEqAccStep b acc o).2.clauses = newClauses ++ acc.2.clauses := by
  classical
  rcases acc with ⟨cur, stc⟩
  unfold preEqAccStep
  cases hAlloc : EncState.allocFresh b stc with
  | mk next stc' =>
      have hClauses : stc'.clauses = stc.clauses := by
        simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := stc)
      have hAcc :=
        addAccStep_clauses_eq_append (b := b) (cur := cur) (next := next) (eqb := o) (st := stc')
      refine ⟨addAccStep_clauses b cur next o, ?_⟩
      simp [hAlloc, hClauses, hAcc, List.cons_append, preEqAccStep_clauses_eq_append_aux]

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- The clause component of preEqObligation fold doesn't depend on the first
    component of accumulator -/
lemma preEqObligation_fold_clauses_indep
    (b : Bounds S) (t t' : b.times)
    (xs : List (WId b))
    (acc1 acc2 : List (FVar b)) (st : EncState b) :
    (xs.foldl (preEqObligationStep b t t') (acc1, st)).2.clauses =
    (xs.foldl (preEqObligationStep b t t') (acc2, st)).2.clauses := by
  classical
  revert acc1 acc2 st
  induction xs with
  | nil => intro acc1 acc2 st; rfl
  | cons w ws ih =>
      intro acc1 acc2 st
      simp only [List.foldl_cons]
      cases hDw : mkDw b t' w st with
      | mk d stDw =>
          cases hOw : mkOw b t w d stDw with
          | mk o stOw =>
              have h1 : preEqObligationStep b t t' (acc1, st) w = (o :: acc1, stOw) := by
                simp [preEqObligationStep, hDw, hOw]
              have h2 : preEqObligationStep b t t' (acc2, st) w = (o :: acc2, stOw) := by
                simp [preEqObligationStep, hDw, hOw]
              rw [h1, h2]
              apply ih

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in


lemma preEqObligation_fold_clauses_eq_append
    (b : Bounds S) (t t' : b.times)
    (xs : List (WId b))
    (acc : List (FVar b) × EncState b) :
    ∃ newClauses,
      (xs.foldl (preEqObligationStep b t t') acc).2.clauses =
        newClauses ++ acc.2.clauses := by
  classical
  induction xs generalizing acc with
  | nil =>
      exact ⟨[], by cases acc; simp⟩
  | cons w ws ih =>
      rcases preEqObligationStep_clauses_eq_append
        (b := b) (t := t) (t' := t') (acc := acc) (w := w) with
        ⟨newStep, hStep⟩
      rcases ih (preEqObligationStep b t t' acc w) with ⟨newTail, hTail⟩
      refine ⟨newTail ++ newStep, ?_⟩
      (cases acc; simp [hStep, hTail, List.append_assoc])




omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma preEqObligation_fold_clauses_subset
    (b : Bounds S) (t t' : b.times)
    (xs : List (WId b))
    {init : List (FVar b) × EncState b}
    {os : List (FVar b)} {st1 : EncState b}
    (hFold :
      (os, st1) =
        xs.foldl (preEqObligationStep b t t') init) :
    init.2.clauses ⊆ st1.clauses := by
  classical
  have hStep :
      ∀ acc w,
        acc.2.clauses ⊆
          (preEqObligationStep b t t' acc w).2.clauses := by
    intro acc w
    exact
      preEqObligationStep_clauses_subset
        (b := b) (t := t) (t' := t')
        (acc := acc) (w := w)
  have hResult :=
    foldl_subset_snd
      (b := b)
      (f := preEqObligationStep b t t')
      (hStep := hStep)
      (xs := xs)
      (init := init)
  have hSnd :
      st1 =
        (xs.foldl (preEqObligationStep b t t') init).2 := by
    simpa [hFold] using congrArg Prod.snd hFold
  simpa [hSnd] using hResult

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma preEqAccStep_clauses_subset (b : Bounds S)
    (acc : FVar b × EncState b) (o : FVar b) :
    acc.2.clauses ⊆ (preEqAccStep b acc o).2.clauses := by
  classical
  rcases acc with ⟨cur, stc⟩
  unfold preEqAccStep
  cases hAlloc : EncState.allocFresh b stc with
  | mk next stc' =>
      have hAllocEq :
          stc'.clauses = stc.clauses := by
        simpa [hAlloc] using
          EncState.allocFresh_clauses_eq (b := b) (st := stc)
      intro clause hClause
      have hClause' : clause ∈ stc'.clauses := by
        simpa [hAllocEq] using hClause
      have hSubset :=
        addAccStep_clauses_subset
          (b := b) (cur := cur) (next := next) (eqb := o)
          (st := stc')
      have hRes := hSubset hClause'
      simpa [hAlloc] using hRes

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma preEqAcc_fold_clauses_subset (b : Bounds S)
    (xs : List (FVar b))
    {init : FVar b × EncState b} {result : FVar b × EncState b}
    (hFold :
      result = xs.foldl (preEqAccStep b) init) :
    init.2.clauses ⊆ result.2.clauses := by
  classical
  have hStep :
      ∀ acc o,
        acc.2.clauses ⊆ (preEqAccStep b acc o).2.clauses := by
    intro acc o
    exact preEqAccStep_clauses_subset (b := b) (acc := acc) (o := o)
  have hResult :=
    foldl_subset_snd
      (b := b)
      (f := preEqAccStep b)
      (hStep := hStep)
      (xs := xs)
      (init := init)
  simpa [hFold] using hResult

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma preEqAcc_fold_all_true
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (xs : List (FVar b))
    {base : FVar b} {stBase : EncState b}
    {result : FVar b × EncState b}
    (hFold :
      result = xs.foldl (preEqAccStep b) (base, stBase))
    (hClauses :
      result.2.clauses.all (SAT.Clause.eval σ) = true)
    (hFinal : σ (FVar.toVar b result.1) = true) :
    ∀ o ∈ xs, σ (FVar.toVar b o) = true := by
  classical
  refine
    (and_accumulator_all_true
      (b := b) (σ := σ)
      (xs := xs)
      (inputBit := fun o => o)
      (base := base)
      (st_init := stBase)
      (result := result)
      (hResult := hFold)
      (hClauses := hClauses)
      (hFinal := hFinal))

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma preEqAcc_fold_base_true
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (xs : List (FVar b))
    {base : FVar b} {stBase : EncState b}
    {result : FVar b × EncState b}
    (hFold :
      result = xs.foldl (preEqAccStep b) (base, stBase))
    (hClauses :
      result.2.clauses.all (SAT.Clause.eval σ) = true)
    (hFinal : σ (FVar.toVar b result.1) = true) :
    σ (FVar.toVar b base) = true := by
  classical
  refine
    (and_accumulator_base_true
      (b := b) (σ := σ)
      (xs := xs)
      (inputBit := fun o => o)
      (base := base)
      (st_init := stBase)
      (result := result)
      (hResult := hFold)
      (hClauses := hClauses)
      (hFinal := hFinal))

/-!
## Structural Determinism Lemmas

These lemmas establish that the encoding behaves consistently across different starting states.
-/

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- preEqAccStep allocates 1 Fresh and returns it. -/
lemma preEqAccStep_fst (b : Bounds S) (acc : FVar b × EncState b) (o : FVar b) :
    (preEqAccStep b acc o).1 = { id := acc.2.nextFresh } := by
  unfold preEqAccStep
  simp only [EncState.allocFresh]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- preEqAccStep increments nextFresh by exactly 1. -/
lemma preEqAccStep_nextFresh (b : Bounds S) (acc : FVar b × EncState b) (o : FVar b) :
    (preEqAccStep b acc o).2.nextFresh = acc.2.nextFresh + 1 := by
  unfold preEqAccStep addAccStep
  simp only [EncState.allocFresh, EncState.addClause]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The clauses added by preEqAccStep (exact form). -/
lemma preEqAccStep_clauses_eq (b : Bounds S) (acc : FVar b × EncState b) (o : FVar b) :
    (preEqAccStep b acc o).2.clauses =
      addAccStep_clauses b acc.1 ⟨acc.2.nextFresh⟩ o ++ acc.2.clauses := by
  unfold preEqAccStep
  simp only [EncState.allocFresh]
  exact addAccStep_clauses_eq_append b acc.1 ⟨acc.2.nextFresh⟩ o acc.2

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Structural determinism for preEqAccStep: if σ satisfies the clauses at state acc.2,
    then σ' (with Fresh vars shifted by offset) satisfies the clauses at state acc'.2.

    preEqAccStep allocates 1 Fresh var `next` and adds 3 clauses:
    - [¬next, cur] (next → cur)
    - [¬next, o] (next → o)
    - [¬cur, ¬o, next] (cur ∧ o → next)

    All inputs (cur from acc.1, o) and the new variable (next) are Fresh. -/
lemma preEqAccStep_structural_determinism (b : Bounds S)
    (acc acc' : FVar b × EncState b) (o o' : FVar b) (offset : Nat)
    (hOffset : offset = acc'.2.nextFresh - acc.2.nextFresh)
    (hMono : acc.2.nextFresh ≤ acc'.2.nextFresh)
    (hWF : EncState.WellFormed acc'.2)
    (hCurShift : acc'.1.id = acc.1.id + offset)
    (hOShift : o'.id = o.id + offset)
    (hCurGe : acc.1.id ≥ acc.2.nextFresh)
    (hOGe : o.id ≥ acc.2.nextFresh)
    (σ : SAT.Assignment (Var b))
    (hSat : (preEqAccStep b acc o).2.clauses.all (SAT.Clause.eval σ) = true)
    (hSatBase : acc'.2.clauses.all (SAT.Clause.eval σ) = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < acc'.2.nextFresh then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    (preEqAccStep b acc' o').2.clauses.all (SAT.Clause.eval σ') = true := by
  classical
  intro σ'
  rw [List.all_eq_true]
  intro clause hClause

  -- Get clause structures
  have hClausesEq := preEqAccStep_clauses_eq b acc' o'
  have hNextSt := preEqAccStep_fst b acc o
  have hNextSt' := preEqAccStep_fst b acc' o'

  -- Fresh indices for shifted variables
  -- cur' is at acc.1.id + offset, which is >= acc'.2.nextFresh
  have hCur'Ge : acc'.1.id ≥ acc'.2.nextFresh := by
    rw [hCurShift, hOffset]; omega
  have hCurNotLt : ¬ acc'.1.id < acc'.2.nextFresh := Nat.not_lt.mpr hCur'Ge

  -- o' is at o.id + offset, which is >= acc'.2.nextFresh
  have hO'Ge : o'.id ≥ acc'.2.nextFresh := by
    rw [hOShift, hOffset]; omega
  have hONotLt : ¬ o'.id < acc'.2.nextFresh := Nat.not_lt.mpr hO'Ge

  -- next' is at acc'.2.nextFresh (not < itself)
  have hNextNotLt : ¬ acc'.2.nextFresh < acc'.2.nextFresh := Nat.lt_irrefl _

  rw [hClausesEq] at hClause
  -- addAccStep_clauses has 3 clauses
  unfold addAccStep_clauses at hClause
  cases hClause with
  | head =>
      -- Clause 1: [¬cur', ¬o', next']
      have hClausesSt := preEqAccStep_clauses_eq b acc o
      have hClauseSt : [SAT.Lit.neg (FVar.toVar b acc.1), SAT.Lit.neg (FVar.toVar b o),
          SAT.Lit.pos (FVar.toVar b ⟨acc.2.nextFresh⟩)] ∈ (preEqAccStep b acc o).2.clauses := by
        rw [hClausesSt]
        unfold addAccStep_clauses
        exact List.Mem.head _
      have hEvalSt := List.all_eq_true.mp hSat _ hClauseSt
      rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
      rcases hLitMem with ⟨⟩ | ⟨_, h1⟩
      · -- lit = neg cur
        refine ⟨SAT.Lit.neg (FVar.toVar b acc'.1), List.Mem.head _, ?_⟩
        simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
        simp only [σ', hCurShift]
        have hCurNotLt' : ¬ acc.1.id + offset < acc'.2.nextFresh :=
          Nat.not_lt.mpr (by rw [hOffset]; omega : acc.1.id + offset ≥ acc'.2.nextFresh)
        simp only [hCurNotLt', ↓reduceIte, Nat.add_sub_cancel]
        exact hLitTrue
      · rcases h1 with ⟨⟩ | ⟨_, h2⟩
        · -- lit = neg o
          refine ⟨SAT.Lit.neg (FVar.toVar b o'),
              List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
          simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
          simp only [σ', hOShift]
          have hONotLt' : ¬ o.id + offset < acc'.2.nextFresh :=
            Nat.not_lt.mpr (by rw [hOffset]; omega : o.id + offset ≥ acc'.2.nextFresh)
          simp only [hONotLt', ↓reduceIte, Nat.add_sub_cancel]
          exact hLitTrue
        · rcases h2 with ⟨⟩ | ⟨_, h3⟩
          · -- lit = pos next
            refine ⟨SAT.Lit.pos (FVar.toVar b ⟨acc'.2.nextFresh⟩),
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.Mem.head _)), ?_⟩
            simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
            simp only [σ', hNextNotLt, ↓reduceIte]
            have hEq : acc'.2.nextFresh - offset = acc.2.nextFresh := by rw [hOffset]; omega
            simp only [hEq]
            exact hLitTrue
          · cases h3

  | tail _ h1 =>
      cases h1 with
      | head =>
          -- Clause 2: [¬next', o']
          have hClausesSt := preEqAccStep_clauses_eq b acc o
          have hClauseSt : [SAT.Lit.neg (FVar.toVar b ⟨acc.2.nextFresh⟩),
              SAT.Lit.pos (FVar.toVar b o)] ∈ (preEqAccStep b acc o).2.clauses := by
            rw [hClausesSt]
            unfold addAccStep_clauses
            exact List.mem_cons_of_mem _ (List.Mem.head _)
          have hEvalSt := List.all_eq_true.mp hSat _ hClauseSt
          rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
          rcases hLitMem with ⟨⟩ | ⟨_, h2⟩
          · -- lit = neg next
            refine ⟨SAT.Lit.neg (FVar.toVar b ⟨acc'.2.nextFresh⟩), List.Mem.head _, ?_⟩
            simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
            simp only [σ', hNextNotLt, ↓reduceIte]
            have hEq : acc'.2.nextFresh - offset = acc.2.nextFresh := by rw [hOffset]; omega
            simp only [hEq]
            exact hLitTrue
          · rcases h2 with ⟨⟩ | ⟨_, h3⟩
            · -- lit = pos o
              refine ⟨SAT.Lit.pos (FVar.toVar b o'),
                  List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
              simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
              simp only [σ', hOShift]
              have hONotLt' : ¬ o.id + offset < acc'.2.nextFresh :=
                Nat.not_lt.mpr (by rw [hOffset]; omega : o.id + offset ≥ acc'.2.nextFresh)
              simp only [hONotLt', ↓reduceIte, Nat.add_sub_cancel]
              exact hLitTrue
            · cases h3

      | tail _ h2 =>
          cases h2 with
          | head =>
              -- Clause 3: [¬next', cur']
              have hClausesSt := preEqAccStep_clauses_eq b acc o
              have hClauseSt : [SAT.Lit.neg (FVar.toVar b ⟨acc.2.nextFresh⟩),
                  SAT.Lit.pos (FVar.toVar b acc.1)] ∈ (preEqAccStep b acc o).2.clauses := by
                rw [hClausesSt]
                unfold addAccStep_clauses
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.Mem.head _))
              have hEvalSt := List.all_eq_true.mp hSat _ hClauseSt
              rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
              obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
              rcases hLitMem with ⟨⟩ | ⟨_, h3⟩
              · -- lit = neg next
                refine ⟨SAT.Lit.neg (FVar.toVar b ⟨acc'.2.nextFresh⟩), List.Mem.head _, ?_⟩
                simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
                simp only [σ', hNextNotLt, ↓reduceIte]
                have hEq : acc'.2.nextFresh - offset = acc.2.nextFresh := by rw [hOffset]; omega
                simp only [hEq]
                exact hLitTrue
              · rcases h3 with ⟨⟩ | ⟨_, h4⟩
                · -- lit = pos cur
                  refine ⟨SAT.Lit.pos (FVar.toVar b acc'.1),
                      List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
                  simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
                  simp only [σ', hCurShift]
                  have hCurNotLt' : ¬ acc.1.id + offset < acc'.2.nextFresh :=
                    Nat.not_lt.mpr (by rw [hOffset]; omega : acc.1.id + offset ≥ acc'.2.nextFresh)
                  simp only [hCurNotLt', ↓reduceIte, Nat.add_sub_cancel]
                  exact hLitTrue
                · cases h4

          | tail _ h3 =>
              -- Inherited from acc'.2.clauses
              have hInBase : clause ∈ acc'.2.clauses := h3
              have hEvalBase := List.all_eq_true.mp hSatBase clause hInBase
              rw [SAT.Clause.eval_eq_any] at hEvalBase ⊢
              rw [List.any_eq_true] at hEvalBase ⊢
              obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalBase
              refine ⟨lit, hLitMem, ?_⟩
              have hClauseWF : clauseFreshBelow clause acc'.2.nextFresh := hWF clause hInBase
              cases lit with
              | pos v =>
                  simp only [SAT.Lit.eval] at hLitTrue ⊢
                  cases v with
                  | Fresh n =>
                      have hLt : n < acc'.2.nextFresh := by
                        have h := hClauseWF (SAT.Lit.pos (Var.Fresh n)) hLitMem
                        simp only [litFreshBelow, SAT.Lit.getVar] at h
                        exact h
                      simp only [σ', hLt, ↓reduceIte]
                      exact hLitTrue
                  | _ => exact hLitTrue
              | neg v =>
                  simp only [SAT.Lit.eval] at hLitTrue ⊢
                  cases v with
                  | Fresh n =>
                      have hLt : n < acc'.2.nextFresh := by
                        have h := hClauseWF (SAT.Lit.neg (Var.Fresh n)) hLitMem
                        simp only [litFreshBelow, SAT.Lit.getVar] at h
                        exact h
                      simp only [σ', hLt, ↓reduceIte]
                      exact hLitTrue
                  | _ => exact hLitTrue

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Structural determinism for NEW clauses only from preEqAccStep.
    Unlike preEqAccStep_structural_determinism, this doesn't require σ to satisfy
    the base state's clauses - only the output state's clauses. This is sufficient for
    proving satisfaction of NEW clauses (those not in the base state). -/
lemma preEqAccStep_newClauses_structural_determinism_threshold (b : Bounds S)
    (acc acc' : FVar b × EncState b) (o o' : FVar b) (offset threshold : Nat)
    (hOffset : offset = acc'.2.nextFresh - acc.2.nextFresh)
    (hMono : acc.2.nextFresh ≤ acc'.2.nextFresh)
    (hCurShift : acc'.1.id = acc.1.id + offset)
    (hOShift : o'.id = o.id + offset)
    (hCurGeTh : acc.1.id ≥ threshold) -- cur at or after threshold
    (hOGeTh : o.id ≥ threshold) -- o at or after threshold
    (hThresholdLe : threshold ≤ acc.2.nextFresh) -- threshold before acc
    (hWF : acc.2.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (preEqAccStep b acc o).2.clauses, c ∉ acc.2.clauses →
               SAT.Clause.eval σ c = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (preEqAccStep b acc' o').2.clauses)
    (hClauseNotInBase : clause ∉ acc'.2.clauses) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < threshold + offset then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    SAT.Clause.eval σ' clause = true := by
  intro σ'
  -- The NEW clauses are exactly the 3 clauses from addAccStep_clauses
  have hClausesEq := preEqAccStep_clauses_eq b acc' o'
  rw [hClausesEq] at hClauseMem
  cases List.mem_append.mp hClauseMem with
  | inl hNew =>
      -- clause is one of the 3 new clauses
      -- All Fresh vars in new clauses have index >= threshold + offset

      -- Fresh indices for shifted variables (>= threshold + offset)
      -- After hCurShift rewrites acc'.1.id to acc.1.id + offset, we need to
      -- show that acc.1.id + offset >= threshold + offset (equivalently acc.1.id >= threshold)
      have hCurIdNotLt : ¬ acc.1.id + offset < threshold + offset := by omega
      have hOIdNotLt : ¬ o.id + offset < threshold + offset := by omega
      have hNextNotLt : ¬ acc'.2.nextFresh < threshold + offset := by rw [hOffset]; omega

      have hClausesSt := preEqAccStep_clauses_eq b acc o
      simp only [addAccStep_clauses, List.mem_cons, List.mem_nil_iff, or_false] at hNew
      rcases hNew with hC1 | hC2 | hC3
      · -- Clause 1: [¬cur', ¬o', next']
        subst hC1
        have hClauseSt : [SAT.Lit.neg (FVar.toVar b acc.1), SAT.Lit.neg (FVar.toVar b o),
            SAT.Lit.pos (FVar.toVar b ⟨acc.2.nextFresh⟩)] ∈ (preEqAccStep b acc o).2.clauses := by
          rw [hClausesSt]; unfold addAccStep_clauses; exact List.Mem.head _
        -- Clause is NEW: contains Fresh(acc.2.nextFresh), but WF says clauses in acc.2 have Fresh < nextFresh
        have hNotInAcc : [SAT.Lit.neg (FVar.toVar b acc.1), SAT.Lit.neg (FVar.toVar b o),
            SAT.Lit.pos (FVar.toVar b ⟨acc.2.nextFresh⟩)] ∉ acc.2.clauses := by
          intro hIn
          have hClauseBound := hWF _ hIn
          unfold clauseFreshBelow at hClauseBound
          have hFreshLt := hClauseBound (SAT.Lit.pos (FVar.toVar b ⟨acc.2.nextFresh⟩)) (by simp)
          simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar] at hFreshLt
          exact Nat.lt_irrefl _ hFreshLt
        have hEvalSt := hSatNew _ hClauseSt hNotInAcc
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
        rcases hLitMem with ⟨⟩ | ⟨_, h1⟩
        · -- lit = neg cur
          refine ⟨SAT.Lit.neg (FVar.toVar b acc'.1), List.Mem.head _, ?_⟩
          simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
          simp only [σ', hCurShift, hCurIdNotLt, ↓reduceIte, Nat.add_sub_cancel]; exact hLitTrue
        · rcases h1 with ⟨⟩ | ⟨_, h2⟩
          · -- lit = neg o
            refine ⟨SAT.Lit.neg (FVar.toVar b o'), List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
            simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
            simp only [σ', hOShift, hOIdNotLt, ↓reduceIte, Nat.add_sub_cancel]; exact hLitTrue
          · rcases h2 with ⟨⟩ | ⟨_, h3⟩
            · -- lit = pos next
              refine ⟨SAT.Lit.pos (FVar.toVar b ⟨acc'.2.nextFresh⟩),
                  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.Mem.head _)), ?_⟩
              simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
              simp only [σ', hNextNotLt, ↓reduceIte]
              have hEq : acc'.2.nextFresh - offset = acc.2.nextFresh := by rw [hOffset]; omega
              simp only [hEq]; exact hLitTrue
            · cases h3

      · -- Clause 2: [¬next', o']
        subst hC2
        have hClauseSt : [SAT.Lit.neg (FVar.toVar b ⟨acc.2.nextFresh⟩),
            SAT.Lit.pos (FVar.toVar b o)] ∈ (preEqAccStep b acc o).2.clauses := by
          rw [hClausesSt]; unfold addAccStep_clauses
          exact List.mem_cons_of_mem _ (List.Mem.head _)
        have hNotInAcc : [SAT.Lit.neg (FVar.toVar b ⟨acc.2.nextFresh⟩),
            SAT.Lit.pos (FVar.toVar b o)] ∉ acc.2.clauses := by
          intro hIn
          have hClauseBound := hWF _ hIn
          unfold clauseFreshBelow at hClauseBound
          have hFreshLt := hClauseBound (SAT.Lit.neg (FVar.toVar b ⟨acc.2.nextFresh⟩)) (by simp)
          simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar] at hFreshLt
          exact Nat.lt_irrefl _ hFreshLt
        have hEvalSt := hSatNew _ hClauseSt hNotInAcc
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
        rcases hLitMem with ⟨⟩ | ⟨_, h2⟩
        · -- lit = neg next
          refine ⟨SAT.Lit.neg (FVar.toVar b ⟨acc'.2.nextFresh⟩), List.Mem.head _, ?_⟩
          simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
          simp only [σ', hNextNotLt, ↓reduceIte]
          have hEq : acc'.2.nextFresh - offset = acc.2.nextFresh := by rw [hOffset]; omega
          simp only [hEq]; exact hLitTrue
        · rcases h2 with ⟨⟩ | ⟨_, h3⟩
          · -- lit = pos o
            refine ⟨SAT.Lit.pos (FVar.toVar b o'), List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
            simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
            simp only [σ', hOShift, hOIdNotLt, ↓reduceIte, Nat.add_sub_cancel]; exact hLitTrue
          · cases h3

      · -- Clause 3: [¬next', cur']
        subst hC3
        have hClauseSt : [SAT.Lit.neg (FVar.toVar b ⟨acc.2.nextFresh⟩),
            SAT.Lit.pos (FVar.toVar b acc.1)] ∈ (preEqAccStep b acc o).2.clauses := by
          rw [hClausesSt]; unfold addAccStep_clauses
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.Mem.head _))
        have hNotInAcc : [SAT.Lit.neg (FVar.toVar b ⟨acc.2.nextFresh⟩),
            SAT.Lit.pos (FVar.toVar b acc.1)] ∉ acc.2.clauses := by
          intro hIn
          have hClauseBound := hWF _ hIn
          unfold clauseFreshBelow at hClauseBound
          have hFreshLt := hClauseBound (SAT.Lit.neg (FVar.toVar b ⟨acc.2.nextFresh⟩)) (by simp)
          simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar] at hFreshLt
          exact Nat.lt_irrefl _ hFreshLt
        have hEvalSt := hSatNew _ hClauseSt hNotInAcc
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
        rcases hLitMem with ⟨⟩ | ⟨_, h3⟩
        · -- lit = neg next
          refine ⟨SAT.Lit.neg (FVar.toVar b ⟨acc'.2.nextFresh⟩), List.Mem.head _, ?_⟩
          simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
          simp only [σ', hNextNotLt, ↓reduceIte]
          have hEq : acc'.2.nextFresh - offset = acc.2.nextFresh := by rw [hOffset]; omega
          simp only [hEq]; exact hLitTrue
        · rcases h3 with ⟨⟩ | ⟨_, h4⟩
          · -- lit = pos cur
            refine ⟨SAT.Lit.pos (FVar.toVar b acc'.1), List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
            simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
            simp only [σ', hCurShift, hCurIdNotLt, ↓reduceIte, Nat.add_sub_cancel]; exact hLitTrue
          · cases h4

  | inr hOld => exact absurd hOld hClauseNotInBase

-- ============================================================================
-- Well-formedness preservation lemmas for PreEq encoding (moved here for use below)
-- ============================================================================

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- addAccStep preserves well-formedness when input Fresh vars have id < st.nextFresh. -/
lemma addAccStep_wf (b : Bounds S) (cur next eqb : FVar b) (st : EncState b)
    (hWF : EncState.WellFormed st)
    (hCur : cur.id < st.nextFresh) (hNext : next.id < st.nextFresh) (hEqb : eqb.id < st.nextFresh) :
    EncState.WellFormed (addAccStep b cur next eqb st) := by
  unfold addAccStep
  -- 3 addClause operations, each using Fresh vars with known bounds
  let c1 := [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)]
  let c2 := [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)]
  let c3 := [SAT.Lit.neg (FVar.toVar b cur), SAT.Lit.neg (FVar.toVar b eqb),
             SAT.Lit.pos (FVar.toVar b next)]
  have h1 : clauseFreshBelow c1 st.nextFresh := by
    intro lit hLit; simp only [c1, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h => subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar]; exact hNext
    | inr h => subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar]; exact hCur
  let st1 := EncState.addClause b st c1
  have hWF1 : st1.WellFormed := EncState.addClause_wf hWF c1 h1
  have hSt1Next : st1.nextFresh = st.nextFresh := EncState.addClause_nextFresh b st c1
  have h2 : clauseFreshBelow c2 st1.nextFresh := by
    rw [hSt1Next]
    intro lit hLit; simp only [c2, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h => subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar]; exact hNext
    | inr h => subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar]; exact hEqb
  let st2 := EncState.addClause b st1 c2
  have hWF2 : st2.WellFormed := EncState.addClause_wf hWF1 c2 h2
  have hSt2Next : st2.nextFresh = st.nextFresh := by
    simp only [st2, st1, EncState.addClause_nextFresh]
  have h3 : clauseFreshBelow c3 st2.nextFresh := by
    rw [hSt2Next]
    intro lit hLit; simp only [c3, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    rcases hLit with h | h | h
    · subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar]; exact hCur
    · subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar]; exact hEqb
    · subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar]; exact hNext
  exact EncState.addClause_wf hWF2 c3 h3

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- preEqAccStep preserves well-formedness and the returned Fresh var has proper bounds.
    Given: acc.2.WellFormed, cur=acc.1 with cur.id < acc.2.nextFresh, o.id < acc.2.nextFresh
    Returns: WellFormed (result.2), result.1.id < result.2.nextFresh -/
lemma preEqAccStep_wf (b : Bounds S) (acc : FVar b × EncState b) (o : FVar b)
    (hWF : EncState.WellFormed acc.2)
    (hCur : acc.1.id < acc.2.nextFresh)
    (hO : o.id < acc.2.nextFresh) :
    EncState.WellFormed (preEqAccStep b acc o).2 ∧
    (preEqAccStep b acc o).1.id < (preEqAccStep b acc o).2.nextFresh := by
  unfold preEqAccStep
  simp only
  -- allocFresh: next.id = acc.2.nextFresh, st'.nextFresh = acc.2.nextFresh + 1
  have hNextId : (EncState.allocFresh b acc.2).1.id = acc.2.nextFresh := by
    simp [EncState.allocFresh]
  have hNextNext : (EncState.allocFresh b acc.2).2.nextFresh = acc.2.nextFresh + 1 :=
    EncState.allocFresh_nextFresh b acc.2
  have hAllocWF := EncState.allocFresh_wf hWF
  -- Now addAccStep with cur.id < nextFresh+1, next.id < nextFresh+1, o.id < nextFresh+1
  have hCur' : acc.1.id < (EncState.allocFresh b acc.2).2.nextFresh := by rw [hNextNext]; omega
  have hNext' : (EncState.allocFresh b acc.2).1.id < (EncState.allocFresh b acc.2).2.nextFresh := by
    rw [hNextId, hNextNext]; omega
  have hO' : o.id < (EncState.allocFresh b acc.2).2.nextFresh := by rw [hNextNext]; omega
  have hAccWF := addAccStep_wf b acc.1 (EncState.allocFresh b acc.2).1 o
      (EncState.allocFresh b acc.2).2 hAllocWF hCur' hNext' hO'
  -- addAccStep preserves nextFresh
  have hAccNext : (addAccStep b acc.1 (EncState.allocFresh b acc.2).1 o
      (EncState.allocFresh b acc.2).2).nextFresh = (EncState.allocFresh b acc.2).2.nextFresh := by
    simp only [addAccStep, EncState.addClause_nextFresh]
  constructor
  · exact hAccWF
  · rw [hAccNext, hNextId, hNextNext]; omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- Fold-level structural determinism for NEW clauses from preEqAccStep fold.
    Given two parallel folds over shifted obligation lists with offset states,
    if σ satisfies ALL clauses from the os-side fold, then σ' satisfies any
    NEW clause (not inherited from acc'.2) from the os'-side fold.

    Key invariants maintained through the fold:
    - offset = acc'.2.nextFresh - acc.2.nextFresh (constant)
    - acc'.1.id = acc.1.id + offset (cur shifts by offset)
    - All obligations shift by offset
    - Fresh vars >= threshold go through the shift mapping

    This lemma only handles NEW clauses. For inherited clauses, the caller
    should handle them separately (e.g., via preEqObligation SD lemmas). -/
lemma foldl_preEqAccStep_newClauses_structural_determinism (b : Bounds S)
    (os os' : List (FVar b))
    (acc acc' : FVar b × EncState b) (offset threshold : Nat)
    (hOffset : offset = acc'.2.nextFresh - acc.2.nextFresh)
    (hMono : acc.2.nextFresh ≤ acc'.2.nextFresh)
    (hCurShift : acc'.1.id = acc.1.id + offset)
    (hCurGeTh : acc.1.id ≥ threshold)
    (hCurLtNext : acc.1.id < acc.2.nextFresh)
    (hThresholdLe : threshold ≤ acc.2.nextFresh) -- threshold before acc's nextFresh
    (hWF : acc.2.WellFormed)
    (hOsLen : os'.length = os.length)
    (hOsShift : ∀ i (hi : i < os.length),
        (os'.get ⟨i, hOsLen ▸ hi⟩).id = (os.get ⟨i, hi⟩).id + offset)
    (hOsGeTh : ∀ o ∈ os, o.id ≥ threshold)
    (hOsLtNext : ∀ o ∈ os, o.id < acc.2.nextFresh)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (os.foldl (preEqAccStep b) acc).2.clauses, c ∉ acc.2.clauses →
               SAT.Clause.eval σ c = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (os'.foldl (preEqAccStep b) acc').2.clauses)
    (hClauseNew : clause ∉ acc'.2.clauses) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < threshold + offset then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v
    SAT.Clause.eval σ' clause = true := by
  intro σ'
  classical
  -- We use suffices to track intermediate states with proper offset invariants
  -- Key invariants:
  -- - accCur.1.id >= threshold (cur is at or after threshold)
  -- - accCur.1.id < accCur.2.nextFresh (for WF preservation)
  -- - threshold <= accCur.2.nextFresh (threshold before acc's nextFresh)
  -- - accCur.2.WellFormed (needed for proving NEW clause condition)
  -- - ∀ o ∈ os_suff, o.id < accCur.2.nextFresh (for WF preservation)
  suffices ∀ (os_suff os'_suff : List (FVar b))
      (accCur accCur' : FVar b × EncState b),
      offset = accCur'.2.nextFresh - accCur.2.nextFresh →
      accCur.2.nextFresh ≤ accCur'.2.nextFresh →
      accCur'.1.id = accCur.1.id + offset →
      accCur.1.id ≥ threshold →
      accCur.1.id < accCur.2.nextFresh →
      threshold ≤ accCur.2.nextFresh →  -- threshold before acc
      accCur.2.WellFormed →
      os'_suff.length = os_suff.length →
      (∀ i (hi : i < os_suff.length) (hi' : i < os'_suff.length),
          (os'_suff.get ⟨i, hi'⟩).id = (os_suff.get ⟨i, hi⟩).id + offset) →
      (∀ o ∈ os_suff, o.id ≥ threshold) →
      (∀ o ∈ os_suff, o.id < accCur.2.nextFresh) →
      (∀ c ∈ (os_suff.foldl (preEqAccStep b) accCur).2.clauses, c ∉ accCur.2.clauses →
          SAT.Clause.eval σ c = true) →
      clause ∈ (os'_suff.foldl (preEqAccStep b) accCur').2.clauses →
      clause ∉ accCur'.2.clauses →
      SAT.Clause.eval σ' clause = true by
    have hOsShift' : ∀ i (hi : i < os.length) (hi' : i < os'.length),
        (os'.get ⟨i, hi'⟩).id = (os.get ⟨i, hi⟩).id + offset := by
      intro i hi hi'
      exact hOsShift i hi
    exact this os os' acc acc' hOffset hMono hCurShift hCurGeTh hCurLtNext hThresholdLe hWF hOsLen
        hOsShift' hOsGeTh hOsLtNext hSatNew hClauseMem hClauseNew

  intro os_suff os'_suff accCur accCur'
  induction os_suff generalizing os'_suff accCur accCur' with
  | nil =>
      intro _ _ _ _ _ _ _ hLen _ _ _ _ hIn hNotIn
      have hOs'Nil : os'_suff = [] := by
        cases os'_suff with
        | nil => rfl
        | cons _ _ => simp at hLen
      simp only [hOs'Nil, List.foldl_nil] at hIn
      exact absurd hIn hNotIn
  | cons o os_tl ih =>
      intro hOffCur hMonCur hCurShCur hCurGeTh_Cur hCurLtNext_Cur hThLe_Cur hWFCur hLen hOsShCur
          hOsGeTh_Cur hOsLtNext_Cur hSatNewCur hInCur hNotInCur
      cases os'_suff with
      | nil => simp at hLen
      | cons o' os'_tl =>
          simp only [List.foldl_cons] at hSatNewCur hInCur

          have hStepNext : (preEqAccStep b accCur o).2.nextFresh = accCur.2.nextFresh + 1 :=
            preEqAccStep_nextFresh b accCur o
          have hStepNext' : (preEqAccStep b accCur' o').2.nextFresh =
              accCur'.2.nextFresh + 1 :=
            preEqAccStep_nextFresh b accCur' o'
          have hOShift : o'.id = o.id + offset := by
            have h := hOsShCur 0 (by simp) (by simp)
            exact h
          have hOGeTh : o.id ≥ threshold := hOsGeTh_Cur o (by simp)

          -- Check if clause is from this step or from tail
          by_cases hInStep' : clause ∈ (preEqAccStep b accCur' o').2.clauses
          · -- Clause is from this step (or inherited into this step from accCur')
            by_cases hInAccCur' : clause ∈ accCur'.2.clauses
            · -- Inherited from accCur' into this step
              exact absurd hInAccCur' hNotInCur
            · -- New clause from this step - use threshold SD lemma
              -- Get σ satisfaction for NEW clauses in this step on accCur side
              have hSatStepNew : ∀ c ∈ (preEqAccStep b accCur o).2.clauses,
                  c ∉ accCur.2.clauses → SAT.Clause.eval σ c = true := by
                intro c hC hNotInAccCur
                have hFoldSub := preEqAcc_fold_clauses_subset b os_tl
                    (init := preEqAccStep b accCur o) (hFold := rfl)
                exact hSatNewCur c (hFoldSub hC) hNotInAccCur

              -- threshold ≤ accCur.2.nextFresh (from invariant hThLe_Cur)
              have hThLe : threshold ≤ accCur.2.nextFresh := hThLe_Cur

              -- Apply threshold SD lemma - σ' has same threshold, so result is exactly σ'
              exact preEqAccStep_newClauses_structural_determinism_threshold b accCur accCur'
                  o o' offset threshold hOffCur hMonCur hCurShCur hOShift hCurGeTh_Cur hOGeTh
                  hThLe hWFCur σ hSatStepNew clause hInStep' hInAccCur'

          · -- Clause is from the tail of the fold - use IH
            have hLen' : os'_tl.length = os_tl.length := by simp at hLen; exact hLen
            have hOff' : offset = (preEqAccStep b accCur' o').2.nextFresh -
                (preEqAccStep b accCur o).2.nextFresh := by
              rw [hStepNext, hStepNext', hOffCur]; omega
            have hMon' : (preEqAccStep b accCur o).2.nextFresh ≤
                (preEqAccStep b accCur' o').2.nextFresh := by
              rw [hStepNext, hStepNext']; omega
            have hCurSh' : (preEqAccStep b accCur' o').1.id =
                (preEqAccStep b accCur o).1.id + offset := by
              rw [preEqAccStep_fst, preEqAccStep_fst]
              simp only [hOffCur]; omega
            -- After preEqAccStep, result.1.id = input.2.nextFresh which is >= threshold
            have hCurGeTh' : (preEqAccStep b accCur o).1.id ≥ threshold := by
              rw [preEqAccStep_fst]; omega
            -- threshold <= (step result).2.nextFresh since it grew
            have hThLe' : threshold ≤ (preEqAccStep b accCur o).2.nextFresh := by
              rw [hStepNext]; omega
            have hOsSh' : ∀ i (hi : i < os_tl.length) (hi' : i < os'_tl.length),
                (os'_tl.get ⟨i, hi'⟩).id = (os_tl.get ⟨i, hi⟩).id + offset := by
              intro i hi _
              have hi' : i + 1 < (o :: os_tl).length := by simp; omega
              have hShift := hOsShCur (i + 1) hi' (by simp [hLen']; omega)
              simp only [List.get_cons_succ] at hShift
              convert hShift using 2
            have hOsGeTh' : ∀ o_t ∈ os_tl, o_t.id ≥ threshold :=
              fun o_t ho_t => hOsGeTh_Cur o_t (List.mem_cons_of_mem o ho_t)
            -- clause must be in the tail fold since it's not in (preEqAccStep b accCur' o').2
            have hClauseInTail : clause ∈ (os'_tl.foldl (preEqAccStep b)
                (preEqAccStep b accCur' o')).2.clauses := hInCur
            -- clause is not in the step's output
            have hClauseNotInStep : clause ∉ (preEqAccStep b accCur' o').2.clauses := hInStep'
            -- Get the bound for o
            have hOLtNext : o.id < accCur.2.nextFresh := hOsLtNext_Cur o (by simp)
            -- WF is preserved through step (with cur and o bounds)
            have hStepWF := preEqAccStep_wf b accCur o hWFCur hCurLtNext_Cur hOLtNext
            have hWF' : (preEqAccStep b accCur o).2.WellFormed := hStepWF.1
            have hCurLtNext' : (preEqAccStep b accCur o).1.id < (preEqAccStep b accCur o).2.nextFresh :=
              hStepWF.2
            -- os_tl FVars still have id < new nextFresh (since nextFresh grew)
            have hOsLtNext' : ∀ o_t ∈ os_tl, o_t.id < (preEqAccStep b accCur o).2.nextFresh := by
              intro o_t ho_t
              have h := hOsLtNext_Cur o_t (List.mem_cons_of_mem o ho_t)
              rw [hStepNext]; omega
            -- Convert satisfaction to NEW clauses form for tail
            have hSatTailNew : ∀ c ∈ (os_tl.foldl (preEqAccStep b) (preEqAccStep b accCur o)).2.clauses,
                c ∉ (preEqAccStep b accCur o).2.clauses → SAT.Clause.eval σ c = true := by
              intro c hC hNotInStep
              -- c is in the full fold output but not in the first step
              -- So c is NEW relative to accCur (since step only adds clauses from accCur + new)
              have hNotInAccCur : c ∉ accCur.2.clauses := by
                intro hInAccCur
                have hInStep := preEqAccStep_clauses_subset b accCur o hInAccCur
                exact hNotInStep hInStep
              exact hSatNewCur c hC hNotInAccCur

            exact ih os'_tl (preEqAccStep b accCur o) (preEqAccStep b accCur' o')
              hOff' hMon' hCurSh' hCurGeTh' hCurLtNext' hThLe' hWF' hLen' hOsSh' hOsGeTh' hOsLtNext'
              hSatTailNew hClauseInTail hClauseNotInStep

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- preEqObligationStep increments nextFresh in a way that depends only on world w.
    This is the key property: the increment is the same regardless of starting state. -/
lemma preEqObligationStep_nextFresh_increment (b : Bounds S) (t t' : b.times)
    (w : WId b) (st1 st2 : EncState b) :
    (preEqObligationStep b t t' ([], st1) w).2.nextFresh - st1.nextFresh =
    (preEqObligationStep b t t' ([], st2) w).2.nextFresh - st2.nextFresh := by
  -- Both follow the same path through mkDw and mkOw
  -- mkDw's increment depends only on candidates = allWorlds.filter(sameSig w)
  -- mkOw adds 1 Fresh
  unfold preEqObligationStep
  simp only
  -- The increment from mkDw depends on cands.length (or 1 for empty case)
  -- Plus mkOw adds exactly 1
  have hOw1 : (mkOw b t w (mkDw b t' w st1).1 (mkDw b t' w st1).2).2.nextFresh =
      (mkDw b t' w st1).2.nextFresh + 1 :=
    mkOw_nextFresh b t w (mkDw b t' w st1).1 (mkDw b t' w st1).2
  have hOw2 : (mkOw b t w (mkDw b t' w st2).1 (mkDw b t' w st2).2).2.nextFresh =
      (mkDw b t' w st2).2.nextFresh + 1 :=
    mkOw_nextFresh b t w (mkDw b t' w st2).1 (mkDw b t' w st2).2
  rw [hOw1, hOw2]
  -- Now need mkDw increment is same for both
  -- Goal: (mkDw b t' w st1).2.nextFresh + 1 - st1.nextFresh =
  --       (mkDw b t' w st2).2.nextFresh + 1 - st2.nextFresh
  -- mkDw_snd_nextFresh_eq tells us the formula for each, which is the same for both
  -- Both mkDw's add same increment since they use same cands list
  -- (cands depends on w, not on starting state)
  have hDw1 := mkDw_snd_nextFresh_eq b t' w st1
  have hDw2 := mkDw_snd_nextFresh_eq b t' w st2
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  simp only at hDw1 hDw2
  cases hEmpty : cands.isEmpty
  · simp only [hEmpty, ↓reduceIte, Bool.false_eq_true] at hDw1 hDw2; omega
  · simp only [hEmpty, ↓reduceIte] at hDw1 hDw2; omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Structural determinism for NEW clauses only from preEqObligationStep.
    Unlike preEqObligationStep_structural_determinism, this doesn't require σ to satisfy
    the base state's clauses - only the output state's clauses. This is sufficient for
    proving satisfaction of NEW clauses (those not in the base state).
    This is the key lemma for the fold proof where we don't have σ satisfaction
    of intermediate st'-side states. -/
lemma preEqObligationStep_newClauses_structural_determinism (b : Bounds S) (t t' : b.times)
    (w : WId b) (acc acc' : List (FVar b) × EncState b) (offset : Nat)
    (hOffset : offset = acc'.2.nextFresh - acc.2.nextFresh)
    (hMono : acc.2.nextFresh ≤ acc'.2.nextFresh)
    (hWF : acc.2.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (preEqObligationStep b t t' acc w).2.clauses, c ∉ acc.2.clauses →
        SAT.Clause.eval σ c = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (preEqObligationStep b t t' acc' w).2.clauses)
    (hClauseNotInBase : clause ∉ acc'.2.clauses) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < acc'.2.nextFresh then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    SAT.Clause.eval σ' clause = true := by
  intro σ'
  classical
  -- Decompose preEqObligationStep into mkOw ∘ mkDw
  simp only [preEqObligationStep] at hClauseMem hSatNew

  -- Get clause structure for both acc and acc'
  have hOwClausesAcc :=
    mkOw_clauses_eq_append b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
  have hOwClausesAcc' :=
    mkOw_clauses_eq_append b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2
  rcases mkDw_clauses_eq_append (b := b) (t' := t') (w := w) (st := acc.2) with
    ⟨newDwAcc, hDwAccEq⟩
  rcases mkDw_clauses_eq_append (b := b) (t' := t') (w := w) (st := acc'.2) with
    ⟨newDwAcc', hDwAcc'Eq⟩

  -- Key indices
  have hDAccGe : (mkDw b t' w acc.2).1.id ≥ acc.2.nextFresh := mkDw_fst_ge b t' w acc.2
  have hDAcc'Ge : (mkDw b t' w acc'.2).1.id ≥ acc'.2.nextFresh := mkDw_fst_ge b t' w acc'.2

  have hDAccId := mkDw_fst_id b t' w acc.2
  have hDAcc'Id := mkDw_fst_id b t' w acc'.2

  have hDwNextAcc := mkDw_snd_nextFresh_eq b t' w acc.2
  have hDwNextAcc' := mkDw_snd_nextFresh_eq b t' w acc'.2

  have hOAccId := mkOw_fst_id b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
  have hOAcc'Id := mkOw_fst_id b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2

  -- D and O indices differ by offset
  have hDShift : (mkDw b t' w acc'.2).1.id = (mkDw b t' w acc.2).1.id + offset := by
    simp only [hDAccId, hDAcc'Id, hOffset]
    split <;> omega

  have hOShift : (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id =
                 (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1.id + offset := by
    simp only [hOAccId, hOAcc'Id, hDwNextAcc, hDwNextAcc', hOffset]
    split <;> omega

  -- Decompose clause membership
  rw [hOwClausesAcc'] at hClauseMem
  cases List.mem_append.mp hClauseMem with
  | inl hInOwClauses' =>
    -- clause is one of the 3 mkOw clauses (for acc')
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hInOwClauses'

    -- Get the corresponding acc-side satisfaction from hSatNew
    -- O.id = (mkDw ...).2.nextFresh ≥ acc.2.nextFresh, so mkOw clauses are NEW
    have hOId := mkOw_fst_id b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
    have hOGe : (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1.id ≥
        acc.2.nextFresh := by
      rw [hOId]
      have h := mkDw_snd_nextFresh_ge b t' w acc.2
      omega
    -- Helper: mkOw clauses have Fresh O, so not in acc.2.clauses (by WF)
    have hOwClauseNew : ∀ c ∈ [[SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
              (mkDw b t' w acc.2).2).1),
          SAT.Lit.neg (FVar.toVar b (mkDw b t' w acc.2).1)],
        [SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
              (mkDw b t' w acc.2).2).1),
          SAT.Lit.pos (Var.Mem t w)],
        [SAT.Lit.neg (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
              (mkDw b t' w acc.2).2).1),
          SAT.Lit.neg (Var.Mem t w),
          SAT.Lit.pos (FVar.toVar b (mkDw b t' w acc.2).1)]], c ∉ acc.2.clauses := by
      intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with hc1 | hc2 | hc3
      all_goals
        intro hIn
        have hClauseWF := hWF _ hIn
        first
        | have hLit : SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
              (mkDw b t' w acc.2).2).1) ∈ c := by subst hc1 <;> simp
        | have hLit : SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
              (mkDw b t' w acc.2).2).1) ∈ c := by subst hc2 <;> simp
        | have hLit : SAT.Lit.neg (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
              (mkDw b t' w acc.2).2).1) ∈ c := by subst hc3; simp
        have hLitWF := hClauseWF _ hLit
        simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar] at hLitWF
        omega
    -- Now derive satisfaction from hSatNew
    have hSatOwClauses :
        ([ [SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
                (mkDw b t' w acc.2).2).1),
            SAT.Lit.neg (FVar.toVar b (mkDw b t' w acc.2).1)]
          , [SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
                (mkDw b t' w acc.2).2).1),
            SAT.Lit.pos (Var.Mem t w)]
          , [SAT.Lit.neg (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
                (mkDw b t' w acc.2).2).1),
            SAT.Lit.neg (Var.Mem t w),
            SAT.Lit.pos (FVar.toVar b (mkDw b t' w acc.2).1)] ]).all
          (SAT.Clause.eval σ) = true := by
      rw [List.all_eq_true]
      intro c hc
      apply hSatNew c
      · rw [hOwClausesAcc]; exact List.mem_append.mpr (Or.inl hc)
      · exact hOwClauseNew c hc

    -- Prove each mkOw clause case using SAT.Clause.eval_eq_any to find satisfying literal
    rcases hInOwClauses' with hC1 | hC2 | hC3
    · -- Case 1: clause = [pos o', neg d']
      subst hC1
      have hSatC1 : SAT.Clause.eval σ [SAT.Lit.pos (FVar.toVar b (mkOw b t w
            (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1),
          SAT.Lit.neg (FVar.toVar b (mkDw b t' w acc.2).1)] = true := by
        simp only [List.all_cons, Bool.and_eq_true, List.all_nil, and_true] at hSatOwClauses
        exact hSatOwClauses.1
      rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC1 ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC1
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
      rcases hLitMem with hL1 | hL2
      · -- lit = pos o
        have hO'Ge : (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id ≥
            acc'.2.nextFresh := by
          rw [hOAcc'Id]
          have h := mkDw_snd_nextFresh_ge b t' w acc'.2
          omega
        refine ⟨SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc'.2).1
            (mkDw b t' w acc'.2).2).1), by simp, ?_⟩
        simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hO'Ge, ↓reduceIte]
        rw [show (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id -
              offset =
            (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1.id by
          omega]
        subst hL1; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
      · -- lit = neg d
        have hD'Ge : (mkDw b t' w acc'.2).1.id ≥ acc'.2.nextFresh := hDAcc'Ge
        refine ⟨SAT.Lit.neg (FVar.toVar b (mkDw b t' w acc'.2).1), by simp, ?_⟩
        simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hD'Ge, ↓reduceIte]
        rw [show (mkDw b t' w acc'.2).1.id - offset =
            (mkDw b t' w acc.2).1.id by omega]
        subst hL2; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
    · -- Case 2: clause = [pos o', pos (Mem t w)]
      subst hC2
      have hSatC2 : SAT.Clause.eval σ [SAT.Lit.pos (FVar.toVar b (mkOw b t w
            (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1),
          SAT.Lit.pos (Var.Mem t w)] = true := by
        simp only [List.all_cons, Bool.and_eq_true, List.all_nil, and_true] at hSatOwClauses
        exact hSatOwClauses.2.1
      rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC2 ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
      rcases hLitMem with hL1 | hL2
      · -- lit = pos o
        have hO'Ge : (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id ≥
            acc'.2.nextFresh := by
          rw [hOAcc'Id]
          have h := mkDw_snd_nextFresh_ge b t' w acc'.2
          omega
        refine ⟨SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc'.2).1
            (mkDw b t' w acc'.2).2).1), by simp, ?_⟩
        simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hO'Ge, ↓reduceIte]
        rw [show (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id -
              offset =
            (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1.id by
          omega]
        subst hL1; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
      · -- lit = pos (Mem t w) - non-Fresh
        refine ⟨SAT.Lit.pos (Var.Mem t w), by simp, ?_⟩
        simp only [SAT.Lit.eval, σ']
        subst hL2; simp only [SAT.Lit.eval] at hLitTrue; exact hLitTrue
    · -- Case 3: clause = [neg o', neg (Mem t w), pos d']
      subst hC3
      have hSatC3 : SAT.Clause.eval σ [SAT.Lit.neg (FVar.toVar b (mkOw b t w
            (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1),
          SAT.Lit.neg (Var.Mem t w),
          SAT.Lit.pos (FVar.toVar b (mkDw b t' w acc.2).1)] = true := by
        simp only [List.all_cons, Bool.and_eq_true, List.all_nil, and_true] at hSatOwClauses
        exact hSatOwClauses.2.2
      rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC3 ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC3
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
      rcases hLitMem with hL1 | hL2 | hL3
      · -- lit = neg o
        have hO'Ge : (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id ≥
            acc'.2.nextFresh := by
          rw [hOAcc'Id]
          have h := mkDw_snd_nextFresh_ge b t' w acc'.2
          omega
        refine ⟨SAT.Lit.neg (FVar.toVar b (mkOw b t w (mkDw b t' w acc'.2).1
            (mkDw b t' w acc'.2).2).1), by simp, ?_⟩
        simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hO'Ge, ↓reduceIte]
        rw [show (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id -
              offset =
            (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1.id by
          omega]
        subst hL1; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
      · -- lit = neg (Mem t w) - non-Fresh
        refine ⟨SAT.Lit.neg (Var.Mem t w), by simp, ?_⟩
        simp only [SAT.Lit.eval, σ']
        subst hL2; simp only [SAT.Lit.eval] at hLitTrue; exact hLitTrue
      · -- lit = pos d
        have hD'Ge : (mkDw b t' w acc'.2).1.id ≥ acc'.2.nextFresh := hDAcc'Ge
        refine ⟨SAT.Lit.pos (FVar.toVar b (mkDw b t' w acc'.2).1), by simp, ?_⟩
        simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hD'Ge, ↓reduceIte]
        rw [show (mkDw b t' w acc'.2).1.id - offset =
            (mkDw b t' w acc.2).1.id by omega]
        subst hL3; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
  | inr hInDwOrBase' =>
    -- clause is in (mkDw b t' w acc'.2).2.clauses
    rw [hDwAcc'Eq] at hInDwOrBase'
    cases List.mem_append.mp hInDwOrBase' with
    | inl hInNewDw' =>
      -- clause is in newDwAcc' (mkDw's new clauses for acc')
      -- Use mkDw_newClauses_structural_determinism
      -- First derive clause ∈ (mkDw b t' w acc'.2).2.clauses
      have hClauseInMkDw' : clause ∈ (mkDw b t' w acc'.2).2.clauses := by
        rw [hDwAcc'Eq]
        exact List.mem_append.mpr (Or.inl hInNewDw')
      -- Derive hSatNew for mkDw output (NEW clauses only)
      have hSatNewMkDw : ∀ c ∈ (mkDw b t' w acc.2).2.clauses, c ∉ acc.2.clauses →
          SAT.Clause.eval σ c = true := by
        intro c hc hNotAcc
        apply hSatNew c
        · rw [hOwClausesAcc]; exact List.mem_append.mpr (Or.inr hc)
        · exact hNotAcc
      -- Apply the helper lemma
      exact mkDw_newClauses_structural_determinism b t' w acc.2 acc'.2 offset hOffset hMono hWF σ
        hSatNewMkDw clause hClauseInMkDw' hClauseNotInBase
    | inr hInBase' =>
      -- clause ∈ acc'.2.clauses - contradicts hClauseNotInBase
      exact absurd hInBase' hClauseNotInBase

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Fresh variables in new clauses of preEqObligationStep have index >= input state's nextFresh.
    This is because Fresh vars are allocated starting at the input nextFresh. -/
lemma preEqObligationStep_newClauses_fresh_ge (b : Bounds S) (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (preEqObligationStep b t t' acc w).2.clauses)
    (hNotInAcc : clause ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ clause)
    (n : Nat) (hFresh : lit.getVar = Var.Fresh n) :
    n ≥ acc.2.nextFresh := by
  classical
  -- Unfold preEqObligationStep
  simp only [preEqObligationStep] at hClause

  -- Key facts about Fresh indices (using direct expressions)
  have hDGe : (mkDw b t' w acc.2).1.id ≥ acc.2.nextFresh := mkDw_fst_ge b t' w acc.2
  have hStDwGe : (mkDw b t' w acc.2).2.nextFresh ≥ acc.2.nextFresh := by
    have h := mkDw_snd_nextFresh_ge b t' w acc.2; omega
  have hOId : (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1.id =
              (mkDw b t' w acc.2).2.nextFresh :=
    mkOw_fst_id b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
  have hOGe : (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1.id ≥ acc.2.nextFresh := by
    rw [hOId]; exact hStDwGe

  -- Decompose clauses using existing lemmas
  have hOwClausesEq :=
    mkOw_clauses_eq_append b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
  rcases mkDw_clauses_eq_append (b := b) (t' := t') (w := w) (st := acc.2) with
    ⟨newDw, hDwClausesEq⟩

  -- Transform hClause using the decomposition lemmas
  rw [hOwClausesEq, hDwClausesEq] at hClause

  -- clause is in one of: 3 mkOw clauses, newDw, or acc.2.clauses
  -- Since hNotInAcc says clause ∉ acc.2.clauses, clause is in mkOw or newDw
  -- Split into mkOw clauses vs (newDw ++ acc.2.clauses)
  cases List.mem_append.mp hClause with
  | inl hInOwClauses =>
    -- clause is in the 3-element list of mkOw clauses
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hInOwClauses
    rcases hInOwClauses with hOwC1 | hOwC2 | hOwC3
    · -- Case 1: clause = [pos o, neg d]
      subst hOwC1
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      rcases hLit with hPosO | hNegD
      · -- lit = pos o
        subst hPosO
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        injection hFresh with hN; omega
      · -- lit = neg d
        subst hNegD
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        injection hFresh with hN; omega
    · -- Case 2: clause = [pos o, pos (Mem t w)]
      subst hOwC2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      rcases hLit with hPosO | hMem
      · -- lit = pos o
        subst hPosO
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        injection hFresh with hN; omega
      · -- lit = pos (Mem t w) - not Fresh, contradiction
        subst hMem; simp only [SAT.Lit.getVar] at hFresh; exact Var.noConfusion hFresh
    · -- Case 3: clause = [neg o, neg (Mem t w), pos d]
      subst hOwC3
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      rcases hLit with hNegO | hMem | hPosD
      · -- lit = neg o
        subst hNegO
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        injection hFresh with hN; omega
      · -- lit = neg (Mem t w) - not Fresh, contradiction
        subst hMem; simp only [SAT.Lit.getVar] at hFresh; exact Var.noConfusion hFresh
      · -- lit = pos d
        subst hPosD
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        injection hFresh with hN; omega
  | inr hInDwOrAcc =>
    -- clause is in newDw ++ acc.2.clauses
    cases List.mem_append.mp hInDwOrAcc with
    | inl hDwClause =>
      -- Case 4: clause ∈ newDw (from mkDw)
      -- Need to show clause ∈ (mkDw b t' w acc.2).2.clauses
      have hInMkDw : clause ∈ (mkDw b t' w acc.2).2.clauses := by
        rw [hDwClausesEq]; exact List.mem_append_left _ hDwClause
      exact mkDw_newClauses_fresh_ge b t' w acc.2 clause hInMkDw hNotInAcc lit hLit n hFresh
    | inr hAccClause =>
      -- Case 5: clause ∈ acc.2.clauses - contradicts hNotInAcc
      exact absurd hAccClause hNotInAcc

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- New clauses from preEqObligationStep have at least one Fresh variable.
    preEqObligationStep = mkDw then mkOw, both of which add clauses with Fresh vars. -/
lemma preEqObligationStep_newClause_exists_fresh (b : Bounds S) (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (preEqObligationStep b t t' acc w).2.clauses)
    (hNotInAcc : clause ∉ acc.2.clauses) :
    ∃ lit ∈ clause, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  classical
  simp only [preEqObligationStep] at hClause
  -- preEqObligationStep does: mkDw → mkOw
  -- Clauses come from mkOw output, which is either:
  -- 1. New clauses from mkOw (contain Fresh o)
  -- 2. Clauses from mkDw (which contain Fresh d or are from acc.2)
  let stDw := (mkDw b t' w acc.2).2
  by_cases hInDw : clause ∈ stDw.clauses
  · -- clause ∈ mkDw output
    by_cases hInAcc : clause ∈ acc.2.clauses
    · exact absurd hInAcc hNotInAcc
    · -- clause is new from mkDw
      -- hInDw : clause ∈ stDw.clauses = clause ∈ (mkDw b t' w acc.2).2.clauses
      have ⟨lit, hLit, n, hFresh, _⟩ := mkDw_newClause_exists_fresh_ge b t' w acc.2 clause
        hInDw hInAcc
      exact ⟨lit, hLit, n, hFresh⟩
  · -- clause ∉ mkDw output, so clause is new from mkOw
    have ⟨lit, hLit, n, hFresh, _⟩ := mkOw_newClause_exists_fresh_ge b t w
      (mkDw b t' w acc.2).1 stDw clause hClause hInDw
    exact ⟨lit, hLit, n, hFresh⟩

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- preEqObligationStep preserves well-formedness. -/
lemma preEqObligationStep_wf (b : Bounds S) (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b)
    (hWF : EncState.WellFormed acc.2) :
    EncState.WellFormed (preEqObligationStep b t t' acc w).2 := by
  unfold preEqObligationStep
  simp only
  -- preEqObligationStep = mkOw ∘ mkDw
  have hDwWF := mkDw_wf b t' w acc.2 hWF
  have hDLt := mkDw_fst_lt_snd_nextFresh b t' w acc.2
  exact mkOw_wf b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2 hDwWF hDLt

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Fold-level structural determinism for NEW clauses from preEqObligationStep fold.
    Given two parallel folds over the same world list with offset states,
    if σ satisfies ALL clauses from the ws-side fold, then σ' satisfies any
    NEW clause (not inherited from st'.clauses) from the ws'-side fold.

    This is the newClauses version that doesn't require σ to satisfy st'.clauses. -/
lemma foldl_preEqObligationStep_newClauses_structural_determinism (b : Bounds S)
    (t t' : b.times) (ws : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : st.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (ws.foldl (preEqObligationStep b t t') ([], st)).2.clauses,
               c ∉ st.clauses → SAT.Clause.eval σ c = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (ws.foldl (preEqObligationStep b t t') ([], st')).2.clauses)
    (hClauseNew : clause ∉ st'.clauses) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < st'.nextFresh then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    SAT.Clause.eval σ' clause = true := by
  intro σ'
  classical
  suffices ∀ (wws : List (WId b)) (accCur accCur' : List (FVar b) × EncState b),
      offset = accCur'.2.nextFresh - accCur.2.nextFresh →
      accCur.2.nextFresh ≤ accCur'.2.nextFresh →
      st'.nextFresh ≤ accCur'.2.nextFresh → -- Track st' threshold
      accCur.2.WellFormed → -- Track WF
      st.nextFresh ≤ accCur.2.nextFresh → -- Track st threshold for hSatNew
      (∀ c ∈ (wws.foldl (preEqObligationStep b t t') accCur).2.clauses,
         c ∉ st.clauses → SAT.Clause.eval σ c = true) →
      clause ∈ (wws.foldl (preEqObligationStep b t t') accCur').2.clauses →
      clause ∉ accCur'.2.clauses →
      SAT.Clause.eval σ' clause = true by
    exact this ws ([], st) ([], st') hOffset hMono (Nat.le_refl _) hWF (Nat.le_refl _)
      hSatNew hClauseMem hClauseNew

  intro wws accCur accCur'
  induction wws generalizing accCur accCur' with
  | nil =>
      intro _ _ _ _ _ _ hIn hNotIn
      simp only [List.foldl_nil] at hIn
      exact absurd hIn hNotIn
  | cons w ws_tl ih =>
      intro hOffCur hMonCur hStGeCur hWFCur hStGeAcc hSatCur hInCur hNotInCur
      simp only [List.foldl_cons] at hSatCur hInCur

      set stepCur := preEqObligationStep b t t' accCur w
      set stepCur' := preEqObligationStep b t t' accCur' w

      -- Offset is preserved through the step
      -- Key: preEqObligationStep's effect on .2 only depends on input .2, not .1
      -- So (preEqObligationStep acc w).2 = (preEqObligationStep ([], acc.2) w).2
      have hStepOffset : offset = stepCur'.2.nextFresh - stepCur.2.nextFresh := by
        -- preEqObligationStep's effect on .2 only depends on input .2, not .1
        -- Key: (preEqObligationStep acc w).2 = (mkOw (mkDw acc.2)).2
        -- So (preEqObligationStep acc w).2.nextFresh = (mkOw (mkDw acc.2)).2.nextFresh
        -- which only depends on acc.2, not acc.1
        have hIncr := preEqObligationStep_nextFresh_increment b t t' w accCur.2 accCur'.2
        -- hIncr : (preEqObligationStep ([], accCur.2) w).2.nextFresh - accCur.2.nextFresh =
        --         (preEqObligationStep ([], accCur'.2) w).2.nextFresh - accCur'.2.nextFresh
        -- We need monotonicity to apply omega
        have hStepGe := mkDw_snd_nextFresh_ge b t' w accCur.2
        have hStepGe' := mkDw_snd_nextFresh_ge b t' w accCur'.2
        have hOw := mkOw_nextFresh b t w (mkDw b t' w accCur.2).1 (mkDw b t' w accCur.2).2
        have hOw' := mkOw_nextFresh b t w (mkDw b t' w accCur'.2).1 (mkDw b t' w accCur'.2).2
        -- Unfold to get the same form as hIncr
        simp only [stepCur, stepCur', preEqObligationStep] at hIncr ⊢
        omega
      have hStepMono : stepCur.2.nextFresh ≤ stepCur'.2.nextFresh := by
        -- From hStepOffset: offset = stepCur'.2.nextFresh - stepCur.2.nextFresh
        -- offset ≥ 0, so stepCur.2.nextFresh ≤ stepCur'.2.nextFresh
        simp only [stepCur, stepCur']
        -- Use the increment lemma to relate preEqObligationStep outputs
        have hInc := preEqObligationStep_nextFresh_increment b t t' w accCur.2 accCur'.2
        have hGe := mkDw_snd_nextFresh_ge b t' w accCur.2
        have hGe' := mkDw_snd_nextFresh_ge b t' w accCur'.2
        have hOw := mkOw_nextFresh b t w (mkDw b t' w accCur.2).1 (mkDw b t' w accCur.2).2
        have hOw' := mkOw_nextFresh b t w (mkDw b t' w accCur'.2).1 (mkDw b t' w accCur'.2).2
        simp only [preEqObligationStep] at hInc ⊢
        omega

      by_cases hInStep' : clause ∈ stepCur'.2.clauses
      · -- Clause is from this step (or inherited from accCur')
        by_cases hInAccCur' : clause ∈ accCur'.2.clauses
        · exact absurd hInAccCur' hNotInCur
        · -- New clause from this step - use step-level SD
          -- Derive hSatNewStep for NEW clauses from this step
          -- Key insight: new clauses from step have Fresh vars >= accCur.2.nextFresh
          -- Since st.nextFresh <= accCur.2.nextFresh, Fresh vars >= st.nextFresh
          -- By WF of st, such clauses can't be in st.clauses
          have hSatNewStep : ∀ c ∈ stepCur.2.clauses, c ∉ accCur.2.clauses →
              SAT.Clause.eval σ c = true := by
            intro c hcMem hNotAcc
            -- c is in fold output (by subset from step to fold)
            have hFoldSub := preEqObligation_fold_clauses_subset b t t' ws_tl
                (init := stepCur) rfl
            have hInFold : c ∈ (ws_tl.foldl (preEqObligationStep b t t') stepCur).2.clauses :=
              hFoldSub hcMem
            -- Show c ∉ st.clauses by WF argument
            have hNotSt : c ∉ st.clauses := by
              intro hIn
              -- st is WF, so clauses in st.clauses have Fresh < st.nextFresh
              have hCFB := hWF c hIn
              -- New clauses from preEqObligationStep have Fresh vars >= acc.nextFresh
              -- So any Fresh var in c has id >= accCur.2.nextFresh >= st.nextFresh
              -- But WF says Fresh vars in st.clauses have id < st.nextFresh
              -- This is a contradiction
              -- We need to find ONE Fresh var in c to get the contradiction
              -- All new clauses from preEqObligationStep have at least one Fresh var
              -- (from mkDw/mkOw structure)
              -- Use the structure: preEqObligationStep = mkOw ∘ mkDw
              -- Both mkOw and mkDw add clauses with Fresh vars
              simp only [preEqObligationStep] at hcMem
              -- The clause is from mkOw output
              have hOwSub := mkOw_clauses_subset b t w (mkDw b t' w accCur.2).1
                  (mkDw b t' w accCur.2).2
              -- Either from mkDw (has d Fresh var) or from mkOw (has o Fresh var)
              by_cases hInDw : c ∈ (mkDw b t' w accCur.2).2.clauses
              · -- c is from mkDw - use hNotAcc directly (c ∉ accCur.2.clauses)
                -- mkDw adds clauses with Fresh var d where d.id = acc.2.nextFresh
                -- Get a Fresh lit from c and apply the bound
                have hFreshGe := mkDw_newClause_exists_fresh_ge b t' w accCur.2 c hInDw hNotAcc
                obtain ⟨lit, hLitMem, n, hFresh, hNGe⟩ := hFreshGe
                have hLitFB := hCFB lit hLitMem
                simp only [litFreshBelow] at hLitFB
                rw [hFresh] at hLitFB
                omega
              · -- c is NEW from mkOw (not in mkDw output)
                -- mkOw adds clauses with Fresh var o where o.id >= mkDw.nextFresh
                have hOwNew := mkOw_newClause_exists_fresh_ge b t w (mkDw b t' w accCur.2).1
                    (mkDw b t' w accCur.2).2 c hcMem hInDw
                obtain ⟨lit, hLitMem, n, hFresh, hNGe⟩ := hOwNew
                have hDwMono := mkDw_snd_nextFresh_ge b t' w accCur.2
                have hLitFB := hCFB lit hLitMem
                simp only [litFreshBelow] at hLitFB
                rw [hFresh] at hLitFB
                omega
            exact hSatCur c hInFold hNotSt

          -- The step-level SD lemma uses threshold = accCur'.2.nextFresh
          -- We need to relate this to our σ' which uses threshold = st'.nextFresh
          -- Define the step-level σ'' and show our σ' agrees on this clause
          let σ'' : SAT.Assignment (Var b) := fun v =>
            match v with
            | Var.Fresh n =>
                if n < accCur'.2.nextFresh then σ v
                else σ (Var.Fresh (n - offset))
            | _ => σ v
          have hSD := preEqObligationStep_newClauses_structural_determinism b t t' w
              accCur accCur' offset hOffCur hMonCur hWFCur σ hSatNewStep clause hInStep'
              hInAccCur'

          -- The key: clause has Fresh vars >= accCur'.2.nextFresh (from step output)
          -- and accCur'.2.nextFresh >= st'.nextFresh (from hStGeCur)
          -- so σ' maps them the same way as σ'' would
          -- hSD has type: let σ' := ...; SAT.Clause.eval σ' clause = true
          -- After beta reducing the let, it becomes: SAT.Clause.eval σ'' clause = true
          simp only at hSD  -- Reduce the let binding
          rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSD ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hSD
          refine ⟨lit, hLitMem, ?_⟩

          -- Fresh vars in new clauses are >= accCur'.2.nextFresh
          cases lit with
          | pos v =>
              simp only [SAT.Lit.eval] at hLitTrue ⊢
              cases v with
              | Fresh n =>
                  -- Use preEqObligationStep_newClauses_fresh_ge to get n >= accCur'.2.nextFresh
                  have hLitFreshGe : n ≥ accCur'.2.nextFresh :=
                    preEqObligationStep_newClauses_fresh_ge b t t' accCur' w clause
                        hInStep' hInAccCur' (SAT.Lit.pos (Var.Fresh n)) hLitMem n rfl
                  -- n >= accCur'.2.nextFresh >= st'.nextFresh
                  have hGe : n ≥ st'.nextFresh := Nat.le_trans hStGeCur hLitFreshGe
                  have hNotLt : ¬ n < st'.nextFresh := Nat.not_lt.mpr hGe
                  have hNotLtCur : ¬ n < accCur'.2.nextFresh := Nat.not_lt.mpr hLitFreshGe
                  simp only [σ', hNotLt, hNotLtCur, ↓reduceIte] at hLitTrue ⊢
                  exact hLitTrue
              | _ => simp only [σ'] at hLitTrue ⊢; exact hLitTrue
          | neg v =>
              simp only [SAT.Lit.eval] at hLitTrue ⊢
              cases v with
              | Fresh n =>
                  have hLitFreshGe : n ≥ accCur'.2.nextFresh :=
                    preEqObligationStep_newClauses_fresh_ge b t t' accCur' w clause
                        hInStep' hInAccCur' (SAT.Lit.neg (Var.Fresh n)) hLitMem n rfl
                  have hGe : n ≥ st'.nextFresh := Nat.le_trans hStGeCur hLitFreshGe
                  have hNotLt : ¬ n < st'.nextFresh := Nat.not_lt.mpr hGe
                  have hNotLtCur : ¬ n < accCur'.2.nextFresh := Nat.not_lt.mpr hLitFreshGe
                  simp only [σ', hNotLt, hNotLtCur, ↓reduceIte] at hLitTrue ⊢
                  exact hLitTrue
              | _ => simp only [σ'] at hLitTrue ⊢; exact hLitTrue

      · -- Clause is from the tail of the fold - use IH
        have hStGeCur' : st'.nextFresh ≤ stepCur'.2.nextFresh := by
          -- Inline: preEqObligationStep = mkOw ∘ mkDw, both add 1
          simp only [stepCur', preEqObligationStep]
          have hDw := mkDw_snd_nextFresh_ge b t' w accCur'.2
          have hOw := mkOw_nextFresh b t w (mkDw b t' w accCur'.2).1 (mkDw b t' w accCur'.2).2
          omega
        have hWFStep : stepCur.2.WellFormed :=
          preEqObligationStep_wf b t t' accCur w hWFCur
        -- st.nextFresh ≤ stepCur.2.nextFresh (from hStGeAcc and step monotonicity)
        have hStGeStep : st.nextFresh ≤ stepCur.2.nextFresh := by
          simp only [stepCur, preEqObligationStep]
          have hDw := mkDw_snd_nextFresh_ge b t' w accCur.2
          have hOw := mkOw_nextFresh b t w (mkDw b t' w accCur.2).1 (mkDw b t' w accCur.2).2
          omega
        exact ih stepCur stepCur' hStepOffset hStepMono hStGeCur' hWFStep hStGeStep
          hSatCur hInCur hInStep'

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Structural determinism for preEqObligationStep.
    preEqObligationStep composes mkDw then mkOw. -/
lemma preEqObligationStep_structural_determinism (b : Bounds S) (t t' : b.times)
    (w : WId b) (acc acc' : List (FVar b) × EncState b) (offset : Nat)
    (hOffset : offset = acc'.2.nextFresh - acc.2.nextFresh)
    (hMono : acc.2.nextFresh ≤ acc'.2.nextFresh)
    (hWF : EncState.WellFormed acc'.2)
    (σ : SAT.Assignment (Var b))
    (hSat : (preEqObligationStep b t t' acc w).2.clauses.all (SAT.Clause.eval σ) = true)
    (hSatBase : acc'.2.clauses.all (SAT.Clause.eval σ) = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < acc'.2.nextFresh then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    (preEqObligationStep b t t' acc' w).2.clauses.all (SAT.Clause.eval σ') = true := by
  classical
  intro σ'

  -- Rewrite using preEqObligationStep definition
  -- preEqObligationStep does: (d, stDw) := mkDw b t' w acc.2; (o, stOw) := mkOw b t w d stDw
  -- The final state is stOw = (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).2
  simp only [preEqObligationStep] at hSat ⊢

  -- Step 1: Get mkDw clause satisfaction from final state
  have hMkDwSubset : (mkDw b t' w acc.2).2.clauses ⊆
      (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).2.clauses :=
    mkOw_clauses_subset b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
  have hSatDw : (mkDw b t' w acc.2).2.clauses.all (SAT.Clause.eval σ) = true := by
    rw [List.all_eq_true] at hSat ⊢
    intro c hc
    exact hSat c (hMkDwSubset hc)

  -- Step 2: Apply mkDw_structural_determinism
  have hDwSD := mkDw_structural_determinism b t' w acc.2 acc'.2 offset
    hOffset hMono hWF σ hSatDw hSatBase

  -- Step 3: Prove d'.id = d.id + offset
  have hDShift : (mkDw b t' w acc'.2).1.id = (mkDw b t' w acc.2).1.id + offset := by
    show (mkDw b t' w acc'.2).1.id = (mkDw b t' w acc.2).1.id + offset
    generalize hSt : acc.2 = st
    generalize hSt' : acc'.2 = st'
    have hOff : offset = st'.nextFresh - st.nextFresh := by rw [← hSt, ← hSt']; exact hOffset
    have hM : st.nextFresh ≤ st'.nextFresh := by rw [← hSt, ← hSt']; exact hMono
    unfold mkDw
    set cands := (WId.allWorlds b).filter (fun w'' => sameSig b w w'')
    by_cases hEmpty : cands = []
    · simp only [cands, hEmpty, EncState.allocFresh, hOff]; omega
    · obtain ⟨c, cs, hCands⟩ := List.exists_cons_of_ne_nil hEmpty
      simp only [cands, hCands, mkBigOrIff_fst]
      have hFoldFresh : (List.foldl (fun (ac : List (Var b) × EncState b) w'' =>
          let (vs, st'') := ac
          let (y, st''') := mkY b t' w w'' st''
          (FVar.toVar b y :: vs, st''')) ([], st) (c :: cs)).2.nextFresh =
          st.nextFresh + (c :: cs).length := mkDw_fold_nextFresh b t' w (c :: cs) ([], st)
      have hFoldFresh' : (List.foldl (fun (ac : List (Var b) × EncState b) w'' =>
          let (vs, st'') := ac
          let (y, st''') := mkY b t' w w'' st''
          (FVar.toVar b y :: vs, st''')) ([], st') (c :: cs)).2.nextFresh =
          st'.nextFresh + (c :: cs).length := mkDw_fold_nextFresh b t' w (c :: cs) ([], st')
      rw [hFoldFresh, hFoldFresh', hOff]; omega

  -- Step 4: Prove offset preservation through mkDw
  have hDwOffset : offset = (mkDw b t' w acc'.2).2.nextFresh - (mkDw b t' w acc.2).2.nextFresh := by
    show offset = (mkDw b t' w acc'.2).2.nextFresh - (mkDw b t' w acc.2).2.nextFresh
    generalize hSt : acc.2 = st
    generalize hSt' : acc'.2 = st'
    have hOff : offset = st'.nextFresh - st.nextFresh := by rw [← hSt, ← hSt']; exact hOffset
    unfold mkDw
    set cands := (WId.allWorlds b).filter (fun w'' => sameSig b w w'')
    by_cases hEmpty : cands = []
    · simp only [cands, hEmpty, EncState.allocFresh, EncState.addClause, hOff]; omega
    · obtain ⟨c, cs, hCands⟩ := List.exists_cons_of_ne_nil hEmpty
      simp only [cands, hCands, mkBigOrIff_nextFresh]
      have hFoldFresh : (List.foldl (fun (ac : List (Var b) × EncState b) w'' =>
          let (vs, st'') := ac
          let (y, st''') := mkY b t' w w'' st''
          (FVar.toVar b y :: vs, st''')) ([], st) (c :: cs)).2.nextFresh =
          st.nextFresh + (c :: cs).length := mkDw_fold_nextFresh b t' w (c :: cs) ([], st)
      have hFoldFresh' : (List.foldl (fun (ac : List (Var b) × EncState b) w'' =>
          let (vs, st'') := ac
          let (y, st''') := mkY b t' w w'' st''
          (FVar.toVar b y :: vs, st''')) ([], st') (c :: cs)).2.nextFresh =
          st'.nextFresh + (c :: cs).length := mkDw_fold_nextFresh b t' w (c :: cs) ([], st')
      rw [hFoldFresh, hFoldFresh', hOff]; omega

  -- Step 5: Prove d.id ≥ acc.2.nextFresh (the original base state)
  have hDGe : (mkDw b t' w acc.2).1.id ≥ acc.2.nextFresh := mkDw_fst_ge b t' w acc.2
  have hDGe' : (mkDw b t' w acc'.2).1.id ≥ acc'.2.nextFresh := mkDw_fst_ge b t' w acc'.2

  -- Step 6: Show d'.id ≥ acc'.2.nextFresh (so σ' uses unshift for d')
  have hD'GeBase : (mkDw b t' w acc'.2).1.id ≥ acc'.2.nextFresh := hDGe'

  -- Step 7: Show o.id ≥ acc.2.nextFresh and o'.id ≥ acc'.2.nextFresh
  -- o is allocated after d, so o.id ≥ (mkDw output).nextFresh ≥ acc.2.nextFresh
  have hOGe : (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1.id ≥ acc.2.nextFresh := by
    have h1 := mkOw_fst b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
    have h2 := mkDw_snd_nextFresh_ge b t' w acc.2
    simp only [h1]
    omega
  have hOGe' :
      (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id ≥
      acc'.2.nextFresh := by
    have h1 := mkOw_fst b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2
    have h2 := mkDw_snd_nextFresh_ge b t' w acc'.2
    simp only [h1]
    omega

  -- Step 8: Show o'.id = o.id + offset
  -- First we need to show (mkDw..acc.2).2.nextFresh ≤ (mkDw..acc'.2).2.nextFresh
  -- Use the structure of mkDw: mkDw adds a deterministic amount based on cands.length
  -- Since the cands are the same for both calls, the nextFresh increment is the same
  have hDwMono : (mkDw b t' w acc.2).2.nextFresh ≤ (mkDw b t' w acc'.2).2.nextFresh := by
    classical
    set cands := (WId.allWorlds b).filter (fun w'' => sameSig b w w'')
    by_cases hEmpty : cands = []
    · -- Empty case: mkDw just allocates 1 fresh
      have h1 : (mkDw b t' w acc.2).2.nextFresh = acc.2.nextFresh + 1 := by
        unfold mkDw
        simp only [cands, hEmpty, EncState.allocFresh, EncState.addClause]
      have h2 : (mkDw b t' w acc'.2).2.nextFresh = acc'.2.nextFresh + 1 := by
        unfold mkDw
        simp only [cands, hEmpty, EncState.allocFresh, EncState.addClause]
      rw [h1, h2]; omega
    · -- Non-empty case: fold + mkBigOrIff
      obtain ⟨c, cs, hCands⟩ := List.exists_cons_of_ne_nil hEmpty
      have hF := mkDw_fold_nextFresh b t' w (c :: cs) ([], acc.2)
      have hF' := mkDw_fold_nextFresh b t' w (c :: cs) ([], acc'.2)
      have h1 : (mkDw b t' w acc.2).2.nextFresh = acc.2.nextFresh + (c :: cs).length + 1 := by
        unfold mkDw
        simp only [cands, hCands, mkBigOrIff_nextFresh, hF]
      have h2 : (mkDw b t' w acc'.2).2.nextFresh = acc'.2.nextFresh + (c :: cs).length + 1 := by
        unfold mkDw
        simp only [cands, hCands, mkBigOrIff_nextFresh, hF']
      rw [h1, h2]; omega
  have hOShift : (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id =
      (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).1.id + offset := by
    simp only [mkOw_fst]
    have h := hDwOffset
    have hM := hDwMono
    omega

  -- Step 9: Handle mkOw clauses directly
  -- The final clauses are: mkOw's 3 clauses + inherited (mkDw + base)
  have hOwClausesEq := mkOw_clauses_eq_append b t w
    (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2
  rw [hOwClausesEq]
  rw [List.all_eq_true]
  intro clause hClause
  cases hClause with
  | head =>
      -- Clause 1: [o', ¬d']
      have hOwClausesEqSt :=
        mkOw_clauses_eq_append b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
      have hClauseSt :
          [SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
              (mkDw b t' w acc.2).2).1),
            SAT.Lit.neg (FVar.toVar b (mkDw b t' w acc.2).1)] ∈
          (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).2.clauses := by
        rw [hOwClausesEqSt]; exact List.Mem.head _
      have hEvalSt := List.all_eq_true.mp hSat _ hClauseSt
      rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
      rcases hLitMem with ⟨⟩ | ⟨_, h1⟩
      · -- lit = pos o
        refine ⟨SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc'.2).1
              (mkDw b t' w acc'.2).2).1),
            List.Mem.head _, ?_⟩
        simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
        simp only [σ']
        have hNotLt :
            ¬ (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id <
              acc'.2.nextFresh :=
          Nat.not_lt.mpr hOGe'
        simp only [hNotLt, ↓reduceIte]
        rw [hOShift, Nat.add_sub_cancel]
        exact hLitTrue
      · rcases h1 with ⟨⟩ | ⟨_, h2⟩
        · -- lit = neg d
          refine ⟨SAT.Lit.neg (FVar.toVar b (mkDw b t' w acc'.2).1),
              List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
          simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
          simp only [σ']
          have hNotLt : ¬ (mkDw b t' w acc'.2).1.id < acc'.2.nextFresh :=
            Nat.not_lt.mpr hD'GeBase
          simp only [hNotLt, ↓reduceIte]
          rw [hDShift, Nat.add_sub_cancel]
          exact hLitTrue
        · cases h2
  | tail _ h1 =>
      cases h1 with
      | head =>
          -- Clause 2: [o', Mem t w]
          have hOwClausesEqSt :=
            mkOw_clauses_eq_append b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
          have hClauseSt :
              [SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
                  (mkDw b t' w acc.2).2).1),
                SAT.Lit.pos (Var.Mem t w)] ∈
              (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).2.clauses := by
            rw [hOwClausesEqSt]; exact List.mem_cons_of_mem _ (List.Mem.head _)
          have hEvalSt := List.all_eq_true.mp hSat _ hClauseSt
          rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
          rcases hLitMem with ⟨⟩ | ⟨_, h2⟩
          · -- lit = pos o
            refine ⟨SAT.Lit.pos (FVar.toVar b (mkOw b t w (mkDw b t' w acc'.2).1
                  (mkDw b t' w acc'.2).2).1),
                List.Mem.head _, ?_⟩
            simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
            simp only [σ']
            have hNotLt :
                ¬ (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id <
                  acc'.2.nextFresh :=
              Nat.not_lt.mpr hOGe'
            simp only [hNotLt, ↓reduceIte]
            rw [hOShift, Nat.add_sub_cancel]
            exact hLitTrue
          · rcases h2 with ⟨⟩ | ⟨_, h3⟩
            · -- lit = pos Mem (non-Fresh)
              refine ⟨SAT.Lit.pos (Var.Mem t w),
                  List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
              simp only [SAT.Lit.eval, σ']
              exact hLitTrue
            · cases h3
      | tail _ h2 =>
          cases h2 with
          | head =>
              -- Clause 3: [¬o', ¬Mem t w, d']
              have hOwClausesEqSt :=
                mkOw_clauses_eq_append b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
              have hClauseSt :
                  [SAT.Lit.neg (FVar.toVar b (mkOw b t w (mkDw b t' w acc.2).1
                      (mkDw b t' w acc.2).2).1),
                    SAT.Lit.neg (Var.Mem t w),
                    SAT.Lit.pos (FVar.toVar b (mkDw b t' w acc.2).1)] ∈
                  (mkOw b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2).2.clauses := by
                rw [hOwClausesEqSt]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.Mem.head _))
              have hEvalSt := List.all_eq_true.mp hSat _ hClauseSt
              rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
              obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
              rcases hLitMem with ⟨⟩ | ⟨_, h3⟩
              · -- lit = neg o
                refine ⟨SAT.Lit.neg (FVar.toVar b (mkOw b t w (mkDw b t' w acc'.2).1
                      (mkDw b t' w acc'.2).2).1),
                    List.Mem.head _, ?_⟩
                simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
                simp only [σ']
                have hNotLt :
                    ¬ (mkOw b t w (mkDw b t' w acc'.2).1 (mkDw b t' w acc'.2).2).1.id <
                      acc'.2.nextFresh :=
                  Nat.not_lt.mpr hOGe'
                simp only [hNotLt, ↓reduceIte]
                rw [hOShift, Nat.add_sub_cancel]
                exact hLitTrue
              · rcases h3 with ⟨⟩ | ⟨_, h4⟩
                · -- lit = neg Mem (non-Fresh)
                  refine ⟨SAT.Lit.neg (Var.Mem t w),
                      List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
                  simp only [SAT.Lit.eval, σ']
                  exact hLitTrue
                · rcases h4 with ⟨⟩ | ⟨_, h5⟩
                  · -- lit = pos d
                    refine ⟨SAT.Lit.pos (FVar.toVar b (mkDw b t' w acc'.2).1),
                        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.Mem.head _)), ?_⟩
                    simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
                    simp only [σ']
                    have hNotLt : ¬ (mkDw b t' w acc'.2).1.id < acc'.2.nextFresh :=
                      Nat.not_lt.mpr hD'GeBase
                    simp only [hNotLt, ↓reduceIte]
                    rw [hDShift, Nat.add_sub_cancel]
                    exact hLitTrue
                  · cases h5
          | tail _ h3 =>
              -- Inherited clauses from mkDw
              have hDwSD' := hDwSD
              rw [List.all_eq_true] at hDwSD'
              exact hDwSD' clause h3

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- preEqObligationStep increases nextFresh. -/
lemma preEqObligationStep_nextFresh_ge (b : Bounds S) (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b) :
    acc.2.nextFresh ≤ (preEqObligationStep b t t' acc w).2.nextFresh := by
  unfold preEqObligationStep
  simp only
  have hDw := mkDw_snd_nextFresh_ge b t' w acc.2
  have hOw := mkOw_nextFresh b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
  omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- addPreEqPair_core is monotonic in nextFresh.
    Uses preEqObligationStep (monotonic) twice, allocFresh (+1), preEqAccStep folds (monotonic),
    and addPreEqExpose (preserves). -/
lemma addPreEqPair_core_nextFresh_mono (b : Bounds S) (H0 H' : b.times) (st : EncState b) :
    st.nextFresh ≤ (addPreEqPair_core b H0 H' st).nextFresh := by
  classical
  simp only [addPreEqPair_core]
  -- Step through the definition, proving monotonicity at each step
  -- Step 1: First obligation fold
  have hObl1 : ∀ acc w, acc.2.nextFresh ≤ (preEqObligationStep b H0 H' acc w).2.nextFresh :=
    preEqObligationStep_nextFresh_ge b H0 H'
  have hObl2 : ∀ acc w, acc.2.nextFresh ≤ (preEqObligationStep b H' H0 acc w).2.nextFresh :=
    preEqObligationStep_nextFresh_ge b H' H0
  -- Define intermediate states upfront
  let fold1Result := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)
  let st1 : EncState b := fold1Result.2
  let fold2Init : List (FVar b) × EncState b := ([], st1)
  -- Step 1: First obligation fold
  have h1 : st.nextFresh ≤ fold1Result.2.nextFresh :=
    foldl_nextFresh_mono_pair (WId.allWorlds b) ([], st) (preEqObligationStep b H0 H') hObl1
  -- Step 2: Second obligation fold
  have h2 : st1.nextFresh ≤
      ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) fold2Init).2.nextFresh :=
    foldl_nextFresh_mono_pair (WId.allWorlds b) fold2Init (preEqObligationStep b H' H0) hObl2
  -- Step 3: allocFresh
  have h3 : ∀ stx, stx.nextFresh < (EncState.allocFresh b stx).2.nextFresh := by
    intro stx; simp [EncState.allocFresh_nextFresh]
  -- Step 4: addClause preserves
  have h4 : ∀ stx c, (EncState.addClause b stx c).nextFresh = stx.nextFresh := by
    intro _ _; simp [EncState.addClause]
  -- Step 5: preEqAccStep folds monotonic
  have hAcc : ∀ acc o, acc.2.nextFresh ≤ (preEqAccStep b acc o).2.nextFresh := by
    intro acc o; rw [preEqAccStep_nextFresh]; omega
  -- Step 6: addPreEqExpose preserves
  have hExpose : ∀ stx v, (addPreEqExpose b H0 H' v stx).nextFresh = stx.nextFresh :=
    fun _ _ => addPreEqExpose_nextFresh b H0 H' _ _
  -- Chain: st → fold1 → fold2 → allocFresh → addClause → accFold1 → accFold2 → expose
  -- Use let bindings for clarity
  let fold2Result := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) fold2Init
  let st2 : EncState b := fold2Result.2
  let obls1 : List (FVar b) := fold1Result.1
  let obls2 : List (FVar b) := fold2Result.1
  let allocResult := EncState.allocFresh b st2
  let u : FVar b := allocResult.1
  let st3 : EncState b := allocResult.2
  let st4 : EncState b := EncState.addClause b st3 [SAT.Lit.pos (FVar.toVar b u)]
  let accFold1Init : FVar b × EncState b := (u, st4)
  let accFold1Result := obls1.foldl (preEqAccStep b) accFold1Init
  let accFold2Init : FVar b × EncState b := (accFold1Result.1, accFold1Result.2)
  let accFold2Result := obls2.foldl (preEqAccStep b) accFold2Init
  let finalResult := addPreEqExpose b H0 H' accFold2Result.1 accFold2Result.2

  -- Now prove each step
  have hAlloc : st2.nextFresh < st3.nextFresh := h3 st2
  have hAdd : st3.nextFresh = st4.nextFresh := h4 st3 [SAT.Lit.pos (FVar.toVar b u)]
  have hAccFold1 : st4.nextFresh ≤ accFold1Result.2.nextFresh :=
    foldl_nextFresh_mono_pair obls1 accFold1Init (preEqAccStep b) hAcc
  have hAccFold2 : accFold1Result.2.nextFresh ≤ accFold2Result.2.nextFresh :=
    foldl_nextFresh_mono_pair obls2 accFold2Init (preEqAccStep b) hAcc
  have hExp : accFold2Result.2.nextFresh = finalResult.nextFresh :=
    hExpose accFold2Result.2 accFold2Result.1

  -- Show the goal equals our finalResult
  change st.nextFresh ≤ finalResult.nextFresh
  calc st.nextFresh
    _ ≤ st1.nextFresh := h1
    _ ≤ st2.nextFresh := h2
    _ ≤ st3.nextFresh := Nat.le_of_lt hAlloc
    _ = st4.nextFresh := hAdd
    _ ≤ accFold1Result.2.nextFresh := hAccFold1
    _ ≤ accFold2Result.2.nextFresh := hAccFold2
    _ = finalResult.nextFresh := hExp

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- addPreEqPair is monotonic in nextFresh.
    Delegates to addPreEqPair_core (monotonic) and optionally adds one clause (preserves). -/
lemma addPreEqPair_nextFresh_mono (b : Bounds S) (H0 H' : b.times) (st : EncState b) :
    st.nextFresh ≤ (addPreEqPair b H0 H' st).nextFresh := by
  classical
  unfold addPreEqPair
  by_cases hEq : H0 = H'
  · subst hEq
    simp only [↓reduceIte, EncState.addClause]
    exact addPreEqPair_core_nextFresh_mono b H0 H0 st
  · simp only [hEq, ↓reduceIte]
    exact addPreEqPair_core_nextFresh_mono b H0 H' st

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Fresh vars in NEW clauses from preEqObligationStep fold have index ≥ init.2.nextFresh.
    Each step allocates Fresh vars starting from its input nextFresh, so all
    Fresh vars in new clauses have index ≥ the initial nextFresh. -/
lemma preEqObligationStep_foldl_newClause_fresh_ge (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (init : List (FVar b) × EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (ws.foldl (preEqObligationStep b t t') init).2.clauses)
    (hNotInit : clause ∉ init.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ clause)
    (n : Nat) (hFresh : lit.getVar = Var.Fresh n) :
    n ≥ init.2.nextFresh := by
  induction ws generalizing init with
  | nil =>
      simp only [List.foldl_nil] at hClause
      exact absurd hClause hNotInit
  | cons w ws' ih =>
      simp only [List.foldl_cons] at hClause
      have hStepMono := preEqObligationStep_nextFresh_ge b t t' init w
      by_cases hInInit : clause ∈ init.2.clauses
      · exact absurd hInInit hNotInit
      · by_cases hInStep : clause ∈ (preEqObligationStep b t t' init w).2.clauses
        · -- clause is NEW from this step
          exact preEqObligationStep_newClauses_fresh_ge b t t' init w clause hInStep hInInit
            lit hLit n hFresh
        · -- clause is from tail fold
          have hGe := ih (preEqObligationStep b t t' init w) hClause hInStep
          omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- New clauses from preEqObligationStep fold have at least one Fresh variable.
    Each step uses mkDw and mkOw which add clauses containing Fresh vars. -/
lemma preEqObligationStep_foldl_newClause_exists_fresh (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (init : List (FVar b) × EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (ws.foldl (preEqObligationStep b t t') init).2.clauses)
    (hNotInit : clause ∉ init.2.clauses) :
    ∃ lit ∈ clause, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  induction ws generalizing init with
  | nil =>
      simp only [List.foldl_nil] at hClause
      exact absurd hClause hNotInit
  | cons w ws' ih =>
      simp only [List.foldl_cons] at hClause
      by_cases hInStep : clause ∈ (preEqObligationStep b t t' init w).2.clauses
      · -- clause is in step output
        by_cases hInInit : clause ∈ init.2.clauses
        · exact absurd hInInit hNotInit
        · -- clause is new from this step
          exact preEqObligationStep_newClause_exists_fresh b t t' init w clause hInStep hInInit
      · -- clause is from tail fold (not in step output)
        exact ih (preEqObligationStep b t t' init w) hClause hInStep

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- The fold of preEqObligationStep preserves the offset between two starting states.
    This is because each step adds the same number of Fresh variables regardless
    of starting state. -/
lemma preEqObligationStep_foldl_offset_preserved (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (st st' : EncState b) :
    (ws.foldl (preEqObligationStep b t t') ([], st')).2.nextFresh -
      (ws.foldl (preEqObligationStep b t t') ([], st)).2.nextFresh =
    st'.nextFresh - st.nextFresh := by
  induction ws generalizing st st' with
  | nil => simp
  | cons w ws' ih =>
      simp only [List.foldl_cons]
      -- Apply IH to intermediate states
      have hIncr := preEqObligationStep_nextFresh_increment b t t' w st st'
      -- IH with intermediate states
      have ihApp := ih (preEqObligationStep b t t' ([], st) w).2
                       (preEqObligationStep b t t' ([], st') w).2
      -- Need to show the folds over ws' starting from step results
      -- have same offset as step results themselves
      -- The fold's .2.nextFresh only depends on init.2, not init.1
      -- So we can rewrite the init's .1 component
      have hFoldNextFreshIndep : ∀ (wws : List (WId b)) (init1 init2 : List (FVar b) × EncState b),
          init1.2 = init2.2 →
          (wws.foldl (preEqObligationStep b t t') init1).2.nextFresh =
          (wws.foldl (preEqObligationStep b t t') init2).2.nextFresh := by
        intro wws init1 init2 hEq
        induction wws generalizing init1 init2 with
        | nil => simp only [List.foldl_nil]; exact congrArg (EncState.nextFresh) hEq
        | cons w'' wws' ih' =>
            simp only [List.foldl_cons]
            apply ih'
            unfold preEqObligationStep
            simp only [hEq]
      simp only [preEqObligationStep] at ihApp ⊢
      -- Define the intermediate mkOw results
      set ow := mkOw b t w (mkDw b t' w st).1 (mkDw b t' w st).2 with hOwDef
      set ow' := mkOw b t w (mkDw b t' w st').1 (mkDw b t' w st').2 with hOw'Def
      -- The goal has inits ([o], ow.2) and ([o'], ow'.2)
      -- But ihApp uses inits ([], ow.2) and ([], ow'.2)
      -- Use independence: fold.nextFresh only depends on init.2
      have hGoalEq1 : (ws'.foldl (preEqObligationStep b t t') ([ow'.1], ow'.2)).2.nextFresh =
          (ws'.foldl (preEqObligationStep b t t') ([], ow'.2)).2.nextFresh :=
        hFoldNextFreshIndep ws' ([ow'.1], ow'.2) ([], ow'.2) rfl
      have hGoalEq2 : (ws'.foldl (preEqObligationStep b t t') ([ow.1], ow.2)).2.nextFresh =
          (ws'.foldl (preEqObligationStep b t t') ([], ow.2)).2.nextFresh :=
        hFoldNextFreshIndep ws' ([ow.1], ow.2) ([], ow.2) rfl
      have hIntOffset : ow'.2.nextFresh - ow.2.nextFresh = st'.nextFresh - st.nextFresh := by
        -- mkDw and mkOw add the same increments regardless of starting state
        -- ow = mkOw (mkDw st), ow' = mkOw (mkDw st')
        -- Both add same number of Fresh vars
        simp only [hOw'Def, hOwDef]
        have hOwNext : (mkOw b t w (mkDw b t' w st).1 (mkDw b t' w st).2).2.nextFresh =
            (mkDw b t' w st).2.nextFresh + 1 :=
          mkOw_nextFresh b t w (mkDw b t' w st).1 (mkDw b t' w st).2
        have hOw'Next : (mkOw b t w (mkDw b t' w st').1 (mkDw b t' w st').2).2.nextFresh =
            (mkDw b t' w st').2.nextFresh + 1 :=
          mkOw_nextFresh b t w (mkDw b t' w st').1 (mkDw b t' w st').2
        rw [hOwNext, hOw'Next]
        have hDw := mkDw_snd_nextFresh_eq b t' w st
        have hDw' := mkDw_snd_nextFresh_eq b t' w st'
        set cands := (WId.allWorlds b).filter (fun w'' => sameSig b w w'')
        simp only at hDw hDw'
        cases hEmpty : cands.isEmpty
        · simp only [hEmpty, ↓reduceIte, Bool.false_eq_true] at hDw hDw'; omega
        · simp only [hEmpty, ↓reduceIte] at hDw hDw'; omega
      rw [hGoalEq1, hGoalEq2, ihApp]
      exact hIntOffset

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- The fold of preEqObligationStep over ws yields a list of length ws.length.
    Each step prepends one FVar, so the final list length equals the input list length. -/
lemma preEqObligationStep_foldl_fst_length (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (init : List (FVar b) × EncState b) :
    (ws.foldl (preEqObligationStep b t t') init).1.length = init.1.length + ws.length := by
  induction ws generalizing init with
  | nil => simp
  | cons w ws' ih =>
      simp only [List.foldl_cons]
      rw [ih]
      unfold preEqObligationStep
      simp only [List.length_cons]
      omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- The fold of preEqObligationStep over ws starting from different states produces
    lists of the same length.
    Since both folds process the same ws, both add ws.length FVars. -/
lemma preEqObligationStep_foldl_fst_length_eq (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (st st' : EncState b) :
    (ws.foldl (preEqObligationStep b t t') ([], st')).1.length =
    (ws.foldl (preEqObligationStep b t t') ([], st)).1.length := by
  rw [preEqObligationStep_foldl_fst_length, preEqObligationStep_foldl_fst_length]

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Generalized version: FVar IDs shift by offset through fold, for arbitrary initial lists. -/
lemma preEqObligationStep_foldl_fst_shift_gen (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (init init' : List (FVar b) × EncState b) (offset : Nat)
    (hOffset : offset = init'.2.nextFresh - init.2.nextFresh)
    (hMono : init.2.nextFresh ≤ init'.2.nextFresh)
    (hLenEq : init'.1.length = init.1.length)
    (hInitShift : ∀ i (hi : i < init.1.length),
        (init'.1.get ⟨i, hLenEq ▸ hi⟩).id = (init.1.get ⟨i, hi⟩).id + offset) :
    let fold := ws.foldl (preEqObligationStep b t t') init
    let fold' := ws.foldl (preEqObligationStep b t t') init'
    let hLenEq' : fold'.1.length = fold.1.length := by
      rw [preEqObligationStep_foldl_fst_length, preEqObligationStep_foldl_fst_length, hLenEq]
    ∀ i (hi : i < fold.1.length),
      (fold'.1.get ⟨i, hLenEq' ▸ hi⟩).id = (fold.1.get ⟨i, hi⟩).id + offset := by
  classical
  induction ws generalizing init init' with
  | nil =>
      intro fold fold' hLenEq' i hi
      -- fold = init, fold' = init' by definition
      exact hInitShift i hi
  | cons w ws' ih =>
      intro fold fold' hLenEq' i hi
      -- Define intermediate results
      set step := preEqObligationStep b t t' init w with hStepDef
      set step' := preEqObligationStep b t t' init' w with hStep'Def
      -- Define the mkOw/mkDw components
      set o := (mkOw b t w (mkDw b t' w init.2).1 (mkDw b t' w init.2).2).1
      set o' := (mkOw b t w (mkDw b t' w init'.2).1 (mkDw b t' w init'.2).2).1
      -- step.1 = o :: init.1 (definitionally via preEqObligationStep unfolding)
      have hStepFst : step.1 = o :: init.1 := rfl
      have hStep'Fst : step'.1 = o' :: init'.1 := rfl
      -- Offset preservation: explicitly compute nextFresh
      -- step.2 = (mkOw b t w (mkDw ...) (mkDw ...).2).2
      -- step.2.nextFresh = (mkDw b t' w init.2).2.nextFresh + 1 (by mkOw_nextFresh)
      have hStepNext : step.2.nextFresh = (mkDw b t' w init.2).2.nextFresh + 1 :=
        mkOw_nextFresh b t w (mkDw b t' w init.2).1 (mkDw b t' w init.2).2
      have hStep'Next : step'.2.nextFresh = (mkDw b t' w init'.2).2.nextFresh + 1 :=
        mkOw_nextFresh b t w (mkDw b t' w init'.2).1 (mkDw b t' w init'.2).2
      have hDwNext := mkDw_snd_nextFresh_eq b t' w init.2
      have hDwNext' := mkDw_snd_nextFresh_eq b t' w init'.2
      have hOffset' : offset = step'.2.nextFresh - step.2.nextFresh := by
        simp only [hStepNext, hStep'Next, hDwNext, hDwNext', hOffset]
        split <;> omega
      have hMono' : step.2.nextFresh ≤ step'.2.nextFresh := by
        simp only [hStepNext, hStep'Next, hDwNext, hDwNext']
        split <;> omega
      -- Length preservation
      have hStepLenEq : step'.1.length = step.1.length := by
        simp only [hStepFst, hStep'Fst, List.length_cons, hLenEq]
      -- Shift for step lists
      have hStepShift : ∀ j (hj : j < step.1.length),
          (step'.1.get ⟨j, hStepLenEq ▸ hj⟩).id = (step.1.get ⟨j, hj⟩).id + offset := by
        intro j hj
        cases j with
        | zero =>
            -- Head element: step.1 = o :: init.1, so step.1[0] = o
            -- step.1.get ⟨0, hj⟩ = o and step'.1.get ⟨0, ...⟩ = o' (definitionally)
            have hGet0 : step.1.get ⟨0, hj⟩ = o := by rfl
            have hGet0' : step'.1.get ⟨0, hStepLenEq ▸ hj⟩ = o' := by rfl
            rw [hGet0, hGet0']
            -- Now goal: o'.id = o.id + offset
            -- o.id = (mkDw b t' w init.2).2.nextFresh (from mkOw_fst_id)
            -- o'.id = (mkDw b t' w init'.2).2.nextFresh (from mkOw_fst_id)
            have hOId : o.id = (mkDw b t' w init.2).2.nextFresh :=
              mkOw_fst_id b t w (mkDw b t' w init.2).1 (mkDw b t' w init.2).2
            have hO'Id : o'.id = (mkDw b t' w init'.2).2.nextFresh :=
              mkOw_fst_id b t w (mkDw b t' w init'.2).1 (mkDw b t' w init'.2).2
            rw [hOId, hO'Id, hDwNext, hDwNext', hOffset]
            -- Now goal is: if cands.isEmpty then ... else ... = (if ... then ... else ...) + ...
            split <;> omega
        | succ j' =>
            -- Tail element from init: step.1[j'+1] = init.1[j']
            have hj' : j' < init.1.length := by
              have hLen : step.1.length = init.1.length + 1 := by rfl
              omega
            have hj'' : j' < init'.1.length := hLenEq ▸ hj'
            change (init'.1.get ⟨j', hj''⟩).id = (init.1.get ⟨j', hj'⟩).id + offset
            exact hInitShift j' hj'
      -- Apply IH
      exact ih step step' hOffset' hMono' hStepLenEq hStepShift i hi

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- The FVar IDs in the fold's result list are shifted by the offset between starting states.
    Each step creates FVars via mkDw and mkOw using allocFresh, so IDs track nextFresh. -/
lemma preEqObligationStep_foldl_fst_shift (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh) :
    let fold := ws.foldl (preEqObligationStep b t t') ([], st)
    let fold' := ws.foldl (preEqObligationStep b t t') ([], st')
    ∀ i (hi : i < fold.1.length),
      (fold'.1.get ⟨i, preEqObligationStep_foldl_fst_length_eq b t t' ws st st' ▸ hi⟩).id =
      (fold.1.get ⟨i, hi⟩).id + offset := by
  intro fold fold' i hi
  have hGen := preEqObligationStep_foldl_fst_shift_gen b t t' ws ([], st) ([], st')
      offset hOffset hMono rfl (fun j hj => (Nat.not_lt_zero j hj).elim)
  exact hGen i hi

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- The fold of preEqObligationStep preserves well-formedness. -/
lemma preEqObligationStep_foldl_wf (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (acc : List (FVar b) × EncState b)
    (hWF : EncState.WellFormed acc.2) :
    EncState.WellFormed (ws.foldl (preEqObligationStep b t t') acc).2 := by
  induction ws generalizing acc with
  | nil => exact hWF
  | cons w ws' ih =>
      simp only [List.foldl_cons]
      apply ih
      exact preEqObligationStep_wf b t t' acc w hWF

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- The fold of preEqObligationStep is monotonic in nextFresh. -/
lemma preEqObligationStep_foldl_mono (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (acc : List (FVar b) × EncState b) :
    acc.2.nextFresh ≤ (ws.foldl (preEqObligationStep b t t') acc).2.nextFresh := by
  induction ws generalizing acc with
  | nil => simp
  | cons w ws' ih =>
      simp only [List.foldl_cons]
      have hStep := preEqObligationStep_nextFresh_ge b t t' acc w
      have hRest := ih (preEqObligationStep b t t' acc w)
      omega

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- addPreEqExpose preserves well-formedness when the Fresh var has id < st.nextFresh. -/
lemma addPreEqExpose_wf (b : Bounds S) (H0 H' : b.times) (v : FVar b) (st : EncState b)
    (hWF : EncState.WellFormed st) (hV : v.id < st.nextFresh) :
    EncState.WellFormed (addPreEqExpose b H0 H' v st) := by
  unfold addPreEqExpose
  let c1 := [SAT.Lit.neg (Var.PreEq H0 H'), SAT.Lit.pos (FVar.toVar b v)]
  let c2 := [SAT.Lit.neg (FVar.toVar b v), SAT.Lit.pos (Var.PreEq H0 H')]
  have h1 : clauseFreshBelow c1 st.nextFresh := by
    intro lit hLit; simp only [c1, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h => subst h; simp only [litFreshBelow, SAT.Lit.getVar]
    | inr h => subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar]; exact hV
  let st1 := EncState.addClause b st c1
  have hWF1 : st1.WellFormed := EncState.addClause_wf hWF c1 h1
  have hSt1Next : st1.nextFresh = st.nextFresh := EncState.addClause_nextFresh b st c1
  have h2 : clauseFreshBelow c2 st1.nextFresh := by
    rw [hSt1Next]
    intro lit hLit; simp only [c2, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h => subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar]; exact hV
    | inr h => subst h; simp only [litFreshBelow, SAT.Lit.getVar]
  exact EncState.addClause_wf hWF1 c2 h2

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Fold of preEqAccStep preserves well-formedness and Fresh var bounds.
    Invariant: cur.id < st.nextFresh, all o.id in os < init.2.nextFresh → WF preserved -/
lemma preEqAccStep_foldl_wf (b : Bounds S) (os : List (FVar b)) (init : FVar b × EncState b)
    (hWF : EncState.WellFormed init.2)
    (hCur : init.1.id < init.2.nextFresh)
    (hOs : ∀ o ∈ os, o.id < init.2.nextFresh) :
    EncState.WellFormed (os.foldl (preEqAccStep b) init).2 ∧
    (os.foldl (preEqAccStep b) init).1.id < (os.foldl (preEqAccStep b) init).2.nextFresh := by
  induction os generalizing init with
  | nil => exact ⟨hWF, hCur⟩
  | cons o os' ih =>
      simp only [List.foldl_cons]
      have hO : o.id < init.2.nextFresh := hOs o (by simp)
      have hStep := preEqAccStep_wf b init o hWF hCur hO
      have hStepNext : (preEqAccStep b init o).2.nextFresh = init.2.nextFresh + 1 :=
        preEqAccStep_nextFresh b init o
      have hOs' : ∀ o' ∈ os', o'.id < (preEqAccStep b init o).2.nextFresh := by
        intro o' ho'
        have := hOs o' (List.mem_cons_of_mem o ho')
        rw [hStepNext]; omega
      exact ih (preEqAccStep b init o) hStep.1 hStep.2 hOs'

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Fresh vars in NEW clauses from preEqAccStep have index ≥ baseline.
    preEqAccStep uses cur (acc.1), newly allocated next, and o.
    If all these have id ≥ baseline, then any Fresh var in a new clause has index ≥ baseline. -/
lemma preEqAccStep_newClause_fresh_ge (b : Bounds S) (acc : FVar b × EncState b) (o : FVar b)
    (baseline : Nat)
    (hBaseline : baseline ≤ acc.2.nextFresh)
    (hCur : acc.1.id ≥ baseline) (hO : o.id ≥ baseline)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (preEqAccStep b acc o).2.clauses)
    (hNotAcc : clause ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ clause)
    (n : Nat) (hFresh : lit.getVar = Var.Fresh n) :
    n ≥ baseline := by
  -- preEqAccStep adds 3 clauses with vars: cur (acc.1), next (allocd at acc.2.nextFresh), o
  -- All have id ≥ baseline
  have hClausesEq := preEqAccStep_clauses_eq b acc o
  -- The new clauses use: acc.1 (cur), ⟨acc.2.nextFresh⟩ (next), o
  rw [hClausesEq] at hClause
  cases List.mem_append.mp hClause with
  | inl hNew =>
      -- clause is in the 3 new clauses from addAccStep_clauses
      simp only [addAccStep_clauses, List.mem_cons, List.mem_nil_iff, or_false] at hNew
      rcases hNew with hC1 | hC2 | hC3
      · -- clause = [neg cur, neg o, pos next] where next.id = acc.2.nextFresh
        subst hC1
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
        rcases hLit with h1 | h2 | h3
        · rw [h1] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : acc.1.id = n := Var.Fresh.inj hFresh; omega
        · rw [h2] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : o.id = n := Var.Fresh.inj hFresh; omega
        · rw [h3] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : acc.2.nextFresh = n := Var.Fresh.inj hFresh; omega
      · -- clause = [neg next, pos o]
        subst hC2
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
        rcases hLit with h1 | h2
        · rw [h1] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : acc.2.nextFresh = n := Var.Fresh.inj hFresh; omega
        · rw [h2] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : o.id = n := Var.Fresh.inj hFresh; omega
      · -- clause = [neg next, pos cur]
        subst hC3
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
        rcases hLit with h1 | h2
        · rw [h1] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : acc.2.nextFresh = n := Var.Fresh.inj hFresh; omega
        · rw [h2] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hn : acc.1.id = n := Var.Fresh.inj hFresh; omega
  | inr hOld => exact absurd hOld hNotAcc

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- New clauses from preEqAccStep have at least one Fresh variable.
    preEqAccStep adds 3 clauses with cur, next (Fresh), and o. The next var is Fresh. -/
lemma preEqAccStep_newClause_exists_fresh (b : Bounds S) (acc : FVar b × EncState b) (o : FVar b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (preEqAccStep b acc o).2.clauses)
    (hNotAcc : clause ∉ acc.2.clauses) :
    ∃ lit ∈ clause, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  have hClausesEq := preEqAccStep_clauses_eq b acc o
  rw [hClausesEq] at hClause
  cases List.mem_append.mp hClause with
  | inl hNew =>
      simp only [addAccStep_clauses, List.mem_cons, List.mem_nil_iff, or_false] at hNew
      -- next is allocated at acc.2.nextFresh
      let next : FVar b := ⟨acc.2.nextFresh⟩
      rcases hNew with hC1 | hC2 | hC3
      · -- clause = [neg cur, neg o, pos next]
        exact ⟨SAT.Lit.pos (FVar.toVar b next), by subst hC1; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
               next.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
      · -- clause = [neg next, pos o]
        exact ⟨SAT.Lit.neg (FVar.toVar b next), by subst hC2; exact List.Mem.head _,
               next.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
      · -- clause = [neg next, pos cur]
        exact ⟨SAT.Lit.neg (FVar.toVar b next), by subst hC3; exact List.Mem.head _,
               next.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
  | inr hOld => exact absurd hOld hNotAcc

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- New clauses from preEqAccStep fold have at least one Fresh variable. -/
lemma preEqAccStep_foldl_newClause_exists_fresh (b : Bounds S) (os : List (FVar b))
    (init : FVar b × EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (os.foldl (preEqAccStep b) init).2.clauses)
    (hNotInit : clause ∉ init.2.clauses) :
    ∃ lit ∈ clause, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  induction os generalizing init with
  | nil =>
      simp only [List.foldl_nil] at hClause
      exact absurd hClause hNotInit
  | cons o os' ih =>
      simp only [List.foldl_cons] at hClause
      by_cases hInStep : clause ∈ (preEqAccStep b init o).2.clauses
      · by_cases hInInit : clause ∈ init.2.clauses
        · exact absurd hInInit hNotInit
        · exact preEqAccStep_newClause_exists_fresh b init o clause hInStep hInInit
      · exact ih (preEqAccStep b init o) hClause hInStep

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Fresh vars in NEW clauses from addPreEqExpose have index ≥ baseline.
    addPreEqExpose adds two clauses using PreEq (not Fresh) and v (a Fresh var).
    So any Fresh var in new clauses has index = v.id ≥ baseline. -/
lemma addPreEqExpose_newClause_fresh_ge (b : Bounds S) (H0 H' : b.times) (v : FVar b)
    (st : EncState b) (baseline : Nat)
    (hV : v.id ≥ baseline)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (addPreEqExpose b H0 H' v st).clauses)
    (hNotSt : clause ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ clause)
    (n : Nat) (hFresh : lit.getVar = Var.Fresh n) :
    n ≥ baseline := by
  unfold addPreEqExpose at hClause
  simp only [EncState.addClause] at hClause
  -- New clauses: [neg (PreEq H0 H'), pos (FVar.toVar v)], [neg (FVar.toVar v), pos (PreEq H0 H')]
  cases hClause with
  | head =>
      -- clause = [neg v, pos PreEq]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      rcases hLit with h1 | h2
      · rw [h1] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : v.id = n := Var.Fresh.inj hFresh; omega
      · rw [h2] at hFresh; simp only [SAT.Lit.getVar] at hFresh
        exact Var.noConfusion hFresh
  | tail _ hTail =>
      cases hTail with
      | head =>
          -- clause = [neg PreEq, pos v]
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with h1 | h2
          · rw [h1] at hFresh; simp only [SAT.Lit.getVar] at hFresh
            exact Var.noConfusion hFresh
          · rw [h2] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : v.id = n := Var.Fresh.inj hFresh; omega
      | tail _ hTail2 => exact absurd hTail2 hNotSt

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- New clauses from addPreEqExpose have at least one Fresh variable.
    addPreEqExpose adds [neg PreEq, pos v] and [neg v, pos PreEq], both containing v (Fresh). -/
lemma addPreEqExpose_newClause_exists_fresh (b : Bounds S) (H0 H' : b.times) (v : FVar b)
    (st : EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (addPreEqExpose b H0 H' v st).clauses)
    (hNotSt : clause ∉ st.clauses) :
    ∃ lit ∈ clause, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  unfold addPreEqExpose at hClause
  simp only [EncState.addClause] at hClause
  cases hClause with
  | head =>
      -- clause = [neg v, pos PreEq]
      exact ⟨SAT.Lit.neg (FVar.toVar b v), List.Mem.head _, v.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
  | tail _ hTail =>
      cases hTail with
      | head =>
          -- clause = [neg PreEq, pos v]
          exact ⟨SAT.Lit.pos (FVar.toVar b v), List.Mem.tail _ (List.Mem.head _),
                 v.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
      | tail _ hTail2 => exact absurd hTail2 hNotSt

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Structural determinism for addPreEqExpose.
    addPreEqExpose adds two clauses: [neg PreEq, pos v] and [neg v, pos PreEq].
    Both contain PreEq (non-Fresh) and v (Fresh). Since v' = v + offset and v ≥ st.nextFresh,
    the shifted assignment σ' maps v' back to v, preserving satisfaction. -/
lemma addPreEqExpose_structural_determinism (b : Bounds S) (H0 H' : b.times)
    (v v' : FVar b) (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hVShift : v'.id = v.id + offset)
    (hVGe : v.id ≥ st.nextFresh)
    (σ : SAT.Assignment (Var b))
    (hSat : (addPreEqExpose b H0 H' v st).clauses.all (SAT.Clause.eval σ) = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (addPreEqExpose b H0 H' v' st').clauses)
    (hClauseNotInBase : clause ∉ st'.clauses) :
    let σ' : SAT.Assignment (Var b) := fun w =>
      match w with
      | Var.Fresh n => if n < st'.nextFresh then σ w else σ (Var.Fresh (n - offset))
      | _ => σ w
    SAT.Clause.eval σ' clause = true := by
  intro σ'
  classical
  -- addPreEqExpose adds exactly two clauses
  unfold addPreEqExpose at hClauseMem hSat
  simp only [EncState.addClause] at hClauseMem hSat
  -- v' is Fresh with index ≥ st'.nextFresh
  have hV'Ge : v'.id ≥ st'.nextFresh := by rw [hVShift, hOffset]; omega
  have hV'NotLt : ¬ v'.id < st'.nextFresh := Nat.not_lt.mpr hV'Ge
  -- v'.id - offset = v.id
  have hV'Sub : v'.id - offset = v.id := by omega
  -- Case analysis on which clause
  cases hClauseMem with
  | head =>
      -- clause = [neg v', pos (PreEq H0 H')]
      -- Corresponding clause at st: [neg v, pos (PreEq H0 H')]
      have hSatC : SAT.Clause.eval σ [SAT.Lit.neg (FVar.toVar b v),
          SAT.Lit.pos (Var.PreEq H0 H')] = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hSat
        exact hSat.1
      rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
      rcases hLitMem with hL1 | hL2
      · -- lit = neg v, corresponding to neg v'
        refine ⟨SAT.Lit.neg (FVar.toVar b v'), List.Mem.head _, ?_⟩
        simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
        simp only [σ', hV'NotLt, ↓reduceIte, hV'Sub]
        subst hL1; exact hLitTrue
      · -- lit = pos (PreEq H0 H'), same in both clauses
        refine ⟨SAT.Lit.pos (Var.PreEq H0 H'),
            List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
        simp only [SAT.Lit.eval, σ']
        subst hL2; exact hLitTrue
  | tail _ hTail =>
      cases hTail with
      | head =>
          -- clause = [neg (PreEq H0 H'), pos v']
          -- Corresponding clause at st: [neg (PreEq H0 H'), pos v]
          have hSatC : SAT.Clause.eval σ [SAT.Lit.neg (Var.PreEq H0 H'),
              SAT.Lit.pos (FVar.toVar b v)] = true := by
            simp only [List.all_cons, Bool.and_eq_true] at hSat
            exact hSat.2.1
          rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
          rcases hLitMem with hL1 | hL2
          · -- lit = neg (PreEq H0 H'), same in both clauses
            refine ⟨SAT.Lit.neg (Var.PreEq H0 H'), List.Mem.head _, ?_⟩
            simp only [SAT.Lit.eval, σ']
            subst hL1; exact hLitTrue
          · -- lit = pos v, corresponding to pos v'
            refine ⟨SAT.Lit.pos (FVar.toVar b v'),
                List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
            simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue ⊢
            simp only [σ', hV'NotLt, ↓reduceIte, hV'Sub]
            subst hL2; exact hLitTrue
      | tail _ hTail2 => exact absurd hTail2 hClauseNotInBase

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Fresh vars in NEW clauses from preEqAccStep fold have index ≥ baseline.
    This tracks a baseline that is ≤ all Fresh var indices used in the fold:
    - init.1.id ≥ baseline (cur was allocated at or after baseline)
    - ∀ o ∈ os, o.id ≥ baseline (obligations were allocated at or after baseline)
    - baseline ≤ init.2.nextFresh (baseline is at or before current state)
    All new Fresh vars allocated during fold have id ≥ init.2.nextFresh ≥ baseline. -/
lemma preEqAccStep_foldl_newClause_fresh_ge (b : Bounds S) (os : List (FVar b))
    (init : FVar b × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ init.2.nextFresh)
    (hCur : init.1.id ≥ baseline)
    (hOs : ∀ o ∈ os, o.id ≥ baseline)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (os.foldl (preEqAccStep b) init).2.clauses)
    (hNotInit : clause ∉ init.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ clause)
    (n : Nat) (hFresh : lit.getVar = Var.Fresh n) :
    n ≥ baseline := by
  induction os generalizing init with
  | nil =>
      simp only [List.foldl_nil] at hClause
      exact absurd hClause hNotInit
  | cons o os' ih =>
      simp only [List.foldl_cons] at hClause
      have hO : o.id ≥ baseline := hOs o (by simp)
      have hStepNext : (preEqAccStep b init o).2.nextFresh = init.2.nextFresh + 1 :=
        preEqAccStep_nextFresh b init o
      by_cases hInInit : clause ∈ init.2.clauses
      · exact absurd hInInit hNotInit
      · -- clause ∉ init.2.clauses
        by_cases hInStep : clause ∈ (preEqAccStep b init o).2.clauses
        · -- clause is NEW from this step (in step but not in init)
          -- preEqAccStep uses: cur (init.1), next (id = init.2.nextFresh), o
          -- All have id ≥ baseline
          exact preEqAccStep_newClause_fresh_ge b init o baseline hBaseline hCur hO
            clause hInStep hInInit lit hLit n hFresh
        · -- clause ∉ step.clauses, so it's from tail fold
          have hBaseline' : baseline ≤ (preEqAccStep b init o).2.nextFresh := by
            rw [hStepNext]; omega
          have hCur' : (preEqAccStep b init o).1.id ≥ baseline := by
            have hFst := preEqAccStep_fst b init o
            rw [hFst]; omega
          have hOs' : ∀ o' ∈ os', o'.id ≥ baseline := by
            intro o' ho'
            exact hOs o' (List.mem_cons_of_mem o ho')
          exact ih (preEqAccStep b init o) hBaseline' hCur' hOs' hClause hInStep

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Fresh vars accumulated by preEqObligationStep fold have id < final nextFresh.
    The key invariant: each step adds one FVar from mkOw, which has id < step.2.nextFresh. -/
lemma preEqObligationStep_foldl_fvars_lt (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (init : List (FVar b) × EncState b)
    (hInit : ∀ fv ∈ init.1, fv.id < init.2.nextFresh) :
    ∀ fv ∈ (ws.foldl (preEqObligationStep b t t') init).1,
      fv.id < (ws.foldl (preEqObligationStep b t t') init).2.nextFresh := by
  induction ws generalizing init with
  | nil =>
      simp only [List.foldl_nil]
      exact hInit
  | cons w ws' ih =>
      simp only [List.foldl_cons]
      apply ih
      intro fv hfv
      unfold preEqObligationStep at hfv
      simp only at hfv
      rw [List.mem_cons] at hfv
      cases hfv with
      | inl hNew =>
          -- fv is the new mkOw result: has id = (mkDw ...).2.nextFresh
          subst hNew
          have hOId := mkOw_fst_id b t w (mkDw b t' w init.2).1 (mkDw b t' w init.2).2
          have hONext := mkOw_nextFresh b t w (mkDw b t' w init.2).1 (mkDw b t' w init.2).2
          -- Goal: (mkOw ...).1.id < (preEqObligationStep ...).2.nextFresh
          -- (mkOw ...).1.id = (mkDw ...).2.nextFresh (by hOId)
          -- (preEqObligationStep ...).2 = (mkOw ...).2, so nextFresh = (mkDw ...).2.nextFresh + 1
          have hStep : (preEqObligationStep b t t' init w).2.nextFresh =
              (mkOw b t w (mkDw b t' w init.2).1 (mkDw b t' w init.2).2).2.nextFresh := by
            unfold preEqObligationStep; simp only
          rw [hOId, hStep, hONext]
          omega
      | inr hOld =>
          -- fv was in init.1: has id < init.2.nextFresh ≤ step.2.nextFresh
          have hLt := hInit fv hOld
          have hMono := preEqObligationStep_nextFresh_ge b t t' init w
          exact Nat.lt_of_lt_of_le hLt hMono

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Fresh vars accumulated by preEqObligationStep fold have id ≥ a baseline value.
    Uses a baseline parameter that is ≤ init.2.nextFresh and ≤ all existing fvar ids.
    Each new mkOw FVar has id = (mkDw ...).2.nextFresh ≥ init.2.nextFresh ≥ baseline. -/
lemma preEqObligationStep_foldl_fvars_ge (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (init : List (FVar b) × EncState b) (baseline : Nat)
    (hBaseline : baseline ≤ init.2.nextFresh)
    (hInit : ∀ fv ∈ init.1, fv.id ≥ baseline) :
    ∀ fv ∈ (ws.foldl (preEqObligationStep b t t') init).1,
      fv.id ≥ baseline := by
  induction ws generalizing init with
  | nil =>
      simp only [List.foldl_nil]
      exact hInit
  | cons w ws' ih =>
      simp only [List.foldl_cons]
      intro fv hfv
      have hStepMono := preEqObligationStep_nextFresh_ge b t t' init w
      -- The new mkOw FVar has id = (mkDw ...).2.nextFresh ≥ init.2.nextFresh ≥ baseline
      have hNewGe : (mkOw b t w (mkDw b t' w init.2).1 (mkDw b t' w init.2).2).1.id ≥ baseline := by
        have hOId := mkOw_fst_id b t w (mkDw b t' w init.2).1 (mkDw b t' w init.2).2
        have hDwMono := mkDw_snd_nextFresh_ge b t' w init.2
        rw [hOId]; omega
      -- Establish invariant for step: all fvars have id ≥ baseline
      have hStepInit : ∀ fv' ∈ (preEqObligationStep b t t' init w).1, fv'.id ≥ baseline := by
        intro fv' hfv'
        unfold preEqObligationStep at hfv'
        simp only at hfv'
        rw [List.mem_cons] at hfv'
        cases hfv' with
        | inl hNew => subst hNew; exact hNewGe
        | inr hOld => exact hInit fv' hOld
      -- Apply IH with updated baseline bound
      have hBaseline' : baseline ≤ (preEqObligationStep b t t' init w).2.nextFresh := by
        omega
      exact ih (preEqObligationStep b t t' init w) hBaseline' hStepInit fv hfv

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- addPreEqPair_core preserves well-formedness. -/
lemma addPreEqPair_core_wf (b : Bounds S) (H0 H' : b.times) (st : EncState b)
    (hWF : EncState.WellFormed st) :
    EncState.WellFormed (addPreEqPair_core b H0 H' st) := by
  classical
  unfold addPreEqPair_core
  simp only
  -- fold1: preEqObligationStep fold on H0,H'
  let fold1 := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)
  have hFold1WF : EncState.WellFormed fold1.2 :=
    preEqObligationStep_foldl_wf b H0 H' _ ([], st) hWF
  have hFold1Mono : st.nextFresh ≤ fold1.2.nextFresh :=
    preEqObligationStep_foldl_mono b H0 H' _ ([], st)
  have hFold1Fvars : ∀ o ∈ fold1.1, o.id < fold1.2.nextFresh :=
    preEqObligationStep_foldl_fvars_lt b H0 H' (WId.allWorlds b) ([], st)
      (by intro _ hMem; simp at hMem)

  -- fold2: preEqObligationStep fold on H',H0
  let fold2 := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1.2)
  have hFold2WF : EncState.WellFormed fold2.2 :=
    preEqObligationStep_foldl_wf b H' H0 _ ([], fold1.2) hFold1WF
  have hFold2Mono : fold1.2.nextFresh ≤ fold2.2.nextFresh :=
    preEqObligationStep_foldl_mono b H' H0 _ ([], fold1.2)
  have hFold2Fvars : ∀ o ∈ fold2.1, o.id < fold2.2.nextFresh :=
    preEqObligationStep_foldl_fvars_lt b H' H0 (WId.allWorlds b) ([], fold1.2)
      (by intro _ hMem; simp at hMem)
  -- fold1.1 Fresh vars still have id < fold2.2.nextFresh (monotonicity)
  have hFold1FvarsLift : ∀ o ∈ fold1.1, o.id < fold2.2.nextFresh := by
    intro o ho; exact Nat.lt_of_lt_of_le (hFold1Fvars o ho) hFold2Mono

  -- allocFresh: base
  let base := (EncState.allocFresh b fold2.2).1
  let st3 := (EncState.allocFresh b fold2.2).2
  have hAllocWF := EncState.allocFresh_wf hFold2WF
  have hBaseId : base.id = fold2.2.nextFresh := by simp [base, EncState.allocFresh]
  have hSt3Next : st3.nextFresh = fold2.2.nextFresh + 1 := EncState.allocFresh_nextFresh b fold2.2
  have hBaseLt : base.id < st3.nextFresh := by rw [hBaseId, hSt3Next]; omega

  -- addClause: [pos base]
  have hC1 : clauseFreshBelow [SAT.Lit.pos (FVar.toVar b base)] st3.nextFresh := by
    intro lit hLit; simp only [List.mem_singleton] at hLit; subst hLit
    simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hBaseId, hSt3Next]; omega
  let st4 := EncState.addClause b st3 [SAT.Lit.pos (FVar.toVar b base)]
  have hSt4WF := EncState.addClause_wf hAllocWF _ hC1
  have hSt4Next : st4.nextFresh = st3.nextFresh := EncState.addClause_nextFresh b st3 _
  have hBaseLt4 : base.id < st4.nextFresh := by rw [hSt4Next]; exact hBaseLt

  -- Lift fold1.1 and fold2.1 bounds to st4.nextFresh
  have hFold1Lift4 : ∀ o ∈ fold1.1, o.id < st4.nextFresh := by
    intro o ho; rw [hSt4Next, hSt3Next]
    exact Nat.lt_of_lt_of_le (hFold1FvarsLift o ho) (Nat.le_succ _)
  have hFold2Lift4 : ∀ o ∈ fold2.1, o.id < st4.nextFresh := by
    intro o ho; rw [hSt4Next, hSt3Next]
    exact Nat.lt_of_lt_of_le (hFold2Fvars o ho) (Nat.le_succ _)

  -- accFold1: fold preEqAccStep over fold1.1
  let accInit1 : FVar b × EncState b := (base, st4)
  let accFold1 := fold1.1.foldl (preEqAccStep b) accInit1
  have hAccFold1 := preEqAccStep_foldl_wf b fold1.1 accInit1 hSt4WF hBaseLt4 hFold1Lift4
  -- preEqAccStep fold is monotonic in nextFresh: each step increments by 1
  have hAccFold1Mono : st4.nextFresh ≤ accFold1.2.nextFresh := by
    have : ∀ (os : List (FVar b)) (init : FVar b × EncState b),
        init.2.nextFresh ≤ (os.foldl (preEqAccStep b) init).2.nextFresh := by
      intro os init
      induction os generalizing init with
      | nil => rfl
      | cons o os' ih =>
          simp only [List.foldl_cons]
          have hStep := preEqAccStep_nextFresh b init o
          have hIH := ih (preEqAccStep b init o)
          omega
    exact this fold1.1 accInit1

  -- accFold2: fold preEqAccStep over fold2.1
  let accInit2 : FVar b × EncState b := (accFold1.1, accFold1.2)
  have hFold2Lift5 : ∀ o ∈ fold2.1, o.id < accFold1.2.nextFresh := by
    intro o ho
    have := hFold2Fvars o ho
    calc o.id < fold2.2.nextFresh := this
    _ ≤ st3.nextFresh := by rw [hSt3Next]; omega
    _ = st4.nextFresh := hSt4Next.symm
    _ ≤ accFold1.2.nextFresh := hAccFold1Mono
  let accFold2 := fold2.1.foldl (preEqAccStep b) accInit2
  have hAccFold2 := preEqAccStep_foldl_wf b fold2.1 accInit2 hAccFold1.1 hAccFold1.2 hFold2Lift5

  -- addPreEqExpose
  have hFinalLt : accFold2.1.id < accFold2.2.nextFresh := hAccFold2.2
  exact addPreEqExpose_wf b H0 H' accFold2.1 accFold2.2 hAccFold2.1 hFinalLt

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- addPreEqPair preserves well-formedness. -/
lemma addPreEqPair_wf (b : Bounds S) (H0 H' : b.times) (st : EncState b)
    (hWF : EncState.WellFormed st) :
    EncState.WellFormed (addPreEqPair b H0 H' st) := by
  classical
  unfold addPreEqPair
  have hCoreWF := addPreEqPair_core_wf b H0 H' st hWF
  by_cases hEq : H0 = H'
  · subst hEq
    simp only [↓reduceIte]
    have hC : clauseFreshBelow [SAT.Lit.pos (Var.PreEq H0 H0)]
        (addPreEqPair_core b H0 H0 st).nextFresh := by
      intro lit hLit; simp only [List.mem_singleton] at hLit; subst hLit
      simp only [litFreshBelow, SAT.Lit.getVar]
    exact EncState.addClause_wf hCoreWF _ hC
  · simp only [hEq, ↓reduceIte]
    exact hCoreWF

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- addPreEqFrom preserves well-formedness. -/
lemma addPreEqFrom_wf (b : Bounds S) (H0 : b.times) (st : EncState b)
    (hWF : EncState.WellFormed st) :
    EncState.WellFormed (addPreEqFrom b H0 st) := by
  simp only [addPreEqFrom]
  induction (Bounds.timesL b) generalizing st with
  | nil => exact hWF
  | cons H' tl ih =>
      simp only [List.foldl_cons]
      apply ih
      exact addPreEqPair_wf b H0 H' st hWF

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The cur FVar in a preEqAccStep fold maintains id ≥ baseline throughout. -/
lemma preEqAccStep_foldl_fst_ge (b : Bounds S) (os : List (FVar b))
    (init : FVar b × EncState b) (baseline : Nat)
    (hCur : init.1.id ≥ baseline) (hBaseline : baseline ≤ init.2.nextFresh) :
    (os.foldl (preEqAccStep b) init).1.id ≥ baseline := by
  induction os generalizing init with
  | nil => simp only [List.foldl_nil]; exact hCur
  | cons o os' ih =>
      simp only [List.foldl_cons]
      apply ih
      · have hFst := preEqAccStep_fst b init o
        simp only [hFst]; exact hBaseline
      · have hNext := preEqAccStep_nextFresh b init o; omega

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- preEqAccStep fold is monotonic in nextFresh. -/
lemma preEqAccStep_foldl_nextFresh_mono (b : Bounds S) (os : List (FVar b))
    (init : FVar b × EncState b) :
    init.2.nextFresh ≤ (os.foldl (preEqAccStep b) init).2.nextFresh := by
  induction os generalizing init with
  | nil => rfl
  | cons o os' ih =>
      simp only [List.foldl_cons]
      have hStep := preEqAccStep_nextFresh b init o
      exact Nat.le_trans (by omega) (ih _)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The exact nextFresh after a preEqAccStep fold: increments by list length. -/
lemma preEqAccStep_foldl_nextFresh_eq (b : Bounds S) (os : List (FVar b))
    (init : FVar b × EncState b) :
    (os.foldl (preEqAccStep b) init).2.nextFresh = init.2.nextFresh + os.length := by
  induction os generalizing init with
  | nil => simp
  | cons o os' ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, preEqAccStep_nextFresh]; ring

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The exact fst.id after a non-empty preEqAccStep fold: last allocated Fresh var. -/
lemma preEqAccStep_foldl_fst_id (b : Bounds S) (os : List (FVar b))
    (init : FVar b × EncState b) (hNonEmpty : os ≠ []) :
    (os.foldl (preEqAccStep b) init).1.id = init.2.nextFresh + os.length - 1 := by
  induction os generalizing init with
  | nil => exact absurd rfl hNonEmpty
  | cons o os' ih =>
      simp only [List.foldl_cons, List.length_cons]
      match hNil : os' with
      | [] =>
          simp only [List.foldl_nil]
          rw [preEqAccStep_fst]; simp
      | o' :: os'' =>
          have hNonEmpty' : o' :: os'' ≠ [] := List.cons_ne_nil o' os''
          rw [ih (preEqAccStep b init o) hNonEmpty']
          rw [preEqAccStep_nextFresh]
          omega

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- preEqAccStep fold preserves offset between parallel runs. -/
lemma preEqAccStep_foldl_offset (b : Bounds S) (os os' : List (FVar b))
    (init init' : FVar b × EncState b) (offset : Nat)
    (hOffset : offset = init'.2.nextFresh - init.2.nextFresh)
    (hMono : init.2.nextFresh ≤ init'.2.nextFresh)
    (hLen : os'.length = os.length)
    (hCurShift : init'.1.id = init.1.id + offset) :
    (os'.foldl (preEqAccStep b) init').2.nextFresh -
    (os.foldl (preEqAccStep b) init).2.nextFresh = offset := by
  rw [preEqAccStep_foldl_nextFresh_eq, preEqAccStep_foldl_nextFresh_eq, hLen]
  omega

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- preEqAccStep fold preserves cur shift between parallel runs. -/
lemma preEqAccStep_foldl_fst_shift (b : Bounds S) (os os' : List (FVar b))
    (init init' : FVar b × EncState b) (offset : Nat)
    (hOffset : offset = init'.2.nextFresh - init.2.nextFresh)
    (hMono : init.2.nextFresh ≤ init'.2.nextFresh)
    (hLen : os'.length = os.length)
    (hOsShift : ∀ i (hi : i < os.length),
        (os'.get ⟨i, hLen ▸ hi⟩).id = (os.get ⟨i, hi⟩).id + offset)
    (hCurShift : init'.1.id = init.1.id + offset) :
    (os'.foldl (preEqAccStep b) init').1.id =
    (os.foldl (preEqAccStep b) init).1.id + offset := by
  match hNilOs : os, hNilOs' : os' with
  | [], [] => simp only [List.foldl_nil]; exact hCurShift
  | [], _ :: _ => simp at hLen
  | _ :: _, [] => simp at hLen
  | o :: os_tail, o' :: os'_tail =>
      have hNonEmpty : o :: os_tail ≠ [] := List.cons_ne_nil o os_tail
      have hNonEmpty' : o' :: os'_tail ≠ [] := List.cons_ne_nil o' os'_tail
      rw [preEqAccStep_foldl_fst_id b (o :: os_tail) init hNonEmpty]
      rw [preEqAccStep_foldl_fst_id b (o' :: os'_tail) init' hNonEmpty']
      simp only [List.length_cons] at hLen ⊢
      -- offset = init'.2.nextFresh - init.2.nextFresh and init.2.nextFresh ≤ init'.2.nextFresh
      -- means init'.2.nextFresh = init.2.nextFresh + offset
      have hAdd : init'.2.nextFresh = init.2.nextFresh + offset := by omega
      omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Fresh vars in NEW clauses from addPreEqPair_core have index ≥ st.nextFresh.
    This traces through the entire structure:
    1. preEqObligationStep folds for H0 and H' - use preEqObligationStep_foldl_newClause_fresh_ge
    2. allocFresh + addClause [pos base] - base.id = fold2.2.nextFresh ≥ st.nextFresh
    3. preEqAccStep folds - use preEqAccStep_foldl_newClause_fresh_ge
    4. addPreEqExpose - use addPreEqExpose_newClause_fresh_ge -/
lemma addPreEqPair_core_newClause_fresh_ge (b : Bounds S) (H0 H' : b.times) (st : EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (addPreEqPair_core b H0 H' st).clauses)
    (hNotSt : clause ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ clause)
    (n : Nat) (hFresh : lit.getVar = Var.Fresh n) :
    n ≥ st.nextFresh := by
  classical
  unfold addPreEqPair_core at hClause
  simp only at hClause
  -- Define intermediate states
  let fold1 := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)
  let fold2 := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1.2)
  let allocRes := EncState.allocFresh b fold2.2
  let base := allocRes.1
  let st3 := EncState.addClause b allocRes.2 [SAT.Lit.pos (FVar.toVar b base)]
  let accFold1 := fold1.1.foldl (preEqAccStep b) (base, st3)
  let accFold2 := fold2.1.foldl (preEqAccStep b) (accFold1.1, accFold1.2)
  -- Establish monotonicity facts
  have hFold1Mono : st.nextFresh ≤ fold1.2.nextFresh :=
    preEqObligationStep_foldl_mono b H0 H' _ ([], st)
  have hFold2Mono : fold1.2.nextFresh ≤ fold2.2.nextFresh :=
    preEqObligationStep_foldl_mono b H' H0 _ ([], fold1.2)
  have hAllocNext : allocRes.2.nextFresh = fold2.2.nextFresh + 1 :=
    EncState.allocFresh_nextFresh b fold2.2
  have hBaseId : base.id = fold2.2.nextFresh := by
    simp only [base, allocRes, EncState.allocFresh]
  have hSt3Next : st3.nextFresh = allocRes.2.nextFresh :=
    EncState.addClause_nextFresh b allocRes.2 _
  have hBaseGe : base.id ≥ st.nextFresh := by rw [hBaseId]; omega
  have hSt3Baseline : st.nextFresh ≤ st3.nextFresh := by rw [hSt3Next, hAllocNext]; omega
  have hAcc1Mono : st.nextFresh ≤ accFold1.2.nextFresh := by
    have h : (base, st3).2.nextFresh ≤ accFold1.2.nextFresh :=
      preEqAccStep_foldl_nextFresh_mono b fold1.1 (base, st3)
    exact Nat.le_trans hSt3Baseline h
  -- Key bounds on obligations
  have hOsGe1 : ∀ o ∈ fold1.1, o.id ≥ st.nextFresh :=
    preEqObligationStep_foldl_fvars_ge b H0 H' (WId.allWorlds b) ([], st) st.nextFresh
      (Nat.le_refl _) (by simp)
  have hOsGe2 : ∀ o ∈ fold2.1, o.id ≥ st.nextFresh := by
    intro o ho
    have h := preEqObligationStep_foldl_fvars_ge b H' H0 (WId.allWorlds b) ([], fold1.2)
      fold1.2.nextFresh (Nat.le_refl _) (by simp) o ho
    omega
  -- Key bounds on accFold1.1 and accFold2.1
  have hAcc1CurGe : accFold1.1.id ≥ st.nextFresh :=
    preEqAccStep_foldl_fst_ge b fold1.1 (base, st3) st.nextFresh hBaseGe hSt3Baseline
  have hAcc2CurGe : accFold2.1.id ≥ st.nextFresh :=
    preEqAccStep_foldl_fst_ge b fold2.1 (accFold1.1, accFold1.2) st.nextFresh hAcc1CurGe hAcc1Mono
  -- Trace clause through the pipeline
  if hInSt : clause ∈ st.clauses then exact absurd hInSt hNotSt
  else if hInFold1 : clause ∈ fold1.2.clauses then
    exact preEqObligationStep_foldl_newClause_fresh_ge b H0 H' (WId.allWorlds b) ([], st)
      clause hInFold1 hInSt lit hLit n hFresh
  else if hInFold2 : clause ∈ fold2.2.clauses then
    have hGe : n ≥ fold1.2.nextFresh :=
      preEqObligationStep_foldl_newClause_fresh_ge b H' H0 (WId.allWorlds b) ([], fold1.2)
        clause hInFold2 hInFold1 lit hLit n hFresh
    exact Nat.le_trans hFold1Mono hGe
  else if hInAlloc : clause ∈ allocRes.2.clauses then
    have hEq : allocRes.2.clauses = fold2.2.clauses := EncState.allocFresh_clauses_eq b fold2.2
    exact absurd (hEq ▸ hInAlloc) hInFold2
  else if hInSt3 : clause ∈ st3.clauses then
    simp only [st3, EncState.addClause] at hInSt3
    cases hInSt3 with
    | head =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
        rw [hLit] at hFresh
        simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : base.id = n := Var.Fresh.inj hFresh
        rw [← hn]; exact hBaseGe
    | tail _ hTail => exact absurd hTail hInAlloc
  else if hInAcc1 : clause ∈ accFold1.2.clauses then
    exact preEqAccStep_foldl_newClause_fresh_ge b fold1.1 (base, st3) st.nextFresh
      hSt3Baseline hBaseGe hOsGe1 clause hInAcc1 hInSt3 lit hLit n hFresh
  else if hInAcc2 : clause ∈ accFold2.2.clauses then
    exact preEqAccStep_foldl_newClause_fresh_ge b fold2.1 (accFold1.1, accFold1.2) st.nextFresh
      hAcc1Mono hAcc1CurGe hOsGe2 clause hInAcc2 hInAcc1 lit hLit n hFresh
  else
    have hInExpose : clause ∈ (addPreEqExpose b H0 H' accFold2.1 accFold2.2).clauses := hClause
    exact addPreEqExpose_newClause_fresh_ge b H0 H' accFold2.1 accFold2.2 st.nextFresh
      hAcc2CurGe clause hInExpose hInAcc2 lit hLit n hFresh

/-- New clauses from addPreEqPair_core contain at least one Fresh variable.

    This is the "existence" version of addPreEqPair_core_newClause_fresh_ge.
    addPreEqPair_core uses Tseytin gadgets that all allocate Fresh variables,
    so every new clause references at least one Fresh variable.

    Proof structure: Each stage of addPreEqPair_core adds clauses containing Fresh vars:
    1. preEqObligationStep folds (mkOw) - mkOw_newClause_exists_fresh_ge
    2. allocFresh + addClause [pos base] - base is Fresh by construction
    3. preEqAccStep folds (mkAndIff) - mkAndIff allocates Fresh vars
    4. addPreEqExpose - references the accumulated Fresh var

    TODO: Create existence lemmas for preEqObligationStep_foldl, preEqAccStep_foldl,
    addPreEqExpose to complete this proof. -/
lemma addPreEqPair_core_newClause_has_fresh (b : Bounds S) (H0 H' : b.times) (st : EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (addPreEqPair_core b H0 H' st).clauses)
    (hNotSt : clause ∉ st.clauses) :
    ∃ lit ∈ clause, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  classical
  unfold addPreEqPair_core at hClause
  simp only at hClause
  -- Define intermediate states (same as addPreEqPair_core_newClause_fresh_ge)
  let fold1 := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)
  let fold2 := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1.2)
  let allocRes := EncState.allocFresh b fold2.2
  let base := allocRes.1
  let st3 := EncState.addClause b allocRes.2 [SAT.Lit.pos (FVar.toVar b base)]
  let accFold1 := fold1.1.foldl (preEqAccStep b) (base, st3)
  let accFold2 := fold2.1.foldl (preEqAccStep b) (accFold1.1, accFold1.2)
  -- Trace clause through the pipeline - each stage adds clauses with Fresh vars
  if hInSt : clause ∈ st.clauses then exact absurd hInSt hNotSt
  else if hInFold1 : clause ∈ fold1.2.clauses then
    -- clause is from first preEqObligationStep fold
    exact preEqObligationStep_foldl_newClause_exists_fresh b H0 H' (WId.allWorlds b) ([], st)
      clause hInFold1 hInSt
  else if hInFold2 : clause ∈ fold2.2.clauses then
    -- clause is from second preEqObligationStep fold
    exact preEqObligationStep_foldl_newClause_exists_fresh b H' H0 (WId.allWorlds b) ([], fold1.2)
      clause hInFold2 hInFold1
  else if hInAlloc : clause ∈ allocRes.2.clauses then
    have hEq : allocRes.2.clauses = fold2.2.clauses := EncState.allocFresh_clauses_eq b fold2.2
    exact absurd (hEq ▸ hInAlloc) hInFold2
  else if hInSt3 : clause ∈ st3.clauses then
    simp only [st3, EncState.addClause] at hInSt3
    cases hInSt3 with
    | head =>
        -- clause = [pos base], and base is Fresh
        exact ⟨SAT.Lit.pos (FVar.toVar b base), List.Mem.head _,
          base.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
    | tail _ hTail => exact absurd hTail hInAlloc
  else if hInAcc1 : clause ∈ accFold1.2.clauses then
    -- clause is from first preEqAccStep fold
    exact preEqAccStep_foldl_newClause_exists_fresh b fold1.1 (base, st3) clause hInAcc1 hInSt3
  else if hInAcc2 : clause ∈ accFold2.2.clauses then
    -- clause is from second preEqAccStep fold
    exact preEqAccStep_foldl_newClause_exists_fresh b fold2.1 (accFold1.1, accFold1.2)
      clause hInAcc2 hInAcc1
  else
    -- clause is from addPreEqExpose
    have hInExpose : clause ∈ (addPreEqExpose b H0 H' accFold2.1 accFold2.2).clauses := hClause
    exact addPreEqExpose_newClause_exists_fresh b H0 H' accFold2.1 accFold2.2 clause hInExpose hInAcc2

/-- Non-Fresh new clauses from addPreEqFrom are exactly the reflexivity clause.

    If c is new from addPreEqFrom (c ∈ output but c ∉ input) and c has no Fresh vars,
    then c = [pos (PreEq ti ti)]. This is because:
    1. addPreEqPair_core only adds clauses with Fresh vars
    2. addPreEqPair adds [pos (PreEq H0 H')] only when H0 = H'

    TODO: Complete this proof once addPreEqPair_core_newClause_has_fresh is proven.
    The structure is:
    1. Track c through the fold to find which addPreEqPair call produced it
    2. If from addPreEqPair_core: use addPreEqPair_core_newClause_has_fresh → contradiction
    3. If the unit clause: c = [pos (PreEq ti ti)] -/
lemma addPreEqFrom_newClause_nonFresh_eq_refl (b : Bounds S) (ti : b.times) (st : EncState b)
    (c : SAT.Clause (Var b))
    (hcIn : c ∈ (addPreEqFrom b ti st).clauses)
    (hcNotOld : c ∉ st.clauses)
    (hNoFresh : ∀ lit ∈ c, ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n) :
    c = [SAT.Lit.pos (Var.PreEq ti ti)] := by
  classical
  -- Prove the stronger statement for arbitrary list
  suffices h : ∀ (times : List b.times) (acc : EncState b),
      c ∈ (times.foldl (fun stCur t => addPreEqPair b ti t stCur) acc).clauses →
      c ∉ acc.clauses →
      c = [SAT.Lit.pos (Var.PreEq ti ti)] by
    simp only [addPreEqFrom] at hcIn
    exact h (Bounds.timesL b) st hcIn hcNotOld
  intro times
  induction times with
  | nil =>
      intro acc hcAcc hcNotAcc
      simp only [List.foldl_nil] at hcAcc
      exact absurd hcAcc hcNotAcc
  | cons H' ts ih =>
      intro acc hcFold hcNotAcc
      simp only [List.foldl_cons] at hcFold
      let stPair := addPreEqPair b ti H' acc
      by_cases hcInPair : c ∈ stPair.clauses
      · -- c comes from this addPreEqPair call or earlier
        by_cases hcInAcc : c ∈ acc.clauses
        · exact absurd hcInAcc hcNotAcc
        · -- c is NEW from this addPreEqPair call
          simp only [stPair, addPreEqPair] at hcInPair
          by_cases hEq : ti = H'
          · -- ti = H': output = addClause stCore [pos (PreEq ti H')]
            subst hEq
            simp only [↓reduceIte, EncState.addClause] at hcInPair
            cases hcInPair with
            | head => rfl
            | tail _ hCore =>
                have ⟨lit, hLit, n, hFreshLit⟩ :=
                  addPreEqPair_core_newClause_has_fresh b ti ti acc c hCore hcInAcc
                exact absurd hFreshLit (hNoFresh lit hLit n)
          · -- ti ≠ H': output = addPreEqPair_core
            simp only [hEq, ↓reduceIte] at hcInPair
            have ⟨lit, hLit, n, hFreshLit⟩ :=
              addPreEqPair_core_newClause_has_fresh b ti H' acc c hcInPair hcInAcc
            exact absurd hFreshLit (hNoFresh lit hLit n)
      · -- c is from tail of fold
        exact ih stPair hcFold hcInPair

end Encoding
