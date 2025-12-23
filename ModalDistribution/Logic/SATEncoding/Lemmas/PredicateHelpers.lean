import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Lemmas.NextFreshMono
import ModalDistribution.Logic.SATEncoding.Lemmas.Basic

/-!
# Predicate Encoding Offset Helpers

This file contains helper lemmas for predicate encoding offset preservation.
These lemmas show that various fold operations preserve the "offset" between
two encoding states - a key property for structural determinism.

## Main Lemmas

- `inner_addClause_fold_offset`, `nested_addClause_fold_offset`: Predicate clause folds
- `inner_addClause_fold2_offset`, `nested_addClause_fold2_offset`: Second predicate clause folds
- `preEqAccStep_*`: PreEq accumulator step properties
- `mkY_nextFresh_eq`, `mkDw_*`, `mkOw_*`: Helper function properties
- `preEqObligationStep_*`: PreEq obligation step properties
- `addPreEqPair_*`, `addPreEqFrom_offset`: PreEq pair/from offset preservation
- `addPreEqReflAll_nextFresh'`: Reflexivity clause preservation
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}


/-! ### Helper lemmas for predicate encoding offset preservation -/

/-- Inner fold for first nested structure in predicate encoding preserves offset. -/
lemma inner_addClause_fold_offset (b : Bounds S) (ks : List b.predIx) (w : WId b) (ti : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (ks.foldl (fun stAcc' k =>
      EncState.addClause b stAcc'
        [SAT.Lit.neg (Var.PreEq ti ti), SAT.Lit.neg (Var.Pred w.p ti k),
         SAT.Lit.pos (Var.Pred w.p w.ti k)])
      st').nextFresh =
    (ks.foldl (fun stAcc' k =>
      EncState.addClause b stAcc'
        [SAT.Lit.neg (Var.PreEq ti ti), SAT.Lit.neg (Var.Pred w.p ti k),
         SAT.Lit.pos (Var.Pred w.p w.ti k)])
      st).nextFresh + offset := by
  induction ks generalizing st st' with
  | nil => exact hOffset
  | cons k ks' ih =>
    simp only [List.foldl_cons]
    exact ih (EncState.addClause b st _) (EncState.addClause b st' _)
      (by simp [EncState.addClause, hOffset])

/-- The first nested fold in predicate encoding preserves offset. -/
lemma nested_addClause_fold_offset (b : Bounds S) (ks : List b.predIx) (w : WId b)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    ((Bounds.timesL b).foldl (fun stAcc ti =>
      ks.foldl (fun stAcc' k =>
        EncState.addClause b stAcc'
          [SAT.Lit.neg (Var.PreEq ti ti), SAT.Lit.neg (Var.Pred w.p ti k),
           SAT.Lit.pos (Var.Pred w.p w.ti k)])
        stAcc) st').nextFresh =
    ((Bounds.timesL b).foldl (fun stAcc ti =>
      ks.foldl (fun stAcc' k =>
        EncState.addClause b stAcc'
          [SAT.Lit.neg (Var.PreEq ti ti), SAT.Lit.neg (Var.Pred w.p ti k),
           SAT.Lit.pos (Var.Pred w.p w.ti k)])
        stAcc) st).nextFresh + offset := by
  induction (Bounds.timesL b) generalizing st st' with
  | nil => exact hOffset
  | cons ti tis ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (inner_addClause_fold_offset b ks w ti st st' offset hOffset)

/-- Inner fold for second nested structure in predicate encoding preserves offset. -/
lemma inner_addClause_fold2_offset (b : Bounds S) (ks : List b.predIx) (w : WId b) (H' : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (ks.foldl (fun stAcc k =>
      let backward :=
        [ SAT.Lit.neg (Var.PreEq w.ti H')
        , SAT.Lit.neg (Var.Pred w.p H' k)
        , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
      let forward :=
        [ SAT.Lit.neg (Var.PreEq w.ti H')
        , SAT.Lit.neg (Var.Pred w.p w.ti k)
        , SAT.Lit.pos (Var.Pred w.p H' k) ]
      EncState.addClause b (EncState.addClause b stAcc backward) forward)
      st').nextFresh =
    (ks.foldl (fun stAcc k =>
      let backward :=
        [ SAT.Lit.neg (Var.PreEq w.ti H')
        , SAT.Lit.neg (Var.Pred w.p H' k)
        , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
      let forward :=
        [ SAT.Lit.neg (Var.PreEq w.ti H')
        , SAT.Lit.neg (Var.Pred w.p w.ti k)
        , SAT.Lit.pos (Var.Pred w.p H' k) ]
      EncState.addClause b (EncState.addClause b stAcc backward) forward)
      st).nextFresh + offset := by
  induction ks generalizing st st' with
  | nil => exact hOffset
  | cons k ks' ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (by simp only [EncState.addClause, hOffset])

/-- The second nested fold in predicate encoding preserves offset. -/
lemma nested_addClause_fold2_offset (b : Bounds S) (ks : List b.predIx) (w : WId b)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    ((Bounds.timesL b).foldl (fun stCur H' =>
      ks.foldl (fun stAcc k =>
        let backward :=
          [ SAT.Lit.neg (Var.PreEq w.ti H')
          , SAT.Lit.neg (Var.Pred w.p H' k)
          , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
        let forward :=
          [ SAT.Lit.neg (Var.PreEq w.ti H')
          , SAT.Lit.neg (Var.Pred w.p w.ti k)
          , SAT.Lit.pos (Var.Pred w.p H' k) ]
        EncState.addClause b (EncState.addClause b stAcc backward) forward)
      stCur) st').nextFresh =
    ((Bounds.timesL b).foldl (fun stCur H' =>
      ks.foldl (fun stAcc k =>
        let backward :=
          [ SAT.Lit.neg (Var.PreEq w.ti H')
          , SAT.Lit.neg (Var.Pred w.p H' k)
          , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
        let forward :=
          [ SAT.Lit.neg (Var.PreEq w.ti H')
          , SAT.Lit.neg (Var.Pred w.p w.ti k)
          , SAT.Lit.pos (Var.Pred w.p H' k) ]
        EncState.addClause b (EncState.addClause b stAcc backward) forward)
      stCur) st).nextFresh + offset := by
  induction (Bounds.timesL b) generalizing st st' with
  | nil => exact hOffset
  | cons H' Hs ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (inner_addClause_fold2_offset b ks w H' st st' offset hOffset)

-- Helper lemmas for PreEq offset preservation

lemma preEqAccStep_nextFresh_eq (b : Bounds S)
    (acc : FVar b × EncState b) (o : FVar b) :
    (preEqAccStep b acc o).2.nextFresh = acc.2.nextFresh + 1 := by
  simp only [preEqAccStep, addAccStep, EncState.allocFresh, EncState.addClause]

lemma foldl_preEqAccStep_nextFresh_eq (b : Bounds S)
    (os : List (FVar b)) (acc : FVar b × EncState b) :
    (os.foldl (preEqAccStep b) acc).2.nextFresh = acc.2.nextFresh + os.length := by
  induction os generalizing acc with
  | nil => simp
  | cons o os' ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, preEqAccStep_nextFresh_eq]; ring

lemma foldl_preEqAccStep_offset (b : Bounds S)
    (os os' : List (FVar b)) (acc acc' : FVar b × EncState b)
    (offset : Nat) (hLen : os.length = os'.length)
    (hOffset : acc'.2.nextFresh = acc.2.nextFresh + offset) :
    (os'.foldl (preEqAccStep b) acc').2.nextFresh =
    (os.foldl (preEqAccStep b) acc).2.nextFresh + offset := by
  rw [foldl_preEqAccStep_nextFresh_eq, foldl_preEqAccStep_nextFresh_eq, hOffset, hLen]; ring

lemma mkY_nextFresh_eq (b : Bounds S) (t' : b.times) (w w' : WId b) (st : EncState b) :
    (mkY b t' w w' st).2.nextFresh = st.nextFresh + 1 := by
  simp only [mkY, EncState.allocFresh, EncState.addClause]

lemma mkDw_fold_snd_nextFresh (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (vs : List (Var b)) (st : EncState b) :
    let step := fun (acc : List (Var b) × EncState b) w' =>
      let (vs, st') := acc
      let (y, st'') := mkY b t' w w' st'
      (FVar.toVar b y :: vs, st'')
    (cands.foldl step (vs, st)).2.nextFresh = st.nextFresh + cands.length := by
  intro step
  induction cands generalizing vs st with
  | nil => simp
  | cons w' ws ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hStep : (step (vs, st) w').2 = (mkY b t' w w' st).2 := by simp [step]
    rw [ih, hStep, mkY_nextFresh_eq]; omega

lemma mkOw_nextFresh_eq (b : Bounds S) (t : b.times) (w : WId b)
    (d : FVar b) (st : EncState b) :
    (mkOw b t w d st).2.nextFresh = st.nextFresh + 1 := by
  simp only [mkOw, EncState.allocFresh, EncState.addClause]

lemma mkOw_offset (b : Bounds S) (t : b.times) (w : WId b)
    (d d' : FVar b) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (mkOw b t w d' st').2.nextFresh = (mkOw b t w d st).2.nextFresh + offset := by
  rw [mkOw_nextFresh_eq, mkOw_nextFresh_eq, hOffset]; ring

/-- addPreEqReflAll preserves nextFresh (it only uses addClause). -/
lemma addPreEqReflAll_nextFresh' (b : Bounds S) (st : EncState b) :
    (addPreEqReflAll b st).nextFresh = st.nextFresh := by
  simp only [addPreEqReflAll]
  induction (Bounds.timesL b) generalizing st with
  | nil => rfl
  | cons ti tis ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [EncState.addClause]

variable [DecidableEq S.EventType]

lemma mkDw_nextFresh_eq (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b) :
    let cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
    (mkDw b t' w st).2.nextFresh = st.nextFresh + cands.length + 1 := by
  intro cands
  simp only [mkDw]
  cases hCands : (WId.allWorlds b).filter (fun w' => sameSig b w w') with
  | nil =>
    simp only [EncState.allocFresh, EncState.addClause]
    have hLen : cands.length = 0 := by simp only [cands, hCands, List.length_nil]
    omega
  | cons cand cands' =>
    simp only
    have hFold := mkDw_fold_snd_nextFresh b t' w (cand :: cands') [] st
    simp only at hFold
    rw [mkBigOrIff_nextFresh, hFold]
    have hLen : cands.length = (cand :: cands').length := by simp only [cands, hCands]
    omega

lemma mkDw_offset (b : Bounds S) (t' : b.times) (w : WId b)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (mkDw b t' w st').2.nextFresh = (mkDw b t' w st).2.nextFresh + offset := by
  simp only [mkDw_nextFresh_eq, hOffset]; omega


lemma preEqObligationStep_offset (b : Bounds S) (t t' : b.times)
    (acc acc' : List (FVar b) × EncState b) (w : WId b) (offset : Nat)
    (hOffset : acc'.2.nextFresh = acc.2.nextFresh + offset) :
    (preEqObligationStep b t t' acc' w).2.nextFresh =
    (preEqObligationStep b t t' acc w).2.nextFresh + offset := by
  simp only [preEqObligationStep]
  have hDwOff := mkDw_offset b t' w acc.2 acc'.2 offset hOffset
  exact mkOw_offset b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc'.2).1
    (mkDw b t' w acc.2).2 (mkDw b t' w acc'.2).2 offset hDwOff

lemma foldl_preEqObligationStep_offset (b : Bounds S) (t t' : b.times)
    (worlds : List (WId b))
    (acc acc' : List (FVar b) × EncState b) (offset : Nat)
    (hOffset : acc'.2.nextFresh = acc.2.nextFresh + offset) :
    (worlds.foldl (preEqObligationStep b t t') acc').2.nextFresh =
    (worlds.foldl (preEqObligationStep b t t') acc).2.nextFresh + offset := by
  induction worlds generalizing acc acc' with
  | nil => exact hOffset
  | cons w ws ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (preEqObligationStep_offset b t t' acc acc' w offset hOffset)

lemma preEqObligationStep_fst_length (b : Bounds S) (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b) :
    (preEqObligationStep b t t' acc w).1.length = acc.1.length + 1 := by
  simp only [preEqObligationStep, List.length_cons]

lemma foldl_preEqObligationStep_fst_length (b : Bounds S) (t t' : b.times)
    (worlds : List (WId b)) (acc : List (FVar b) × EncState b) :
    (worlds.foldl (preEqObligationStep b t t') acc).1.length =
    acc.1.length + worlds.length := by
  induction worlds generalizing acc with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, preEqObligationStep_fst_length]; omega

lemma foldl_preEqObligationStep_fst_length_eq (b : Bounds S) (t t' : b.times)
    (worlds : List (WId b)) (st st' : EncState b) :
    (worlds.foldl (preEqObligationStep b t t') ([], st')).1.length =
    (worlds.foldl (preEqObligationStep b t t') ([], st)).1.length := by
  rw [foldl_preEqObligationStep_fst_length, foldl_preEqObligationStep_fst_length]

/-- addPreEqPair_core preserves offset. -/
lemma addPreEqPair_core_offset (b : Bounds S) (H0 H' : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (addPreEqPair_core b H0 H' st').nextFresh =
    (addPreEqPair_core b H0 H' st).nextFresh + offset := by
  simp only [addPreEqPair_core]
  -- Define intermediate states
  let os := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)
  let os' := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], os.2)
  let os_ := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')
  let os'_ := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], os_.2)
  -- Track offsets
  have h1 : os_.2.nextFresh = os.2.nextFresh + offset :=
    foldl_preEqObligationStep_offset b H0 H' _ ([], st) ([], st') offset (by simp [hOffset])
  have h2 : os'_.2.nextFresh = os'.2.nextFresh + offset :=
    foldl_preEqObligationStep_offset b H' H0 _ ([], os.2) ([], os_.2) offset (by simp [h1])
  -- Length equalities
  have hLen1 : os.1.length = os_.1.length :=
    (foldl_preEqObligationStep_fst_length_eq b H0 H' _ st st').symm
  have hLen2 : os'.1.length = os'_.1.length :=
    (foldl_preEqObligationStep_fst_length_eq b H' H0 _ os.2 os_.2).symm
  -- allocFresh + addClause
  have h3 : (EncState.addClause b (EncState.allocFresh b os'_.2).2
      [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b os'_.2).1)]).nextFresh =
    (EncState.addClause b (EncState.allocFresh b os'.2).2
      [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b os'.2).1)]).nextFresh + offset := by
    simp only [EncState.allocFresh, EncState.addClause, h2]; ring
  -- First preEqAccStep fold
  have h4 : (os_.1.foldl (preEqAccStep b)
      ((EncState.allocFresh b os'_.2).1,
       EncState.addClause b (EncState.allocFresh b os'_.2).2
         [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b os'_.2).1)])).2.nextFresh =
    (os.1.foldl (preEqAccStep b)
      ((EncState.allocFresh b os'.2).1,
       EncState.addClause b (EncState.allocFresh b os'.2).2
         [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b os'.2).1)])).2.nextFresh + offset :=
    foldl_preEqAccStep_offset b os.1 os_.1 _ _ offset hLen1 h3
  -- Second preEqAccStep fold
  have h5 : (os'_.1.foldl (preEqAccStep b)
      (os_.1.foldl (preEqAccStep b)
        ((EncState.allocFresh b os'_.2).1,
         EncState.addClause b (EncState.allocFresh b os'_.2).2
           [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b os'_.2).1)]))).2.nextFresh =
    (os'.1.foldl (preEqAccStep b)
      (os.1.foldl (preEqAccStep b)
        ((EncState.allocFresh b os'.2).1,
         EncState.addClause b (EncState.allocFresh b os'.2).2
           [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b os'.2).1)]))).2.nextFresh + offset :=
    foldl_preEqAccStep_offset b os'.1 os'_.1 _ _ offset hLen2 h4
  -- Finally, addPreEqExpose preserves nextFresh
  simp only [addPreEqExpose_nextFresh]
  exact h5

/-- addPreEqPair preserves offset. -/
lemma addPreEqPair_offset (b : Bounds S) (H0 H' : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (addPreEqPair b H0 H' st').nextFresh =
    (addPreEqPair b H0 H' st).nextFresh + offset := by
  simp only [addPreEqPair]
  by_cases hEq : H0 = H'
  · simp only [hEq, ↓reduceIte, EncState.addClause]
    exact addPreEqPair_core_offset b H' H' st st' offset hOffset
  · simp only [hEq, ↓reduceIte]
    exact addPreEqPair_core_offset b H0 H' st st' offset hOffset

/-- addPreEqFrom preserves offset. -/
lemma addPreEqFrom_offset (b : Bounds S) (ti : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (addPreEqFrom b ti st').nextFresh =
    (addPreEqFrom b ti st).nextFresh + offset := by
  simp only [addPreEqFrom]
  induction (Bounds.timesL b) generalizing st st' with
  | nil => exact hOffset
  | cons H' Hs ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (addPreEqPair_offset b ti H' st st' offset hOffset)

/-- Helper: foldl over addPreEqPair preserves clause subset. -/
private lemma addPreEqFrom_foldl_clauses_subset (b : Bounds S) (ti : b.times)
    (times : List b.times) (st : EncState b) :
    st.clauses ⊆ (times.foldl (fun acc H' => addPreEqPair b ti H' acc) st).clauses := by
  induction times generalizing st with
  | nil => intro c hc; exact hc
  | cons t ts ih =>
      simp only [List.foldl_cons]
      intro c hc
      have hStep : st.clauses ⊆ (addPreEqPair b ti t st).clauses :=
        addPreEqPair_clauses_subset b ti t st
      exact ih _ (hStep hc)

/-- preEqObligationStep's nextFresh output only depends on input state's nextFresh, not the list. -/
lemma preEqObligationStep_nextFresh_independent_of_list (b : Bounds S) (t t' : b.times)
    (w : WId b) (os os' : List (FVar b)) (st : EncState b) :
    (preEqObligationStep b t t' (os, st) w).2.nextFresh =
    (preEqObligationStep b t t' (os', st) w).2.nextFresh := by
  -- The nextFresh only depends on mkDw and mkOw, which only use the state
  unfold preEqObligationStep
  simp only

/-- preEqObligationStep increment is independent of both the list component and clauses.
    Only the input nextFresh matters. -/
lemma preEqObligationStep_nextFresh_increment_general (b : Bounds S) (t t' : b.times)
    (w : WId b) (acc acc' : List (FVar b) × EncState b)
    (hEq : acc.2.nextFresh = acc'.2.nextFresh) :
    (preEqObligationStep b t t' acc w).2.nextFresh =
    (preEqObligationStep b t t' acc' w).2.nextFresh := by
  -- First, show step(acc) = step(([], acc.2)) for nextFresh purposes
  have h1 : (preEqObligationStep b t t' acc w).2.nextFresh =
      (preEqObligationStep b t t' ([], acc.2) w).2.nextFresh :=
    preEqObligationStep_nextFresh_independent_of_list b t t' w acc.1 [] acc.2
  have h2 : (preEqObligationStep b t t' acc' w).2.nextFresh =
      (preEqObligationStep b t t' ([], acc'.2) w).2.nextFresh :=
    preEqObligationStep_nextFresh_independent_of_list b t t' w acc'.1 [] acc'.2
  -- Now use the existing increment lemma
  -- hIncr: step([], acc.2) - acc.2 = step([], acc'.2) - acc'.2
  have hIncr := preEqObligationStep_nextFresh_increment b t t' w acc.2 acc'.2
  have hGe1 := preEqObligationStep_nextFresh_ge b t t' ([], acc.2) w
  have hGe2 := preEqObligationStep_nextFresh_ge b t t' ([], acc'.2) w
  -- Since acc.2.nextFresh = acc'.2.nextFresh (hEq), and the increment is the same,
  -- the outputs must be equal
  -- step1 - x = step2 - x where x = acc.2.nextFresh = acc'.2.nextFresh
  -- And step1 ≥ x, step2 ≥ x, so step1 = step2
  simp only [Prod.snd] at hGe1 hGe2
  rw [hEq] at hIncr hGe1
  -- Now hIncr: step([], acc'.2) - acc'.2 = step([], acc'.2) - acc'.2 (trivial!)
  -- Actually we need to be more careful. hIncr says (step([], acc.2) - acc.2) = (step([], acc'.2) - acc'.2)
  -- With hEq: acc.2 = acc'.2 (by nextFresh), so step([], acc.2) - acc'.2 = step([], acc'.2) - acc'.2
  -- Combined with step([], acc.2) ≥ acc.2 = acc'.2, we can conclude step([], acc.2) = step([], acc'.2)
  -- Actually after rewrite, hGe1: acc'.2.nextFresh ≤ step([], acc.2).2.nextFresh
  -- And hGe2: acc'.2.nextFresh ≤ step([], acc'.2).2.nextFresh
  -- hIncr: step([], acc.2) - acc.2 = step([], acc'.2) - acc'.2
  -- Since acc.2 = acc'.2 (nextFresh), we have step([], acc.2) - acc'.2 = step([], acc'.2) - acc'.2
  -- Both steps ≥ acc'.2, so this means step([], acc.2) = step([], acc'.2)
  omega

/-- When two accumulators have states with equal nextFresh, preEqObligationStep fold produces
equal nextFresh. The list component doesn't matter for nextFresh calculation. -/
lemma preEqObligation_fold_nextFresh_eq_of_nextFresh_eq_aux (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (acc acc' : List (FVar b) × EncState b)
    (hEq : acc.2.nextFresh = acc'.2.nextFresh) :
    (ws.foldl (preEqObligationStep b t t') acc).2.nextFresh =
    (ws.foldl (preEqObligationStep b t t') acc').2.nextFresh := by
  induction ws generalizing acc acc' with
  | nil => simp [hEq]
  | cons w ws' ih =>
      simp only [List.foldl_cons]
      apply ih
      exact preEqObligationStep_nextFresh_increment_general b t t' w acc acc' hEq

/-- When two states have equal nextFresh, preEqObligationStep fold produces equal nextFresh.

This is because the encoding's nextFresh increment only depends on input nextFresh, not clauses. -/
lemma preEqObligation_fold_nextFresh_eq_of_nextFresh_eq (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (st st' : EncState b)
    (hEq : st.nextFresh = st'.nextFresh) :
    (ws.foldl (preEqObligationStep b t t') ([], st)).2.nextFresh =
    (ws.foldl (preEqObligationStep b t t') ([], st')).2.nextFresh :=
  preEqObligation_fold_nextFresh_eq_of_nextFresh_eq_aux b t t' ws ([], st) ([], st') hEq

/-- Monotonicity from offset preservation for preEqObligationStep fold.

If st ≤ st' (with st' - st = offset) and the fold preserves offset,
then the fold output at st is ≤ the fold output at st'. -/
lemma preEqObligation_fold_mono_from_offset (b : Bounds S) (t t' : b.times)
    (ws : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh) :
    (ws.foldl (preEqObligationStep b t t') ([], st)).2.nextFresh ≤
    (ws.foldl (preEqObligationStep b t t') ([], st')).2.nextFresh := by
  by_cases hOffZero : offset = 0
  · -- offset = 0 means st.nextFresh = st'.nextFresh
    have hStEq : st.nextFresh = st'.nextFresh := by omega
    have hFoldEq := preEqObligation_fold_nextFresh_eq_of_nextFresh_eq b t t' ws st st' hStEq
    omega
  · -- offset > 0
    have hFoldOffset := preEqObligationStep_foldl_offset_preserved b t t' ws st st'
    -- hFoldOffset : fold' - fold = st' - st
    -- Since offset > 0, st' - st > 0, so fold' - fold > 0, so fold' > fold
    omega

/-- Structural determinism for the base clause [pos base'] in addPreEqPair_core.

This handles the case where clause = [pos base'] from the addClause after allocFresh. -/
lemma addPreEqPair_core_base_clause_SD (b : Bounds S) (H0 H' : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : st.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (addPreEqPair_core b H0 H' st).clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true) :
    let fold1 := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)
    let fold2 := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1.2)
    let base := (EncState.allocFresh b fold2.2).1
    let fold1' := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')
    let fold2' := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1'.2)
    let base' := (EncState.allocFresh b fold2'.2).1
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < st'.nextFresh then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v
    SAT.Clause.eval σ' [SAT.Lit.pos (FVar.toVar b base')] = true := by
  -- Define the lets explicitly in the proof context (keeps connection to definition)
  show SAT.Clause.eval _ [SAT.Lit.pos (FVar.toVar b _)] = true
  -- Define locals with same names
  let fold1 := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)
  let fold2 := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1.2)
  let base := (EncState.allocFresh b fold2.2).1
  let fold1' := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')
  let fold2' := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1'.2)
  let base' := (EncState.allocFresh b fold2'.2).1
  let σ' : SAT.Assignment (Var b) := fun v =>
    match v with
    | Var.Fresh n => if n < st'.nextFresh then σ v else σ (Var.Fresh (n - offset))
    | _ => σ v
  -- Unfold to show base', base identities
  have hBase : base.id = fold2.2.nextFresh := by simp only [base, EncState.allocFresh]
  have hBase' : base'.id = fold2'.2.nextFresh := by simp only [base', EncState.allocFresh]
  -- Get offset facts for fold2
  have hFold1Offset := preEqObligationStep_foldl_offset_preserved b H0 H' (WId.allWorlds b) st st'
  have hFold2Offset := preEqObligationStep_foldl_offset_preserved b H' H0
    (WId.allWorlds b) fold1.2 fold1'.2
  have hFold1Mono := preEqObligation_fold_mono_from_offset b H0 H'
    (WId.allWorlds b) st st' offset hOffset hMono
  have hFold2Mono := preEqObligation_fold_mono_from_offset b H' H0
    (WId.allWorlds b) fold1.2 fold1'.2 (fold1'.2.nextFresh - fold1.2.nextFresh) rfl hFold1Mono
  -- Establish base' - base = offset
  have hBaseShift : base'.id = base.id + offset := by
    simp only [hBase, hBase', hOffset]
    -- Need to tell omega that fold1/fold2 equal the explicit foldl expressions
    have hFold1Eq : fold1.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)).2.nextFresh := rfl
    have hFold1'Eq : fold1'.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2.nextFresh := rfl
    have hFold2Eq : fold2.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1.2)).2.nextFresh := rfl
    have hFold2'Eq : fold2'.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1'.2)).2.nextFresh := rfl
    omega
  -- σ satisfies [pos base] from the final clauses
  simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, or_false, SAT.Lit.eval]
  have hSatBase : σ (FVar.toVar b base) = true := by
    -- Step 1: Show [pos base] is in the output clauses
    have hMem : [SAT.Lit.pos (FVar.toVar b base)] ∈
        (EncState.addClause b (EncState.allocFresh b fold2.2).2
          [SAT.Lit.pos (FVar.toVar b base)]).clauses := by
      simp only [EncState.addClause, List.mem_cons, true_or]
    -- Trace through to final clauses
    let st3 := EncState.addClause b (EncState.allocFresh b fold2.2).2
      [SAT.Lit.pos (FVar.toVar b base)]
    let accFold1 := fold1.1.foldl (preEqAccStep b) (base, st3)
    let accFold2 := fold2.1.foldl (preEqAccStep b) accFold1
    have hAcc1Sub := preEqAcc_fold_clauses_subset b fold1.1 (init := (base, st3)) rfl
    have hAcc2Sub := preEqAcc_fold_clauses_subset b fold2.1 (init := accFold1) rfl
    have hExpSub := addPreEqExpose_clauses_subset b H0 H' accFold2.1 accFold2.2
    have hFinal := hExpSub (hAcc2Sub (hAcc1Sub hMem))
    -- Step 2: Show [pos base] is NOT in st.clauses (base.id ≥ st.nextFresh by WF)
    have hBaseGe : base.id ≥ st.nextFresh := by
      rw [hBase]
      have hFold1Mono := preEqObligationStep_foldl_mono b H0 H' (WId.allWorlds b) ([], st)
      have hFold2Mono := preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1.2)
      exact Nat.le_trans hFold1Mono hFold2Mono
    have hNotInSt : [SAT.Lit.pos (FVar.toVar b base)] ∉ st.clauses := by
      intro hIn
      -- By WF, all Fresh vars in st.clauses have id < st.nextFresh
      -- But base.id ≥ st.nextFresh, contradiction
      have hLit : SAT.Lit.pos (FVar.toVar b base) ∈ [SAT.Lit.pos (FVar.toVar b base)] :=
        List.mem_singleton_self _
      -- hWF : st.WellFormed = ∀ clause ∈ st.clauses, clauseFreshBelow clause st.nextFresh
      have hCFB := hWF _ hIn
      -- clauseFreshBelow clause bound = ∀ lit ∈ clause, litFreshBelow lit bound
      have hFB := hCFB _ hLit
      simp only [litFreshBelow, FVar.toVar] at hFB
      exact Nat.not_lt.mpr hBaseGe hFB
    -- Step 3: Apply hSatNew
    have hEval := hSatNew _ hFinal hNotInSt
    simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, SAT.Lit.eval] at hEval
    simp only [Bool.or_false] at hEval
    exact hEval
  -- Show σ'(base') = σ(base)
  -- Goal: σ' (Fresh base'.id) = true
  -- σ' (Fresh n) = if n < st'.nextFresh then σ (Fresh n) else σ (Fresh (n - offset))
  have hBase'Ge : base'.id ≥ st'.nextFresh := by
    simp only [hBase']
    have hStMono := preEqObligationStep_foldl_mono b H0 H' (WId.allWorlds b) ([], st')
    have hFold1'Mono := preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1'.2)
    -- Connect let bindings to foldl expressions (including ([], x).2 = x)
    have hFold1'Eq : fold1'.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2.nextFresh := rfl
    have hFold2'Eq : fold2'.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1'.2)).2.nextFresh := rfl
    have hSt'Eq : st'.nextFresh = (([], st') : List (FVar b) × EncState b).2.nextFresh := rfl
    have hFold1'2Eq : fold1'.2.nextFresh =
        (([], fold1'.2) : List (FVar b) × EncState b).2.nextFresh := rfl
    omega
  have hNotLt : ¬(base'.id < st'.nextFresh) := Nat.not_lt.mpr hBase'Ge
  have hShift : base'.id - offset = base.id := by
    simp only [hBase, hBase', hOffset]
    have hFold1Eq : fold1.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)).2.nextFresh := rfl
    have hFold1'Eq : fold1'.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2.nextFresh := rfl
    have hFold2Eq : fold2.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1.2)).2.nextFresh := rfl
    have hFold2'Eq : fold2'.2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1'.2)).2.nextFresh := rfl
    omega
  -- Need to establish that the if condition equals ¬hNotLt
  -- Goal has the full allocFresh expression, need to connect to base'
  have hBase'Eq : base'.id = (EncState.allocFresh b fold2'.2).1.id := rfl
  have hFold2'Eq2 : fold2'.2 = ((WId.allWorlds b).foldl (preEqObligationStep b H' H0)
      ([], ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2)).2 := rfl
  -- Simplify the goal
  simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, SAT.Lit.eval, FVar.toVar]
  simp only [Bool.or_false]
  -- The if condition needs to be shown false
  have hCondFalse : ¬((EncState.allocFresh b ((WId.allWorlds b).foldl (preEqObligationStep b H' H0)
      ([], ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2)).2).1.id <
      st'.nextFresh) := by
    simp only [← hBase'Eq, ← hFold2'Eq2]; exact hNotLt
  simp only [hCondFalse, ↓reduceIte]
  -- Now show σ (Fresh (X - offset)) = true where X is the st'-side allocFresh
  -- Need: (allocFresh on st'-side).id - offset = base.id
  -- We have: hShift : base'.id - offset = base.id
  -- and: base'.id = (allocFresh on st'-side).id (via hBase'Eq and hFold2'Eq2)
  have hArgEq : (EncState.allocFresh b ((WId.allWorlds b).foldl (preEqObligationStep b H' H0)
      ([], ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2)).2).1.id - offset =
      base.id := by
    simp only [← hBase'Eq, ← hFold2'Eq2, hShift]
  simp only [hArgEq]
  -- Goal is now σ (Var.Fresh base.id) = true
  -- hSatBase : σ (FVar.toVar b base) = true
  -- FVar.toVar b base = Var.Fresh base.id by definition
  have hToVarEq : Var.Fresh base.id = FVar.toVar b base := rfl
  simp only [hToVarEq]
  exact hSatBase

/-- Structural determinism for NEW clauses from addPreEqPair_core.

This is the core helper for addPreEqPair_newClauses_structural_determinism.
It handles the pipeline of:
1. Two preEqObligationStep folds (for H0→H' and H'→H0 directions)
2. allocFresh + addClause [pos base]
3. Two preEqAccStep folds
4. addPreEqExpose

The proof traces the clause through the pipeline and applies the appropriate SD lemma. -/
lemma addPreEqPair_core_newClauses_SD (b : Bounds S) (H0 H' : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : st.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (addPreEqPair_core b H0 H' st).clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (addPreEqPair_core b H0 H' st').clauses)
    (hClauseNotInBase : clause ∉ st'.clauses) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < st'.nextFresh then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    SAT.Clause.eval σ' clause = true := by
  intro σ'
  classical
  -- Unfold addPreEqPair_core to see the pipeline structure
  simp only [addPreEqPair_core] at hClauseMem hSatNew
  -- Define intermediate states for st-side
  let fold1 := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)
  let fold2 := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1.2)
  let allocRes := EncState.allocFresh b fold2.2
  let base := allocRes.1
  let st3 := EncState.addClause b allocRes.2 [SAT.Lit.pos (FVar.toVar b base)]
  let accFold1 := fold1.1.foldl (preEqAccStep b) (base, st3)
  let accFold2 := fold2.1.foldl (preEqAccStep b) (accFold1.1, accFold1.2)
  -- Define intermediate states for st'-side
  let fold1' := (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')
  let fold2' := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1'.2)
  let allocRes' := EncState.allocFresh b fold2'.2
  let base' := allocRes'.1
  let st3' := EncState.addClause b allocRes'.2 [SAT.Lit.pos (FVar.toVar b base')]
  let accFold1' := fold1'.1.foldl (preEqAccStep b) (base', st3')
  let accFold2' := fold2'.1.foldl (preEqAccStep b) (accFold1'.1, accFold1'.2)
  -- Offset preservation
  have hFold1Offset : fold1'.2.nextFresh - fold1.2.nextFresh = offset := by
    change ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2.nextFresh -
        ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)).2.nextFresh = offset
    rw [hOffset]; exact preEqObligationStep_foldl_offset_preserved b H0 H' (WId.allWorlds b) st st'
  have hFold1Mono : fold1.2.nextFresh ≤ fold1'.2.nextFresh :=
    preEqObligation_fold_mono_from_offset b H0 H' (WId.allWorlds b) st st' offset hOffset hMono
  have hFold2Offset : fold2'.2.nextFresh - fold2.2.nextFresh = offset := by
    change ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1'.2)).2.nextFresh -
        ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], fold1.2)).2.nextFresh = offset
    have h := preEqObligationStep_foldl_offset_preserved b H' H0 (WId.allWorlds b) fold1.2 fold1'.2
    rw [hFold1Offset] at h; exact h
  have hFold2Mono : fold2.2.nextFresh ≤ fold2'.2.nextFresh :=
    preEqObligation_fold_mono_from_offset b H' H0 (WId.allWorlds b) fold1.2 fold1'.2 offset hFold1Offset.symm hFold1Mono
  -- Clause subset chain for st-side (used to establish σ satisfaction)
  have hSubsetChain : st.clauses ⊆ (addPreEqExpose b H0 H' accFold2.1 accFold2.2).clauses := by
    have h1 := preEqObligation_fold_clauses_subset b H0 H' (WId.allWorlds b) (init := ([], st)) rfl
    have h2 := preEqObligation_fold_clauses_subset b H' H0 (WId.allWorlds b) (init := ([], fold1.2)) rfl
    have h3 : fold2.2.clauses ⊆ allocRes.2.clauses := by
      intro c hc; rw [EncState.allocFresh_clauses_eq]; exact hc
    have h4 := EncState.addClause_subset_clauses b allocRes.2 [SAT.Lit.pos (FVar.toVar b base)]
    have h5 := preEqAcc_fold_clauses_subset b fold1.1 (init := (base, st3)) rfl
    have h6 := preEqAcc_fold_clauses_subset b fold2.1 (init := (accFold1.1, accFold1.2)) rfl
    have h7 := addPreEqExpose_clauses_subset b H0 H' accFold2.1 accFold2.2
    intro c hc
    exact h7 (h6 (h5 (h4 (h3 (h2 (h1 hc))))))
  -- Trace clause through pipeline
  -- Build subset chains from intermediate states to final
  have hFold1ToFinal : fold1.2.clauses ⊆ (addPreEqExpose b H0 H' accFold2.1 accFold2.2).clauses := by
    have h2 := preEqObligation_fold_clauses_subset b H' H0
      (WId.allWorlds b) (init := ([], fold1.2)) rfl
    have h3 : fold2.2.clauses ⊆ allocRes.2.clauses := by
      intro c hc; rw [EncState.allocFresh_clauses_eq]; exact hc
    have h4 := EncState.addClause_subset_clauses b allocRes.2 [SAT.Lit.pos (FVar.toVar b base)]
    have h5 := preEqAcc_fold_clauses_subset b fold1.1 (init := (base, st3)) rfl
    have h6 := preEqAcc_fold_clauses_subset b fold2.1 (init := (accFold1.1, accFold1.2)) rfl
    have h7 := addPreEqExpose_clauses_subset b H0 H' accFold2.1 accFold2.2
    intro c hc; exact h7 (h6 (h5 (h4 (h3 (h2 hc)))))
  have hFold2ToFinal : fold2.2.clauses ⊆ (addPreEqExpose b H0 H' accFold2.1 accFold2.2).clauses := by
    have h3 : fold2.2.clauses ⊆ allocRes.2.clauses := by
      intro c hc; rw [EncState.allocFresh_clauses_eq]; exact hc
    have h4 := EncState.addClause_subset_clauses b allocRes.2 [SAT.Lit.pos (FVar.toVar b base)]
    have h5 := preEqAcc_fold_clauses_subset b fold1.1 (init := (base, st3)) rfl
    have h6 := preEqAcc_fold_clauses_subset b fold2.1 (init := (accFold1.1, accFold1.2)) rfl
    have h7 := addPreEqExpose_clauses_subset b H0 H' accFold2.1 accFold2.2
    intro c hc; exact h7 (h6 (h5 (h4 (h3 hc))))
  if hInFold1' : clause ∈ fold1'.2.clauses then
    -- Apply foldl_preEqObligationStep_newClauses_structural_determinism for H0→H' direction
    -- σ satisfies all clauses from fold1 (fold1 ⊆ final output on st-side)
    have hSatFold1 : ∀ c ∈ fold1.2.clauses, c ∉ st.clauses → SAT.Clause.eval σ c = true := by
      intro c hc hNotSt
      exact hSatNew c (hFold1ToFinal hc) hNotSt
    -- clause is new (not in st')
    by_cases hClauseInSt' : clause ∈ st'.clauses
    · exact absurd hClauseInSt' hClauseNotInBase
    · exact foldl_preEqObligationStep_newClauses_structural_determinism b H0 H'
          (WId.allWorlds b) st st' offset hOffset hMono hWF σ hSatFold1 clause hInFold1' hClauseInSt'
  else if hInFold2' : clause ∈ fold2'.2.clauses then
    -- Apply foldl_preEqObligationStep_newClauses_structural_determinism for H'→H0 direction
    -- σ satisfies all clauses from fold2 (fold2 ⊆ final output on st-side)
    have hSatFold2 : ∀ c ∈ fold2.2.clauses, c ∉ fold1.2.clauses → SAT.Clause.eval σ c = true := by
      intro c hc hNotInFold1
      have hNotInSt : c ∉ st.clauses := by
        intro hInSt
        have hInFold1 := preEqObligation_fold_clauses_subset b H0 H' (WId.allWorlds b)
            (init := ([], st)) rfl hInSt
        exact hNotInFold1 hInFold1
      exact hSatNew c (hFold2ToFinal hc) hNotInSt
    -- clause is new (not in fold1'.2)
    -- The SD lemma uses fold1'.2.nextFresh as threshold, but we need st'.nextFresh
    -- For new clauses from fold2', Fresh vars have indices ≥ fold1'.2.nextFresh ≥ st'.nextFresh
    -- So both σ' definitions agree on these vars (both use the else branch)
    have hFold1WF : fold1.2.WellFormed :=
      preEqObligationStep_foldl_wf b H0 H' (WId.allWorlds b) ([], st) hWF
    have hSD := foldl_preEqObligationStep_newClauses_structural_determinism b H' H0
        (WId.allWorlds b) fold1.2 fold1'.2 offset hFold1Offset.symm hFold1Mono hFold1WF σ hSatFold2
        clause hInFold2' hInFold1'
    -- The lemma's σ' (let's call it σ'') is:
    -- σ'' v = if v is Fresh n and n < fold1'.2.nextFresh then σ v else σ (Fresh (n - offset))
    -- Our σ' v = if v is Fresh n and n < st'.nextFresh then σ v else σ (Fresh (n - offset))
    -- For Fresh vars in new clauses from fold2', n ≥ fold1'.2.nextFresh ≥ st'.nextFresh
    -- So both σ' and σ'' return σ (Fresh (n - offset)), meaning σ' = σ'' on these vars
    simp only at hSD
    -- The two σ' definitions are equal for all v since:
    -- - For non-Fresh: both return σ v
    -- - For Fresh n < st'.nextFresh: n < fold1'.2.nextFresh (since st' ≤ fold1'), so both return σ v
    -- - For Fresh n ≥ fold1'.2.nextFresh: n ≥ st'.nextFresh, so both return σ (Fresh (n - offset))
    -- - For Fresh n in [st'.nextFresh, fold1'.2.nextFresh): lemma's σ' returns σ v, ours returns σ (Fresh (n - offset))
    --   BUT: for this clause (new to fold2'), all Fresh vars have n ≥ fold1'.2.nextFresh
    -- To apply: show the assignments agree on all lits in the clause using well-formedness
    have hFold1Ge : st'.nextFresh ≤ fold1'.2.nextFresh :=
      preEqObligationStep_foldl_mono b H0 H' (WId.allWorlds b) ([], st')
    -- Use eval_eq_any to show equivalence
    rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSD ⊢
    obtain ⟨lit, hLitMem, hLitEval⟩ := hSD
    refine ⟨lit, hLitMem, ?_⟩
    -- Show the lit evaluates the same under both σ' definitions
    -- The key: for new clauses (not in fold1'.2), all Fresh vars have index ≥ fold1'.2.nextFresh
    -- This is because the fold allocates fresh vars starting from fold1'.2.nextFresh
    -- The literal's variable either agrees on both σ', or it's a non-Fresh var
    -- Split by lit polarity, then by whether the var is Fresh or not
    match lit, hLitEval with
    | SAT.Lit.pos v, hPosEval =>
        simp only [SAT.Lit.eval]
        match hV : v with
        | Var.Fresh n =>
            have hNGe : n ≥ fold1'.2.nextFresh :=
              preEqObligationStep_foldl_newClause_fresh_ge b H' H0
                (WId.allWorlds b) ([], fold1'.2) clause hInFold2' hInFold1'
                (SAT.Lit.pos (Var.Fresh n)) (hV ▸ hLitMem) n rfl
            have hNGeSt : ¬ n < st'.nextFresh := Nat.not_lt.mpr (Nat.le_trans hFold1Ge hNGe)
            have hNGeFold1 : ¬ n < fold1'.2.nextFresh := Nat.not_lt.mpr hNGe
            simp only [SAT.Lit.eval, hNGeFold1, ↓reduceIte] at hPosEval
            simp only [σ', hNGeSt, ↓reduceIte]
            exact hPosEval
        -- All non-Fresh cases: the match reduces to σ v for both σ' definitions
        | Var.Mem _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.Level _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.Pred _ _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.MinQ _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.ReachT _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.Edge _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.Exists _ _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.PreEq _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.Seq _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.Rep _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.Incomp _ _ _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
        | Var.Acc _ _ _ => simp only [σ'] at hPosEval ⊢; exact hPosEval
    | SAT.Lit.neg v, hNegEval =>
        simp only [SAT.Lit.eval]
        match hV : v with
        | Var.Fresh n =>
            have hNGe : n ≥ fold1'.2.nextFresh :=
              preEqObligationStep_foldl_newClause_fresh_ge b H' H0
                (WId.allWorlds b) ([], fold1'.2) clause hInFold2' hInFold1'
                (SAT.Lit.neg (Var.Fresh n)) (hV ▸ hLitMem) n rfl
            have hNGeSt : ¬ n < st'.nextFresh := Nat.not_lt.mpr (Nat.le_trans hFold1Ge hNGe)
            have hNGeFold1 : ¬ n < fold1'.2.nextFresh := Nat.not_lt.mpr hNGe
            simp only [SAT.Lit.eval, hNGeFold1, ↓reduceIte] at hNegEval
            simp only [σ', hNGeSt, ↓reduceIte]
            exact hNegEval
        -- All non-Fresh cases: the match reduces to σ v for both σ' definitions
        | Var.Mem _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.Level _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.Pred _ _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.MinQ _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.ReachT _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.Edge _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.Exists _ _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.PreEq _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.Seq _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.Rep _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.Incomp _ _ _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
        | Var.Acc _ _ _ => simp only [σ'] at hNegEval ⊢; exact hNegEval
  else if hInAlloc' : clause ∈ allocRes'.2.clauses then
    exact absurd (EncState.allocFresh_clauses_eq b fold2'.2 ▸ hInAlloc') hInFold2'
  else if hInSt3' : clause ∈ st3'.clauses then
    simp only [st3', EncState.addClause] at hInSt3'
    cases hInSt3' with
    | head =>
        -- Base clause SD - hSatNew already in the right form
        exact addPreEqPair_core_base_clause_SD b H0 H' st st' offset hOffset hMono hWF σ hSatNew
    | tail _ hTail => exact absurd hTail hInAlloc'
  else if hInAcc1' : clause ∈ accFold1'.2.clauses then
    -- Use foldl_preEqAccStep_newClauses_structural_determinism
    -- Establish required invariants for the SD lemma:
    -- 1. os = fold1.1, os' = fold1'.1 have same length
    have hOsLen : fold1'.1.length = fold1.1.length :=
      preEqObligationStep_foldl_fst_length_eq b H0 H' (WId.allWorlds b) st st'
    -- 2. FVar IDs in os' are shifted by offset from os
    have hOsShift : ∀ i (hi : i < fold1.1.length),
        (fold1'.1.get ⟨i, hOsLen ▸ hi⟩).id = (fold1.1.get ⟨i, hi⟩).id + offset :=
      preEqObligationStep_foldl_fst_shift b H0 H' (WId.allWorlds b) st st' offset hOffset hMono
    -- 3. All FVars in os have id ≥ st.nextFresh (the threshold)
    have hOsGeTh : ∀ o ∈ fold1.1, o.id ≥ st.nextFresh :=
      preEqObligationStep_foldl_fvars_ge b H0 H' (WId.allWorlds b) ([], st) st.nextFresh
        (le_refl _) (fun _ h => by simp at h)
    -- Establish key intermediate facts
    have hBaseId : base.id = fold2.2.nextFresh := by simp [base, allocRes, EncState.allocFresh]
    have hBase'Id : base'.id = fold2'.2.nextFresh := by simp [base', allocRes', EncState.allocFresh]
    have hAllocNext : allocRes.2.nextFresh = fold2.2.nextFresh + 1 :=
      EncState.allocFresh_nextFresh b fold2.2
    have hAlloc'Next : allocRes'.2.nextFresh = fold2'.2.nextFresh + 1 :=
      EncState.allocFresh_nextFresh b fold2'.2
    have hSt3Next : st3.nextFresh = allocRes.2.nextFresh := EncState.addClause_nextFresh b _ _
    have hSt3'Next : st3'.nextFresh = allocRes'.2.nextFresh := EncState.addClause_nextFresh b _ _
    have hFold1Mono' : st.nextFresh ≤ fold1.2.nextFresh :=
      preEqObligationStep_foldl_mono b H0 H' (WId.allWorlds b) ([], st)
    have hFold2MonoFromFold1 : fold1.2.nextFresh ≤ fold2.2.nextFresh :=
      preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1.2)
    -- 4. base'.id = base.id + offset
    have hBaseShift : base'.id = base.id + offset := by
      simp only [hBaseId, hBase'Id]; omega
    -- 5. base.id = fold2.2.nextFresh ≥ st.nextFresh
    have hBaseGeTh : base.id ≥ st.nextFresh := by simp only [hBaseId]; omega
    -- 6. Offset between st3' and st3
    have hSt3Offset : st3'.nextFresh - st3.nextFresh = offset := by
      simp only [hSt3Next, hSt3'Next, hAllocNext, hAlloc'Next]; omega
    have hSt3Mono : st3.nextFresh ≤ st3'.nextFresh := by
      simp only [hSt3Next, hSt3'Next, hAllocNext, hAlloc'Next]; omega
    -- 7. st.nextFresh ≤ st3.nextFresh (threshold before acc's nextFresh)
    have hThLe : st.nextFresh ≤ st3.nextFresh := by simp only [hSt3Next, hAllocNext]; omega
    -- 8. base.id < st3.nextFresh (cur < acc's nextFresh)
    have hBaseLtSt3 : base.id < st3.nextFresh := by simp only [hBaseId, hSt3Next, hAllocNext]; omega
    -- 9. st3.WellFormed (propagate WF through the pipeline)
    have hFold1WF : fold1.2.WellFormed :=
      preEqObligationStep_foldl_wf b H0 H' (WId.allWorlds b) ([], st) hWF
    have hFold2WF : fold2.2.WellFormed :=
      preEqObligationStep_foldl_wf b H' H0 (WId.allWorlds b) ([], fold1.2) hFold1WF
    have hAllocWF : allocRes.2.WellFormed := EncState.allocFresh_wf hFold2WF
    have hSt3WF : st3.WellFormed := by
      apply EncState.addClause_wf hAllocWF
      intro lit hLit; simp only [List.mem_singleton] at hLit; subst hLit
      simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, base, EncState.allocFresh]
      exact Nat.lt_succ_self _
    -- 10. All FVars in fold1.1 have id < st3.nextFresh
    have hOsLtSt3 : ∀ o ∈ fold1.1, o.id < st3.nextFresh := by
      intro o ho
      have hOLt := preEqObligationStep_foldl_fvars_lt b H0 H' (WId.allWorlds b) ([], st)
          (fun _ h => by simp at h) o ho
      have hFold2Mono := preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1.2)
      have hOLtFold2 : o.id < fold2.2.nextFresh := Nat.lt_of_lt_of_le hOLt hFold2Mono
      simp only [hSt3Next, hAllocNext]; omega
    -- Get σ satisfaction for accFold1 NEW clauses (not in st3)
    have hSatAcc1New : ∀ c ∈ accFold1.2.clauses, c ∉ st3.clauses →
        SAT.Clause.eval σ c = true := by
      intro c hc hNotSt3
      -- c is in accFold1.2, so in final output; need to show c ∉ st.clauses
      have hcInFinal : c ∈ (addPreEqPair_core b H0 H' st).clauses := by
        have h6 := preEqAcc_fold_clauses_subset b fold2.1 (init := (accFold1.1, accFold1.2)) rfl
        have h7 := addPreEqExpose_clauses_subset b H0 H' accFold2.1 accFold2.2
        exact h7 (h6 hc)
      -- If c ∈ st.clauses, then c ∈ st3.clauses (by transitivity)
      have hNotSt : c ∉ st.clauses := by
        intro hInSt
        have hInFold1 := preEqObligation_fold_clauses_subset b H0 H' (WId.allWorlds b)
            (init := ([], st)) rfl hInSt
        have hInFold2 := preEqObligation_fold_clauses_subset b H' H0 (WId.allWorlds b)
            (init := ([], fold1.2)) rfl hInFold1
        have hInAlloc : c ∈ allocRes.2.clauses := EncState.allocFresh_clauses_eq b fold2.2 ▸ hInFold2
        have hInSt3 := EncState.addClause_subset_clauses b allocRes.2
            [SAT.Lit.pos (FVar.toVar b base)] hInAlloc
        exact hNotSt3 hInSt3
      exact hSatNew c hcInFinal hNotSt
    -- Apply the SD lemma
    have hSD := foldl_preEqAccStep_newClauses_structural_determinism b fold1.1 fold1'.1
        (base, st3) (base', st3') offset st.nextFresh
        hSt3Offset.symm hSt3Mono hBaseShift hBaseGeTh hBaseLtSt3 hThLe hSt3WF hOsLen hOsShift
        hOsGeTh hOsLtSt3 σ hSatAcc1New clause hInAcc1' hInSt3'
    -- The SD lemma's σ' uses threshold st.nextFresh + offset = st'.nextFresh
    -- Our σ' uses threshold st'.nextFresh
    -- Since st.nextFresh + offset = st'.nextFresh (by hOffset), they're identical
    simp only at hSD
    have hThEq : st.nextFresh + offset = st'.nextFresh := by omega
    -- Convert hSD to use our σ'
    convert hSD using 2
    ext v
    cases v with
    | Fresh n =>
        simp only [σ']
        rw [hThEq]
    | _ => rfl
  else if hInAcc2' : clause ∈ accFold2'.2.clauses then
    -- Similar to accFold1' case but using fold2.1 and fold2'.1
    -- Core monotonicity facts we'll use throughout
    have hFold1Mono' : st.nextFresh ≤ fold1.2.nextFresh :=
      preEqObligationStep_foldl_mono b H0 H' (WId.allWorlds b) ([], st)
    have hFold1'Mono' : st'.nextFresh ≤ fold1'.2.nextFresh :=
      preEqObligationStep_foldl_mono b H0 H' (WId.allWorlds b) ([], st')
    have hFold2MonoFromFold1 : fold1.2.nextFresh ≤ fold2.2.nextFresh :=
      preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1.2)
    have hFold2'MonoFromFold1' : fold1'.2.nextFresh ≤ fold2'.2.nextFresh :=
      preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1'.2)
    -- Key facts about allocRes/base
    have hBaseId : base.id = fold2.2.nextFresh := by simp [base, allocRes, EncState.allocFresh]
    have hBase'Id : base'.id = fold2'.2.nextFresh := by simp [base', allocRes', EncState.allocFresh]
    have hAllocNext : allocRes.2.nextFresh = fold2.2.nextFresh + 1 :=
      EncState.allocFresh_nextFresh b fold2.2
    have hAlloc'Next : allocRes'.2.nextFresh = fold2'.2.nextFresh + 1 :=
      EncState.allocFresh_nextFresh b fold2'.2
    have hSt3Next : st3.nextFresh = allocRes.2.nextFresh := EncState.addClause_nextFresh b _ _
    have hSt3'Next : st3'.nextFresh = allocRes'.2.nextFresh := EncState.addClause_nextFresh b _ _
    -- Offset preservation through fold1
    have hFold1OffsetPres : fold1'.2.nextFresh - fold1.2.nextFresh = st'.nextFresh - st.nextFresh :=
      preEqObligationStep_foldl_offset_preserved b H0 H' (WId.allWorlds b) st st'
    have hFold1Offset : offset = fold1'.2.nextFresh - fold1.2.nextFresh := by
      rw [hFold1OffsetPres]; exact hOffset
    have hFold1Mono : fold1.2.nextFresh ≤ fold1'.2.nextFresh := by omega
    -- Offset preservation through fold2
    have hFold2OffsetPres : fold2'.2.nextFresh - fold2.2.nextFresh =
        fold1'.2.nextFresh - fold1.2.nextFresh :=
      preEqObligationStep_foldl_offset_preserved b H' H0 (WId.allWorlds b) fold1.2 fold1'.2
    have hFold2Offset : offset = fold2'.2.nextFresh - fold2.2.nextFresh := by
      rw [hFold2OffsetPres]; exact hFold1Offset
    have hFold2Mono : fold2.2.nextFresh ≤ fold2'.2.nextFresh := by omega
    -- 1. os = fold2.1, os' = fold2'.1 have same length
    have hOs2Len : fold2'.1.length = fold2.1.length :=
      preEqObligationStep_foldl_fst_length_eq b H' H0 (WId.allWorlds b) fold1.2 fold1'.2
    -- 2. FVar IDs in os' = fold2'.1 are shifted by offset from os = fold2.1
    have hOs2Shift : ∀ i (hi : i < fold2.1.length),
        (fold2'.1.get ⟨i, hOs2Len ▸ hi⟩).id = (fold2.1.get ⟨i, hi⟩).id + offset :=
      preEqObligationStep_foldl_fst_shift b H' H0 (WId.allWorlds b) fold1.2 fold1'.2
        offset hFold1Offset hFold1Mono
    -- 3. All FVars in fold2.1 have id ≥ st.nextFresh (the threshold)
    have hOs2GeTh : ∀ o ∈ fold2.1, o.id ≥ st.nextFresh := by
      intro o ho
      have hGeFold1 := preEqObligationStep_foldl_fvars_ge b H' H0 (WId.allWorlds b) ([], fold1.2)
          fold1.2.nextFresh (le_refl _) (fun _ h => by simp at h) o ho
      omega
    -- Establish st3 offset invariants
    have hSt3Offset : st3'.nextFresh - st3.nextFresh = offset := by
      simp only [hSt3Next, hSt3'Next, hAllocNext, hAlloc'Next]; omega
    have hSt3Mono : st3.nextFresh ≤ st3'.nextFresh := by
      simp only [hSt3Next, hSt3'Next, hAllocNext, hAlloc'Next]; omega
    have hOsLen : fold1'.1.length = fold1.1.length :=
      preEqObligationStep_foldl_fst_length_eq b H0 H' (WId.allWorlds b) st st'
    have hBaseShift : base'.id = base.id + offset := by
      simp only [hBaseId, hBase'Id]; omega
    -- 4. accFold1' offset and cur shift from accFold1
    have hAcc1Offset : accFold1'.2.nextFresh - accFold1.2.nextFresh = offset :=
      preEqAccStep_foldl_offset b fold1.1 fold1'.1 (base, st3) (base', st3') offset
        hSt3Offset.symm hSt3Mono hOsLen hBaseShift
    have hOsShift : ∀ i (hi : i < fold1.1.length),
        (fold1'.1.get ⟨i, hOsLen ▸ hi⟩).id = (fold1.1.get ⟨i, hi⟩).id + offset :=
      preEqObligationStep_foldl_fst_shift b H0 H' (WId.allWorlds b) st st' offset hOffset hMono
    have hAcc1CurShift : accFold1'.1.id = accFold1.1.id + offset :=
      preEqAccStep_foldl_fst_shift b fold1.1 fold1'.1 (base, st3) (base', st3') offset
        hSt3Offset.symm hSt3Mono hOsLen hOsShift hBaseShift
    have hAcc1Mono : accFold1.2.nextFresh ≤ accFold1'.2.nextFresh := by
      -- Use exact formula: fold.nextFresh = init.nextFresh + os.length
      have h1 : accFold1.2.nextFresh = st3.nextFresh + fold1.1.length :=
        preEqAccStep_foldl_nextFresh_eq b fold1.1 (base, st3)
      have h1' : accFold1'.2.nextFresh = st3'.nextFresh + fold1'.1.length :=
        preEqAccStep_foldl_nextFresh_eq b fold1'.1 (base', st3')
      rw [hOsLen] at h1'
      omega
    -- 5. accFold1.1.id ≥ st.nextFresh (threshold)
    have hAcc1CurGeTh : accFold1.1.id ≥ st.nextFresh := by
      have hBaseGeTh : base.id ≥ st.nextFresh := by simp only [hBaseId]; omega
      have hBaseLeNextFresh : st.nextFresh ≤ st3.nextFresh := by
        simp only [hSt3Next, hAllocNext]; omega
      have hOsGeTh : ∀ o ∈ fold1.1, o.id ≥ st.nextFresh :=
        preEqObligationStep_foldl_fvars_ge b H0 H' (WId.allWorlds b) ([], st) st.nextFresh
          (le_refl _) (fun _ h => by simp at h)
      exact preEqAccStep_foldl_fst_ge b fold1.1 (base, st3) st.nextFresh hBaseGeTh hBaseLeNextFresh
    -- 6. st.nextFresh ≤ accFold1.2.nextFresh
    have hThLeAcc1 : st.nextFresh ≤ accFold1.2.nextFresh := by
      have hThSt3 : st.nextFresh ≤ st3.nextFresh := by
        simp only [hSt3Next, hAllocNext]; omega
      have hSt3Acc1 : st3.nextFresh ≤ accFold1.2.nextFresh :=
        preEqAccStep_foldl_nextFresh_mono b fold1.1 (base, st3)
      omega
    -- 7. Well-formedness chain (needed for the lemmas below)
    have hFold1WF : fold1.2.WellFormed :=
      preEqObligationStep_foldl_wf b H0 H' (WId.allWorlds b) ([], st) hWF
    have hFold2WF : fold2.2.WellFormed :=
      preEqObligationStep_foldl_wf b H' H0 (WId.allWorlds b) ([], fold1.2) hFold1WF
    have hAllocWF : allocRes.2.WellFormed := EncState.allocFresh_wf hFold2WF
    have hSt3WF : st3.WellFormed := by
      apply EncState.addClause_wf hAllocWF
      intro lit hLit; simp only [List.mem_singleton] at hLit; subst hLit
      simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, base, EncState.allocFresh]
      exact Nat.lt_succ_self _
    -- 8. accFold1.1.id < accFold1.2.nextFresh (cur < acc's nextFresh)
    have hAcc1CurLtNext : accFold1.1.id < accFold1.2.nextFresh := by
      have hBaseGeTh : base.id ≥ st.nextFresh := by simp only [hBaseId]; omega
      have hBaseLtSt3 : base.id < st3.nextFresh := by
        simp only [hBaseId, hSt3Next, hAllocNext]; omega
      have hOsGeTh : ∀ o ∈ fold1.1, o.id ≥ st.nextFresh :=
        preEqObligationStep_foldl_fvars_ge b H0 H' (WId.allWorlds b) ([], st) st.nextFresh
          (le_refl _) (fun _ h => by simp at h)
      have hOsLt : ∀ o ∈ fold1.1, o.id < st3.nextFresh := by
        intro o ho
        have hOLt := preEqObligationStep_foldl_fvars_lt b H0 H' (WId.allWorlds b) ([], st)
            (fun _ h => by simp at h) o ho
        have hFold2Mono := preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1.2)
        have hOLtFold2 : o.id < fold2.2.nextFresh := Nat.lt_of_lt_of_le hOLt hFold2Mono
        simp only [hSt3Next, hAllocNext]; omega
      exact (preEqAccStep_foldl_wf b fold1.1 (base, st3) hSt3WF hBaseLtSt3 hOsLt).2
    -- 9. accFold1.2.WellFormed
    have hAcc1WF : accFold1.2.WellFormed := by
      have hBaseLtSt3 : base.id < st3.nextFresh := by
        simp only [hBaseId, hSt3Next, hAllocNext]; omega
      have hOsLt : ∀ o ∈ fold1.1, o.id < st3.nextFresh := by
        intro o ho
        have hOLt := preEqObligationStep_foldl_fvars_lt b H0 H' (WId.allWorlds b) ([], st)
            (fun _ h => by simp at h) o ho
        have hFold2Mono := preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1.2)
        have hOLtFold2 : o.id < fold2.2.nextFresh := Nat.lt_of_lt_of_le hOLt hFold2Mono
        simp only [hSt3Next, hAllocNext]; omega
      exact (preEqAccStep_foldl_wf b fold1.1 (base, st3) hSt3WF hBaseLtSt3 hOsLt).1
    -- 10. All FVars in fold2.1 have id < accFold1.2.nextFresh
    have hOs2LtAcc1 : ∀ o ∈ fold2.1, o.id < accFold1.2.nextFresh := by
      intro o ho
      have hOLt := preEqObligationStep_foldl_fvars_lt b H' H0 (WId.allWorlds b) ([], fold1.2)
          (fun _ h => by simp at h) o ho
      -- hOLt: o.id < fold2.2.nextFresh
      -- accFold1.2.nextFresh = st3.nextFresh + fold1.1.length = (fold2.2.nextFresh + 1) + fold1.1.length
      have hAcc1Mono := preEqAccStep_foldl_nextFresh_mono b fold1.1 (base, st3)
      -- st3.nextFresh = fold2.2.nextFresh + 1
      have hSt3GtFold2 : fold2.2.nextFresh < st3.nextFresh := by
        simp only [hSt3Next, hAllocNext]; omega
      calc o.id < fold2.2.nextFresh := hOLt
           _ < st3.nextFresh := hSt3GtFold2
           _ ≤ accFold1.2.nextFresh := hAcc1Mono
    -- Get σ satisfaction for accFold2 NEW clauses (not in accFold1)
    have hSatAcc2New : ∀ c ∈ accFold2.2.clauses, c ∉ accFold1.2.clauses →
        SAT.Clause.eval σ c = true := by
      intro c hc hNotAcc1
      have hcInFinal : c ∈ (addPreEqPair_core b H0 H' st).clauses := by
        have h7 := addPreEqExpose_clauses_subset b H0 H' accFold2.1 accFold2.2
        exact h7 hc
      -- If c ∈ st.clauses, then c ∈ accFold1.2.clauses
      have hNotSt : c ∉ st.clauses := by
        intro hInSt
        have hInFold1 := preEqObligation_fold_clauses_subset b H0 H' (WId.allWorlds b)
            (init := ([], st)) rfl hInSt
        have hInFold2 := preEqObligation_fold_clauses_subset b H' H0 (WId.allWorlds b)
            (init := ([], fold1.2)) rfl hInFold1
        have hInAlloc : c ∈ allocRes.2.clauses := EncState.allocFresh_clauses_eq b fold2.2 ▸ hInFold2
        have hInSt3 := EncState.addClause_subset_clauses b allocRes.2
            [SAT.Lit.pos (FVar.toVar b base)] hInAlloc
        have hInAcc1 := preEqAcc_fold_clauses_subset b fold1.1 (init := (base, st3)) rfl hInSt3
        exact hNotAcc1 hInAcc1
      exact hSatNew c hcInFinal hNotSt
    -- Apply the SD lemma
    have hSD := foldl_preEqAccStep_newClauses_structural_determinism b fold2.1 fold2'.1
        (accFold1.1, accFold1.2) (accFold1'.1, accFold1'.2) offset st.nextFresh
        hAcc1Offset.symm hAcc1Mono hAcc1CurShift hAcc1CurGeTh hAcc1CurLtNext hThLeAcc1 hAcc1WF
        hOs2Len hOs2Shift hOs2GeTh hOs2LtAcc1 σ hSatAcc2New clause hInAcc2' hInAcc1'
    simp only at hSD
    have hThEq : st.nextFresh + offset = st'.nextFresh := by omega
    convert hSD using 2
    ext v
    cases v with
    | Fresh n => simp only [σ']; rw [hThEq]
    | _ => rfl
  else
    -- Clause is from addPreEqExpose
    -- Use addPreEqExpose_structural_determinism with accFold2.1, accFold2'.1
    -- Need: accFold2'.1.id = accFold2.1.id + offset
    -- Need: accFold2.1.id ≥ st.nextFresh
    -- Core monotonicity facts
    have hFold1Mono' : st.nextFresh ≤ fold1.2.nextFresh :=
      preEqObligationStep_foldl_mono b H0 H' (WId.allWorlds b) ([], st)
    have hFold2MonoFromFold1 : fold1.2.nextFresh ≤ fold2.2.nextFresh :=
      preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1.2)
    have hBaseId : base.id = fold2.2.nextFresh := by simp [base, allocRes, EncState.allocFresh]
    have hBase'Id : base'.id = fold2'.2.nextFresh := by simp [base', allocRes', EncState.allocFresh]
    have hAllocNext : allocRes.2.nextFresh = fold2.2.nextFresh + 1 :=
      EncState.allocFresh_nextFresh b fold2.2
    have hAlloc'Next : allocRes'.2.nextFresh = fold2'.2.nextFresh + 1 :=
      EncState.allocFresh_nextFresh b fold2'.2
    have hSt3Next : st3.nextFresh = allocRes.2.nextFresh := EncState.addClause_nextFresh b _ _
    have hSt3'Next : st3'.nextFresh = allocRes'.2.nextFresh := EncState.addClause_nextFresh b _ _
    -- st3 offset and mono
    have hSt3Offset : st3'.nextFresh - st3.nextFresh = offset := by
      simp only [hSt3Next, hSt3'Next, hAllocNext, hAlloc'Next]; omega
    have hSt3Mono : st3.nextFresh ≤ st3'.nextFresh := by
      simp only [hSt3Next, hSt3'Next, hAllocNext, hAlloc'Next]; omega
    -- base shift
    have hBaseShift : base'.id = base.id + offset := by simp only [hBaseId, hBase'Id]; omega
    -- fold1 lengths and shifts
    have hOsLen : fold1'.1.length = fold1.1.length :=
      preEqObligationStep_foldl_fst_length_eq b H0 H' (WId.allWorlds b) st st'
    have hOsShift : ∀ i (hi : i < fold1.1.length),
        (fold1'.1.get ⟨i, hOsLen ▸ hi⟩).id = (fold1.1.get ⟨i, hi⟩).id + offset :=
      preEqObligationStep_foldl_fst_shift b H0 H' (WId.allWorlds b) st st' offset hOffset hMono
    -- accFold1 offset and shift
    have hAcc1Offset : accFold1'.2.nextFresh - accFold1.2.nextFresh = offset :=
      preEqAccStep_foldl_offset b fold1.1 fold1'.1 (base, st3) (base', st3') offset
        hSt3Offset.symm hSt3Mono hOsLen hBaseShift
    have hAcc1CurShift : accFold1'.1.id = accFold1.1.id + offset :=
      preEqAccStep_foldl_fst_shift b fold1.1 fold1'.1 (base, st3) (base', st3') offset
        hSt3Offset.symm hSt3Mono hOsLen hOsShift hBaseShift
    have hAcc1Mono : accFold1.2.nextFresh ≤ accFold1'.2.nextFresh := by
      have h1 : accFold1.2.nextFresh = st3.nextFresh + fold1.1.length :=
        preEqAccStep_foldl_nextFresh_eq b fold1.1 (base, st3)
      have h1' : accFold1'.2.nextFresh = st3'.nextFresh + fold1'.1.length :=
        preEqAccStep_foldl_nextFresh_eq b fold1'.1 (base', st3')
      rw [hOsLen] at h1'; omega
    -- fold2 lengths and shifts
    have hFold1OffsetPres : fold1'.2.nextFresh - fold1.2.nextFresh = st'.nextFresh - st.nextFresh :=
      preEqObligationStep_foldl_offset_preserved b H0 H' (WId.allWorlds b) st st'
    have hFold1OffsetEq : offset = fold1'.2.nextFresh - fold1.2.nextFresh := by
      rw [hFold1OffsetPres]; exact hOffset
    have hOs2Len : fold2'.1.length = fold2.1.length :=
      preEqObligationStep_foldl_fst_length_eq b H' H0 (WId.allWorlds b) fold1.2 fold1'.2
    have hOs2Shift : ∀ i (hi : i < fold2.1.length),
        (fold2'.1.get ⟨i, hOs2Len ▸ hi⟩).id = (fold2.1.get ⟨i, hi⟩).id + offset :=
      preEqObligationStep_foldl_fst_shift b H' H0 (WId.allWorlds b) fold1.2 fold1'.2
        offset hFold1OffsetEq hFold1Mono
    -- accFold2' FVar shift: accFold2'.1.id = accFold2.1.id + offset
    have hAcc2CurShift : accFold2'.1.id = accFold2.1.id + offset :=
      preEqAccStep_foldl_fst_shift b fold2.1 fold2'.1 (accFold1.1, accFold1.2) (accFold1'.1, accFold1'.2)
        offset hAcc1Offset.symm hAcc1Mono hOs2Len hOs2Shift hAcc1CurShift
    -- accFold2' offset and mono
    have hAcc2Offset : accFold2'.2.nextFresh - accFold2.2.nextFresh = offset :=
      preEqAccStep_foldl_offset b fold2.1 fold2'.1 (accFold1.1, accFold1.2) (accFold1'.1, accFold1'.2)
        offset hAcc1Offset.symm hAcc1Mono hOs2Len hAcc1CurShift
    have hAcc2Mono : accFold2.2.nextFresh ≤ accFold2'.2.nextFresh := by
      have h1 : accFold2.2.nextFresh = accFold1.2.nextFresh + fold2.1.length :=
        preEqAccStep_foldl_nextFresh_eq b fold2.1 (accFold1.1, accFold1.2)
      have h1' : accFold2'.2.nextFresh = accFold1'.2.nextFresh + fold2'.1.length :=
        preEqAccStep_foldl_nextFresh_eq b fold2'.1 (accFold1'.1, accFold1'.2)
      rw [hOs2Len] at h1'; omega
    -- accFold2.1.id ≥ st.nextFresh
    have hAcc2CurGe : accFold2.1.id ≥ st.nextFresh := by
      have hBaseGeTh : base.id ≥ st.nextFresh := by simp only [hBaseId]; omega
      have hBaseLeNextFresh : st.nextFresh ≤ st3.nextFresh := by
        simp only [hSt3Next, hAllocNext]; omega
      have hAcc1CurGe : accFold1.1.id ≥ st.nextFresh :=
        preEqAccStep_foldl_fst_ge b fold1.1 (base, st3) st.nextFresh hBaseGeTh hBaseLeNextFresh
      have hAcc1NextFreshGe : st.nextFresh ≤ accFold1.2.nextFresh := by
        have hThSt3 : st.nextFresh ≤ st3.nextFresh := by simp only [hSt3Next, hAllocNext]; omega
        have hSt3Acc1 : st3.nextFresh ≤ accFold1.2.nextFresh :=
          preEqAccStep_foldl_nextFresh_mono b fold1.1 (base, st3)
        omega
      exact preEqAccStep_foldl_fst_ge b fold2.1 (accFold1.1, accFold1.2) st.nextFresh
        hAcc1CurGe hAcc1NextFreshGe
    -- σ satisfies the TWO new clauses from addPreEqExpose at st
    -- c1 = [neg (PreEq H0 H'), pos v] and c2 = [neg v, pos (PreEq H0 H')] where v = accFold2.1
    -- These are NEW (not in st.clauses) since they contain Fresh var accFold2.1.id ≥ st.nextFresh
    let c1 := [SAT.Lit.neg (Var.PreEq H0 H'), SAT.Lit.pos (FVar.toVar b accFold2.1)]
    let c2 := [SAT.Lit.neg (FVar.toVar b accFold2.1), SAT.Lit.pos (Var.PreEq H0 H')]
    have hC1InFinal : c1 ∈ (addPreEqPair_core b H0 H' st).clauses := by
      simp only [c1, addPreEqPair_core, addPreEqExpose, EncState.addClause]
      exact List.mem_cons_of_mem _ (List.Mem.head _)
    have hC2InFinal : c2 ∈ (addPreEqPair_core b H0 H' st).clauses := by
      simp only [c2, addPreEqPair_core, addPreEqExpose, EncState.addClause]
      exact List.Mem.head _
    -- c1 and c2 are not in st.clauses (contain Fresh var with id ≥ st.nextFresh)
    have hVIdGe : accFold2.1.id ≥ st.nextFresh := by
      have hFold1Mono' : st.nextFresh ≤ fold1.2.nextFresh :=
        preEqObligationStep_foldl_mono b H0 H' (WId.allWorlds b) ([], st)
      have hFold2MonoFromFold1 : fold1.2.nextFresh ≤ fold2.2.nextFresh :=
        preEqObligationStep_foldl_mono b H' H0 (WId.allWorlds b) ([], fold1.2)
      have hAcc1NextFreshGe : st.nextFresh ≤ accFold1.2.nextFresh := by
        have hThSt3 : st.nextFresh ≤ st3.nextFresh := by
          simp only [st3, allocRes, EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]
          omega
        have hSt3Acc1 : st3.nextFresh ≤ accFold1.2.nextFresh :=
          preEqAccStep_foldl_nextFresh_mono b fold1.1 (base, st3)
        omega
      have hAcc1CurGe : accFold1.1.id ≥ st.nextFresh := by
        have hBaseGeTh : base.id ≥ st.nextFresh := by
          simp only [base, allocRes, EncState.allocFresh]; omega
        have hBaseLeNextFresh : st.nextFresh ≤ st3.nextFresh := by
          simp only [st3, allocRes, EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]; omega
        have hOsGeTh : ∀ o ∈ fold1.1, o.id ≥ st.nextFresh :=
          preEqObligationStep_foldl_fvars_ge b H0 H' (WId.allWorlds b) ([], st) st.nextFresh
            (le_refl _) (fun _ h => by simp at h)
        exact preEqAccStep_foldl_fst_ge b fold1.1 (base, st3) st.nextFresh hBaseGeTh hBaseLeNextFresh
      exact preEqAccStep_foldl_fst_ge b fold2.1 (accFold1.1, accFold1.2) st.nextFresh
        hAcc1CurGe hAcc1NextFreshGe
    have hC1NotInSt : c1 ∉ st.clauses := by
      intro hIn
      have hWFst := hWF
      have hClauseBound := hWFst _ hIn
      unfold clauseFreshBelow at hClauseBound
      have hLitBound := hClauseBound (SAT.Lit.pos (FVar.toVar b accFold2.1))
          (List.mem_cons_of_mem _ (List.Mem.head _))
      simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar] at hLitBound
      exact Nat.not_lt.mpr hVIdGe hLitBound
    have hC2NotInSt : c2 ∉ st.clauses := by
      intro hIn
      have hWFst := hWF
      have hClauseBound := hWFst _ hIn
      unfold clauseFreshBelow at hClauseBound
      have hLitBound := hClauseBound (SAT.Lit.neg (FVar.toVar b accFold2.1)) (List.Mem.head _)
      simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar] at hLitBound
      exact Nat.not_lt.mpr hVIdGe hLitBound
    have hSatC1 : SAT.Clause.eval σ c1 = true := hSatNew c1 hC1InFinal hC1NotInSt
    have hSatC2 : SAT.Clause.eval σ c2 = true := hSatNew c2 hC2InFinal hC2NotInSt
    -- accFold2' = addPreEqPair_core output - addPreEqExpose
    -- hClauseMem : clause ∈ (addPreEqExpose b H0 H' accFold2'.1 accFold2'.2).clauses
    -- Since clause ∉ accFold2'.2.clauses (by the final else), it's new to addPreEqExpose
    have hInAcc2'Not : clause ∉ accFold2'.2.clauses := by
      intro h; exact absurd h hInAcc2'
    -- addPreEqExpose adds two clauses:
    -- c1 = [neg (PreEq H0 H'), pos v] and c2 = [neg v, pos (PreEq H0 H')]
    -- Since hInAcc2'Not : clause ∉ accFold2'.2.clauses, clause is one of these two
    unfold addPreEqExpose at hClauseMem
    simp only [EncState.addClause] at hClauseMem
    -- accFold2'.1.id is shifted from accFold2.1.id by offset
    -- But accFold2'.1.id might be < accFold2'.2.nextFresh ≤ st'.nextFresh? No:
    -- accFold2'.1.id = accFold2.1.id + offset
    -- accFold2'.2.nextFresh = accFold2.2.nextFresh + offset
    -- accFold2.1.id = accFold2.2.nextFresh - 1 (for non-empty fold2.1)
    -- So accFold2'.1.id = accFold2.2.nextFresh - 1 + offset = accFold2'.2.nextFresh - 1
    -- This means accFold2'.1.id < accFold2'.2.nextFresh
    -- But st'.nextFresh ≤ accFold2'.2.nextFresh, so accFold2'.1.id could be < st'.nextFresh
    -- Actually accFold2'.1.id = accFold2.1.id + offset
    -- And st.nextFresh ≤ accFold2.2.nextFresh, so accFold2.1.id >= st.nextFresh - 1
    -- Hmm, need to be more careful
    -- Key: σ'(Fresh n) when n = accFold2'.1.id:
    --   If n < st'.nextFresh: σ'(Fresh n) = σ(Fresh n)
    --   If n ≥ st'.nextFresh: σ'(Fresh n) = σ(Fresh(n - offset)) = σ(Fresh(accFold2.1.id))
    -- σ satisfies [neg v, pos PreEq] and [neg PreEq, pos v] at st (accFold2.2) with v = accFold2.1
    -- Case analysis on which clause we have
    have hV'Id : accFold2'.1.id = accFold2.1.id + offset := hAcc2CurShift
    have hV'Sub : accFold2'.1.id - offset = accFold2.1.id := by omega
    -- Check if accFold2'.1.id ≥ st'.nextFresh
    by_cases hV'Ge : accFold2'.1.id ≥ st'.nextFresh
    case pos =>
      -- accFold2'.1.id ≥ st'.nextFresh, so σ'(Fresh(accFold2'.1.id)) = σ(Fresh(accFold2.1.id))
      cases hClauseMem with
      | head =>
          -- clause = [neg accFold2'.1, pos (PreEq H0 H')]
          -- This corresponds to c2 = [neg v, pos PreEq]
          have hSatC : SAT.Clause.eval σ [SAT.Lit.neg (FVar.toVar b accFold2.1),
              SAT.Lit.pos (Var.PreEq H0 H')] = true := hSatC2
          rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
          rcases hLitMem with hL1 | hL2
          · -- lit = neg accFold2.1
            refine ⟨SAT.Lit.neg (FVar.toVar b accFold2'.1), List.Mem.head _, ?_⟩
            simp only [SAT.Lit.eval, FVar.toVar, σ', Nat.not_lt.mpr hV'Ge, ↓reduceIte, hV'Sub]
            subst hL1; exact hLitTrue
          · -- lit = pos (PreEq H0 H')
            refine ⟨SAT.Lit.pos (Var.PreEq H0 H'),
                List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
            simp only [SAT.Lit.eval, σ']
            subst hL2; exact hLitTrue
      | tail _ hTail =>
          cases hTail with
          | head =>
              -- clause = [neg (PreEq H0 H'), pos accFold2'.1]
              -- This corresponds to c1 = [neg PreEq, pos v]
              have hSatC : SAT.Clause.eval σ [SAT.Lit.neg (Var.PreEq H0 H'),
                  SAT.Lit.pos (FVar.toVar b accFold2.1)] = true := hSatC1
              rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC ⊢
              obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
              rcases hLitMem with hL1 | hL2
              · -- lit = neg (PreEq H0 H')
                refine ⟨SAT.Lit.neg (Var.PreEq H0 H'), List.Mem.head _, ?_⟩
                simp only [SAT.Lit.eval, σ']
                subst hL1; exact hLitTrue
              · -- lit = pos accFold2.1
                refine ⟨SAT.Lit.pos (FVar.toVar b accFold2'.1),
                    List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
                simp only [SAT.Lit.eval, FVar.toVar, σ', Nat.not_lt.mpr hV'Ge, ↓reduceIte, hV'Sub]
                subst hL2; exact hLitTrue
          | tail _ hTail2 => exact absurd hTail2 hInAcc2'Not
    case neg =>
      -- accFold2'.1.id < st'.nextFresh
      -- Then σ'(Fresh(accFold2'.1.id)) = σ(Fresh(accFold2'.1.id))
      -- But we need σ'(Fresh(accFold2'.1.id)) to relate to σ(Fresh(accFold2.1.id))
      -- Since accFold2'.1.id < st'.nextFresh and accFold2'.1.id = accFold2.1.id + offset
      -- We have accFold2.1.id + offset < st'.nextFresh = st.nextFresh + offset
      -- So accFold2.1.id < st.nextFresh
      -- But accFold2.1 was allocated during the acc fold starting from accFold1
      -- accFold2.1.id ≥ st3.nextFresh > fold2.2.nextFresh ≥ fold1.2.nextFresh ≥ st.nextFresh
      -- So accFold2.1.id ≥ st.nextFresh, contradiction with accFold2.1.id < st.nextFresh
      have hContra : accFold2.1.id < st.nextFresh := by
        have h := Nat.not_le.mp hV'Ge
        omega
      exact absurd hAcc2CurGe (Nat.not_le.mpr hContra)

/-- Structural determinism for NEW clauses from addPreEqPair.

For a NEW clause (not inherited from st') in addPreEqPair's output at st',
if σ satisfies all clauses from addPreEqPair at st, then σ' satisfies the new clause.

The key insight: Both encodings use identical time parameters (H0, H'),
so they produce structurally identical clauses with only Fresh var indices shifted.
The σ' transformation maps Fresh(n) in step' back to Fresh(n-offset) in step,
preserving satisfaction. -/
lemma addPreEqPair_newClauses_structural_determinism (b : Bounds S) (H0 H' : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : st.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (addPreEqPair b H0 H' st).clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true)
    -- Structural correspondence: non-Fresh clauses are the same in st and st'
    (hNonFreshCorr : ∀ c, (∀ lit ∈ c, match lit.getVar with | Var.Fresh _ => False | _ => True) →
                     (c ∈ st.clauses ↔ c ∈ st'.clauses))
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (addPreEqPair b H0 H' st').clauses)
    (hClauseNotInBase : clause ∉ st'.clauses) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < st'.nextFresh then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    SAT.Clause.eval σ' clause = true := by
  intro σ'
  classical
  by_cases hEq : H0 = H'
  · -- Reflexivity case: addPreEqPair adds [pos (PreEq H0 H')]
    subst hEq
    simp only [addPreEqPair, ↓reduceIte] at hClauseMem hSatNew
    simp only [EncState.addClause] at hClauseMem
    cases hClauseMem with
    | head =>
        simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, or_false, SAT.Lit.eval, σ']
        -- The reflexive PreEq clause [pos (PreEq H0 H0)] has no Fresh vars
        -- so it's NEW (not in st.clauses, since st is WF and this wasn't added yet)
        have hReflMem : [SAT.Lit.pos (Var.PreEq H0 H0)] ∈
            (EncState.addClause b (addPreEqPair_core b H0 H0 st) [SAT.Lit.pos (Var.PreEq H0 H0)]).clauses := by
          simp only [EncState.addClause, List.mem_cons, true_or]
        -- This clause has no Fresh vars, so use hNonFreshCorr to show it's not in st.clauses
        have hReflNew : [SAT.Lit.pos (Var.PreEq H0 H0)] ∉ st.clauses := by
          -- The reflexive PreEq clause has no Fresh vars
          have hNoFresh : ∀ lit ∈ [SAT.Lit.pos (Var.PreEq H0 H0)],
              match lit.getVar with | Var.Fresh _ => False | _ => True := by
            intro lit hLit
            simp only [List.mem_singleton] at hLit
            subst hLit
            -- The match on Var.PreEq evaluates to True (the _ => True case)
            trivial
          -- By hNonFreshCorr, this clause is in st.clauses iff in st'.clauses
          have hCorr := hNonFreshCorr [SAT.Lit.pos (Var.PreEq H0 H0)] hNoFresh
          -- hClauseNotInBase says clause ∉ st'.clauses (where clause = [pos (PreEq H0 H0)])
          -- So by hCorr, it's not in st.clauses either
          rw [hCorr]
          exact hClauseNotInBase
        have hSatRefl := hSatNew _ hReflMem hReflNew
        simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, or_false, SAT.Lit.eval] at hSatRefl
        exact hSatRefl
    | tail _ hTail =>
        -- Derive satisfaction for addPreEqPair_core clauses
        have hSatCore : ∀ c ∈ (addPreEqPair_core b H0 H0 st).clauses, c ∉ st.clauses →
            SAT.Clause.eval σ c = true := by
          intro c hc hNotSt
          have hMem : c ∈ (EncState.addClause b (addPreEqPair_core b H0 H0 st)
              [SAT.Lit.pos (Var.PreEq H0 H0)]).clauses := by
            simp only [EncState.addClause, List.mem_cons]; right; exact hc
          exact hSatNew c hMem hNotSt
        -- Apply addPreEqPair_core_newClauses_SD which now takes hSatNew form
        exact addPreEqPair_core_newClauses_SD b H0 H0 st st' offset hOffset hMono hWF σ
            hSatCore clause hTail hClauseNotInBase
  · -- Non-reflexivity case: addPreEqPair reduces to addPreEqPair_core directly
    simp only [addPreEqPair, hEq, ↓reduceIte] at hClauseMem hSatNew
    -- After simp, hClauseMem and hSatNew are already in the form expected by addPreEqPair_core_newClauses_SD
    exact addPreEqPair_core_newClauses_SD b H0 H' st st' offset hOffset hMono hWF σ
        hSatNew clause hClauseMem hClauseNotInBase

/-- The inline σ' used in SD lemmas equals shiftedAssignment. -/
private lemma inlineShiftedEq (b : Bounds S) (σ : SAT.Assignment (Var b))
    (threshold offset : Nat) :
    (fun v => match v with
      | Var.Fresh n => if n < threshold then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v) = shiftedAssignment b σ threshold offset := by
  funext v
  simp only [shiftedAssignment, Var.unshift]
  cases v <;> rfl

/-- Wrapper: addPreEqPair_core_newClauses_SD with shiftedAssignment return type. -/
lemma addPreEqPair_core_newClauses_SD' (b : Bounds S) (H0 H' : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : st.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (addPreEqPair_core b H0 H' st).clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (addPreEqPair_core b H0 H' st').clauses)
    (hClauseNotInBase : clause ∉ st'.clauses) :
    SAT.Clause.eval (shiftedAssignment b σ st'.nextFresh offset) clause = true := by
  have h := addPreEqPair_core_newClauses_SD b H0 H' st st' offset hOffset hMono hWF σ
      hSatNew clause hClauseMem hClauseNotInBase
  simp only [inlineShiftedEq] at h
  exact h

/-- Helper: clause evaluation agrees under shifted assignment threshold changes.
    If all Fresh vars in clause have index >= threshold2, then evaluating with
    threshold1 equals evaluating with threshold2 (when threshold1 <= threshold2). -/
private lemma clause_eval_shiftedAssignment_threshold_agree' (b : Bounds S)
    (σ : SAT.Assignment (Var b)) (threshold1 threshold2 offset : Nat)
    (hLe : threshold1 ≤ threshold2) (c : SAT.Clause (Var b))
    (hFreshGe : ∀ lit, lit ∈ c → ∀ n, SAT.Lit.getVar lit = Var.Fresh n → n ≥ threshold2) :
    SAT.Clause.eval (shiftedAssignment b σ threshold1 offset) c =
    SAT.Clause.eval (shiftedAssignment b σ threshold2 offset) c := by
  simp only [SAT.Clause.eval_eq_any]
  induction c with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.any_cons]
    have hHdFresh : ∀ n, SAT.Lit.getVar hd = Var.Fresh n → n ≥ threshold2 :=
      hFreshGe hd List.mem_cons_self
    -- Show lit eval agrees
    have hLitEq : SAT.Lit.eval (shiftedAssignment b σ threshold1 offset) hd =
                  SAT.Lit.eval (shiftedAssignment b σ threshold2 offset) hd := by
      simp only [SAT.Lit.eval]
      cases hd with
      | pos v =>
        cases v with
        | Fresh n =>
          have hGe := hHdFresh n (by simp [SAT.Lit.getVar])
          exact shiftedAssignment_agree_ge b σ threshold1 threshold2 offset hLe n hGe
        | _ => rfl
      | neg v =>
        cases v with
        | Fresh n =>
          have hGe := hHdFresh n (by simp [SAT.Lit.getVar])
          exact congrArg (! ·) (shiftedAssignment_agree_ge b σ threshold1 threshold2 offset hLe n hGe)
        | _ => rfl
    rw [hLitEq]
    have hTlFresh : ∀ l, l ∈ tl → ∀ n, SAT.Lit.getVar l = Var.Fresh n → n ≥ threshold2 :=
      fun l hl => hFreshGe l (List.mem_cons_of_mem hd hl)
    rw [ih hTlFresh]

/-- Fresh vars in NEW clauses from fold of addPreEqPair have index >= input nextFresh. -/
private lemma foldPreEqPair_newClause_fresh_ge (b : Bounds S) (ti : b.times)
    (L : List b.times) (st : EncState b)
    (c : SAT.Clause (Var b))
    (hc : c ∈ (L.foldl (fun acc H' => addPreEqPair b ti H' acc) st).clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ st.nextFresh := by
  induction L generalizing st with
  | nil =>
    simp only [List.foldl_nil] at hc
    exact absurd hc hcNotOld
  | cons H' rest ih =>
    simp only [List.foldl_cons] at hc
    let acc := addPreEqPair b ti H' st
    by_cases hcInAcc : c ∈ acc.clauses
    · -- Clause came from this addPreEqPair step
      by_cases hcInSt : c ∈ st.clauses
      · exact absurd hcInSt hcNotOld
      · -- New clause from addPreEqPair
        exact addPreEqPair_newClause_fresh_ge b ti H' st c hcInAcc hcInSt lit hLit n hFresh
    · -- Clause came from later in fold
      have hGe := ih acc hc hcInAcc
      have hMono := addPreEqPair_nextFresh_mono b ti H' st
      exact Nat.le_trans hMono hGe

/-- Helper: structural determinism for fold of addPreEqPair over an explicit list. -/
private lemma foldPreEqPair_structural_determinism (b : Bounds S) (ti : b.times)
    (L : List b.times) (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : st.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (L.foldl (fun acc H' => addPreEqPair b ti H' acc) st).clauses,
               c ∉ st.clauses → SAT.Clause.eval σ c = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (L.foldl (fun acc H' => addPreEqPair b ti H' acc) st').clauses)
    (hClauseNotInBase : clause ∉ st'.clauses)
    (hHasFresh : ∃ lit ∈ clause, ∃ n, SAT.Lit.getVar lit = Var.Fresh n) :
    SAT.Clause.eval (shiftedAssignment b σ st'.nextFresh offset) clause = true := by
  classical
  induction L generalizing st st' with
  | nil =>
      -- Empty fold: clause ∈ st'.clauses contradicts hClauseNotInBase
      exact absurd hClauseMem hClauseNotInBase
  | cons H' rest ih =>
      simp only [List.foldl_cons] at hClauseMem hSatNew
      -- clause ∈ (rest.foldl ... (addPreEqPair b ti H' st')).clauses
      let acc := addPreEqPair b ti H' st
      let acc' := addPreEqPair b ti H' st'
      by_cases hInAcc' : clause ∈ acc'.clauses
      · -- Clause came from this addPreEqPair step
        by_cases hInSt' : clause ∈ st'.clauses
        · exact absurd hInSt' hClauseNotInBase
        · -- New clause from addPreEqPair at st'
          -- Since clause has Fresh vars, it must be from addPreEqPair_core
          -- (the reflexivity clause [pos (PreEq ti ti)] has no Fresh vars)
          by_cases hEq : ti = H'
          · -- Reflexive case: addPreEqPair = addPreEqPair_core + addClause
            subst hEq
            simp only [acc', addPreEqPair, ↓reduceIte, EncState.addClause, List.mem_cons] at hInAcc'
            cases hInAcc' with
            | inl hRefl =>
                -- clause = [pos (PreEq ti ti)], but this has no Fresh vars
                exfalso
                obtain ⟨lit, hLit, n, hFreshLit⟩ := hHasFresh
                rw [hRefl] at hLit
                simp only [List.mem_singleton] at hLit
                subst hLit
                simp only [SAT.Lit.getVar] at hFreshLit
                exact Var.noConfusion hFreshLit
            | inr hCore =>
                -- clause ∈ addPreEqPair_core clauses
                have hSatCore : ∀ c ∈ (addPreEqPair_core b ti ti st).clauses, c ∉ st.clauses →
                    SAT.Clause.eval σ c = true := by
                  intro c hc hNotSt
                  apply hSatNew
                  · -- c ∈ full fold result
                    have hInAcc : c ∈ acc.clauses := by
                      simp only [acc, addPreEqPair, ↓reduceIte, EncState.addClause, List.mem_cons]
                      right; exact hc
                    exact foldl_subset_state (fun acc'' H'' => addPreEqPair b ti H'' acc'')
                        (fun acc'' H'' => addPreEqPair_clauses_subset b ti H'' acc'')
                        rest acc hInAcc
                  · exact hNotSt
                -- Apply addPreEqPair_core_newClauses_SD'
                exact addPreEqPair_core_newClauses_SD' b ti ti st st' offset hOffset hMono hWF σ
                    hSatCore clause hCore hInSt'
          · -- Non-reflexive case: addPreEqPair = addPreEqPair_core directly
            have hCoreEq : acc' = addPreEqPair_core b ti H' st' := by
              simp only [acc', addPreEqPair, hEq, ↓reduceIte]
            have hCoreEq2 : acc = addPreEqPair_core b ti H' st := by
              simp only [acc, addPreEqPair, hEq, ↓reduceIte]
            rw [hCoreEq] at hInAcc'
            have hSatCore : ∀ c ∈ (addPreEqPair_core b ti H' st).clauses, c ∉ st.clauses →
                SAT.Clause.eval σ c = true := by
              intro c hc hNotSt
              apply hSatNew
              · have hInAcc : c ∈ acc.clauses := by rw [hCoreEq2]; exact hc
                exact foldl_subset_state (fun acc'' H'' => addPreEqPair b ti H'' acc'')
                    (fun acc'' H'' => addPreEqPair_clauses_subset b ti H'' acc'')
                    rest acc hInAcc
              · exact hNotSt
            exact addPreEqPair_core_newClauses_SD' b ti H' st st' offset hOffset hMono hWF σ
                hSatCore clause hInAcc' hInSt'
      · -- Clause came from deeper in the fold (not from first addPreEqPair)
        -- Apply IH with accumulated states
        have hOffsetAdd : st'.nextFresh = st.nextFresh + offset := by omega
        have hOffsetEq := addPreEqPair_offset b ti H' st st' offset hOffsetAdd
        -- hOffsetEq : acc'.nextFresh = acc.nextFresh + offset
        have hOffset' : offset = acc'.nextFresh - acc.nextFresh := by
          simp only [acc, acc'] at hOffsetEq ⊢
          omega
        have hMono' : acc.nextFresh ≤ acc'.nextFresh := by
          simp only [acc, acc'] at hOffsetEq ⊢
          omega
        have hWF' : acc.WellFormed := addPreEqPair_wf b ti H' st hWF
        have hSat' : ∀ c ∈ (rest.foldl (fun acc'' H'' => addPreEqPair b ti H'' acc'') acc).clauses,
            c ∉ acc.clauses → SAT.Clause.eval σ c = true := by
          intro c hc hNotAcc
          apply hSatNew
          · exact hc
          · intro hInSt
            exact hNotAcc (addPreEqPair_clauses_subset b ti H' st hInSt)
        have hClauseNotInAcc' : clause ∉ acc'.clauses := hInAcc'
        -- IH gives us evaluation at threshold acc'.nextFresh
        have hIH := ih acc acc' hOffset' hMono' hWF' hSat' hClauseMem hClauseNotInAcc'
        -- We need evaluation at threshold st'.nextFresh
        -- Use clause_eval_shiftedAssignment_threshold_agree:
        -- Since clause is new from rest fold at acc', all Fresh vars have index >= acc'.nextFresh
        -- And st'.nextFresh <= acc'.nextFresh by monotonicity
        have hThresholdLe : st'.nextFresh ≤ acc'.nextFresh := by
          have h := addPreEqPair_nextFresh_mono b ti H' st'
          simp only [acc']
          exact h
        -- All Fresh vars in clause have index >= acc'.nextFresh
        have hFreshGe : ∀ lit, lit ∈ clause → ∀ n, SAT.Lit.getVar lit = Var.Fresh n →
            n ≥ acc'.nextFresh := by
          intro lit hLit n hFreshLit
          -- clause is new to rest fold at acc'
          have hFoldFresh := foldPreEqPair_newClause_fresh_ge b ti rest acc' clause
            hClauseMem hClauseNotInAcc' lit hLit n hFreshLit
          exact hFoldFresh
        have hEvalEq := clause_eval_shiftedAssignment_threshold_agree' b σ
          st'.nextFresh acc'.nextFresh offset hThresholdLe clause hFreshGe
        rw [hEvalEq]
        exact hIH

/-- Structural determinism for addPreEqFrom when the clause has Fresh variables.

Since the clause has Fresh vars, it must have come from some addPreEqPair_core step
(the only source of Fresh clauses in addPreEqFrom). We trace through the fold
and apply addPreEqPair_core_newClauses_SD at the appropriate step. -/
lemma addPreEqFrom_structural_determinism (b : Bounds S) (ti : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : st.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (addPreEqFrom b ti st).clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (addPreEqFrom b ti st').clauses)
    (hClauseNotInBase : clause ∉ st'.clauses)
    (hHasFresh : ∃ lit ∈ clause, ∃ n, SAT.Lit.getVar lit = Var.Fresh n) :
    SAT.Clause.eval (shiftedAssignment b σ st'.nextFresh offset) clause = true := by
  simp only [addPreEqFrom] at hClauseMem hSatNew
  exact foldPreEqPair_structural_determinism b ti (Bounds.timesL b) st st' offset
      hOffset hMono hWF σ hSatNew clause hClauseMem hClauseNotInBase hHasFresh

end Encoding
