import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.ClausePreservation
import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly
import ModalDistribution.Logic.SATEncoding.PreEqSoundness
import ModalDistribution.Logic.SATEncoding.PreEqCompleteness

namespace Encoding

open ModalDistribution Logic

variable {S : Signature}
variable [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value]

/-! ### Guard clauses used by the predicate encoding -/

def guardBackward (b : Bounds S) (w : WId b) (H' : b.times) (k : b.predIx) :
    SAT.Clause (Var b) :=
  [ SAT.Lit.neg (Var.PreEq w.ti H')
  , SAT.Lit.neg (Var.Pred w.p H' k)
  , SAT.Lit.pos (Var.Pred w.p w.ti k) ]

def guardForward (b : Bounds S) (w : WId b) (H' : b.times) (k : b.predIx) :
    SAT.Clause (Var b) :=
  [ SAT.Lit.neg (Var.PreEq w.ti H')
  , SAT.Lit.neg (Var.Pred w.p w.ti k)
  , SAT.Lit.pos (Var.Pred w.p H' k) ]

def guardStep (b : Bounds S) (idxs : List b.predIx)
    (w : WId b) (H' : b.times) (st : EncState b) : EncState b :=
  idxs.foldl (fun stAcc k =>
    let stAcc := EncState.addClause b stAcc (guardBackward b w H' k)
    EncState.addClause b stAcc (guardForward b w H' k)) st

def predicateFold (b : Bounds S) (idxs : List b.predIx)
    (w : WId b) (st : EncState b) : EncState b :=
  (Bounds.timesL b).foldl (fun stAcc H' => guardStep b idxs w H' stAcc) st

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
lemma guardStep_clauses_subset
    (b : Bounds S) (idxs : List b.predIx)
    (w : WId b) (H' : b.times) (st : EncState b) :
    st.clauses ⊆ (guardStep b idxs w H' st).clauses := by
  -- Proof strategy (Plan §3):
  -- 1. Induct on `idxs`, treating each step as two successive calls to `EncState.addClause`.
  -- 2. Use `addClause_preserves` to extend the subset relation across each insertion.
  -- 3. Chain the inclusions via the inductive hypothesis.
  let step :
      EncState b → b.predIx → EncState b :=
    fun stAcc a =>
      EncState.addClause b
        (EncState.addClause b stAcc (guardBackward b w H' a))
        (guardForward b w H' a)
  have hStep :
      ∀ stAcc (a : b.predIx),
        stAcc.clauses ⊆ (step stAcc a).clauses := by
    intro stAcc a clause hClause
    have hClause' :=
      (addClause_preserves (b := b)
        (st := stAcc)
        (clause := guardBackward b w H' a)) hClause
    exact
      (addClause_preserves (b := b)
        (st := EncState.addClause b stAcc (guardBackward b w H' a))
        (clause := guardForward b w H' a)) hClause'
  have hSubset :=
    foldl_step_clauses_subset
      (b := b)
      (xs := idxs)
      (st := st)
      (f := step)
      (hStep := hStep)
  simpa [guardStep, step] using hSubset

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
lemma predicateFold_clauses_subset
    (b : Bounds S) (idxs : List b.predIx)
    (w : WId b) (st : EncState b) :
    st.clauses ⊆ (predicateFold b idxs w st).clauses := by
  let step :
      EncState b → b.times → EncState b :=
    fun stAcc H' => guardStep b idxs w H' stAcc
  have hStep :
      ∀ stAcc (H' : b.times),
        stAcc.clauses ⊆ (step stAcc H').clauses := by
    intro stAcc H'
    simpa [step] using
      (guardStep_clauses_subset
        (b := b) (idxs := idxs) (w := w) (H' := H') (st := stAcc))
  have hSubset :=
    foldl_step_clauses_subset
      (b := b)
      (xs := Bounds.timesL b)
      (st := st)
      (f := step)
      (hStep := hStep)
  simpa [predicateFold, step] using hSubset


lemma predicate_clause_mem
    (b : Bounds S) (atom : PredicateAtom S) (w : WId b)
    (st : EncState b) (clause : SAT.Clause (Var b))
    (hClause :
      clause ∈
        (mkBigOrIff b
          ((predIxList b ⟨atom.sym, atom.args⟩).map
            (fun k => Var.Pred w.p w.ti k))
          st).2.clauses) :
    clause ∈ (encodeFormula b (.predicate atom) w st).2.clauses := by
  set pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
  set idxs := predIxList b pred
  set literals := idxs.map (fun k => Var.Pred w.p w.ti k)
  cases hMk : mkBigOrIff b literals st with
  | mk u st₁ =>
      have hClause₁ : clause ∈ st₁.clauses := by
        simpa [literals, hMk] using hClause
      have hMk_snd : (mkBigOrIff b literals st).2 = st₁ := by
        simpa using congrArg Prod.snd hMk
      by_cases hEmpty : idxs = []
      · have hMk_empty : (mkBigOrIff b [] st).2 = st₁ := by
          simpa [idxs, literals, hEmpty] using hMk_snd
        have hEncode :
            (encodeFormula b (.predicate atom) w st).2 = st₁ := by
          simp [encodeFormula, pred, idxs, hEmpty, hMk_empty]
        simpa [hEncode]
      · have hSubset₂ :
            clause ∈ (addPreEqFrom b w.ti st₁).clauses :=
          (addPreEqFrom_clauses_subset (b := b) (H0 := w.ti) (st := st₁)) hClause₁
        let st₂ := addPreEqFrom b w.ti st₁
        let st₃ := addPreEqReflAll b st₂
        have hSubset₃ :
            clause ∈ st₃.clauses :=
          (addPreEqReflAll_clauses_subset (b := b) (st := st₂)) hSubset₂
        have hSubset₄ :
            clause ∈ (predicateFold b idxs w st₃).clauses :=
          (predicateFold_clauses_subset
            (b := b) (idxs := idxs) (w := w) (st := st₃)) hSubset₃
        have hEncodeState :
            (encodeFormula b (.predicate atom) w st).2 =
              predicateFold b idxs w st₃ := by
          simp [encodeFormula, pred, idxs, literals, hMk, hEmpty,
            st₂, st₃, predicateFold, guardStep, guardBackward, guardForward]
        have hEncodeClauses :
            (encodeFormula b (.predicate atom) w st).2.clauses =
              (predicateFold b idxs w st₃).clauses :=
          congrArg EncState.clauses hEncodeState
        have hFinal :
            clause ∈ (encodeFormula b (.predicate atom) w st).2.clauses := by
          simpa [hEncodeClauses] using hSubset₄
        exact hFinal

lemma control_true_of_predVar
    (b : Bounds S) (atom : PredicateAtom S) (w : WId b)
    (st : EncState b) (σ : SAT.Assignment (Var b))
    {k : b.predIx}
    (hk : k ∈ predIxList b ⟨atom.sym, atom.args⟩)
    (hPred : σ (Var.Pred w.p w.ti k) = true)
    (hClauses :
      (encodeFormula b (.predicate atom) w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    σ (FVar.toVar b (encodeFormula b (.predicate atom) w st).1) = true := by
  -- Proof strategy (Plan §3):
  -- 1. Locate the clause `[¬Pred(w.p,w.ti,k), u]` via `predicate_clause_mem`.
  -- 2. Combine `hClauses` with `List.all_eq_true` to justify that the
  --    clause evaluates to true under σ.
  -- 3. Evaluate the clause using `hPred`, forcing the literal on `u` to be true.
  classical
  set pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
  set idxs := predIxList b pred
  have hkIdxs : k ∈ idxs := by
    simpa [idxs] using hk
  set literals := idxs.map (fun k => Var.Pred w.p w.ti k)
  cases hMk : mkBigOrIff b literals st with
  | mk u st₁ =>
      by_cases hEmpty : idxs = []
      · have : False := by
          simp [idxs, hEmpty] at hk
        exact this.elim
      · let clause :=
          [ SAT.Lit.neg (Var.Pred w.p w.ti k)
          , SAT.Lit.pos (FVar.toVar b u) ]
        have hkLit :
            Var.Pred w.p w.ti k ∈ literals := by
          simp [literals, idxs, hkIdxs]
        have hClause_mk :
            clause ∈ st₁.clauses := by
          have hMem :=
            mkBigOrIff_unit_clause_mem
              (b := b) (vs := literals) (st := st)
              (v := Var.Pred w.p w.ti k) hkLit
          simpa [clause, hMk] using hMem
        let st₂ := addPreEqFrom b w.ti st₁
        let st₃ :=
          (Bounds.timesL b).foldl
            (fun stCur H' =>
              idxs.foldl (fun stAcc k =>
                let backward :=
                  [ SAT.Lit.neg (Var.PreEq w.ti H')
                  , SAT.Lit.neg (Var.Pred w.p H' k)
                  , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
                let forward :=
                  [ SAT.Lit.neg (Var.PreEq w.ti H')
                  , SAT.Lit.neg (Var.Pred w.p w.ti k)
                  , SAT.Lit.pos (Var.Pred w.p H' k) ]
                let stAcc := EncState.addClause b stAcc backward
                EncState.addClause b stAcc forward) stCur)
            st₂
        have hClause_final :
            clause ∈ (encodeFormula b (.predicate atom) w st).2.clauses := by
          have hClause' :
              clause ∈
                (mkBigOrIff b literals st).2.clauses := by
            simpa [clause, hMk] using hClause_mk
          simpa [encodeFormula, pred, idxs, literals, hMk, hEmpty, st₂, st₃]
            using
              (predicate_clause_mem
                (b := b) (atom := atom) (w := w)
                (st := st) (clause := clause)
                (hClause := hClause'))
        have hAll := List.all_eq_true.1 hClauses
        have hClauseEval :
            SAT.Clause.eval σ clause = true :=
          hAll _ hClause_final
        have hFVar :
            σ (FVar.toVar b u) = true := by
          simpa [clause, SAT.Clause.eval, SAT.Lit.eval, hPred]
            using hClauseEval
        have hEncodeVar :
            (encodeFormula b (.predicate atom) w st).1 = u := by
          simp [encodeFormula, pred, idxs, literals, hMk, hEmpty]
        simpa [hEncodeVar] using hFVar

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
lemma preEq_refl_unit_mem (b : Bounds S) (t : b.times) (st : EncState b) :
    [SAT.Lit.pos (Var.PreEq t t)] ∈ (addPreEqPair b t t st).clauses := by
  classical
  -- addPreEqPair adds the reflexivity unit clause when H0 = H'
  unfold addPreEqPair
  simp [EncState.addClause]

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
lemma addPreEqFrom_refl_unit_mem (b : Bounds S) (t : b.times) (st : EncState b) :
    [SAT.Lit.pos (Var.PreEq t t)] ∈ (addPreEqFrom b t st).clauses := by
  classical
  -- addPreEqFrom folds over all times, calling addPreEqPair b t H' for each H'
  -- When H' = t, it adds the unit clause via addPreEqPair b t t
  unfold addPreEqFrom
  have hMem : t ∈ Bounds.timesL b := by simp [Bounds.timesL]
  -- Use list membership to split around t
  obtain ⟨before, after, hSplit⟩ := List.mem_iff_append.mp hMem
  rw [hSplit]
  simp only [List.foldl_append, List.foldl_cons]
  -- After folding over `before`, we get some state stBefore
  let stBefore := before.foldl (fun acc H' => addPreEqPair b t H' acc) st
  -- Then we apply addPreEqPair b t t, which adds the unit clause
  have hUnit : [SAT.Lit.pos (Var.PreEq t t)] ∈ (addPreEqPair b t t stBefore).clauses :=
    preEq_refl_unit_mem b t stBefore
  -- This clause is preserved through folding over `after`
  have hStep : ∀ stAcc (H' : b.times),
      stAcc.clauses ⊆ (addPreEqPair b t H' stAcc).clauses :=
    fun stAcc H' => addPreEqPair_clauses_subset b t H' stAcc
  have hSubset := foldl_step_clauses_subset b after (addPreEqPair b t t stBefore)
    (fun acc H' => addPreEqPair b t H' acc) hStep
  exact hSubset hUnit

lemma preEq_self_true
    (b : Bounds S) (atom : PredicateAtom S) (w : WId b)
    (st : EncState b) (σ : SAT.Assignment (Var b))
    (hNonEmpty : predIxList b ⟨atom.sym, atom.args⟩ ≠ [])
    (hClauses :
      (encodeFormula b (.predicate atom) w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    σ (Var.PreEq w.ti w.ti) = true := by
  -- Proof strategy (Plan §2):
  -- The predicate encoding calls addPreEqFrom b w.ti st1, which calls addPreEqPair b w.ti w.ti.
  -- That adds the unit clause [PreEq(w.ti, w.ti)], which we extract and evaluate.
  -- Note: We require hNonEmpty because when idxs = [], no PreEq clauses are added.
  classical
  set pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
  set idxs := predIxList b pred
  set literals := idxs.map (fun k => Var.Pred w.p w.ti k)
  cases hMk : mkBigOrIff b literals st with
  | mk u st₁ =>
      -- Non-empty case (guaranteed by hNonEmpty)
      let st₂ := addPreEqFrom b w.ti st₁
      let st₃ := addPreEqReflAll b st₂
      -- Get the unit clause from addPreEqFrom
      have hUnitInSt2 : [SAT.Lit.pos (Var.PreEq w.ti w.ti)] ∈ st₂.clauses :=
        addPreEqFrom_refl_unit_mem b w.ti st₁
      have hUnitInSt3 :
          [SAT.Lit.pos (Var.PreEq w.ti w.ti)] ∈ st₃.clauses :=
        (addPreEqReflAll_clauses_subset (b := b) (st := st₂)) hUnitInSt2
      -- Show it's preserved through predicateFold to final encoding
      have hUnitInFinal : [SAT.Lit.pos (Var.PreEq w.ti w.ti)] ∈
          (encodeFormula b (.predicate atom) w st).2.clauses := by
        have h1 :
            st₃.clauses ⊆ (predicateFold b idxs w st₃).clauses :=
          predicateFold_clauses_subset b idxs w st₃
        have : [SAT.Lit.pos (Var.PreEq w.ti w.ti)] ∈
            (predicateFold b idxs w st₃).clauses :=
          h1 hUnitInSt3
        have h2 : (predicateFold b idxs w st₃).clauses =
            (encodeFormula b (.predicate atom) w st).2.clauses := by
          unfold encodeFormula
          simp only [pred, idxs, literals, hMk, st₂, st₃]
          split_ifs with hEmpty
          · exact absurd hEmpty hNonEmpty
          · rfl
        simpa [h2]
      -- Evaluate the unit clause under hClauses
      have hEval : SAT.Clause.eval σ [SAT.Lit.pos (Var.PreEq w.ti w.ti)] = true :=
        (List.all_eq_true.mp hClauses) _ hUnitInFinal
      -- Extract the result
      simpa [SAT.Clause.eval, SAT.Lit.eval] using hEval

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Membership lemma: guardBackward clause is added to guardStep state -/
lemma guardBackward_in_guardStep
    (b : Bounds S) (idxs : List b.predIx) (w : WId b)
    (H' : b.times) (k : b.predIx) (st : EncState b)
    (hk : k ∈ idxs) :
    guardBackward b w H' k ∈ (guardStep b idxs w H' st).clauses := by
  unfold guardStep
  -- Split the list around k
  obtain ⟨before, after, hSplit⟩ := List.mem_iff_append.mp hk
  rw [hSplit, List.foldl_append, List.foldl_cons]
  -- After folding over `before`, we add guardBackward for k
  let f := fun stAcc (k' : b.predIx) =>
    EncState.addClause b
      (EncState.addClause b stAcc (guardBackward b w H' k'))
      (guardForward b w H' k')
  let stBefore := before.foldl f st
  -- The clause is added when processing k
  have hInStep : guardBackward b w H' k ∈ (f stBefore k).clauses := by
    simp only [f, EncState.addClause, List.mem_cons, true_or, or_true]
  -- It's preserved through the rest of the fold
  have hStep : ∀ stAcc (a : b.predIx), stAcc.clauses ⊆ (f stAcc a).clauses := by
    intro stAcc a clause hClause
    simp only [f, EncState.addClause, List.mem_cons]
    right; right; exact hClause
  exact foldl_step_clauses_subset b after (f stBefore k) f hStep hInStep

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- guardStep is monotone: st1 ⊆ st2 implies guardStep st1 ⊆ guardStep st2 -/
lemma guardStep_mono
    (b : Bounds S) (idxs : List b.predIx) (w : WId b)
    (H' : b.times) (st1 st2 : EncState b)
    (hSub : st1.clauses ⊆ st2.clauses) :
    (guardStep b idxs w H' st1).clauses ⊆ (guardStep b idxs w H' st2).clauses := by
  unfold guardStep
  let f := fun stAcc (k' : b.predIx) =>
    EncState.addClause b
      (EncState.addClause b stAcc (guardBackward b w H' k'))
      (guardForward b w H' k')
  -- We need to show the fold on st1 is subset of fold on st2
  -- Since f only adds clauses, and st1 ⊆ st2, this follows
  revert st1 st2 hSub
  induction idxs with
  | nil =>
      intro st1 st2 hSub
      simp only [List.foldl]
      exact hSub
  | cons k ks ih =>
      intro st1 st2 hSub
      simp only [List.foldl]
      apply ih
      -- Show f st1 k ⊆ f st2 k
      intro clause hClause
      simp only [f, EncState.addClause, List.mem_cons] at hClause ⊢
      rcases hClause with hNew | hOld
      · left; exact hNew
      · right
        rcases hOld with hNew' | hOld'
        · left; exact hNew'
        · right; exact hSub hOld'

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Membership lemma: guardStep H' clauses are in predicateFold -/
lemma guardStep_mem_predicateFold
    (b : Bounds S) (idxs : List b.predIx) (w : WId b)
    (H' : b.times) (st : EncState b) (clause : SAT.Clause (Var b))
    (hMem : clause ∈ (guardStep b idxs w H' st).clauses) :
    clause ∈ (predicateFold b idxs w st).clauses := by
  unfold predicateFold
  have hH'Mem : H' ∈ Bounds.timesL b := by simp [Bounds.timesL]
  -- Split the list around H'
  obtain ⟨before, after, hSplit⟩ := List.mem_iff_append.mp hH'Mem
  rw [hSplit, List.foldl_append, List.foldl_cons]
  let f := fun stAcc (t : b.times) => guardStep b idxs w t stAcc
  let stBefore := before.foldl f st
  -- The clause is in (guardStep H' stBefore) after folding before
  have hSubsetBefore : st.clauses ⊆ stBefore.clauses := by
    have hStep : ∀ stAcc (t : b.times), stAcc.clauses ⊆ (f stAcc t).clauses := by
      intro stAcc t; exact guardStep_clauses_subset b idxs w t stAcc
    exact foldl_step_clauses_subset b before st f hStep
  have hInGuardStep : clause ∈ (f stBefore H').clauses := by
    exact guardStep_mono b idxs w H' st stBefore hSubsetBefore hMem
  have hStep : ∀ stAcc (t : b.times), stAcc.clauses ⊆ (f stAcc t).clauses := by
    intro stAcc t; exact guardStep_clauses_subset b idxs w t stAcc
  exact foldl_step_clauses_subset b after (f stBefore H') f hStep hInGuardStep

/-- Membership of backward guard clause in predicate encoding -/
lemma guardBackward_mem
    (b : Bounds S) (atom : PredicateAtom S) (w : WId b)
    (st : EncState b) (H' : b.times) (k : b.predIx)
    (hk : k ∈ predIxList b ⟨atom.sym, atom.args⟩) :
    guardBackward b w H' k ∈
      (encodeFormula b (.predicate atom) w st).2.clauses := by
  classical
  set pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
  set idxs := predIxList b pred
  have hkIdxs : k ∈ idxs := by simpa [idxs] using hk
  set literals := idxs.map (fun k => Var.Pred w.p w.ti k)
  cases hMk : mkBigOrIff b literals st with
  | mk u st₁ =>
      by_cases hEmpty : idxs = []
      · exfalso; simp [idxs, hEmpty] at hk
      · let st₂ := addPreEqFrom b w.ti st₁
        let st₃ := addPreEqReflAll b st₂
        -- The backward guard is added in predicateFold
        have hEncode :
            (encodeFormula b (.predicate atom) w st).2 =
              predicateFold b idxs w st₃ := by
          unfold encodeFormula
          simp only [pred, idxs, literals, hMk, hEmpty, ↓reduceDIte]
          rfl
        rw [hEncode]
        -- Use the lemmas to show membership
        have hInGuardStep := guardBackward_in_guardStep b idxs w H' k st₃ hkIdxs
        exact guardStep_mem_predicateFold b idxs w H' st₃ _ hInGuardStep

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Evaluation of backward guard: if PreEq(w.ti, H') and Pred(w.p, H', k) are true,
    then Pred(w.p, w.ti, k) must be true for the clause to be satisfied. -/
lemma guardBackward_eval
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    {w : WId b} {H' : b.times} {k : b.predIx}
    (hClause : SAT.Clause.eval σ (guardBackward b w H' k) = true)
    (hPreEq : σ (Var.PreEq w.ti H') = true)
    (hPred : σ (Var.Pred w.p H' k) = true) :
    σ (Var.Pred w.p w.ti k) = true := by
  simp [guardBackward, SAT.Clause.eval, SAT.Lit.eval, hPreEq, hPred] at hClause
  exact hClause

/-- Transfer predicate from H' to w.ti using backward guard and PreEq -/
lemma local_pred_true_of_guard
    (b : Bounds S) (atom : PredicateAtom S) (w : WId b)
    (st : EncState b) (σ : SAT.Assignment (Var b))
    (H' : b.times) (k : b.predIx)
    (hk : k ∈ predIxList b ⟨atom.sym, atom.args⟩)
    (hPreEqWH : σ (Var.PreEq w.ti H') = true)
    (hPred : σ (Var.Pred w.p H' k) = true)
    (hClauses :
      (encodeFormula b (.predicate atom) w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    σ (Var.Pred w.p w.ti k) = true := by
  have hClauseMem :
      guardBackward b w H' k ∈
        (encodeFormula b (.predicate atom) w st).2.clauses :=
    guardBackward_mem b atom w st H' k hk
  have hClauseEval :
      SAT.Clause.eval σ (guardBackward b w H' k) = true :=
    (List.all_eq_true.mp hClauses) _ hClauseMem
  exact guardBackward_eval b σ hClauseEval hPreEqWH hPred

lemma encodeFormula_pred_adequate
    (b : Bounds S) (atom : PredicateAtom S)
    (w : WId b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hWF : WF b σ)
    (hClauses :
      (encodeFormula b (.predicate atom) w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (stPreEq : EncState b)
    (hPreEqAll : (addPreEqAll b stPreEq).clauses.all (SAT.Clause.eval σ) = true) :
    σ (FVar.toVar b (encodeFormula b (.predicate atom) w st).1) = true ↔
      ⟨atom.sym, atom.args⟩ ∈ predInterp b σ hWF w.p (decodePre b σ hWF w.ti) := by
  set pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
  set idxs := predIxList b pred
  set literals := idxs.map (fun k => Var.Pred w.p w.ti k)
  cases hMk : mkBigOrIff b literals st with
  | mk u st₁ =>
      have hClausesAll :=
        List.all_eq_true.mp hClauses
      constructor
      · intro hU
        by_cases hEmpty : idxs = []
        · -- Empty case: no predicates, encoding is u ↔ ⊥, vacuous
          have hEncodeVar : (encodeFormula b (.predicate atom) w st).1 = u := by
            unfold encodeFormula
            simp only [pred, idxs, literals, hMk]
            split_ifs
            · rfl
            · contradiction
          have hU' : σ (FVar.toVar b u) = true := by
            simpa [hEncodeVar] using hU
          have hEncodeClauses :
            (encodeFormula b (.predicate atom) w st).2 = st₁ := by
            unfold encodeFormula
            simp only [pred, idxs, literals, hMk]
            split_ifs
            · rfl
            · contradiction
          have hAllMk :
              (mkBigOrIff b literals st).2.clauses.all (SAT.Clause.eval σ) = true := by
            have : (mkBigOrIff b literals st).2 = st₁ := by
              simp only [hMk]
            rw [this, ← hEncodeClauses]
            exact hClauses
          have hExists :=
            mkBigOrIff_exists_true
              (b := b) (vs := literals) (st := st)
              (σ := σ) hAllMk (by simpa [hMk] using hU')
          rcases hExists with ⟨v, hv, _⟩
          simp [literals, hEmpty] at hv
        · -- Non-empty case: normal predicate encoding
          have hEncodeVar : (encodeFormula b (.predicate atom) w st).1 = u := by
            unfold encodeFormula
            simp only [pred, idxs, literals, hMk]
            split_ifs
            · contradiction
            · rfl
          have hU' : σ (FVar.toVar b u) = true := by
            simpa [hEncodeVar] using hU
          let st₂ := addPreEqFrom b w.ti st₁
          let st₃ := addPreEqReflAll b st₂
          have hEncodeClauses :
              (encodeFormula b (.predicate atom) w st).2 =
                predicateFold b idxs w st₃ := by
              simp [encodeFormula, pred, idxs, literals, hMk, hEmpty,
                st₂, st₃, predicateFold, guardStep, guardBackward, guardForward]
          have hAllMk :
              (mkBigOrIff b literals st).2.clauses.all (SAT.Clause.eval σ) = true := by
            refine List.all_eq_true.mpr ?_
            intro clause hClause
            have hClauseMem :
                  clause ∈ (encodeFormula b (.predicate atom) w st).2.clauses :=
                predicate_clause_mem
                  (b := b) (atom := atom) (w := w) (st := st)
                  (clause := clause) (hClause := hClause)
            exact hClausesAll _ hClauseMem
          have hU'_mk : σ (FVar.toVar b (mkBigOrIff b literals st).1) = true := by
            simpa [hMk] using hU'
          have hExists :=
            mkBigOrIff_exists_true
              (b := b) (vs := literals) (st := st)
              (σ := σ) hAllMk hU'_mk
          rcases hExists with ⟨v, hv, hvTrue⟩
          obtain ⟨k, hkIdxs, hkVar⟩ :=
            List.mem_map.1 hv
          subst hkVar
          -- Now we have v = Var.Pred w.p w.ti k and σ v = true, so σ (Var.Pred w.p w.ti k) = true
          have hkPred :
              k ∈ predIxList b ⟨atom.sym, atom.args⟩ := by
            simp only [pred, idxs] at hkIdxs
            exact hkIdxs
          have hkNe : idxs ≠ [] := hEmpty
          have hPreEqSelf :
              σ (Var.PreEq w.ti w.ti) = true :=
            preEq_self_true
              (b := b) (atom := atom) (w := w)
              (st := st) (σ := σ)
              (hNonEmpty := hkNe)
              (hClauses := hClauses)
          have hkTable :
              b.preds.get k = pred := by
            simp only [pred, idxs, predIxList, List.mem_filter] at hkIdxs
            exact of_decide_eq_true hkIdxs.2
          have hTime :=
            ti_mem_timeIndicesFor_decode (b := b) (σ := σ) (hWF := hWF) (ti := w.ti)
          -- Construct witness for predInterp:
          -- ∃ ti ∈ timeIndicesFor, ∃ H', PreEq(ti, H') ∧ pred ∈ predTbl(w.p, H')
          refine ⟨w.ti, hTime, w.ti, hPreEqSelf, ?_⟩
          -- Show pred ∈ predTbl b σ w.p w.ti
          refine ⟨k, hvTrue, hkTable⟩
      · intro hPredMem
        -- Unpack: ∃ ti ∈ timeIndicesFor, ∃ H', PreEq(ti, H') ∧ pred ∈ predTbl(p, H')
        rcases hPredMem with ⟨ti', hTime, H', hPreEq_ti'_H', hTbl⟩
        -- Unpack predTbl: ∃ k, Pred(w.p, H', k) ∧ b.preds.get k = pred
        rcases hTbl with ⟨k, hPred, hkEq⟩
        -- Show k is in the predicate index list
        have hkIdx :
            k ∈ predIxList b ⟨atom.sym, atom.args⟩ := by
          simp [predIxList, pred, hkEq, List.mem_filter, List.mem_finRange]
        by_cases hEmpty : idxs = []
        · -- Empty case: contradiction since k ∈ idxs
          have : k ∈ ([] : List b.predIx) := by
            convert hkIdx using 2
            exact hEmpty.symm
          cases this
        · -- Non-empty case: use PreEq transitivity and backward guard
          -- Step 1: From ti' ∈ timeIndicesFor, get histEq (decodePre ti') (decodePre w.ti)
          have hHistEq_ti'_w :
              PreHistory.histEq (decodePre b σ hWF ti') (decodePre b σ hWF w.ti) :=
            decodePre_histEq_of_mem_timeIndicesFor b σ hWF hTime

          -- Step 2: From PreEq(ti', H') = true, use preEq_sound to get histEq (decodePre ti') (decodePre H')
          have hHistEq_ti'_H' :
              PreHistory.histEq (decodePre b σ hWF ti') (decodePre b σ hWF H') :=
            preEq_sound b σ hWF ti' H' stPreEq hPreEqAll hPreEq_ti'_H'

          -- Step 3: By transitivity, get histEq (decodePre w.ti) (decodePre H')
          have hHistEq_w_H' :
              PreHistory.histEq (decodePre b σ hWF w.ti) (decodePre b σ hWF H') :=
            PreHistory.histEq_trans
              (PreHistory.histEq_symm hHistEq_ti'_w)
              hHistEq_ti'_H'

          -- Step 4: Use preEq_complete to get PreEq(w.ti, H') = true
          have hPreEqWH :
              σ (Var.PreEq w.ti H') = true :=
            preEq_complete b σ hWF w.ti H' stPreEq hPreEqAll hHistEq_w_H'

          -- Step 5: Use backward guard to transfer Pred(w.p, H', k) → Pred(w.p, w.ti, k)
          have hPredWTi :
              σ (Var.Pred w.p w.ti k) = true :=
            local_pred_true_of_guard b atom w st σ H' k hkIdx hPreEqWH hPred hClauses

          exact
            control_true_of_predVar
              (b := b) (atom := atom) (w := w)
              (st := st) (σ := σ) (k := k)
              (hk := hkIdx) (hPred := hPredWTi)
              (hClauses := hClauses)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Transfer predicate membership between histEq-equivalent prehistories.

    This is the key lemma for predicate adequacy: if a predicate holds at some H'
    that is histEq to H, then it also holds at H. This works because predInterp
    uses PreEq to transfer predicates between time indices, and PreEq is sound
    and complete for histEq on decoded prehistories. -/
lemma predInterp_of_histEq
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (p : Fin b.nParticipants) (atom : Signature.AtomicPredType S)
    (H H' : PreHistory (Fin b.nParticipants) (Signature.EventType S))
    (hEq : H'.histEq H)
    (hMem : atom ∈ predInterp b σ hWF p H') :
    atom ∈ predInterp b σ hWF p H := by
  classical
  rcases hMem with ⟨ti, hTi, H'', hPreEq, hTbl⟩
  have hTi' :
      ti ∈ timeIndicesFor b σ hWF H :=
    timeIndicesFor_mem_of_histEq
      (b := b) (σ := σ) (hWF := hWF)
      (H := H) (H' := H') (ti := ti)
      hEq hTi
  exact ⟨ti, hTi', H'', hPreEq, hTbl⟩

end Encoding
