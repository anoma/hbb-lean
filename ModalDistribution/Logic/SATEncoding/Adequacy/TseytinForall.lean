import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.TseytinGadgets
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly

/-!
# Tseytin Correctness for Forall (∀)

This file proves that the Tseytin encoding correctly captures the semantics of
universal quantification formulas.

## Main Result

- `encode_forall_correct`: If the encoding produces control variable u for ∀v.body(v)
  with sub-controls [u₁, ..., uₙ], then u = true iff all uᵢ = true.

## Strategy

The forall encoding uses a conjunction pattern u ↔ (u₁ ∧ ... ∧ uₙ):
- [¬u, uᵢ] for each i: ensures u → uᵢ (forward direction)
- [¬u₁, ..., ¬uₙ, u]: ensures (all uᵢ) → u (backward direction)

Together these enforce u ↔ (u₁ ∧ ... ∧ uₙ).

## Helper Lemmas

The proof requires reasoning about `Clause.eval` which is defined via `List.foldl`.
We provide helper lemmas for:
- Splitting folds with different seeds
- Evaluating clauses on cons and append
- Singleton clause evaluation
- Negation of all-true lists
-/

open ModalDistribution Encoding Logic

namespace Encoding

variable {S : Signature}

open SAT

/-! ## Tseytin Correctness for Forall -/

/-- Forward: from `σ u = true` and satisfaction of `[¬u, uᵢ]` clauses,
    conclude every `uᵢ` is true. -/
lemma encode_forall_forward
    (b : Bounds S) (σ : Assignment (Var b))
    (u : FVar b) (bodyVars : List (FVar b))
    (forwardClauses : List (Clause (Var b)))
    (hForward :
      forwardClauses =
        bodyVars.map (fun uBody =>
          [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)]))
    (hSat : forwardClauses.all (Clause.eval σ) = true)
    (hU : σ (FVar.toVar b u) = true) :
    ∀ uBody ∈ bodyVars, σ (FVar.toVar b uBody) = true := by
  intro uBody hIn
  -- membership of the specific clause
  have hClauseIn :
    [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)] ∈ forwardClauses := by
    rw [hForward]; exact List.mem_map.mpr ⟨uBody, hIn, rfl⟩
  -- that clause evaluates to true
  have hAll := List.all_eq_true.mp hSat
  have hClauseTrue : Clause.eval σ
      [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)] = true :=
    hAll _ hClauseIn
  -- with σ u = true, the clause reduces to σ uBody
  -- eval([¬u, uBody]) = (!σ u) || (σ uBody) = (false) || σ uBody
  simpa [Clause.eval, Lit.eval, hU] using hClauseTrue

/-- Backward: if all `uᵢ` are true and the big clause
    `[¬u₁, …, ¬uₙ, u]` is satisfied, then `σ u = true`. -/
lemma encode_forall_backward
    (b : Bounds S) (σ : Assignment (Var b))
    (u : FVar b) (bodyVars : List (FVar b))
    (backwardClause : Clause (Var b))
    (hBackward :
      backwardClause =
        bodyVars.map (fun uBody => Lit.neg (FVar.toVar b uBody))
          ++ [Lit.pos (FVar.toVar b u)])
    (hSat : Clause.eval σ backwardClause = true)
    (hAllBodies : ∀ uBody ∈ bodyVars, σ (FVar.toVar b uBody) = true) :
    σ (FVar.toVar b u) = true := by
  classical
  -- turn clause evaluation into an `any` witness
  have hClause := hSat
  rw [hBackward] at hClause
  have hClauseAny :=
    Clause.eval_eq_any (σ := σ)
      (C := bodyVars.map (fun uBody => Lit.neg (FVar.toVar b uBody))
            ++ [Lit.pos (FVar.toVar b u)])
  have hAny :
      (bodyVars.map (fun uBody => Lit.neg (FVar.toVar b uBody))
        ++ [Lit.pos (FVar.toVar b u)]).any (fun lit => Lit.eval σ lit) = true := by
    have := hClause
    rw [hClauseAny] at this
    simpa using this
  obtain ⟨lit, hMem, hEval⟩ := (List.any_eq_true).mp hAny
  have hLit_pos : lit = Lit.pos (FVar.toVar b u) := by
    have hSplit := List.mem_append.mp hMem
    cases hSplit with
    | inl hInMap =>
        rcases List.mem_map.mp hInMap with ⟨uBody, hInBody, rfl⟩
        have := hAllBodies uBody hInBody
        -- negative literals cannot evaluate to true under `hAllBodies`
        simp [Lit.eval, this] at hEval
    | inr hInSingleton =>
        simpa [List.mem_singleton] using hInSingleton
  subst hLit_pos
  simpa [Lit.eval] using hEval

/-- If the full clause list `clauses` is exactly the `forall`-encoding
    (`forwardClauses ++ [backwardClause]`), then under `clauses.all eval = true`
    we get the bi-implication. -/
lemma encode_forall_correct
    (b : Bounds S) (σ : Assignment (Var b))
    (u : FVar b) (bodyVars : List (FVar b))
    (clauses : List (Clause (Var b)))
    (hEnc :
      clauses =
        (bodyVars.map (fun uBody =>
          [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)]))
        ++
        [bodyVars.map (fun uBody => Lit.neg (FVar.toVar b uBody))
            ++ [Lit.pos (FVar.toVar b u)]])
    (hSat : clauses.all (Clause.eval σ) = true) :
    (σ (FVar.toVar b u) = true) ↔
      (∀ uBody ∈ bodyVars, σ (FVar.toVar b uBody) = true) := by
  constructor
  · -- → direction: use the forward part's clauses
    intro hU
    -- pull "all true" to membership checker
    have hAll := List.all_eq_true.mp hSat
    -- forward clauses sublist
    let fwd :=
      bodyVars.map (fun uBody =>
        [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)])
    have hFwdSat : fwd.all (Clause.eval σ) = true := by
      -- every member of `fwd` is a member of `clauses` by `hEnc`
      -- so `all` on clauses gives true on fwd members
      -- We don't need a separate lemma: we'll re-use `encode_forall_forward`
      -- by passing `fwd` and the restriction of `hAll`.
      -- Build it explicitly:
      -- show: fwd.all (Clause.eval σ) = true
      -- Turn goal into `List.all_eq_true.mpr` form
      apply List.all_eq_true.mpr
      intro C hC
      -- C ∈ fwd ⇒ C ∈ clauses
      have : C ∈ clauses := by
        rw [hEnc]
        apply List.mem_append.mpr
        exact Or.inl hC
      exact hAll _ this
    -- apply the forward lemma
    exact encode_forall_forward b σ u bodyVars fwd rfl hFwdSat hU
  · -- ← direction: use the single backward clause
    intro hBodies
    -- backward clause
    let back :=
      bodyVars.map (fun uBody => Lit.neg (FVar.toVar b uBody))
        ++ [Lit.pos (FVar.toVar b u)]
    -- it's in `clauses` as the last element (by `hEnc`)
    have hBackIn : back ∈ clauses := by
      rw [hEnc]
      apply List.mem_append.mpr
      right
      simp [back]
    -- evaluate to true by `hSat`
    have hAll := List.all_eq_true.mp hSat
    have hBackSat : Clause.eval σ back = true := hAll _ hBackIn
    -- apply backward lemma
    exact encode_forall_backward b σ u bodyVars back rfl hBackSat hBodies

variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]
variable [DecidableEq S.Value]

/-- Adequacy for encodeFormula forall case: σ(u) = true ↔ ∀v. body(v) holds. -/
lemma encodeFormula_forall_adequate (b : Bounds S) (body : S.Value → Logic.Formula S)
    (w : WId b) (st : EncState b) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (ihBody_iff : ∀ v (st₀ : EncState b),
      let res := encodeFormula b (body v) w st₀
      let uBody := res.1
      let stBody := res.2
      stBody.clauses.all (SAT.Clause.eval σ) = true →
        (σ (FVar.toVar b uBody) = true ↔
          Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
            (decodePre b σ hWF w.ti) (body v)))
    (hClauses : (encodeFormula b (.forall body) w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b (encodeFormula b (.forall body) w st).1) = true) ↔
    Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti)
      (.forall body) := by
  classical
  constructor
  · -- Forward: σ(u) = true → ∀v. Sat (body v)
    intro hU
    simp [Sat]
    intro v
    -- Unfold the encoding to extract bodyVars and the forward/backward clauses
    cases hAlloc : EncState.allocFresh b st with
    | mk u st1 =>
      let encodeConj :
          List b.valIx → EncState b → List (FVar b) × EncState b :=
        fun valIndices stAcc =>
          valIndices.foldl (fun (vars, stCur) vIdx =>
            let v := b.values.get vIdx
            let res := encodeFormula b (body v) w stCur
            (vars ++ [res.1], res.2)
          ) ([], stAcc)
      cases hEncConj : encodeConj (List.finRange b.nVals) st1 with
      | mk bodyVars st2 =>
        let forwardClauses :
            List (Clause (Var b)) :=
          bodyVars.map (fun uBody =>
            [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)])
        let backwardClause :
            Clause (Var b) :=
          bodyVars.map (fun uBody => Lit.neg (FVar.toVar b uBody))
            ++ [Lit.pos (FVar.toVar b u)]
        let st3 :=
          bodyVars.foldl (fun stCur uBody =>
            EncState.addClause b stCur
              [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)]) st2
        let st4 := EncState.addClause b st3 backwardClause

        have hEncodeFormula :
            encodeFormula b (.forall body) w st = (u, st4) := by
          simp [encodeFormula, hAlloc, encodeConj, hEncConj, st3, st4,
            backwardClause]

        have hAll_st4 : st4.clauses.all (Clause.eval σ) = true := by
          simpa [hEncodeFormula] using hClauses

        -- Forward/backward clauses satisfied
        have hForward_mem : forwardClauses ⊆ st4.clauses := by
          intro clause hMem
          rcases List.mem_map.mp hMem with ⟨uBody, hMemBody, rfl⟩
          -- clause added during fold into st3, then included into st4
          have hExists :=
            foldl_exists_state_subset
              (f := fun stCur uB =>
                EncState.addClause b stCur
                  [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uB)])
              (hStep := by
                intro stCur uB
                exact EncState.addClause_subset_clauses (b := b) stCur
                  [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uB)])
              (xs := bodyVars) (x := uBody) (init := st2) hMemBody
          rcases hExists with ⟨st_k, hSubset_k⟩
          have hHead :
              [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)] ∈
                (EncState.addClause b st_k
                  [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)]).clauses := by
            simp [EncState.addClause]
          exact (List.Subset.trans hSubset_k
            (EncState.addClause_subset_clauses (b := b) st3 backwardClause)) hHead

        have hBackward_mem : backwardClause ∈ st4.clauses := by
          simp [st4, EncState.addClause]

        have hConjAll :
            (forwardClauses ++ [backwardClause]).all (Clause.eval σ) = true := by
          apply all_true_of_subset _ hAll_st4
          intro clause hMem
          rcases List.mem_append.mp hMem with hFwd | hBack
          · exact hForward_mem hFwd
          · -- hBack : clause ∈ [backwardClause]
            have hClauseEq : clause = backwardClause := by simpa [List.mem_singleton] using hBack
            subst hClauseEq
            exact hBackward_mem

        have hControl :
            (σ (FVar.toVar b u) = true) ↔
              (∀ uBody ∈ bodyVars, σ (FVar.toVar b uBody) = true) :=
          encode_forall_correct b σ u bodyVars (forwardClauses ++ [backwardClause]) rfl hConjAll

        have hBodiesTrue : ∀ uBody ∈ bodyVars, σ (FVar.toVar b uBody) = true :=
          hControl.mp (by
            -- rewrite σ u using hEncodeFormula
            have : σ (FVar.toVar b u) = true := by
              simpa [hEncodeFormula] using hU
            exact this)

        -- Show st2.clauses are all satisfied (subset of st4)
        have hAll_st2 :
            st2.clauses.all (Clause.eval σ) = true := by
          -- st2 ⊆ st3 by fold, and st3 ⊆ st4 by final addClause
          have hSub_st2_st3 :
              st2.clauses ⊆ st3.clauses := by
            -- foldl_subset_state for the forward clauses
            exact
              (foldl_subset_state
                (f := fun stCur uBody =>
                  EncState.addClause b stCur
                    [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)])
                (hStep := by
                  intro stCur uBody
                  exact EncState.addClause_subset_clauses (b := b) stCur
                    [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)])
                (xs := bodyVars) (init := st2))
          have hSub_st3_st4 :
              st3.clauses ⊆ st4.clauses :=
            EncState.addClause_subset_clauses (b := b) st3 backwardClause
          apply all_true_of_subset (List.Subset.trans hSub_st2_st3 hSub_st3_st4)
          exact hAll_st4

        -- Now prove semantic forall
        obtain ⟨idx, hIdx⟩ := b.values_complete v
        have hIdxMem : idx ∈ List.finRange b.nVals := by simp [List.mem_finRange]

        -- build the prefix state up to idx
        let acc0 : List (FVar b) × EncState b := ([], st1)
        let step :
            List (FVar b) × EncState b → b.valIx →
              List (FVar b) × EncState b :=
          fun (vars, stCur) vIdx =>
            let v := b.values.get vIdx
            let res := encodeFormula b (body v) w stCur
            (vars ++ [res.1], res.2)

        -- compute the fold over finRange to get bodyVars/st2
        have hFold :
            encodeConj (List.finRange b.nVals) st1 =
              (List.finRange b.nVals).foldl step acc0 := rfl
        have hEncConj' := hEncConj
        -- encodeConj is definitionally the fold; extract components
        have hBodyVars :
            ((List.finRange b.nVals).foldl step acc0).1 = bodyVars := by
          have := congrArg Prod.fst hEncConj'
          simpa [hFold] using this
        have hSt2 :
            ((List.finRange b.nVals).foldl step acc0).2 = st2 := by
          have := congrArg Prod.snd hEncConj'
          simpa [hFold] using this

        -- monotonicity of the fold components
        have hStep_snd :
            ∀ stCur vIdx, stCur.2.clauses ⊆ (step stCur vIdx).2.clauses := by
          intro stCur vIdx
          dsimp [step]
          simpa using
            (encodeFormula_clauses_subset (b := b)
              (φ := body (b.values.get vIdx)) w stCur.2)
        have hStep_fst :
            ∀ stCur vIdx, stCur.1 ⊆ (step stCur vIdx).1 := by
          intro stCur vIdx u hMem
          dsimp [step]
          apply List.mem_append.mpr
          exact Or.inl hMem

        -- split the index list at the chosen witness
        obtain ⟨as, bs, hSplit⟩ := exists_split_of_mem hIdxMem
        let st_k := as.foldl step acc0
        let res := encodeFormula b (body v) w st_k.2
        have hStepEval : step st_k idx = (st_k.1 ++ [res.1], res.2) := by
          simp [step, res, hIdx]

        -- relate the full fold to the split prefix/suffix decomposition
        have hFoldSplit :
            (List.finRange b.nVals).foldl step acc0 =
              bs.foldl step (step st_k idx) := by
          calc
            (List.finRange b.nVals).foldl step acc0
                = (as ++ idx :: bs).foldl step acc0 := by simp [hSplit]
            _ = (idx :: bs).foldl step (as.foldl step acc0) := by
                  simp [List.foldl_append]
            _ = bs.foldl step (step st_k idx) := by simp [hStepEval, st_k]

        -- obtain clause satisfaction for the specific body encoding
        have hSubClauses :
            res.2.clauses ⊆ st2.clauses := by
          have hSuffixSub :
              (step st_k idx).2.clauses ⊆
                (bs.foldl step (step st_k idx)).2.clauses :=
            foldl_subset_snd (f := step) (hStep := hStep_snd) bs (step st_k idx)
          have hFinalSnd :
              (bs.foldl step (step st_k idx)).2 = st2 := by
            have h := congrArg Prod.snd hFoldSplit
            calc
              (bs.foldl step (step st_k idx)).2
                  = ((List.finRange b.nVals).foldl step acc0).2 := by
                      simpa using h.symm
              _ = st2 := hSt2
          have hSub : (step st_k idx).2.clauses ⊆ st2.clauses := by
            intro clause hClause
            have hClauseIn := hSuffixSub hClause
            simpa [hFinalSnd] using hClauseIn
          have hSndEq : (step st_k idx).2 = res.2 := by
            simp [hStepEval]
          intro clause hClause
          have hClause' : clause ∈ (step st_k idx).2.clauses := by
            simpa [hSndEq] using hClause
          exact hSub hClause'

        have hResAll : res.2.clauses.all (Clause.eval σ) = true :=
          all_true_of_subset hSubClauses hAll_st2

        -- show the corresponding control variable is present and true
        have hSuffixVars :
            (step st_k idx).1 ⊆ (bs.foldl step (step st_k idx)).1 :=
          foldl_subset_fst (f := step) (hStep := hStep_fst) bs (step st_k idx)
        have hFinalFst :
            (bs.foldl step (step st_k idx)).1 = bodyVars := by
          have h := congrArg Prod.fst hFoldSplit
          calc
            (bs.foldl step (step st_k idx)).1
                = ((List.finRange b.nVals).foldl step acc0).1 := by
                    simpa using h.symm
            _ = bodyVars := hBodyVars
        have hResMem : res.1 ∈ bodyVars := by
          have hMemStep : res.1 ∈ (step st_k idx).1 := by
            simp [hStepEval]
          have hMemFinal : res.1 ∈ (bs.foldl step (step st_k idx)).1 :=
            hSuffixVars hMemStep
          simpa [hFinalFst] using hMemFinal

        -- apply IH to obtain semantic satisfaction for this value
        have hIff := ihBody_iff v st_k.2
        have hIffRes :
            res.2.clauses.all (Clause.eval σ) = true →
              (σ (FVar.toVar b res.1) = true ↔
                Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
                  (decodePre b σ hWF w.ti) (body v)) := by
          simpa [res] using hIff
        have hSatBody :
            Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
              (decodePre b σ hWF w.ti) (body v) :=
          (hIffRes hResAll).mp (hBodiesTrue _ hResMem)

        exact hSatBody
  · -- Backward: (∀v. Sat (body v)) → σ(u) = true
    intro hSat
    simp [Sat] at hSat
    -- Unfold encoding
    cases hAlloc : EncState.allocFresh b st with
    | mk u st1 =>
      let encodeConj :
          List b.valIx → EncState b → List (FVar b) × EncState b :=
        fun valIndices stAcc =>
          valIndices.foldl (fun (vars, stCur) vIdx =>
            let v := b.values.get vIdx
            let res := encodeFormula b (body v) w stCur
            (vars ++ [res.1], res.2)
          ) ([], stAcc)
      cases hEncConj : encodeConj (List.finRange b.nVals) st1 with
      | mk bodyVars st2 =>
        let forwardClauses :
            List (Clause (Var b)) :=
          bodyVars.map (fun uBody =>
            [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)])
        let backwardClause :
            Clause (Var b) :=
          bodyVars.map (fun uBody => Lit.neg (FVar.toVar b uBody))
            ++ [Lit.pos (FVar.toVar b u)]
        let st3 :=
          bodyVars.foldl (fun stCur uBody =>
            EncState.addClause b stCur
              [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)]) st2
        let st4 := EncState.addClause b st3 backwardClause

        have hEncodeFormula :
            encodeFormula b (.forall body) w st = (u, st4) := by
          simp [encodeFormula, hAlloc, encodeConj, hEncConj, st3, st4,
            backwardClause]

        have hAll_st4 : st4.clauses.all (Clause.eval σ) = true := by
          simpa [hEncodeFormula] using hClauses

        have hBackward_mem : backwardClause ∈ st4.clauses := by
          simp [st4, EncState.addClause]

        -- We will show all uBody are true using hSat and IH, then use backward clause
        have hAll_st2 :
            st2.clauses.all (Clause.eval σ) = true := by
          -- st2 ⊆ st3 ⊆ st4
          apply all_true_of_subset
            (List.Subset.trans
              (foldl_subset_state
                (f := fun stCur uBody =>
                  EncState.addClause b stCur
                    [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)])
                (hStep := by
                  intro stCur uBody
                  exact EncState.addClause_subset_clauses (b := b) stCur
                    [Lit.neg (FVar.toVar b u), Lit.pos (FVar.toVar b uBody)])
                (xs := bodyVars) (init := st2))
              (EncState.addClause_subset_clauses (b := b) st3 backwardClause))
          exact hAll_st4

        -- For each bodyVar, derive σ uBody = true using hSat and IH
        have hBodiesTrue :
            ∀ uBody ∈ bodyVars, σ (FVar.toVar b uBody) = true := by
          -- We prove by induction over the fold producing `bodyVars`
          let acc0 : List (FVar b) × EncState b := ([], st1)
          let step :
              List (FVar b) × EncState b → b.valIx →
                List (FVar b) × EncState b :=
            fun (vars, stCur) vIdx =>
              let v := b.values.get vIdx
              let res := encodeFormula b (body v) w stCur
              (vars ++ [res.1], res.2)

          have hFold :
              encodeConj (List.finRange b.nVals) st1 =
                (List.finRange b.nVals).foldl step acc0 := rfl
          have hEncConj' := hEncConj
          have hBodyVars :
              ((List.finRange b.nVals).foldl step acc0).1 = bodyVars := by
            have := congrArg Prod.fst hEncConj'
            simpa [hFold] using this
          have hSt2 :
              ((List.finRange b.nVals).foldl step acc0).2 = st2 := by
            have := congrArg Prod.snd hEncConj'
            simpa [hFold] using this

          -- monotonicity of clauses/vars during the fold
          have hStep_snd :
              ∀ stCur vIdx, stCur.2.clauses ⊆ (step stCur vIdx).2.clauses := by
            intro stCur vIdx
            dsimp [step]
            simpa using
              (encodeFormula_clauses_subset (b := b)
                (φ := body (b.values.get vIdx)) w stCur.2)
          have hStep_fst :
              ∀ stCur vIdx, stCur.1 ⊆ (step stCur vIdx).1 := by
            intro stCur vIdx u hMem
            dsimp [step]
            apply List.mem_append.mpr
            exact Or.inl hMem

          -- Helper: all vars accumulated in a fold are true if the clauses are
          -- satisfied and each body is semantically true.
          have hFold_all :
              ∀ (vals : List b.valIx) (acc : List (FVar b) × EncState b),
                (∀ u ∈ acc.1, σ (FVar.toVar b u) = true) →
                ((vals.foldl step acc).2.clauses.all (Clause.eval σ) = true) →
                (∀ u ∈ (vals.foldl step acc).1, σ (FVar.toVar b u) = true) := by
            intro vals
            induction vals with
            | nil =>
                intro acc hAccTrue _ u hMem
                simpa [List.foldl] using hAccTrue _ hMem
            | cons idx rest ih =>
                intro acc hAccTrue hAll u hMem
                -- current encoding result
                let v := b.values.get idx
                let res := encodeFormula b (body v) w acc.2
                have hStepEval : step acc idx = (acc.1 ++ [res.1], res.2) := by
                  simp [step, res, v]
                have hRestAll :
                    (rest.foldl step (step acc idx)).2.clauses.all (Clause.eval σ) = true := by
                  simpa [List.foldl, hStepEval] using hAll

                -- clauses for res are satisfied (subset of final)
                have hResSubset :
                    res.2.clauses ⊆ (rest.foldl step (step acc idx)).2.clauses := by
                  have hSub :=
                    foldl_subset_snd (f := step) (hStep := hStep_snd) rest (step acc idx)
                  intro clause hClause
                  have hClauseIn : clause ∈ (step acc idx).2.clauses := by
                    simpa [hStepEval] using hClause
                  have hClauseRest := hSub hClauseIn
                  simpa using hClauseRest
                have hResAll : res.2.clauses.all (Clause.eval σ) = true :=
                  all_true_of_subset hResSubset hRestAll

                -- semantic truth gives σ(res.1) = true via IH
                have hSatValue :
                    Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
                      (decodePre b σ hWF w.ti) (body v) := hSat v
                have hIff := ihBody_iff v acc.2
                have hIffRes :
                    res.2.clauses.all (Clause.eval σ) = true →
                      (σ (FVar.toVar b res.1) = true ↔
                        Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
                          (decodePre b σ hWF w.ti) (body v)) := by
                  simpa [res, v] using hIff
                have hResTrue : σ (FVar.toVar b res.1) = true :=
                  (hIffRes hResAll).mpr hSatValue

                -- extend truth to the accumulator after this step
                have hAccStepTrue :
                    ∀ u' ∈ (step acc idx).1, σ (FVar.toVar b u') = true := by
                  intro u' hMem'
                  have hMemList : u' ∈ acc.1 ++ [res.1] := by
                    simpa [hStepEval] using hMem'
                  have hMem'' : u' ∈ acc.1 ∨ u' = res.1 := by
                    rcases List.mem_append.mp hMemList with hInAcc | hInSingleton
                    · exact Or.inl hInAcc
                    · have hEq : u' = res.1 := by
                        simpa [List.mem_singleton] using hInSingleton
                      exact Or.inr hEq
                  cases hMem'' with
                  | inl hInAcc => exact hAccTrue _ hInAcc
                  | inr hEq => simpa [hEq] using hResTrue

                -- recurse on the remainder
                exact ih (acc := step acc idx) hAccStepTrue hRestAll u hMem

          -- instantiate helper on the concrete fold producing bodyVars
          have hAll_fold :
              ((List.finRange b.nVals).foldl step acc0).2.clauses.all
                (Clause.eval σ) = true := by
            simpa [hSt2] using hAll_st2
          have hAllVars :
              ∀ u ∈ ((List.finRange b.nVals).foldl step acc0).1,
                σ (FVar.toVar b u) = true :=
            hFold_all (List.finRange b.nVals) acc0 (by intro u h; cases h) hAll_fold
          intro uBody hMemBody
          have hMemFold : uBody ∈ ((List.finRange b.nVals).foldl step acc0).1 := by
            simpa [hBodyVars] using hMemBody
          exact hAllVars _ hMemFold

        have hBackSat :
            Clause.eval σ backwardClause = true := by
          have hAll := List.all_eq_true.mp hAll_st4
          exact hAll _ hBackward_mem

        -- conclude σ u = true
        have hU :=
          encode_forall_backward b σ u bodyVars backwardClause rfl hBackSat hBodiesTrue
        -- rewrite u to the actual control var
        simpa [hEncodeFormula] using hU

end Encoding
