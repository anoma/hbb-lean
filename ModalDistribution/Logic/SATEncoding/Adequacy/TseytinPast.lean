import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly

/-!
# Tseytin Correctness for Past (past)

This file proves that the Tseytin encoding correctly captures the semantics of
past modal operator formulas.

## Main Result

- `encode_past_witness`: If a witness world satisfies Mem, Place, and φ, then u = true.

## Strategy

The past encoding creates clauses for each potential witness world w':
- [¬Mem(w.ti, w'), ¬Place(w', w.p), ¬u', u]

This represents: (Mem(w.ti, w') ∧ Place(w', w.p) ∧ u') → u

Note: The encoding uses a one-way implication rather than a bi-conditional.
The forward direction (witness implies u) is encoded, but the reverse direction
is not explicitly constrained by these clauses.
-/

open ModalDistribution Encoding Logic

namespace Encoding

variable {S : Signature}

open SAT

/-! ## Witness List Nodup -/

/-- Witnesses list (filtered allWorlds) has no duplicates -/
lemma witnesses_nodup (b : Bounds S) (w : WId b) :
    ((WId.allWorlds b).filterMap fun w' =>
      if w'.p = w.p then some w' else none).Nodup := by
  apply List.Nodup.filterMap
  · intro w1 w2 wOut hMem1 hMem2
    -- hMem1 : wOut ∈ if w1.p = w.p then some w1 else none
    -- hMem2 : wOut ∈ if w2.p = w.p then some w2 else none
    by_cases h1 : w1.p = w.p <;> by_cases h2 : w2.p = w.p <;>
      simp only [h1, h2, Option.mem_def, reduceIte] at hMem1 hMem2
    · -- When both conditions are true: hMem1 : some w1 = some wOut, hMem2 : some w2 = some wOut
      exact Option.some.inj (hMem1.trans hMem2.symm)
    · exact Option.noConfusion hMem2  -- h1 true, h2 false: hMem2 : none = some wOut
    · exact Option.noConfusion hMem1  -- h1 false, h2 true: hMem1 : none = some wOut
    · exact Option.noConfusion hMem1  -- both false: hMem1 : none = some wOut
  · exact WId.allWorlds_nodup b

/-! ## Index-based List Access -/

/-- Indexing into an appended list at the length of the first list gives the head of the second -/
lemma getElem?_append_length {α} (xs ys : List α) :
    (xs ++ ys)[xs.length]? = ys[0]? := by
  induction xs with
  | nil => simp
  | cons _ xs ih => simpa using ih

/-! ## Tseytin Correctness for Past -/

/-- For each witness world, if Mem, Place, and the subformula hold, then u = true.
    TODO: Update for canonical encoding without Var.Place. -/
lemma encode_past_witness (b : Bounds S) (σ : Assignment (Var b))
    (u : FVar b) (w : WId b)
    (witnessPairs : List (FVar b × WId b))
    (clauses : List (Clause (Var b)))
    (hEncoding : clauses =
      witnessPairs.map (fun (u', w') =>
        [Lit.neg (Var.Mem w.ti w'), Lit.neg (FVar.toVar b u'), Lit.pos (FVar.toVar b u)]))
    (hSat : clauses.all (Clause.eval σ) = true)
    (u' : FVar b) (w' : WId b)
    (hWitness : (u', w') ∈ witnessPairs)
    (hMem : σ (Var.Mem w.ti w') = true)
    (hU' : σ (FVar.toVar b u') = true) :
    σ (FVar.toVar b u) = true := by
  classical
  have hAll := List.all_eq_true.mp hSat
  have hClause :
      [Lit.neg (Var.Mem w.ti w'), Lit.neg (FVar.toVar b u'),
        Lit.pos (FVar.toVar b u)] ∈ clauses := by
    rw [hEncoding]
    exact List.mem_map.mpr ⟨(u', w'), hWitness, rfl⟩
  have hEval := hAll _ hClause
  simp [Clause.eval, Lit.eval, hMem, hU'] at hEval
  exact hEval

/-- Forward direction: if any witness satisfies the conditions, then u = true.
    TODO: Update for canonical encoding without Var.Place. -/
lemma encode_past_forward (b : Bounds S) (σ : Assignment (Var b))
    (u : FVar b) (w : WId b)
    (witnessPairs : List (FVar b × WId b))
    (clauses : List (Clause (Var b)))
    (hEncoding : clauses =
      witnessPairs.map (fun (u', w') =>
        [Lit.neg (Var.Mem w.ti w'), Lit.neg (FVar.toVar b u'), Lit.pos (FVar.toVar b u)]))
    (hSat : clauses.all (Clause.eval σ) = true)
    (hWitness : ∃ pair ∈ witnessPairs,
      σ (Var.Mem w.ti pair.2) = true ∧
      σ (FVar.toVar b pair.1) = true) :
    σ (FVar.toVar b u) = true := by
  rcases hWitness with ⟨pair, hPairMem, hMem, hU'⟩
  cases pair with
  | mk u' w' =>
      exact encode_past_witness b σ u w witnessPairs clauses hEncoding hSat u' w' hPairMem hMem hU'

variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]
variable [DecidableEq S.Value]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- For the aux-variable fold, tracks that each aux variable in the output
    corresponds to a specific input pair, and the backward clauses for that
    (aux, pair) are included in the final state.

    If `(auxVars, st₃) = pairs.foldl auxStep ([], st₂)` and `aux ∈ auxVars`,
    then there exists a pair `(u', w')` such that:
    - The backward clauses `[¬aux, Mem(w.ti, w')]` and `[¬aux, u']` are in st₃.clauses -/
lemma auxStep_backward_clauses_in_final
    (b : Bounds S) (w : WId b) (uControl : FVar b)
    (pairs : List (FVar b × WId b)) (st₂ : EncState b)
    (auxVars : List (FVar b)) (st₃ : EncState b)
    (hFold : pairs.foldl
      (fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
        let (u', w') := pair
        let memVar := Var.Mem w.ti w'
        let (aux, stCur) := EncState.allocFresh b acc.2
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
            SAT.Lit.pos (FVar.toVar b uControl)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
            SAT.Lit.pos (FVar.toVar b aux)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
        (acc.1 ++ [aux], stCur)) ([], st₂) = (auxVars, st₃))
    (aux : FVar b) (hAuxMem : aux ∈ auxVars) :
    ∃ (u' : FVar b) (w' : WId b),
      (u', w') ∈ pairs ∧
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (Var.Mem w.ti w')] ∈ st₃.clauses ∧
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')] ∈ st₃.clauses := by
  -- Define the step function components:
  -- g st (u', w') = the fresh aux variable allocated from st
  -- h st (u', w') = the state after adding all four clauses
  let g : EncState b → FVar b × WId b → FVar b :=
    fun st _ => (EncState.allocFresh b st).1
  let h : EncState b → FVar b × WId b → EncState b :=
    fun st pair =>
      let (u', w') := pair
      let memVar := Var.Mem w.ti w'
      let (aux', stCur) := EncState.allocFresh b st
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
          SAT.Lit.pos (FVar.toVar b uControl)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
          SAT.Lit.pos (FVar.toVar b aux')]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux'), SAT.Lit.pos memVar]
      EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux'), SAT.Lit.pos (FVar.toVar b u')]
  -- The step function in hFold is equivalent to (pfx, st) ↦ (pfx ++ [g st a], h st a)
  have hFoldRewrite : pairs.foldl (fun acc pair =>
        let (u', w') := pair
        let memVar := Var.Mem w.ti w'
        let (aux', stCur) := EncState.allocFresh b acc.2
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
            SAT.Lit.pos (FVar.toVar b uControl)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
            SAT.Lit.pos (FVar.toVar b aux')]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux'), SAT.Lit.pos memVar]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux'), SAT.Lit.pos (FVar.toVar b u')]
        (acc.1 ++ [aux'], stCur)) ([], st₂) =
      pairs.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a)) ([], st₂) := rfl
  rw [hFoldRewrite] at hFold
  -- h preserves and extends clauses
  have hClauseSub : ∀ st pair, st.clauses ⊆ (h st pair).clauses := by
    intro st ⟨u', w'⟩
    simp only [h]
    have hAlloc := EncState.allocFresh_clauses_eq (b := b) (st := st)
    let st0 := (EncState.allocFresh b st).2
    let memVar' := Var.Mem w.ti w'
    let aux' := (EncState.allocFresh b st).1
    let c1 := [SAT.Lit.neg memVar', SAT.Lit.neg (FVar.toVar b u'),
                SAT.Lit.pos (FVar.toVar b uControl)]
    let c2 := [SAT.Lit.neg memVar', SAT.Lit.neg (FVar.toVar b u'),
                SAT.Lit.pos (FVar.toVar b aux')]
    let c3 := [SAT.Lit.neg (FVar.toVar b aux'), SAT.Lit.pos memVar']
    let c4 := [SAT.Lit.neg (FVar.toVar b aux'), SAT.Lit.pos (FVar.toVar b u')]
    let st1 := EncState.addClause b st0 c1
    let st2 := EncState.addClause b st1 c2
    let st3 := EncState.addClause b st2 c3
    calc st.clauses
        = st0.clauses := hAlloc
      _ ⊆ st1.clauses := EncState.addClause_subset_clauses (b := b) st0 c1
      _ ⊆ st2.clauses := EncState.addClause_subset_clauses (b := b) st1 c2
      _ ⊆ st3.clauses := EncState.addClause_subset_clauses (b := b) st2 c3
      _ ⊆ _ := EncState.addClause_subset_clauses (b := b) st3 c4
  -- Induction on pairs
  induction pairs generalizing aux auxVars st₂ st₃ with
  | nil =>
      simp only [List.foldl_nil, Prod.mk.injEq] at hFold
      rw [← hFold.1] at hAuxMem
      exact False.elim (List.not_mem_nil hAuxMem)
  | cons hd tl ih =>
      simp only [List.foldl_cons] at hFold
      rcases hd with ⟨u'_hd, w'_hd⟩
      -- Compute one step
      let memVar_hd := Var.Mem w.ti w'_hd
      let aux_hd := g st₂ (u'_hd, w'_hd)
      let st_after_step := h st₂ (u'_hd, w'_hd)
      -- From hFold, extract the final result
      have hFoldResult := hFold
      simp only at hFoldResult
      have hAuxVarsEq : auxVars =
          (tl.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a))
            ([aux_hd], st_after_step)).1 := by
        have h1 := congrArg Prod.fst hFoldResult
        simp only at h1
        exact h1.symm
      have hSt3Eq : st₃ =
          (tl.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a))
            ([aux_hd], st_after_step)).2 := by
        have h1 := congrArg Prod.snd hFoldResult
        simp only at h1
        exact h1.symm
      -- st_after_step.clauses ⊆ st₃.clauses
      have hClausesSub : st_after_step.clauses ⊆ st₃.clauses := by
        rw [hSt3Eq]
        have := foldl_subset_snd (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a))
          (fun acc a => hClauseSub acc.2 a) tl ([aux_hd], st_after_step)
        exact this
      -- Case split: aux = aux_hd or aux came from tl
      by_cases hCase : aux = aux_hd
      · -- aux = aux_hd: the backward clauses were added in the first step
        subst hCase
        refine ⟨u'_hd, w'_hd, List.mem_cons_self, ?_, ?_⟩
        · -- Backward clause 1: [¬aux_hd, Mem] in st₃
          have hIn : [SAT.Lit.neg (FVar.toVar b aux_hd), SAT.Lit.pos memVar_hd]
              ∈ st_after_step.clauses := by
            simp only [st_after_step, h, aux_hd, g, memVar_hd, EncState.addClause, List.mem_cons]
            -- Goal: _ = c4 ∨ True ∨ _ = c2 ∨ _ = c1 ∨ _ ∈ old (True = c3 match)
            right; left; trivial
          exact hClausesSub hIn
        · -- Backward clause 2: [¬aux_hd, u'_hd] in st₃
          have hIn : [SAT.Lit.neg (FVar.toVar b aux_hd), SAT.Lit.pos (FVar.toVar b u'_hd)]
              ∈ st_after_step.clauses := by
            simp only [st_after_step, h, aux_hd, g, EncState.addClause, List.mem_cons]
            -- Goal: True ∨ _ = c3 ∨ _ (True = c4 match)
            left; trivial
          exact hClausesSub hIn
      · -- aux ≠ aux_hd: aux came from folding tl
        -- Use the prefix-append lemmas to show auxVars = [aux_hd] ++ tl_auxVars
        let tl_auxVars :=
          (tl.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a))
            ([], st_after_step)).1
        let tl_st :=
          (tl.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a))
            ([], st_after_step)).2
        -- rest_auxVars = [aux_hd] ++ tl_auxVars (by prefix-preserving property)
        have hRestSplit : auxVars = [aux_hd] ++ tl_auxVars := by
          rw [hAuxVarsEq]
          exact foldl_fst_prefix_append' g h tl [aux_hd] st_after_step
        -- tl_st = st₃ (by prefix-independence of second component)
        have hTlStEq : tl_st = st₃ := by
          rw [hSt3Eq]
          exact (foldl_snd_prefix_indep' g h tl [aux_hd] [] st_after_step).symm
        -- aux ∈ auxVars and aux ≠ aux_hd means aux ∈ tl_auxVars
        have hAuxInTl : aux ∈ tl_auxVars := by
          rw [hRestSplit] at hAuxMem
          rcases List.mem_append.mp hAuxMem with hInHd | hInTl
          · exact absurd (List.mem_singleton.mp hInHd) hCase
          · exact hInTl
        -- Apply IH: ih has signature
        -- ih : ∀ st auxVars st₃ aux, aux ∈ auxVars → hFold → hFoldRewrite → ∃ ...
        have hTlFold :
            tl.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a))
              ([], st_after_step) = (tl_auxVars, tl_st) := rfl
        have hIH := ih st_after_step tl_auxVars tl_st aux hAuxInTl hTlFold rfl
        rcases hIH with ⟨u', w', hPairMem, hBack1, hBack2⟩
        refine ⟨u', w', List.mem_cons_of_mem _ hPairMem, ?_, ?_⟩
        · rw [← hTlStEq]; exact hBack1
        · rw [← hTlStEq]; exact hBack2

/-- Adequacy for encodeFormula past case: σ(u) = true ↔ past φ holds.

    The new aux-variable encoding for `past φ` at world `w`:
    - For each witness w' with w'.p = w.p, we encode φ at w' getting control variable u'
    - We allocate an auxiliary variable aux for each witness representing (Mem ∧ u')
    - Clauses per witness (u', w'):
      1. Type 1: [¬Mem, ¬u', u] — (Mem ∧ u') → u
      2. Aux forward: [¬Mem, ¬u', aux] — (Mem ∧ u') → aux
      3. Aux backward 1: [¬aux, Mem] — aux → Mem
      4. Aux backward 2: [¬aux, u'] — aux → u'
    - Final clause:
      5. Type 2: [¬u, aux₁, ..., auxₙ] — u → (aux₁ ∨ ... ∨ auxₙ)

    This ensures: u ↔ (∃ i. Mem_i ∧ u'_i)
-/
lemma encodeFormula_past_adequate (b : Bounds S) (φ : Logic.Formula S)
    (w : WId b) (st : EncState b) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (ih : ∀ (w' : WId b) (st₀ : EncState b),
      let res := encodeFormula b φ w' st₀
      let uBody := res.1
      let stBody := res.2
    stBody.clauses.all (SAT.Clause.eval σ) = true →
      (σ (FVar.toVar b uBody) = true ↔
        Sat (modelOf b σ hWF) w'.p (b.decodeMaybeEvent w'.ei)
          (decodePre b σ hWF w'.ti) φ))
    (hClauses : (encodeFormula b (.past φ) w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b (encodeFormula b (.past φ) w st).1) = true) ↔
    Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti) (.past φ) := by
  classical
  -- Unfold the encoding structure
  cases hAlloc : EncState.allocFresh b st with
  | mk uControl st₁ =>
      let witnesses :=
        (WId.allWorlds b).filterMap fun w' =>
          if w'.p = w.p then some w' else none
      let step :
          List (FVar b) × EncState b → WId b → List (FVar b) × EncState b :=
        fun (uvars, stCur) w' =>
          let (u', stNext) := encodeFormula b φ w' stCur
          (uvars ++ [u'], stNext)
      let encodeWitnesses (ws : List (WId b)) (stAcc : EncState b) :
          List (FVar b) × EncState b :=
        ws.foldl step ([], stAcc)
      cases hEnc : encodeWitnesses witnesses st₁ with
      | mk witnessVars st₂ =>
          -- Define the aux step matching the encoding
          let auxStep :=
            fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
              let (u', w') := pair
              let memVar := Var.Mem w.ti w'
              let (aux, stCur) := EncState.allocFresh b acc.2
              let stCur := EncState.addClause b stCur
                [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                  SAT.Lit.pos (FVar.toVar b uControl)]
              let stCur := EncState.addClause b stCur
                [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                  SAT.Lit.pos (FVar.toVar b aux)]
              let stCur := EncState.addClause b stCur
                [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
              let stCur := EncState.addClause b stCur
                [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
              (acc.1 ++ [aux], stCur)
          cases hAux : (witnessVars.zip witnesses).foldl auxStep ([], st₂) with
          | mk auxVars st₃ =>
              let auxLits := auxVars.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))
              let st₄ := EncState.addClause b st₃ ([SAT.Lit.neg (FVar.toVar b uControl)] ++ auxLits)

              -- Show the encoding matches
              have hEncode :
                  encodeFormula b (.past φ) w st = (uControl, st₄) := by
                simp only [encodeFormula, hAlloc]
                simp only [encodeWitnesses, step] at hEnc
                have hEq1 : witnesses.foldl (fun (uvars, stCur) w' =>
                    let (u', stNext) := encodeFormula b φ w' stCur
                    (uvars ++ [u'], stNext)) ([], st₁) = (witnessVars, st₂) := by
                  convert hEnc using 2
                rw [hEq1]
                have hAuxStepEq :
                    (fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
                      let (u', w') := pair
                      let memVar := Var.Mem w.ti w'
                      let (aux, stCur) := EncState.allocFresh b acc.2
                      let stCur := EncState.addClause b stCur
                        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                          SAT.Lit.pos (FVar.toVar b uControl)]
                      let stCur := EncState.addClause b stCur
                        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                          SAT.Lit.pos (FVar.toVar b aux)]
                      let stCur := EncState.addClause b stCur
                        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
                      let stCur := EncState.addClause b stCur
                        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
                      (acc.1 ++ [aux], stCur)) = auxStep := rfl
                rw [hAuxStepEq, hAux]

              have hAll_st₄ : st₄.clauses.all (SAT.Clause.eval σ) = true := by
                have h := congrArg Prod.snd hEncode
                simpa [h] using hClauses
              have hAll := List.all_eq_true.mp hAll_st₄

              -- Helper: clause subset lemmas
              have hSub_st₂_st₃ : st₂.clauses ⊆ st₃.clauses := by
                have hAuxStepSub :
                    ∀ (acc : List (FVar b) × EncState b) pair,
                      acc.2.clauses ⊆ (auxStep acc pair).2.clauses := by
                  intro acc ⟨u', w'⟩
                  simp only [auxStep]
                  cases hAF : EncState.allocFresh b acc.2 with
                  | mk aux stCur =>
                      have hAFS : acc.2.clauses ⊆ stCur.clauses := by
                        have eq : stCur = (EncState.allocFresh b acc.2).2 := by cases hAF; rfl
                        intro c hc; rw [eq, EncState.allocFresh_clauses_eq]; exact hc
                      let c1 := [SAT.Lit.neg (Var.Mem w.ti w'),
                                  SAT.Lit.neg (FVar.toVar b u'),
                                  SAT.Lit.pos (FVar.toVar b uControl)]
                      let c2 := [SAT.Lit.neg (Var.Mem w.ti w'),
                                  SAT.Lit.neg (FVar.toVar b u'),
                                  SAT.Lit.pos (FVar.toVar b aux)]
                      let c3 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (Var.Mem w.ti w')]
                      let c4 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
                      calc acc.2.clauses
                          ⊆ stCur.clauses := hAFS
                        _ ⊆ (EncState.addClause b stCur c1).clauses :=
                            EncState.addClause_subset_clauses (b := b) stCur c1
                        _ ⊆ (EncState.addClause b (EncState.addClause b stCur c1) c2).clauses :=
                            EncState.addClause_subset_clauses (b := b) _ c2
                        _ ⊆ (EncState.addClause b
                              (EncState.addClause b
                                (EncState.addClause b stCur c1) c2) c3).clauses :=
                            EncState.addClause_subset_clauses (b := b) _ c3
                        _ ⊆ (EncState.addClause b
                              (EncState.addClause b
                                (EncState.addClause b
                                  (EncState.addClause b stCur c1) c2) c3) c4).clauses :=
                            EncState.addClause_subset_clauses (b := b) _ c4
                simpa [hAux] using
                  (foldl_subset_snd (f := auxStep) (hStep := hAuxStepSub)
                    (xs := witnessVars.zip witnesses) (init := ([], st₂)))

              have hSub_st₃_st₄ : st₃.clauses ⊆ st₄.clauses :=
                EncState.addClause_subset_clauses (b := b) st₃ _

              have hSub_st₂_st₄ : st₂.clauses ⊆ st₄.clauses :=
                List.Subset.trans hSub_st₂_st₃ hSub_st₃_st₄

              have hAll_st₂ : st₂.clauses.all (SAT.Clause.eval σ) = true :=
                all_true_of_subset hSub_st₂_st₄ hAll_st₄

              have hAll_st₃ : st₃.clauses.all (SAT.Clause.eval σ) = true :=
                all_true_of_subset hSub_st₃_st₄ hAll_st₄

              -- Length preservation
              have hStep_snd :
                  ∀ stCur w', stCur.2.clauses ⊆ (step stCur w').2.clauses := by
                intro stCur w' clause hMem
                dsimp [step] at *
                have hSub := encodeFormula_clauses_subset (b := b) (φ := φ) w' stCur.2
                exact hSub hMem

              have hLenAux :
                  ∀ ws (acc : List (FVar b)) (stAcc : EncState b),
                    (List.foldl step (acc, stAcc) ws).1.length = acc.length + ws.length := by
                intro ws
                induction ws with
                | nil => intro acc stAcc; simp [step]
                | cons w' ws ih =>
                    intro acc stAcc
                    simp [step, ih, Nat.add_comm, Nat.add_left_comm]

              have hLenVars : witnessVars.length = witnesses.length := by
                have hLenFold := hLenAux witnesses [] st₁
                have hFst : (List.foldl step ([], st₁) witnesses).1 = witnessVars := by
                  have := congrArg Prod.fst hEnc
                  simpa [encodeWitnesses, step] using this
                simpa [encodeWitnesses, step, hFst] using hLenFold

              have hLenAuxVars : auxVars.length = (witnessVars.zip witnesses).length := by
                have hAuxLenAux :
                    ∀ pairs (acc : List (FVar b)) (stAcc : EncState b),
                      (List.foldl auxStep (acc, stAcc) pairs).1.length =
                        acc.length + pairs.length := by
                  intro pairs
                  induction pairs with
                  | nil => intro acc stAcc; simp [auxStep]
                  | cons p ps ih =>
                      intro acc stAcc
                      simp only [List.foldl_cons, List.length_cons]
                      cases p with
                      | mk u' w' =>
                          simp only [auxStep]
                          cases EncState.allocFresh b stAcc with
                          | mk aux stCur =>
                              let memVar := Var.Mem w.ti w'
                              let c1 := [SAT.Lit.neg memVar,
                                          SAT.Lit.neg (FVar.toVar b u'),
                                          SAT.Lit.pos (FVar.toVar b uControl)]
                              let c2 := [SAT.Lit.neg memVar,
                                          SAT.Lit.neg (FVar.toVar b u'),
                                          SAT.Lit.pos (FVar.toVar b aux)]
                              let c3 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
                              let c4 := [SAT.Lit.neg (FVar.toVar b aux),
                                          SAT.Lit.pos (FVar.toVar b u')]
                              have := ih (acc ++ [aux])
                                (EncState.addClause b
                                  (EncState.addClause b
                                    (EncState.addClause b
                                      (EncState.addClause b stCur c1) c2) c3) c4)
                              simp [Nat.add_comm, Nat.add_left_comm] at this ⊢
                              omega
                have := hAuxLenAux (witnessVars.zip witnesses) [] st₂
                have hFst :
                    (List.foldl auxStep ([], st₂) (witnessVars.zip witnesses)).1 =
                      auxVars := by
                  have := congrArg Prod.fst hAux
                  exact this
                simp [hFst] at this
                simp only [List.length_zip]
                omega

              have hU_eq : uControl = (encodeFormula b (.past φ) w st).1 := by
                simp only [encodeFormula, hAlloc]

              constructor
              · -- Forward: σ(u) = true → Sat (past φ)
                intro hU
                rw [← hU_eq] at hU
                refine (Sat.past (modelOf b σ hWF)
                  ⟨w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti⟩ φ).2 ?_
                -- Use Type 2 clause: [¬u, aux₁, ..., auxₙ]
                have hType2In :
                    ([SAT.Lit.neg (FVar.toVar b uControl)] ++ auxLits) ∈ st₄.clauses := by
                  simp only [st₄, EncState.addClause]
                  left
                have hType2Eval :
                    Clause.eval σ ([SAT.Lit.neg (FVar.toVar b uControl)] ++ auxLits) =
                      true :=
                  hAll _ hType2In
                -- Since σ(u) = true, ¬u is false, so some aux must be true
                have hAny :=
                  (Clause.eval_eq_any (σ := σ)
                    (C := [SAT.Lit.neg (FVar.toVar b uControl)] ++ auxLits)) ▸ hType2Eval
                rcases List.any_eq_true.mp hAny with ⟨lit, hLitMem, hLitEval⟩
                -- Exclude ¬u literal
                have hLitInAux : lit ∈ auxLits := by
                  rcases List.mem_cons.mp hLitMem with hNeg | hRest
                  · -- lit = ¬u, but σ(u) = true so ¬u evaluates to false
                    have hEvalNeg :
                        SAT.Lit.eval σ (SAT.Lit.neg (FVar.toVar b uControl)) = true := by
                      simpa [hNeg] using hLitEval
                    simp [SAT.Lit.eval, hU] at hEvalNeg
                  · exact hRest
                -- lit is some SAT.Lit.pos (FVar.toVar b aux_k)
                rcases List.mem_map.mp hLitInAux with ⟨aux_k, hAuxMem, hEqLit⟩
                subst hEqLit
                have hAuxTrue : σ (FVar.toVar b aux_k) = true := by
                  simpa [SAT.Lit.eval] using hLitEval

                -- Use helper lemma to get the corresponding pair and backward clauses
                rcases auxStep_backward_clauses_in_final b w uControl
                  (witnessVars.zip witnesses) st₂ auxVars st₃ hAux aux_k hAuxMem with
                  ⟨u'_k, w'_k, hPairMem, hBackward1In, hBackward2In⟩

                have hBackward1Eval :
                    Clause.eval σ [SAT.Lit.neg (FVar.toVar b aux_k),
                      SAT.Lit.pos (Var.Mem w.ti w'_k)] = true := by
                  have hAll₃ := List.all_eq_true.mp hAll_st₃
                  exact hAll₃ _ hBackward1In

                have hMemTrue : σ (Var.Mem w.ti w'_k) = true := by
                  simp [Clause.eval, SAT.Lit.eval, hAuxTrue] at hBackward1Eval
                  exact hBackward1Eval

                have hBackward2Eval :
                    Clause.eval σ [SAT.Lit.neg (FVar.toVar b aux_k),
                      SAT.Lit.pos (FVar.toVar b u'_k)] = true := by
                  have hAll₃ := List.all_eq_true.mp hAll_st₃
                  exact hAll₃ _ hBackward2In

                have hU'True : σ (FVar.toVar b u'_k) = true := by
                  simp [Clause.eval, SAT.Lit.eval, hAuxTrue] at hBackward2Eval
                  exact hBackward2Eval

                -- w'_k has same place as w (from being in witnessVars.zip witnesses)
                have hW'InWitnesses : w'_k ∈ witnesses := by
                  exact (List.of_mem_zip hPairMem).2
                have hPlace : w'_k.p = w.p := by
                  rcases List.mem_filterMap.mp hW'InWitnesses with ⟨w'', hwAll, hOpt⟩
                  by_cases hp : w''.p = w.p
                  · have hSome : some w'' = some w'_k := by simpa [hp] using hOpt
                    have hEq : w'' = w'_k := Option.some.inj hSome
                    subst hEq; simp [hp]
                  · simp [hp] at hOpt

                -- u'_k is in witnessVars
                have hU'InVars : u'_k ∈ witnessVars := by
                  exact (List.of_mem_zip hPairMem).1

                -- Find index of w'_k in witnesses to locate encoding state
                rcases exists_split_of_mem (l := witnesses) hW'InWitnesses with ⟨as, bs, hSplit⟩
                let n := as.length
                let st_k : List (FVar b) × EncState b :=
                  List.foldl step ([], st₁) as

                -- Clauses for φ at w'_k are subset of st₂
                have hSub_step_st₂ :
                    (encodeFormula b φ w'_k st_k.2).2.clauses ⊆ st₂.clauses := by
                  have hFold_tail :
                      List.foldl step (step st_k w'_k) bs = (witnessVars, st₂) := by
                    have hEnc' : List.foldl step ([], st₁) witnesses = (witnessVars, st₂) := by
                      simpa [encodeWitnesses] using hEnc
                    simp [hSplit, step, List.foldl_append, List.foldl_cons] at hEnc'
                    exact hEnc'
                  have hTail :=
                    foldl_subset_snd (f := step) (hStep := hStep_snd)
                      (xs := bs) (init := step st_k w'_k)
                  have hTail_snd :
                      (List.foldl step (step st_k w'_k) bs).2 = st₂ := by
                    simpa using congrArg Prod.snd hFold_tail
                  have hSub_stNext_st₂ : (step st_k w'_k).2.clauses ⊆ st₂.clauses := by
                    simpa [hTail_snd] using hTail
                  simpa [step] using hSub_stNext_st₂

                have hAll_stNext :
                    (encodeFormula b φ w'_k st_k.2).2.clauses.all
                      (SAT.Clause.eval σ) = true := by
                  exact all_true_of_subset hSub_step_st₂ hAll_st₂

                -- IH gives Sat φ at w'_k
                -- First show u'_k = (encodeFormula b φ w'_k st_k.2).1
                -- This follows from the fold structure via indexing

                -- w'_k is at index n in witnesses
                have hW'_get : witnesses[n]? = some w'_k := by
                  simp [hSplit, n]

                have hnlt : n < witnesses.length := by
                  cases h : witnesses[n]?
                  · rw [hW'_get] at h; contradiction
                  · have : n < witnesses.length := by
                      by_contra hnge
                      simp [List.getElem?_eq_none_iff.2 (Nat.not_lt.1 hnge)] at h
                    exact this

                -- (u'_k, w'_k) is at index n in the zip since w'_k is at index n in witnesses
                have hPair_at_n :
                    (witnessVars.zip witnesses)[n]? = some (u'_k, w'_k) := by
                  -- Find the actual index where the pair is in the zip
                  rcases List.mem_iff_getElem?.1 hPairMem with ⟨i, hi⟩
                  -- Extract components from zip membership
                  have hZipI := (List.getElem?_zip_eq_some (l₁ := witnessVars)
                    (l₂ := witnesses) (z := (u'_k, w'_k)) (i := i)).1 hi
                  -- hZipI.2 : witnesses[i]? = some w'_k
                  -- hW'_get : witnesses[n]? = some w'_k
                  -- Need to show i = n
                  have hIeqN : i = n := by
                    -- witnesses = as ++ w'_k :: bs
                    -- witnesses[n]? = some w'_k where n = as.length
                    -- witnesses[i]? = some w'_k
                    -- w'_k appears exactly once at index n
                    have hGetI : witnesses[i]? = some w'_k := hZipI.2
                    -- If i < witnesses.length, show i = n
                    have hilt : i < witnesses.length := by
                      by_contra h
                      have hNone : witnesses[i]? = none :=
                        List.getElem?_eq_none_iff.2 (Nat.not_lt.1 h)
                      rw [hNone] at hGetI
                      exact Option.noConfusion hGetI
                    -- Use nodup directly: both hGetI and hW'_get give w'_k at indices i and n
                    have hNodup : witnesses.Nodup := witnesses_nodup b w
                    rcases List.getElem?_eq_some_iff.1 hGetI with ⟨hi, hGet_i'⟩
                    rcases List.getElem?_eq_some_iff.1 hW'_get with ⟨hn, hGet_n'⟩
                    -- Convert bracket notation to get with Fin
                    have hGet_i_fin : witnesses.get ⟨i, hi⟩ = w'_k := hGet_i'
                    have hGet_n_fin : witnesses.get ⟨n, hn⟩ = w'_k := hGet_n'
                    have hGetEq : witnesses.get ⟨i, hi⟩ = witnesses.get ⟨n, hn⟩ :=
                      hGet_i_fin.trans hGet_n_fin.symm
                    -- get_inj_iff : l.get i = l.get j ↔ i = j
                    have hFin_eq : (⟨i, hi⟩ : Fin witnesses.length) = ⟨n, hn⟩ :=
                      (List.Nodup.get_inj_iff hNodup (i := ⟨i, hi⟩) (j := ⟨n, hn⟩)).1 hGetEq
                    exact congrArg Fin.val hFin_eq
                  subst hIeqN
                  exact hi

                have hU'_get : witnessVars[n]? = some u'_k := by
                  have hnlt' : n < witnessVars.length := by simpa [hLenVars] using hnlt
                  have hZip :=
                    (List.getElem?_zip_eq_some (l₁ := witnessVars) (l₂ := witnesses)
                      (z := (u'_k, w'_k)) (i := n)).1 hPair_at_n
                  simpa using hZip.1

                -- The fold structure gives
                -- witnessVars[n] = (encodeFormula b φ witnesses[n] st_k.2).1
                have hFold_append_inner :
                    ∀ (xs : List (FVar b)) (stAcc : EncState b) (ws : List (WId b)),
                      List.foldl step (xs, stAcc) ws =
                        (xs ++ (List.foldl step ([], stAcc) ws).1,
                          (List.foldl step ([], stAcc) ws).2) := by
                  intro xs stAcc ws
                  induction ws generalizing xs stAcc with
                  | nil => simp [step]
                  | cons w' ws ih' =>
                      simp only [List.foldl_cons, step]
                      cases hRes : encodeFormula b φ w' stAcc with
                      | mk u'' stNext =>
                          change List.foldl step (xs ++ [u''], stNext) ws =
                            (xs ++ (List.foldl step ([u''], stNext) ws).1,
                              (List.foldl step ([u''], stNext) ws).2)
                          have hIH := ih' (xs := xs ++ [u'']) (stAcc := stNext)
                          have hIH' := ih' (xs := [u'']) (stAcc := stNext)
                          simp only at hIH'
                          -- hIH': foldl step ([u''], stNext) ws =
                          --   ([u''] ++ (foldl step ([], stNext) ws).1, ...)
                          -- Rewrite goal using hIH' to replace (foldl step ([u''], stNext) ws)
                          rw [hIH']
                          convert hIH using 2; simp only [List.append_assoc]

                have hLen_prefix : st_k.1.length = n := by
                  have hLen := hLenAux as [] st₁
                  simpa [st_k, n] using hLen

                set resW := encodeFormula b φ w'_k st_k.2 with hResW

                have hFold_tail' :
                    List.foldl step (step st_k w'_k) bs = (witnessVars, st₂) := by
                  have hEnc' : List.foldl step ([], st₁) witnesses = (witnessVars, st₂) := by
                    simpa [encodeWitnesses] using hEnc
                  simp [hSplit, step, List.foldl_append, List.foldl_cons] at hEnc'
                  exact hEnc'

                have hVars_append :
                    witnessVars =
                      st_k.1 ++ resW.1 ::
                        (List.foldl step ([], resW.2) bs).1 := by
                  have hFst := congrArg Prod.fst hFold_tail'
                  simp [step] at hFst
                  have hDecomp :=
                    congrArg Prod.fst
                      (hFold_append_inner (xs := st_k.1 ++ [resW.1])
                        (stAcc := resW.2) (ws := bs))
                  have hEq := Eq.trans hFst.symm hDecomp
                  simp [List.append_assoc] at hEq
                  simpa using hEq

                have hGet_append_len_inner :
                    ∀ {α} (xs ys : List α),
                      (xs ++ ys)[xs.length]? = ys[0]? := by
                  intro α xs ys
                  induction xs with
                  | nil => simp
                  | cons _ xs ih => simpa using ih

                have hGet_resW :
                    witnessVars[n]? = some resW.1 := by
                  have hLen : st_k.1.length = n := hLen_prefix
                  have hIdx :=
                    hGet_append_len_inner (xs := st_k.1)
                      (ys := resW.1 :: (List.foldl step ([], resW.2) bs).1)
                  have hIdx' :
                      (st_k.1 ++ resW.1 ::
                        (List.foldl step ([], resW.2) bs).1)[n]? =
                        some resW.1 := by
                    simp [hLen]
                  simpa [hVars_append] using hIdx'

                have hVar_eq : (encodeFormula b φ w'_k st_k.2).1 = u'_k := by
                  have hEqSome : some u'_k = some resW.1 := by
                    rw [← hU'_get, ← hGet_resW]
                  have hEq : u'_k = resW.1 := Option.some.inj hEqSome
                  simp [resW, hEq]

                have hU'AtEnc :
                    σ (FVar.toVar b (encodeFormula b φ w'_k st_k.2).1) = true := by
                  rw [hVar_eq]
                  exact hU'True

                have hIff := ih w'_k st_k.2 hAll_stNext
                have hSatBody :
                    Sat (modelOf b σ hWF) w'_k.p (b.decodeMaybeEvent w'_k.ei)
                      (decodePre b σ hWF w'_k.ti) φ :=
                  hIff.mp hU'AtEnc

                -- Membership in prehistory
                have hMemIn :
                    (w'_k.p, b.decodeMaybeEvent w'_k.ei,
                      decodePre b σ hWF w'_k.ti) ∈
                      decodePre b σ hWF w.ti :=
                  mem_decodePre_of_memVar b σ hWF w.ti w'_k hMemTrue

                -- Construct the semantic witness
                refine ⟨⟨w'_k.p, b.decodeMaybeEvent w'_k.ei, decodePre b σ hWF w'_k.ti⟩,
                        hMemIn, hPlace, hSatBody⟩

              · -- Backward: Sat (past φ) → σ(u) = true
                intro hSat
                rcases (Sat.past (modelOf b σ hWF)
                  ⟨w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti⟩ φ).1 hSat with
                  ⟨t, htMem, htPlace, hSatφ⟩
                -- Extract witness world
                rcases (mem_decodePre_iff_memVar b σ hWF w.ti t).1 htMem with
                  ⟨wWitness, hMemVar, hEq⟩
                have hPlace : wWitness.p = w.p := by
                  have : t.place = w.p := htPlace
                  rw [← hEq] at this
                  exact this
                -- wWitness is in witnesses
                have hWitnessMem : wWitness ∈ witnesses := by
                  have hAll := WId.mem_allWorlds b wWitness
                  simp [witnesses, hPlace, hAll]
                -- Find index
                rcases exists_split_of_mem (l := witnesses) hWitnessMem with ⟨as, bs, hSplit⟩
                let n := as.length
                have hWitness_get : witnesses[n]? = some wWitness := by
                  simp [hSplit, n]
                have hnlt : n < witnesses.length := by
                  cases h : witnesses[n]?
                  · rw [hWitness_get] at h; contradiction
                  · have : n < witnesses.length := by
                      by_contra hnge
                      simp [List.getElem?_eq_none_iff.2 (Nat.not_lt.1 hnge)] at h
                    exact this

                let uWitness : FVar b := witnessVars.get ⟨n, by simpa [hLenVars] using hnlt⟩
                let witnessPairs := witnessVars.zip witnesses

                have hPair_get? :
                    witnessPairs[n]? = some (uWitness, wWitness) := by
                  have hVars_get : witnessVars[n]? = some uWitness := by
                    have hnlt' : n < witnessVars.length := by simpa [hLenVars] using hnlt
                    simp [uWitness, hnlt']
                  have hZip :=
                    (List.getElem?_zip_eq_some (l₁ := witnessVars) (l₂ := witnesses)
                        (z := (uWitness, wWitness)) (i := n)).2
                      ⟨by simpa using hVars_get, by simpa using hWitness_get⟩
                  simpa [witnessPairs] using hZip

                have hPair_mem : (uWitness, wWitness) ∈ witnessPairs :=
                  (List.mem_iff_getElem?).2 ⟨n, hPair_get?⟩

                -- Type 1 clause [¬Mem, ¬u', u] gives u = true when Mem and u' are true
                have hType1In :
                    [SAT.Lit.neg (Var.Mem w.ti wWitness),
                     SAT.Lit.neg (FVar.toVar b uWitness),
                     SAT.Lit.pos (FVar.toVar b uControl)] ∈ st₃.clauses := by
                  have hExists :=
                    foldl_exists_state_subset_snd
                      (f := auxStep)
                      (hStep := by
                        intro acc pair
                        cases pair with
                        | mk u' w' =>
                            simp only [auxStep]
                            cases hAF : EncState.allocFresh b acc.2 with
                            | mk aux stCur =>
                                have hAFS : acc.2.clauses ⊆ stCur.clauses := by
                                  have eq : stCur = (EncState.allocFresh b acc.2).2 := by
                                    cases hAF; rfl
                                  intro c hc
                                  rw [eq, EncState.allocFresh_clauses_eq]; exact hc
                                let memVar := Var.Mem w.ti w'
                                let c1 := [SAT.Lit.neg memVar,
                                            SAT.Lit.neg (FVar.toVar b u'),
                                            SAT.Lit.pos (FVar.toVar b uControl)]
                                let c2 := [SAT.Lit.neg memVar,
                                            SAT.Lit.neg (FVar.toVar b u'),
                                            SAT.Lit.pos (FVar.toVar b aux)]
                                let c3 := [SAT.Lit.neg (FVar.toVar b aux),
                                            SAT.Lit.pos memVar]
                                let c4 := [SAT.Lit.neg (FVar.toVar b aux),
                                            SAT.Lit.pos (FVar.toVar b u')]
                                calc acc.2.clauses
                                    ⊆ stCur.clauses := hAFS
                                  _ ⊆ (EncState.addClause b stCur c1).clauses :=
                                      EncState.addClause_subset_clauses (b := b) _ _
                                  _ ⊆ (EncState.addClause b
                                        (EncState.addClause b stCur c1) c2).clauses :=
                                      EncState.addClause_subset_clauses (b := b) _ _
                                  _ ⊆ (EncState.addClause b
                                        (EncState.addClause b
                                          (EncState.addClause b stCur c1) c2) c3).clauses :=
                                      EncState.addClause_subset_clauses (b := b) _ _
                                  _ ⊆ (EncState.addClause b
                                        (EncState.addClause b
                                          (EncState.addClause b
                                            (EncState.addClause b stCur c1) c2) c3) c4).clauses :=
                                      EncState.addClause_subset_clauses (b := b) _ _)
                      (xs := witnessPairs) (x := (uWitness, wWitness)) (init := ([], st₂)) hPair_mem
                  rcases hExists with ⟨st_k', hSubset⟩
                  have hClauseIn :
                      [SAT.Lit.neg (Var.Mem w.ti wWitness),
                       SAT.Lit.neg (FVar.toVar b uWitness),
                       SAT.Lit.pos (FVar.toVar b uControl)] ∈
                        (auxStep st_k' (uWitness, wWitness)).2.clauses := by
                    simp only [auxStep]
                    cases EncState.allocFresh b st_k'.2 with
                    | mk aux stCur =>
                        simp [EncState.addClause]
                  -- Connect the fold result to st₃ using hAux
                  have hFoldEq : (List.foldl auxStep ([], st₂) witnessPairs).2 = st₃ := by
                    rw [hAux]
                  rw [← hFoldEq]
                  exact hSubset hClauseIn

                have hType1Eval :
                    Clause.eval σ [SAT.Lit.neg (Var.Mem w.ti wWitness),
                      SAT.Lit.neg (FVar.toVar b uWitness),
                      SAT.Lit.pos (FVar.toVar b uControl)] = true := by
                  have hAll₃ := List.all_eq_true.mp hAll_st₃
                  exact hAll₃ _ hType1In

                -- Need σ(uWitness) = true from IH
                -- First find the state after encoding witnesses up to wWitness
                let st_k : List (FVar b) × EncState b :=
                  List.foldl step ([], st₁) as

                -- Clauses for φ at wWitness are subset of st₂
                have hSub_step_st₂ :
                    (encodeFormula b φ wWitness st_k.2).2.clauses ⊆ st₂.clauses := by
                  have hFold_tail :
                      List.foldl step (step st_k wWitness) bs = (witnessVars, st₂) := by
                    have hEnc' : List.foldl step ([], st₁) witnesses = (witnessVars, st₂) := by
                      simpa [encodeWitnesses] using hEnc
                    simp [hSplit, step, List.foldl_append, List.foldl_cons] at hEnc'
                    exact hEnc'
                  have hTail :=
                    foldl_subset_snd (f := step) (hStep := hStep_snd)
                      (xs := bs) (init := step st_k wWitness)
                  have hTail_snd :
                      (List.foldl step (step st_k wWitness) bs).2 = st₂ := by
                    simpa using congrArg Prod.snd hFold_tail
                  have hSub_stNext_st₂ : (step st_k wWitness).2.clauses ⊆ st₂.clauses := by
                    simpa [hTail_snd] using hTail
                  simpa [step] using hSub_stNext_st₂

                have hAll_stNext :
                    (encodeFormula b φ wWitness st_k.2).2.clauses.all
                      (SAT.Clause.eval σ) = true := by
                  exact all_true_of_subset hSub_step_st₂ hAll_st₂

                -- Use IH backward: Sat φ at wWitness → σ(u') = true
                -- First transform hSatφ to use wWitness coordinates
                have hSatBody :
                    Sat (modelOf b σ hWF) wWitness.p (b.decodeMaybeEvent wWitness.ei)
                      (decodePre b σ hWF wWitness.ti) φ := by
                  have hEqSymm :
                    t = ⟨wWitness.p, b.decodeMaybeEvent wWitness.ei,
                          decodePre b σ hWF wWitness.ti⟩ := hEq.symm
                  rw [hEqSymm] at hSatφ
                  exact hSatφ

                have hIff := ih wWitness st_k.2 hAll_stNext

                -- Show uWitness = (encodeFormula b φ wWitness st_k.2).1
                -- This follows the same indexing pattern as the forward direction
                have hLen_prefix : st_k.1.length = n := by
                  have hLen := hLenAux as [] st₁
                  simpa [st_k, n] using hLen

                -- Fold append lemma (same as forward direction)
                have hFold_append_inner_bwd :
                    ∀ (xs : List (FVar b)) (stAcc : EncState b) (ws : List (WId b)),
                      List.foldl step (xs, stAcc) ws =
                        (xs ++ (List.foldl step ([], stAcc) ws).1,
                          (List.foldl step ([], stAcc) ws).2) := by
                  intro xs stAcc ws
                  induction ws generalizing xs stAcc with
                  | nil => simp [step]
                  | cons w' ws ih' =>
                      simp only [List.foldl_cons, step]
                      cases hRes : encodeFormula b φ w' stAcc with
                      | mk u'' stNext =>
                          change List.foldl step (xs ++ [u''], stNext) ws =
                            (xs ++ (List.foldl step ([u''], stNext) ws).1,
                              (List.foldl step ([u''], stNext) ws).2)
                          have hIH := ih' (xs := xs ++ [u'']) (stAcc := stNext)
                          have hIH' := ih' (xs := [u'']) (stAcc := stNext)
                          rw [hIH']
                          convert hIH using 2; simp only [List.append_assoc]

                set resW := encodeFormula b φ wWitness st_k.2 with hResW
                have hFold_tail' :
                    List.foldl step (step st_k wWitness) bs = (witnessVars, st₂) := by
                  have hEnc' : List.foldl step ([], st₁) witnesses = (witnessVars, st₂) := by
                    simpa [encodeWitnesses] using hEnc
                  simp [hSplit, step, List.foldl_append, List.foldl_cons] at hEnc'
                  exact hEnc'
                have hVars_append :
                    witnessVars =
                      st_k.1 ++ resW.1 ::
                        (List.foldl step ([], resW.2) bs).1 := by
                  have hFst := congrArg Prod.fst hFold_tail'
                  simp [step] at hFst
                  have hDecomp :=
                    congrArg Prod.fst
                      (hFold_append_inner_bwd (xs := st_k.1 ++ [resW.1])
                        (stAcc := resW.2) (ws := bs))
                  have hEq := Eq.trans hFst.symm hDecomp
                  simp [List.append_assoc] at hEq
                  simpa using hEq
                have hGet_resW :
                    witnessVars[n]? = some resW.1 := by
                  have hLen : st_k.1.length = n := hLen_prefix
                  have hIdx' :
                      (st_k.1 ++ resW.1 ::
                        (List.foldl step ([], resW.2) bs).1)[n]? =
                        some resW.1 := by
                    simp [hLen]
                  simpa [hVars_append] using hIdx'
                have hVars_get : witnessVars[n]? = some uWitness := by
                  have hnlt' : n < witnessVars.length := by simpa [hLenVars] using hnlt
                  simp [uWitness, hnlt']
                have hVar_eq : (encodeFormula b φ wWitness st_k.2).1 = uWitness := by
                  have hEqSome : some uWitness = some resW.1 := by
                    rw [← hVars_get, ← hGet_resW]
                  have hEq : uWitness = resW.1 := Option.some.inj hEqSome
                  simp [resW, hEq]

                have hUWitnessTrue : σ (FVar.toVar b uWitness) = true := by
                  have hEncTrue := hIff.2 hSatBody
                  rw [← hVar_eq]
                  exact hEncTrue

                -- From Type 1 clause: (Mem ∧ uWitness) → uControl
                have hUControl : σ (FVar.toVar b uControl) = true := by
                  simp [Clause.eval, SAT.Lit.eval, hUWitnessTrue] at hType1Eval
                  cases hType1Eval with
                  | inl h =>
                      -- h : σ (Var.Mem w.ti wWitness) = false
                      -- but hMemVar : σ (Var.Mem w.ti wWitness) = true
                      have : False := by rw [hMemVar] at h; exact Bool.noConfusion h
                      cases this
                  | inr h => exact h

                rw [← hU_eq]
                exact hUControl

end Encoding
