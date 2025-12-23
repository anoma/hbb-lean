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
# Tseytin Correctness for AtEnd (atEnd)

This file proves that the Tseytin encoding correctly captures the semantics of
atEnd formulas.

## Main Result

- `encode_atEnd_correct`: If the encoding produces control variable u for atEnd φ
  with sub-control u', then u = true iff u' = true.

## Strategy

The atEnd encoding simply creates a bi-conditional u ↔ u' where u' encodes φ
at the end world (participant p, event †, root prehistory).

This uses two clauses:
- [¬u, u']: if u then u'
- [¬u', u]: if u' then u

Together these enforce u ↔ u'.
-/

open ModalDistribution Encoding Logic

namespace Encoding

variable {S : Signature}

/-! ## Tseytin Correctness for AtEnd -/

/-- The atEnd encoding produces u ↔ u'.

    Forward direction: if u = true, then u' = true. -/
lemma encode_atEnd_forward (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u u' : FVar b) (clauses : List (SAT.Clause (Var b)))
    (hEncoding : clauses =
      [[SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b u')],
       [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true)
    (hU : σ (FVar.toVar b u) = true) :
    σ (FVar.toVar b u') = true := by
  -- The first clause is [¬u, u']
  -- If σ(u) = true and the clause is satisfied, then σ(u') = true
  have hClauseIn :
      [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b u')] ∈ clauses := by
    rw [hEncoding]
    simp

  have hClauseTrue : SAT.Clause.eval σ
      [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b u')] = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Evaluate the clause
  unfold SAT.Clause.eval at hClauseTrue
  simp [SAT.Lit.eval, hU] at hClauseTrue
  exact hClauseTrue

/-- The atEnd encoding produces u ↔ u'.

    Backward direction: if u' = true, then u = true. -/
lemma encode_atEnd_backward (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u u' : FVar b) (clauses : List (SAT.Clause (Var b)))
    (hEncoding : clauses =
      [[SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b u')],
       [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true)
    (hU' : σ (FVar.toVar b u') = true) :
    σ (FVar.toVar b u) = true := by
  -- The second clause is [¬u', u]
  -- If σ(u') = true and the clause is satisfied, then σ(u) = true
  have hClauseIn :
      [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b u)] ∈ clauses := by
    rw [hEncoding]
    simp

  have hClauseTrue : SAT.Clause.eval σ
      [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b u)] = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Evaluate the clause
  unfold SAT.Clause.eval at hClauseTrue
  simp [SAT.Lit.eval, hU'] at hClauseTrue
  exact hClauseTrue

/-- Main correctness: σ(u) = true ↔ σ(u') = true.

    The atEnd encoding correctly captures the bi-conditional. -/
lemma encode_atEnd_correct (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u u' : FVar b) (clauses : List (SAT.Clause (Var b)))
    (hEncoding : clauses =
      [[SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b u')],
       [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b u) = true) ↔ (σ (FVar.toVar b u') = true) := by
  constructor
  · exact encode_atEnd_forward b σ u u' clauses hEncoding hSat
  · exact encode_atEnd_backward b σ u u' clauses hEncoding hSat

variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]
variable [DecidableEq S.Value]

/-- Adequacy for encodeFormula atEnd case: σ(u) = true ↔ atEnd φ holds. -/
lemma encodeFormula_atEnd_adequate (b : Bounds S) (φ : Logic.Formula S)
    (w : WId b) (st : EncState b) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (ih : ∀ st₀ : EncState b,
      let res := encodeFormula b φ ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st₀
      let uBody := res.1
      let stBody := res.2
      stBody.clauses.all (SAT.Clause.eval σ) = true →
        (σ (FVar.toVar b uBody) = true ↔
          Sat (modelOf b σ hWF) w.p † (decodePre b σ hWF b.root) φ))
    (hClauses : (encodeFormula b (.atEnd φ) w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b (encodeFormula b (.atEnd φ) w st).1) = true) ↔
    Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti) (.atEnd φ) := by
  constructor
  · -- Forward: σ(u) = true → atEnd φ holds
    intro hU
    classical
    -- Canonical world at the end of the history for participant w.p
    set wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
    -- Unfold the encoding to expose the sub-encoding and the two Tseytin clauses
    set bodyRes := encodeFormula b φ wEnd st with hBody
    rcases bodyRes with ⟨uBody, stBody⟩
    set allocRes := EncState.allocFresh b stBody with hAlloc
    rcases allocRes with ⟨u, st2⟩
    have hEncode :
        encodeFormula b (.atEnd φ) w st =
          (u,
            EncState.addClause b
              (EncState.addClause b st2
                [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
              [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)]) := by
      simp only [encodeFormula]
      congr 1
      · rw [← hBody, ← hAlloc]
      · rw [← hBody, ← hAlloc]
    have hClauses' :
        (EncState.addClause b
            (EncState.addClause b st2
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
            [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)]).clauses.all
              (SAT.Clause.eval σ) = true := by
      simpa [hEncode] using hClauses
    -- Extract the all-true evidence for the sub-encoding
    have hBodyClauses : stBody.clauses.all (SAT.Clause.eval σ) = true := by
      -- Clauses are preserved by allocFresh and grow monotonically via addClause
      have hClauseEq : st2.clauses = stBody.clauses := by
        have := EncState.allocFresh_clauses_eq b stBody
        rw [← hAlloc] at this
        exact this
      have hSubset1 : stBody.clauses ⊆ st2.clauses := by
        simp [hClauseEq]
      have hSubset2 : st2.clauses ⊆
          (EncState.addClause b st2
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]).clauses :=
        EncState.addClause_subset_clauses
          (b := b) (st := st2)
          (clause := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
      have hSubset3 :
          (EncState.addClause b st2
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]).clauses ⊆
            (EncState.addClause b
              (EncState.addClause b st2
                [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
              [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)]).clauses :=
        EncState.addClause_subset_clauses
          (b := b)
          (st := EncState.addClause b st2
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
          (clause := [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)])
      exact
        all_true_of_subset
          (show stBody.clauses ⊆ _ from
            List.Subset.trans hSubset1 (List.Subset.trans hSubset2 hSubset3))
          hClauses'
    -- Use the Tseytin clause [¬u, uBody] to deduce σ(uBody)=true
    have hAll := List.all_eq_true.mp hClauses'
    have hClauseForward :
        SAT.Clause.eval σ
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)] = true := by
      have hMem :
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)] ∈
            (EncState.addClause b st2
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]).clauses := by
        simp [EncState.addClause]
      -- This clause is the tail of the final clause list
      have hMemFinal :
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)] ∈
            (EncState.addClause b
              (EncState.addClause b st2
                [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
              [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)]).clauses := by
        simp [EncState.addClause]
      exact hAll _ hMemFinal
    have hUBody : σ (FVar.toVar b uBody) = true := by
      have hU' : σ (FVar.toVar b u) = true := by
        have := congr_arg Prod.fst hEncode
        simp at this
        rw [← this]
        exact hU
      unfold SAT.Clause.eval SAT.Lit.eval at hClauseForward
      simp [hU'] at hClauseForward
      exact hClauseForward
    -- Apply the induction hypothesis to the sub-encoding at the canonical world
    have hBodyClauses' : (encodeFormula b φ wEnd st).2.clauses.all (SAT.Clause.eval σ) = true := by
      rw [← hBody]
      exact hBodyClauses
    have hIh : (σ (FVar.toVar b uBody) = true) ↔
        Sat (modelOf b σ hWF) w.p † (decodePre b σ hWF b.root) φ := by
      have := ih st hBodyClauses'
      rw [← hBody] at this
      simp at this
      exact this
    have hSatBody :
        Sat (modelOf b σ hWF) w.p † (decodePre b σ hWF b.root) φ := by
      apply hIh.mp
      exact hUBody
    -- Semantics of atEnd ignores the current event/history
    unfold Sat
    simpa [modelOf] using hSatBody
  · -- Backward: atEnd φ holds → σ(u) = true
    intro hSat
    classical
    set wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
    set bodyRes := encodeFormula b φ wEnd st with hBody
    rcases bodyRes with ⟨uBody, stBody⟩
    set allocRes := EncState.allocFresh b stBody with hAlloc
    rcases allocRes with ⟨u, st2⟩
    have hEncode :
        encodeFormula b (.atEnd φ) w st =
          (u,
            EncState.addClause b
              (EncState.addClause b st2
                [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
              [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)]) := by
      simp only [encodeFormula]
      congr 1
      · rw [← hBody, ← hAlloc]
      · rw [← hBody, ← hAlloc]
    have hClauses' :
        (EncState.addClause b
            (EncState.addClause b st2
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
            [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)]).clauses.all
              (SAT.Clause.eval σ) = true := by
      simpa [hEncode] using hClauses
    -- Extract clause truths as before
    have hAll := List.all_eq_true.mp hClauses'
    have hClauseBackward :
        SAT.Clause.eval σ
            [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)] = true := by
      have hMem :
          [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)] ∈
            (EncState.addClause b
              (EncState.addClause b st2
                [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
              [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)]).clauses := by
        simp [EncState.addClause]
      exact hAll _ hMem
    -- As before, infer that the sub-encoding clauses all hold
    have hBodyClauses : stBody.clauses.all (SAT.Clause.eval σ) = true := by
      have hClauseEq : st2.clauses = stBody.clauses := by
        have := EncState.allocFresh_clauses_eq b stBody
        rw [← hAlloc] at this
        exact this
      have hSubset1 : stBody.clauses ⊆ st2.clauses := by
        simp [hClauseEq]
      have hSubset2 : st2.clauses ⊆
          (EncState.addClause b st2
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]).clauses :=
        EncState.addClause_subset_clauses
          (b := b) (st := st2)
          (clause := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
      have hSubset3 :
          (EncState.addClause b st2
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]).clauses ⊆
            (EncState.addClause b
              (EncState.addClause b st2
                [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
              [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)]).clauses :=
        EncState.addClause_subset_clauses
          (b := b)
          (st := EncState.addClause b st2
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
          (clause := [SAT.Lit.neg (FVar.toVar b uBody), SAT.Lit.pos (FVar.toVar b u)])
      exact
        all_true_of_subset
          (show stBody.clauses ⊆ _ from
            List.Subset.trans hSubset1 (List.Subset.trans hSubset2 hSubset3))
          hClauses'
    -- IH: semantic assumption implies σ(uBody)=true
    have hBodyClauses' : (encodeFormula b φ wEnd st).2.clauses.all (SAT.Clause.eval σ) = true := by
      rw [← hBody]
      exact hBodyClauses
    have hIh : (σ (FVar.toVar b uBody) = true) ↔
        Sat (modelOf b σ hWF) w.p † (decodePre b σ hWF b.root) φ := by
      have := ih st hBodyClauses'
      rw [← hBody] at this
      simp at this
      exact this
    have hUBody : σ (FVar.toVar b uBody) = true := by
      apply hIh.mpr
      -- Sat (.atEnd φ) gives Sat φ at the canonical root world
      unfold Sat at hSat
      simpa [modelOf] using hSat
    -- Finally evaluate the backward clause to conclude σ(u)=true
    have hU : σ (FVar.toVar b u) = true := by
      unfold SAT.Clause.eval at hClauseBackward
      simp [SAT.Lit.eval, hUBody] at hClauseBackward
      exact hClauseBackward
    rw [hEncode]
    exact hU

end Encoding
