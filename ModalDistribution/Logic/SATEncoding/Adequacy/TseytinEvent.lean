import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.PreEqEncoding
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly
import ModalDistribution.Logic.SATEncoding.PreEqCompleteness
import ModalDistribution.Logic.SATEncoding.PreEqSoundness

/-!
# Tseytin Correctness for Event Formulas

This file proves that the Tseytin encoding correctly captures the semantics of
event formulas using PreEq to relate time indices with equal decoded prehistories.

## Main Result

- `encodeFormula_event_adequate`: The encoding of `event atom` at world `w` produces
  a control variable `u` such that `σ(u) = true` iff the event formula holds
  semantically at world `w` in the extracted model.

## Strategy

Event formulas are evaluated at a world with components `(w.p, evt, H)`.
The semantics checks whether there exists a witness world-id `w'` such that:
- `w'.p = w.p` (same participant)
- `decodeMaybeEvent w'.ei = some evt` (event component matches)
- `decodePre b σ w'.ti = decodePre b σ w.ti` (prehistory matches via PreEq)
- The world is in the model's history (Mem(root, w'))

The encoding creates:
1. For each potential witness `w'`: `z_{w'} ↔ (PreEq(w.ti, w'.ti) ∧ Mem(root, w'))`
2. Final control: `u ↔ (∨ z_{w'})`

This uses PreEq to relate time indices that decode to the same prehistory.
-/

open ModalDistribution Encoding Logic PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]
variable [DecidableEq S.Value]

/-! ## Helper Lemmas for mkMemEq -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The mkMemEq gadget encodes `eqb ↔ (Mem(H,w) = Mem(H',w))`.

    Forward direction: eqb = true implies membership bits are equal. -/
lemma mkMemEq_adequate_forward
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (H H' : b.times) (w : WId b) (st : EncState b)
    (hClauses : (mkMemEq b H H' w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hEqb : σ (FVar.toVar b (mkMemEq b H H' w st).1) = true) :
    σ (Var.Mem H w) = σ (Var.Mem H' w) := by
  -- mkMemEq creates 4 Tseytin clauses implementing eqb ↔ (memH = memH')
  -- Clause 1: [¬eqb, ¬memH, memH']    (eqb ∧ memH → memH')
  -- Clause 2: [¬eqb, memH, ¬memH']    (eqb ∧ ¬memH → ¬memH')
  -- From eqb = true, these clauses force memH = memH'

  -- Unfold mkMemEq definition to expose the clauses
  unfold mkMemEq at hClauses hEqb

  -- Extract the allocated variable and the intermediate states
  cases hAlloc : EncState.allocFresh b st with
  | mk eqb st1 =>
      -- Simplify using the allocation
      simp only [hAlloc] at hEqb hClauses

      -- Define the membership variables for clarity
      let memH  := Var.Mem H w
      let memH' := Var.Mem H' w

      -- Convert List.all to forall
      have hAllClauses := List.all_eq_true.mp hClauses

      -- Reason about Boolean values: memH and memH' are Bools
      cases hMemH : σ memH <;> cases hMemH' : σ memH'
      · -- Both false: this is consistent
        rfl
      · -- memH = false, memH' = true: contradicts clause 2
        exfalso
        -- Clause 2: [¬eqb, memH, ¬memH'] added at second addClause
        let clause2 := [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos memH, SAT.Lit.neg memH']
        -- Show clause2 is in the final clause list
        have hMem2 : clause2 ∈
            (EncState.addClause b
              (EncState.addClause b
                (EncState.addClause b
                  (EncState.addClause b st1
                    [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg memH, SAT.Lit.pos memH'])
                  clause2)
                [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.pos memH, SAT.Lit.pos memH'])
              [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.neg memH, SAT.Lit.neg memH']).clauses := by
          simp [EncState.addClause]
        have hClause2 := hAllClauses clause2 hMem2
        -- Evaluate clause2: [¬eqb, memH, ¬memH']
        -- With eqb=true, memH=false, memH'=true, all literals are false
        simp only [clause2, SAT.Clause.eval, SAT.Lit.eval, List.foldl] at hClause2
        simp only [hEqb, hMemH, hMemH', Bool.not_true, Bool.or_false] at hClause2
        cases hClause2
      · -- memH = true, memH' = false: contradicts clause 1
        exfalso
        -- Clause 1: [¬eqb, ¬memH, memH'] added at first addClause
        let clause1 := [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg memH, SAT.Lit.pos memH']
        -- Show clause1 is in the final clause list
        have hMem1 : clause1 ∈
            (EncState.addClause b
              (EncState.addClause b
                (EncState.addClause b
                  (EncState.addClause b st1
                    clause1)
                  [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos memH, SAT.Lit.neg memH'])
                [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.pos memH, SAT.Lit.pos memH'])
              [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.neg memH, SAT.Lit.neg memH']).clauses := by
          simp [EncState.addClause]
        have hClause1 := hAllClauses clause1 hMem1
        -- Evaluate clause1: [¬eqb, ¬memH, memH']
        -- With eqb=true, memH=true, memH'=false, all literals are false
        simp only [clause1, SAT.Clause.eval, SAT.Lit.eval, List.foldl] at hClause1
        simp only [hEqb, hMemH, hMemH', Bool.not_true, Bool.or_false] at hClause1
        cases hClause1
      · -- Both true: this is consistent
        rfl

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Backward direction: equal membership bits imply eqb = true. -/
lemma mkMemEq_adequate_backward
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (H H' : b.times) (w : WId b) (st : EncState b)
    (hClauses : (mkMemEq b H H' w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hMem : σ (Var.Mem H w) = σ (Var.Mem H' w)) :
    σ (FVar.toVar b (mkMemEq b H H' w st).1) = true := by
  unfold mkMemEq at hClauses ⊢
  cases hAlloc : EncState.allocFresh b st with
  | mk eqb st1 =>
      simp only [hAlloc] at hClauses ⊢
      let memH  := Var.Mem H w
      let memH' := Var.Mem H' w
      let clause₁ :=
        [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg memH, SAT.Lit.pos memH']
      let clause₂ :=
        [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos memH, SAT.Lit.neg memH']
      let clause₃ :=
        [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.pos memH, SAT.Lit.pos memH']
      let clause₄ :=
        [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.neg memH, SAT.Lit.neg memH']
      have hAllClauses :
          ∀ clause ∈
              (EncState.addClause b
                (EncState.addClause b
                  (EncState.addClause b
                    (EncState.addClause b st1 clause₁) clause₂)
                  clause₃)
                clause₄).clauses,
                SAT.Clause.eval σ clause = true :=
        List.all_eq_true.mp
          (by
            simpa [EncState.addClause, clause₁, clause₂, clause₃, clause₄] using hClauses)
      cases hMemH : σ memH
      · -- Both membership bits are false, so clause₃ forces eqb = true
        have hMemH' : σ memH' = false := by
          simpa [hMemH] using (hMem ▸ hMemH)
        have hClause₃ :
            SAT.Clause.eval σ clause₃ = true :=
          hAllClauses clause₃ (by
            simp [EncState.addClause, clause₁, clause₂, clause₃, clause₄])
        simpa [clause₃, SAT.Clause.eval, SAT.Lit.eval, List.foldl,
               hMemH, hMemH', Bool.false_or, Bool.or_false,
               Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
          using hClause₃
      · -- Both membership bits are true, so clause₄ forces eqb = true
        have hMemH' : σ memH' = true := by
          simpa [hMemH] using (hMem ▸ hMemH)
        have hClause₄ :
            SAT.Clause.eval σ clause₄ = true :=
          hAllClauses clause₄ (by
            simp [EncState.addClause, clause₁, clause₂, clause₃, clause₄])
        simpa [clause₄, SAT.Clause.eval, SAT.Lit.eval, List.foldl,
               hMemH, hMemH', Bool.false_or, Bool.or_false,
               Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
          using hClause₄


/-! ## Helper Lemmas for PreEq -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If all membership bits are equal, then decoded prehistories are equal.

    This is the core property: decodePre depends only on membership bits. -/
lemma mem_eq_all_implies_decodePre_eq
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (ti ti' : b.times)
    (hMemEq : ∀ w : WId b, σ (Var.Mem ti w) = σ (Var.Mem ti' w)) :
    decodePre b σ hWF ti = decodePre b σ hWF ti' := by
  classical
  -- Membership implies positive fuel (otherwise decoder would be empty)
  have fuel_pos_of_mem :
      ∀ {H : b.times} {w : WId b}, σ (Var.Mem H w) = true → 0 < fuelOf b σ H := by
    intro H w hMemTrue
    by_contra hNonPos
    have hEmpty : decodePre b σ hWF H = PreHistory.empty := by
      unfold decodePre
      simp [hNonPos]
    have hWorld :=
      mem_decodePre_of_memVar (b := b) (σ := σ) (hWF := hWF)
        (H := H) (w := w) hMemTrue
    have hContr :
        (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti) ∈ PreHistory.empty := by
      simp [hEmpty] at hWorld
    exact
      (PreHistory.not_mem_empty
          (P := Fin b.nParticipants) (Event := Signature.EventType S)
          (e := (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti)))
        hContr
  have hPred :
      (fun w : WId b => σ (Var.Mem ti w)) =
        fun w : WId b => σ (Var.Mem ti' w) :=
    funext hMemEq
  -- Case 1: some membership bit is true, so both decoders take the non-empty branch
  by_cases hHasMem : ∃ w : WId b, σ (Var.Mem ti w) = true
  · obtain ⟨w, hMemTrue⟩ := hHasMem
    have hMemTrue' : σ (Var.Mem ti' w) = true := by
      simpa [hMemEq w] using hMemTrue
    have hFuel  : 0 < fuelOf b σ ti  := fuel_pos_of_mem hMemTrue
    have hFuel' : 0 < fuelOf b σ ti' := fuel_pos_of_mem hMemTrue'
    unfold decodePre
    simp [hFuel, hFuel', hPred]
  -- Case 2: all membership bits are false, so both decoders return empty
  · have hMemFalse : ∀ w : WId b, σ (Var.Mem ti w) = false := by
      intro w
      cases hVal : σ (Var.Mem ti w) with
      | false => rfl
      | true =>
          exact False.elim (hHasMem ⟨w, hVal⟩)
    have hMemFalse' : ∀ w : WId b, σ (Var.Mem ti' w) = false := by
      intro w
      exact (hMemEq w).symm.trans (hMemFalse w)
    have hPredFalse :
        (fun w : WId b => σ (Var.Mem ti w)) = fun _ => false :=
      funext hMemFalse
    have hPredFalse' :
        (fun w : WId b => σ (Var.Mem ti' w)) = fun _ => false :=
      funext hMemFalse'
    have hZero :
        decodePre b σ hWF ti = PreHistory.empty := by
      have hSubset :
          decodePre b σ hWF ti ⊆ PreHistory.empty := by
        intro w hw
        obtain ⟨wId, _, hMem⟩ :=
          exists_memVar_of_mem_decodePre (b := b) (σ := σ) (hWF := hWF)
            (H := ti) (w := w) hw
        have hFalse : σ (Var.Mem ti wId) = false := hMemFalse wId
        simp [hFalse] at hMem
      exact
        (PreHistory.subset_empty_iff
          (h := decodePre b σ hWF ti)).1 hSubset
    have hZero' :
        decodePre b σ hWF ti' = PreHistory.empty := by
      have hSubset :
          decodePre b σ hWF ti' ⊆ PreHistory.empty := by
        intro w hw
        obtain ⟨wId, _, hMem⟩ :=
          exists_memVar_of_mem_decodePre (b := b) (σ := σ) (hWF := hWF)
            (H := ti') (w := w) hw
        have hFalse : σ (Var.Mem ti' wId) = false := hMemFalse' wId
        simp [hFalse] at hMem
      exact
        (PreHistory.subset_empty_iff
          (h := decodePre b σ hWF ti')).1 hSubset
    simp [hZero, hZero']

/-! ## Helper Lemmas for Event Encoding -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The length of the witness variables list equals the length of the input pairs
    plus initial accumulator. -/
lemma event_witness_fold_length (b : Bounds S) (st : EncState b) (pairs : List (Var b × Var b))
    (acc : List (Var b)) :
    (pairs.foldl (eventWitnessStep b) (acc, st)).1.length = acc.length + pairs.length := by
  induction pairs generalizing st acc with
  | nil => simp
  | cons pair tail ih =>
    simp [eventWitnessStep, ih, Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The witness variables list extends the accumulator. -/
lemma event_witness_fold_extends (b : Bounds S) (st : EncState b) (pairs : List (Var b × Var b))
    (acc : List (Var b)) :
    acc <+: (pairs.foldl (eventWitnessStep b) (acc, st)).1 := by
  induction pairs generalizing st acc with
  | nil => simp
  | cons pair tail ih =>
    simp [eventWitnessStep]
    apply List.IsPrefix.trans _ (ih _ _)
    apply List.prefix_append

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The clauses accumulate during the fold. -/
lemma event_witness_fold_clauses_subset
    (b : Bounds S) (st : EncState b) (pairs : List (Var b × Var b))
    (acc : List (Var b)) :
    st.clauses ⊆ (pairs.foldl (eventWitnessStep b) (acc, st)).2.clauses := by
  induction pairs generalizing st acc with
  | nil => simp
  | cons pair tail ih =>
    intro c h
    simp [eventWitnessStep] at h ⊢
    -- Follow the three addClause steps; each preserves existing clauses.
    have hAlloc :
        c ∈ (EncState.allocFresh b st).2.clauses := by
      simpa [EncState.allocFresh_clauses_eq] using h
    have hAdd1 :
        c ∈
          (EncState.addClause b (EncState.allocFresh b st).2
            [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
             SAT.Lit.pos pair.fst]).clauses :=
      EncState.addClause_subset_clauses
        (b := b) (st := (EncState.allocFresh b st).2) _ hAlloc
    have hAdd2 :
        c ∈
          (EncState.addClause b
            (EncState.addClause b (EncState.allocFresh b st).2
              [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
               SAT.Lit.pos pair.fst])
            [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
             SAT.Lit.pos pair.snd]).clauses :=
      EncState.addClause_subset_clauses
        (b := b)
        (st :=
          EncState.addClause b (EncState.allocFresh b st).2
            [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
             SAT.Lit.pos pair.fst])
        _ hAdd1
    have hAdd3 :
        c ∈
          (EncState.addClause b
            (EncState.addClause b
              (EncState.addClause b (EncState.allocFresh b st).2
                [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
                 SAT.Lit.pos pair.fst])
              [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
               SAT.Lit.pos pair.snd])
            [SAT.Lit.neg pair.fst, SAT.Lit.neg pair.snd,
             SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)]).clauses :=
      EncState.addClause_subset_clauses
        (b := b)
        (st :=
          EncState.addClause b
            (EncState.addClause b (EncState.allocFresh b st).2
              [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
               SAT.Lit.pos pair.fst])
            [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
             SAT.Lit.pos pair.snd])
        _ hAdd2
    exact ih _ _ hAdd3

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- After one step, acc.length is a valid index into the resulting variables list. -/
lemma eventWitnessStep_idx_valid (b : Bounds S) (acc : List (Var b)) (st : EncState b)
    (pair : Var b × Var b) :
    acc.length < (eventWitnessStep b (acc, st) pair).1.length := by
  unfold eventWitnessStep
  cases EncState.allocFresh b st
  simp

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper lemma: if res = stepRes ++ rest, then indexed elements at
    positions < stepRes.length are equal. -/
lemma list_append_getElem_left_eq {α : Type*} (stepRes rest : List α) (i : Nat)
    (hStep : i < stepRes.length) (hRes : i < (stepRes ++ rest).length) :
    (stepRes ++ rest)[i]'hRes = stepRes[i]'hStep := by
  exact List.getElem_append_left hStep

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- After one `eventWitnessStep`, the fresh variable encodes `preEq ∧ mem`. -/
lemma eventWitnessStep_correct
    (b : Bounds S) (acc : List (Var b)) (st : EncState b) (pair : Var b × Var b)
    (σ : SAT.Assignment (Var b))
    (hClauses :
      (eventWitnessStep b (acc, st) pair).2.clauses.all (SAT.Clause.eval σ) = true) :
    (σ ((eventWitnessStep b (acc, st) pair).1[acc.length]'
        (eventWitnessStep_idx_valid b acc st pair)) = true ↔
      σ pair.1 = true ∧ σ pair.2 = true) := by
  unfold eventWitnessStep
  cases hAlloc : EncState.allocFresh b st with
  | mk zFresh st₁ =>
      simp only [hAlloc]
      set zVar := FVar.toVar b zFresh
      -- Establish that the indexed element equals zVar
      have hIdx : (acc ++ [zVar])[acc.length]'(by simp) = zVar := by
        have hLen : acc.length ≥ acc.length := Nat.le_refl _
        rw [List.getElem_append_right hLen]
        simp
      have hAll := List.all_eq_true.mp (by simpa [eventWitnessStep, hAlloc] using hClauses)
      have hClause1 :
          SAT.Clause.eval σ [SAT.Lit.neg zVar, SAT.Lit.pos pair.1] = true := by
        apply hAll
        unfold EncState.addClause
        aesop
      have hClause2 :
          SAT.Clause.eval σ [SAT.Lit.neg zVar, SAT.Lit.pos pair.2] = true := by
        apply hAll
        unfold EncState.addClause
        aesop
      have hClause3 :
          SAT.Clause.eval σ
            [SAT.Lit.neg pair.1, SAT.Lit.neg pair.2, SAT.Lit.pos zVar] = true := by
        apply hAll
        unfold EncState.addClause
        aesop
      rw [hIdx]
      constructor
      · intro hz
        constructor
        · have h1 : σ zVar = false ∨ σ pair.1 = true := by
            simp [SAT.Clause.eval, SAT.Lit.eval, List.foldl] at hClause1
            exact hClause1
          cases h1
          · next hFalse => rw [hz] at hFalse; cases hFalse
          · next hTrue => exact hTrue
        · have h2 : σ zVar = false ∨ σ pair.2 = true := by
            simp [SAT.Clause.eval, SAT.Lit.eval, List.foldl] at hClause2
            exact hClause2
          cases h2
          · next hFalse => rw [hz] at hFalse; cases hFalse
          · next hTrue => exact hTrue
      · intro hBoth
        rcases hBoth with ⟨hPre, hMem⟩
        have h3 : (σ pair.1 = false ∨ σ pair.2 = false) ∨ σ zVar = true := by
          simp [SAT.Clause.eval, SAT.Lit.eval, List.foldl] at hClause3
          exact hClause3
        cases h3
        · next h3' =>
            cases h3'
            · next hFalse => rw [hPre] at hFalse; cases hFalse
            · next hFalse => rw [hMem] at hFalse; cases hFalse
        · next hTrue => exact hTrue

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Generalized correctness of the witness variables produced by the fold. -/
lemma event_witness_fold_correct_general (b : Bounds S) (st : EncState b)
    (pairs : List (Var b × Var b)) (acc : List (Var b)) (σ : SAT.Assignment (Var b))
    (hClauses :
      (pairs.foldl (eventWitnessStep b) (acc, st)).2.clauses.all
        (SAT.Clause.eval σ) = true) :
    ∀ (i : Nat) (h : i < pairs.length),
      let res := pairs.foldl (eventWitnessStep b) (acc, st)
      let z := res.1[acc.length + i]'(by
        have hLen := event_witness_fold_length (b := b) (st := st) (pairs := pairs) (acc := acc)
        have hLt : acc.length + i < acc.length + pairs.length := Nat.add_lt_add_left h _
        simpa [res, hLen] using hLt)
      let pair := pairs[i]
      (σ z = true ↔ σ pair.1 = true ∧ σ pair.2 = true) := by
  induction pairs generalizing st acc with
  | nil =>
      intro i hi
      cases hi
  | cons pair tail ih =>
      intro i hi
      simp at hi
      have hClauses' :
          (tail.foldl (eventWitnessStep b) (eventWitnessStep b (acc, st) pair)).2.clauses.all
            (SAT.Clause.eval σ) = true := by
        simpa [List.foldl_cons] using hClauses
      have hStepClauses :
          (eventWitnessStep b (acc, st) pair).2.clauses.all (SAT.Clause.eval σ) = true := by
        have hSub :=
          event_witness_fold_clauses_subset
            (b := b) (st := (eventWitnessStep b (acc, st) pair).2)
            (pairs := tail) (acc := (eventWitnessStep b (acc, st) pair).1)
        exact all_true_of_subset hSub hClauses'
      cases i with
      | zero =>
          -- The first fresh variable corresponds to `pair`.
          set stepRes := eventWitnessStep b (acc, st) pair
          set res := tail.foldl (eventWitnessStep b) stepRes
          have hPrefix :
              stepRes.1 <+: res.1 :=
            event_witness_fold_extends b stepRes.2 tail stepRes.1
          rcases hPrefix with ⟨rest, hRest⟩
          have hStepIff :=
            eventWitnessStep_correct
              (b := b) (acc := acc) (st := st) (pair := pair)
              (σ := σ) (hClauses := hStepClauses)
          have hIdxStep : acc.length < stepRes.1.length := by
            simp [stepRes, eventWitnessStep]
          have hIdxRes : acc.length < res.1.length := by
            have hLen : stepRes.1.length ≤ res.1.length := by
              rw [← hRest]
              simp
            exact Nat.lt_of_lt_of_le hIdxStep hLen
          have hPair : (pair :: tail)[0] = pair := by simp
          have hLen : acc.length + 0 = acc.length := by simp
          have hRes :
              (pair :: tail).foldl (eventWitnessStep b) (acc, st) =
                res := by
            rfl
          -- Prove the biconditional directly
          have hGoalIdx : acc.length + 0 < res.1.length := by simp only [hLen]; exact hIdxRes
          change (σ (res.1[acc.length + 0]'hGoalIdx) = true ↔
                σ (pair :: tail)[0].1 = true ∧ σ (pair :: tail)[0].2 = true)
          simp only [hPair, hLen]
          -- Prove the biconditional by showing the indexed elements produce the same result
          have hSame : σ (res.1[acc.length]'hIdxRes) = σ (stepRes.1[acc.length]'hIdxStep) := by
            have hEq : res.1 = stepRes.1 ++ rest := hRest.symm
            simp_rw [hEq]
            simp only [List.getElem_append_left hIdxStep]
          rw [hSame]
          exact hStepIff
      | succ i =>
          have hiTail : i < tail.length := Nat.lt_of_succ_lt_succ hi
          set stepRes := eventWitnessStep b (acc, st) pair
          have hClausesTail :
              (tail.foldl (eventWitnessStep b) stepRes).2.clauses.all
                (SAT.Clause.eval σ) = true := by
            simpa [stepRes] using hClauses'
          have hIH :=
            ih (st := stepRes.2) (acc := stepRes.1)
              (hClauses := hClausesTail) (i := i) hiTail
          have hPair : (pair :: tail)[Nat.succ i] = tail[i] := by simp
          have hIdx :
              acc.length + Nat.succ i =
                stepRes.1.length + i := by
            unfold stepRes eventWitnessStep
            simp [Nat.add_comm, Nat.add_left_comm]
          have hRes :
              (pair :: tail).foldl (eventWitnessStep b) (acc, st) =
                tail.foldl (eventWitnessStep b) stepRes := by
            rfl
          simp only [hRes, hPair, hIdx]
          exact hIH

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Correctness of the witness variables: z ↔ (preEq ∧ mem). -/
lemma event_witness_fold_correct (b : Bounds S) (st : EncState b)
    (pairs : List (Var b × Var b)) (σ : SAT.Assignment (Var b))
    (hClauses :
      (pairs.foldl (eventWitnessStep b) ([], st)).2.clauses.all
        (SAT.Clause.eval σ) = true) :
    ∀ (i : Nat) (h : i < pairs.length),
      let res := pairs.foldl (eventWitnessStep b) ([], st)
      let z := res.1[i]'(by rw [event_witness_fold_length]; simp; exact h)
      let (preEq, mem) := pairs[i]
      (σ z = true ↔ σ preEq = true ∧ σ mem = true) := by
  intro i h
  simpa [event_witness_fold_length] using
    (event_witness_fold_correct_general
      (b := b) (st := st) (pairs := pairs) (acc := [])
      (σ := σ) (hClauses := hClauses) i h)

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Characterization of witness pairs for event encoding. -/
lemma event_witness_pairs_mem_iff (b : Bounds S) (w : WId b) (evt : Signature.EventType S)
    (pair : Var b × Var b) :
    pair ∈ eventWitnessPairs b w evt ↔
    ∃ w' ∈ WId.allWorlds b,
      w'.p = w.p ∧
      b.decodeMaybeEvent w'.ei = MaybeEvent.some evt ∧
      pair = (Var.PreEq w.ti w'.ti, Var.Mem b.root w') := by
  unfold eventWitnessPairs
  rw [List.mem_filterMap]
  constructor
  · intro h
    obtain ⟨w', hMem, hEq⟩ := h
    split at hEq
    · split at hEq
      · split at hEq
        · injection hEq with hPair
          subst hPair
          refine ⟨w', hMem, ?_, ?_, rfl⟩
          · simp_all
          · simp_all
        · contradiction
      · contradiction
    · contradiction
  · intro h
    obtain ⟨w', hMem, hPart, hEvt, hPair⟩ := h
    refine ⟨w', hMem, ?_⟩
    simp [hPart, hEvt]
    exact hPair.symm

/-! ## Adequacy for Event Encoding -/

/-- Adequacy for encodeFormula event case: σ(u) = true ↔ event formula holds.

    The encoding uses PreEq to witness worlds with the same decoded prehistory.
    PreEq(w.ti, w'.ti) = true means decodePre σ w.ti = decodePre σ w'.ti.

    This matches the semantics: event atom holds iff there exists a witness in the
    root history with matching (participant, event, prehistory). -/

lemma encodeFormula_event_adequate
    (b : Bounds S) (atom : Logic.EventAtom S)
    (w : WId b) (st : EncState b)
    (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (hClauses :
      (encodeFormula b (.event atom) w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (stPreEq : EncState b)
    (hPreEq : (addPreEqAll b stPreEq).clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b (encodeFormula b (.event atom) w st).1) = true) ↔
    Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti) (.event atom) := by
  classical
  let evt : Signature.EventType S := ⟨atom.sym, atom.args⟩

  cases hGuard : b.decodeMaybeEvent w.ei with
  | none =>
      cases hAlloc : EncState.allocFresh b st with
      | mk u st1 =>
          have hEnc :
              encodeFormula b (.event atom) w st =
                (u, EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u)]) := by
            simp [encodeFormula, hGuard, hAlloc]
          have hClauseTrue :
              SAT.Clause.eval σ [SAT.Lit.neg (FVar.toVar b u)] = true := by
            have hAll := List.all_eq_true.mp (by simpa [hEnc] using hClauses)
            exact hAll _ (by simp [EncState.addClause])
          have hUFalse : σ (FVar.toVar b u) = false := by
            simpa [SAT.Clause.eval, SAT.Lit.eval] using hClauseTrue
          constructor
          · intro h
            have hVar :
                FVar.toVar b (encodeFormula b (.event atom) w st).1 =
                  FVar.toVar b u := by
              simp [hEnc]
            have hFalse :
                σ (FVar.toVar b (encodeFormula b (.event atom) w st).1) = false := by
              simp [hVar, hUFalse]
            simp [hFalse] at h
          · intro hSat
            have hSatFalse :
                ¬ Sat (modelOf b σ hWF) w.p MaybeEvent.none
                    (decodePre b σ hWF w.ti) (.event atom) := by
              simp [Sat]
            exact (hSatFalse (by simpa [hGuard] using hSat)).elim
  | some e =>
      by_cases hEq : e = evt
      · subst hEq
        classical
        let witnessPairs := eventWitnessPairs b w evt
        cases hFold : witnessPairs.foldl (eventWitnessStep b) ([], st) with
        | mk witnessVars st1 =>
            cases hMk : mkBigOrIff b witnessVars st1 with
            | mk u st2 =>
                have hWitnessEq :
                    List.foldl (eventWitnessStep b) ([], st) witnessPairs =
                      (witnessVars, st1) := hFold
                have hMkEq :
                    mkBigOrIff b witnessVars st1 = (u, st2) := hMk
                have hEncDef :
                    encodeFormula b (.event atom) w st = (u, st2) := by
                  unfold encodeFormula encodeFormulaEvent
                  simp only [evt, hGuard, dite_true]
                  rw [hFold, hMk]
                have hClauses2 :
                    st2.clauses.all (SAT.Clause.eval σ) = true := by
                  simpa [hEncDef] using hClauses
                have hClausesMkBig :
                    (mkBigOrIff b witnessVars st1).2.clauses.all
                      (SAT.Clause.eval σ) = true := by
                  simpa [hMk] using hClauses2
                have hWitnessClauses :
                    (witnessPairs.foldl (eventWitnessStep b) ([], st)).2.clauses.all
                      (SAT.Clause.eval σ) = true := by
                  have hSub :=
                    mkBigOrIff_clauses_subset (b := b) (vs := witnessVars) (st := st1)
                  have hAll := all_true_of_subset hSub hClausesMkBig
                  simpa [hFold] using hAll

                -- Note: PreEq soundness/completeness now requires hPreEq from caller
                -- (addPreEqAll is called once in encodeAssumptions, not per-formula)
                have hPreEqSound :
                    ∀ {t₁ t₂},
                      σ (Var.PreEq t₁ t₂) = true →
                        histEq (decodePre b σ hWF t₁) (decodePre b σ hWF t₂) := by
                  intro t₁ t₂ hPre
                  exact preEq_sound b σ hWF t₁ t₂ stPreEq hPreEq hPre
                have hPreEqComplete :
                    ∀ {t₁ t₂},
                      histEq (decodePre b σ hWF t₁) (decodePre b σ hWF t₂) →
                        σ (Var.PreEq t₁ t₂) = true := by
                  intro t₁ t₂ hHist
                  exact preEq_complete b σ hWF t₁ t₂ stPreEq hPreEq hHist

                constructor
                · intro hU
                  have hU' : σ (FVar.toVar b (mkBigOrIff b witnessVars st1).1) = true := by
                    have hVar :
                        FVar.toVar b (encodeFormula b (.event atom) w st).1 =
                          FVar.toVar b (mkBigOrIff b witnessVars st1).1 := by
                      simp [hEncDef, hMk]
                    simpa [hVar] using hU
                  obtain ⟨z, hZMem, hZTrue⟩ :=
                    mkBigOrIff_exists_true b witnessVars st1 σ hClausesMkBig hU'
                  obtain ⟨idx, hZEq⟩ := List.mem_iff_get.mp hZMem
                  have hIdxPairs :
                      idx.val < witnessPairs.length := by
                    have hLen :=
                      event_witness_fold_length (b := b) (st := st)
                        (pairs := witnessPairs) (acc := ([] : List (Var b)))
                    have hLenVars :
                        witnessVars.length = witnessPairs.length := by
                      simp [hFold] at hLen
                      exact hLen
                    rw [← hLenVars]
                    exact idx.isLt
                  let pair := witnessPairs[idx.val]'hIdxPairs
                  have hZIff :
                      σ (witnessVars[idx]) = true ↔
                        σ pair.1 = true ∧ σ pair.2 = true := by
                    have hStep :=
                      event_witness_fold_correct
                        (b := b) (st := st) (pairs := witnessPairs) (σ := σ)
                        (hClauses := hWitnessClauses) idx.val hIdxPairs
                    simp [hFold] at hStep
                    exact hStep
                  have hPreMem :
                      σ pair.1 = true ∧ σ pair.2 = true := by
                    have hZEq' : z = witnessVars[idx] := hZEq.symm
                    rw [hZEq'] at hZTrue
                    exact hZIff.mp hZTrue
                  have hPairMem : pair ∈ witnessPairs := by
                    change witnessPairs[idx.val]'hIdxPairs ∈ witnessPairs
                    apply List.getElem_mem
                  obtain ⟨w', hWorldMem, hPart, hEvt, hPairEq⟩ :=
                    (event_witness_pairs_mem_iff
                      (b := b) (w := w) (evt := evt) (pair := pair)).1 hPairMem
                  have hHistEq :
                      histEq (decodePre b σ hWF w.ti) (decodePre b σ hWF w'.ti) :=
                    by
                      have hPreEq : σ (Var.PreEq w.ti w'.ti) = true := by
                        simpa [hPairEq] using hPreMem.1
                      exact hPreEqSound hPreEq
                  have hMemDecoded :
                      (w'.p, b.decodeMaybeEvent w'.ei,
                        decodePre b σ hWF w'.ti) ∈
                          decodePre b σ hWF b.root := by
                    have hMemVar : σ (Var.Mem b.root w') = true := by
                      simpa [hPairEq] using hPreMem.2
                    exact mem_decodePre_of_memVar b σ hWF b.root w' hMemVar
                  unfold Sat
                  -- Sat expects:
                  --   evt = MaybeEvent.some ... ∧
                  --   ∃ H', (p, evt', H') ∈ history ∧ histEq H' H
                  -- But we're at participant w.p with event w.ei
                  -- (which equals MaybeEvent.some evt by hGuard)
                  -- We need to show the guard matches and there's a witness
                  have hEvtEq : MaybeEvent.some evt =
                      MaybeEvent.some ⟨atom.sym, atom.args⟩ := by
                    rfl
                  refine ⟨hEvtEq, ?_⟩
                  refine ⟨decodePre b σ hWF w'.ti, ?_⟩
                  constructor
                  · -- Show (w.p, MaybeEvent.some evt, decodePre σ w'.ti) ∈ history
                    simp [hPart, hEvt] at hMemDecoded
                    exact hMemDecoded
                  · exact histEq_symm hHistEq
                · intro hSat
                  unfold Sat at hSat
                  rcases hSat with ⟨hEvtEq, H', hMem, hHist⟩
                  -- hMem : (w.p, MaybeEvent.some evt, H') ∈
                  --        (modelOf b σ hWF).history.val
                  -- which is the decoded root history
                  have hMem' : (w.p, MaybeEvent.some evt, H') ∈ decodePre b σ hWF b.root := by
                    unfold modelOf at hMem
                    simp at hMem
                    exact hMem
                  obtain ⟨w', hWorldEq, hMemVar⟩ :=
                    exists_memVar_of_mem_decodePre b σ hWF b.root
                      (w := (w.p, MaybeEvent.some evt, H')) hMem'
                  obtain ⟨hPart', hEvent', hHistPre⟩ : w'.p = w.p ∧
                      b.decodeMaybeEvent w'.ei = MaybeEvent.some evt ∧
                      decodePre b σ hWF w'.ti = H' := by
                    have : (w'.p, b.decodeMaybeEvent w'.ei, decodePre b σ hWF w'.ti) =
                           (w.p, MaybeEvent.some evt, H') := hWorldEq
                    simp at this
                    exact this
                  have hHistEq :
                      histEq (decodePre b σ hWF w.ti) (decodePre b σ hWF w'.ti) := by
                    rw [hHistPre]
                    exact histEq_symm hHist
                  have hPreEqTrue : σ (Var.PreEq w.ti w'.ti) = true :=
                    hPreEqComplete hHistEq
                  have hPairMem :
                      (Var.PreEq w.ti w'.ti, Var.Mem b.root w') ∈ witnessPairs := by
                    have hInAll : w' ∈ WId.allWorlds b := WId.mem_allWorlds b w'
                    exact
                      (event_witness_pairs_mem_iff
                        (b := b) (w := w) (evt := evt) (pair := _)).2
                        ⟨w', hInAll, hPart', hEvent', rfl⟩
                  obtain ⟨idx, hPairEq⟩ := List.mem_iff_get.mp hPairMem
                  have hIdxVars :
                      idx.val < witnessVars.length := by
                    have hLen :=
                      event_witness_fold_length (b := b) (st := st)
                        (pairs := witnessPairs) (acc := ([] : List (Var b)))
                    have hLenVars :
                        witnessVars.length = witnessPairs.length := by
                      simp [hFold] at hLen
                      exact hLen
                    rw [hLenVars]
                    exact idx.isLt
                  have hZIff :
                      σ (witnessVars[idx]) = true ↔
                        σ (Var.PreEq w.ti w'.ti) = true ∧
                          σ (Var.Mem b.root w') = true := by
                    have hIdxPairs' : idx.val < witnessPairs.length := by
                      exact idx.isLt
                    have hStep :=
                      event_witness_fold_correct
                        (b := b) (st := st) (pairs := witnessPairs) (σ := σ)
                        (hClauses := hWitnessClauses) idx.val hIdxPairs'
                    simp [hFold] at hStep
                    have : witnessPairs[idx.val]'hIdxPairs' =
                           (Var.PreEq w.ti w'.ti, Var.Mem b.root w') := hPairEq
                    simp_rw [this] at hStep
                    exact hStep
                  have hZTrue : σ (witnessVars[idx]) = true :=
                    (hZIff.mpr ⟨hPreEqTrue, hMemVar⟩)
                  have hZMem : witnessVars[idx] ∈ witnessVars := by
                    apply List.get_mem
                  have hUnitMem' :
                      [SAT.Lit.neg (witnessVars[idx]),
                       SAT.Lit.pos (FVar.toVar b (mkBigOrIff b witnessVars st1).1)] ∈
                        (mkBigOrIff b witnessVars st1).2.clauses :=
                    mkBigOrIff_unit_clause_mem
                      (b := b) (vs := witnessVars) (st := st1)
                      (v := witnessVars[idx]) hZMem
                  have hUnitMem :
                      [SAT.Lit.neg (witnessVars[idx]),
                       SAT.Lit.pos (FVar.toVar b u)] ∈
                        (mkBigOrIff b witnessVars st1).2.clauses := by
                    simpa [hMk] using hUnitMem'
                  have hUnitTrue :
                      SAT.Clause.eval σ
                        [SAT.Lit.neg (witnessVars[idx]),
                         SAT.Lit.pos (FVar.toVar b u)] = true := by
                    have hMem2 : [SAT.Lit.neg (witnessVars[idx]),
                                   SAT.Lit.pos (FVar.toVar b u)] ∈
                                   (mkBigOrIff b witnessVars st1).2.clauses := hUnitMem
                    exact (List.all_eq_true.mp hClausesMkBig) _ hMem2
                  have hUTrue : σ (FVar.toVar b u) = true := by
                    simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl,
                      Bool.false_or] at hUnitTrue
                    rw [hZTrue, Bool.not_true, Bool.false_or] at hUnitTrue
                    exact hUnitTrue
                  simpa [hEncDef] using hUTrue
      · -- Guard fails because event mismatches
        cases hAlloc : EncState.allocFresh b st with
        | mk u st1 =>
            have hEnc :
                encodeFormula b (.event atom) w st =
                  (u, EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u)]) := by
              unfold encodeFormula
              simp only [hGuard]
              split
              · contradiction
              · rw [hAlloc]
            have hClauseTrue :
                SAT.Clause.eval σ [SAT.Lit.neg (FVar.toVar b u)] = true := by
              have hAll := List.all_eq_true.mp (by simpa [hEnc] using hClauses)
              exact hAll _ (by simp [EncState.addClause])
            have hUFalse : σ (FVar.toVar b u) = false := by
              simp [SAT.Clause.eval, SAT.Lit.eval] at hClauseTrue
              exact hClauseTrue
            constructor
            · intro h
              have hVar :
                  FVar.toVar b (encodeFormula b (.event atom) w st).1 =
                    FVar.toVar b u := by
                simp [hEnc]
              have hFalse :
                  σ (FVar.toVar b (encodeFormula b (.event atom) w st).1) = false := by
                simp [hVar, hUFalse]
              simp [hFalse] at h
            · intro hSat
              exfalso
              -- hSat says the formula holds at (w.p, MaybeEvent.some e, decodePre σ w.ti)
              -- But we're at world w where w.ei decodes to MaybeEvent.some e
              have hSat' : Sat (modelOf b σ hWF) w.p (MaybeEvent.some e)
                              (decodePre b σ hWF w.ti) (.event atom) := by
                simpa [hGuard] using hSat
              -- Unfold Sat for event formula
              unfold Sat at hSat'
              -- hSat' : MaybeEvent.some e = MaybeEvent.some ⟨atom.sym, atom.args⟩ ∧ ...
              have hEvtEq : e = evt := by
                have : MaybeEvent.some e = MaybeEvent.some ⟨atom.sym, atom.args⟩ := hSat'.1
                injection this
              exact hEq hEvtEq

end Encoding
