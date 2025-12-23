import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Lemmas.Basic
import ModalDistribution.Logic.SATEncoding.Lemmas.NextFreshMono

/-!
# Event Witness Step Lemmas

This file contains lemmas about eventWitnessStep and related operations:

- `eventWitnessStep_nextFresh_mono`: eventWitnessStep is monotonic in nextFresh
- `eventWitnessStep_newClause_fresh_ge`: Fresh vars in new clauses have id ≥ input nextFresh
- `encodeFormulaEvent_nextFresh_mono`: encodeFormulaEvent increases nextFresh
- `encodeTupleControl_nextFresh`: encodeTupleControl increases nextFresh by exactly 1
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}

/-- eventWitnessStep is monotonic in nextFresh.
    It does allocFresh (increases by 1) then 3x addClause (preserves). -/
lemma eventWitnessStep_nextFresh_mono (b : Bounds S) (acc : List (Var b) × EncState b)
    (pair : Var b × Var b) :
    acc.2.nextFresh ≤ (eventWitnessStep b acc pair).2.nextFresh := by
  simp only [eventWitnessStep]
  simp only [EncState.addClause, EncState.allocFresh_nextFresh]
  omega

/-- Helper for foldl with eventWitnessStep - uses accumulator pair. -/
lemma foldl_eventWitnessStep_nextFresh_mono (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b) :
    acc.2.nextFresh ≤ (pairs.foldl (eventWitnessStep b) acc).2.nextFresh := by
  induction pairs generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (eventWitnessStep_nextFresh_mono b acc hd) (ih _)

/-- eventWitnessStep adds exactly 1 to nextFresh. -/
lemma eventWitnessStep_nextFresh_eq (b : Bounds S) (acc : List (Var b) × EncState b)
    (pair : Var b × Var b) :
    (eventWitnessStep b acc pair).2.nextFresh = acc.2.nextFresh + 1 := by
  simp only [eventWitnessStep]
  simp only [EncState.addClause, EncState.allocFresh_nextFresh]

/-- The fold of eventWitnessStep adds exactly pairs.length to nextFresh. -/
lemma foldl_eventWitnessStep_nextFresh_eq (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b) :
    (pairs.foldl (eventWitnessStep b) acc).2.nextFresh = acc.2.nextFresh + pairs.length := by
  induction pairs generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, eventWitnessStep_nextFresh_eq]
    ring

/-- The fold of eventWitnessStep preserves offset: if we start at states differing by offset,
    we end at states also differing by offset. -/
lemma foldl_eventWitnessStep_offset (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc acc' : List (Var b) × EncState b) (offset : Nat)
    (hOffset : acc'.2.nextFresh = acc.2.nextFresh + offset) :
    (pairs.foldl (eventWitnessStep b) acc').2.nextFresh =
    (pairs.foldl (eventWitnessStep b) acc).2.nextFresh + offset := by
  simp only [foldl_eventWitnessStep_nextFresh_eq, hOffset]
  ring

/-- A Var is not a Fresh variable -/
def Var.notFresh (b : Bounds S) : Var b → Prop
  | Var.Mem _ _ => True
  | Var.Level _ _ => True
  | Var.Pred _ _ _ => True
  | Var.MinQ _ _ => True
  | Var.ReachT _ => True
  | Var.Edge _ _ => True
  | Var.Fresh _ => False
  | Var.Exists _ _ _ => True
  | Var.PreEq _ _ => True
  | Var.Seq _ _ => True
  | Var.Rep _ => True
  | Var.Incomp _ _ _ _ => True
  | Var.Acc _ _ _ => True

/-- If v is not fresh, then it's not equal to any Fresh n. -/
lemma Var.notFresh_ne_Fresh (b : Bounds S) (v : Var b) (h : Var.notFresh b v) (n : Nat) :
    v ≠ Var.Fresh n := by
  cases v <;> simp only [Var.notFresh] at h <;> intro heq <;> cases heq

/-- eventWitnessStep only adds clauses whose Fresh vars have id = input.nextFresh.
    The only Fresh var in NEW clauses from eventWitnessStep is z with id = stAcc.nextFresh.
    The other vars (preEq, mem) come from the input pair and are assumed not Fresh. -/
lemma eventWitnessStep_newClause_fresh_ge (b : Bounds S) (acc : List (Var b) × EncState b)
    (pair : Var b × Var b) (hPair1 : Var.notFresh b pair.1) (hPair2 : Var.notFresh b pair.2)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (eventWitnessStep b acc pair).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ acc.2.nextFresh := by
  simp only [eventWitnessStep] at hcNew
  -- z.id = acc.2.nextFresh
  have hZId : (EncState.allocFresh b acc.2).1.id = acc.2.nextFresh :=
    EncState.allocFresh_fst (b := b) acc.2
  -- The 3 NEW clauses are:
  -- clause1 = [neg z, pos pair.1]
  -- clause2 = [neg z, pos pair.2]
  -- clause3 = [neg pair.1, neg pair.2, pos z]
  simp only [EncState.addClause] at hcNew
  cases hcNew with
  | head =>
      -- c = [neg pair.1, neg pair.2, pos z]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      rcases hLit with h1 | h2 | h3
      · -- lit = neg pair.1
        rw [h1] at hFresh; simp only [SAT.Lit.getVar] at hFresh
        -- pair.1 is not Fresh (by hPair1), so hFresh gives a contradiction
        match hv : pair.1, hPair1 with
        | Var.Mem _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Level _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Pred _ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.MinQ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.ReachT _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Edge _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Exists _ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.PreEq _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Seq _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Rep _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Incomp _ _ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Acc _ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Fresh _, hNF => simp only [Var.notFresh] at hNF
      · -- lit = neg pair.2
        rw [h2] at hFresh; simp only [SAT.Lit.getVar] at hFresh
        match hv : pair.2, hPair2 with
        | Var.Mem _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Level _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Pred _ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.MinQ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.ReachT _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Edge _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Exists _ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.PreEq _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Seq _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Rep _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Incomp _ _ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Acc _ _ _, _ => rw [hv] at hFresh; cases hFresh
        | Var.Fresh _, hNF => simp only [Var.notFresh] at hNF
      · -- lit = pos (FVar.toVar z) (Fresh z.id = acc.2.nextFresh)
        rw [h3] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
        have hn : (EncState.allocFresh b acc.2).1.id = n := Var.Fresh.inj hFresh
        omega
  | tail _ h1 =>
      cases h1 with
      | head =>
          -- c = [neg z, pos pair.2]
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
          rcases hLit with h1 | h2
          · rw [h1] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
            have hn : (EncState.allocFresh b acc.2).1.id = n := Var.Fresh.inj hFresh
            omega
          · rw [h2] at hFresh; simp only [SAT.Lit.getVar] at hFresh
            match hv : pair.2, hPair2 with
            | Var.Mem _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.Level _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.Pred _ _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.MinQ _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.ReachT _, _ => rw [hv] at hFresh; cases hFresh
            | Var.Edge _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.Exists _ _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.PreEq _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.Seq _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.Rep _, _ => rw [hv] at hFresh; cases hFresh
            | Var.Incomp _ _ _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.Acc _ _ _, _ => rw [hv] at hFresh; cases hFresh
            | Var.Fresh _, hNF => simp only [Var.notFresh] at hNF
      | tail _ h2 =>
          cases h2 with
          | head =>
              -- c = [neg z, pos pair.1]
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
              rcases hLit with h1 | h2
              · rw [h1] at hFresh; simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
                have hn : (EncState.allocFresh b acc.2).1.id = n := Var.Fresh.inj hFresh
                omega
              · rw [h2] at hFresh; simp only [SAT.Lit.getVar] at hFresh
                match hv : pair.1, hPair1 with
                | Var.Mem _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.Level _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.Pred _ _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.MinQ _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.ReachT _, _ => rw [hv] at hFresh; cases hFresh
                | Var.Edge _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.Exists _ _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.PreEq _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.Seq _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.Rep _, _ => rw [hv] at hFresh; cases hFresh
                | Var.Incomp _ _ _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.Acc _ _ _, _ => rw [hv] at hFresh; cases hFresh
                | Var.Fresh _, hNF => simp only [Var.notFresh] at hNF
          | tail _ hInAcc =>
              -- c ∈ allocFresh output clauses = acc.2.clauses
              have hStAcc : (EncState.allocFresh b acc.2).2.clauses = acc.2.clauses :=
                EncState.allocFresh_clauses_eq (b := b) acc.2
              rw [hStAcc] at hInAcc
              exact absurd hInAcc hcNotOld


/-- Fresh vars in NEW clauses from foldl eventWitnessStep have id ≥ input.nextFresh.
    Requires that all pairs have notFresh components. -/
lemma foldl_eventWitnessStep_newClause_fresh_ge (b : Bounds S)
    (pairs : List (Var b × Var b))
    (hPairsNotFresh : ∀ p ∈ pairs, Var.notFresh b p.1 ∧ Var.notFresh b p.2)
    (acc : List (Var b) × EncState b) (c : SAT.Clause (Var b))
    (hcNew : c ∈ (pairs.foldl (eventWitnessStep b) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ acc.2.nextFresh := by
  induction pairs generalizing acc c lit n with
  | nil =>
      simp only [List.foldl_nil] at hcNew
      exact absurd hcNew hcNotOld
  | cons hd tl ih =>
      simp only [List.foldl_cons] at hcNew
      have hHdNotFresh := hPairsNotFresh hd (List.mem_cons_self (a := hd) (l := tl))
      have hTlNotFresh : ∀ p ∈ tl, Var.notFresh b p.1 ∧ Var.notFresh b p.2 := fun p hp =>
        hPairsNotFresh p (List.mem_cons_of_mem hd hp)
      by_cases hcStep : c ∈ (eventWitnessStep b acc hd).2.clauses
      · by_cases hcAcc : c ∈ acc.2.clauses
        · exact absurd hcAcc hcNotOld
        · -- c is NEW in eventWitnessStep output
          exact eventWitnessStep_newClause_fresh_ge b acc hd hHdNotFresh.1 hHdNotFresh.2
            c hcStep hcAcc lit hLit n hFresh
      · -- c ∉ step.2.clauses, so c is from the tail fold
        have hFromTail := ih hTlNotFresh (eventWitnessStep b acc hd)
          c hcNew hcStep lit hLit n hFresh
        have hMono := eventWitnessStep_nextFresh_mono b acc hd
        omega

/-- Helper: every var in the output list is either from the input list or is Fresh
    with id ≥ acc.2.nextFresh -/
lemma foldl_eventWitnessStep_witnessVars_fresh_ge (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b)
    (v : Var b) (hv : v ∈ (pairs.foldl (eventWitnessStep b) acc).1) (n : Nat)
    (hFresh : v = Var.Fresh n) :
    v ∈ acc.1 ∨ n ≥ acc.2.nextFresh := by
  induction pairs generalizing acc v n with
  | nil =>
      simp only [List.foldl_nil] at hv
      exact Or.inl hv
  | cons hd tl ih =>
      simp only [List.foldl_cons] at hv
      -- eventWitnessStep appends FVar.toVar b z where z = allocFresh output
      -- So new list = acc.1 ++ [Var.Fresh acc.2.nextFresh]
      have hStep : (eventWitnessStep b acc hd).1 = acc.1 ++ [Var.Fresh acc.2.nextFresh] := by
        simp only [eventWitnessStep, FVar.toVar]
        have hAllocId : (EncState.allocFresh b acc.2).1.id = acc.2.nextFresh :=
          EncState.allocFresh_fst (b := b) acc.2
        simp only [hAllocId]
      have hStepState : (eventWitnessStep b acc hd).2.nextFresh = acc.2.nextFresh + 1 := by
        simp only [eventWitnessStep]
        have hAllocNF : (EncState.allocFresh b acc.2).2.nextFresh = acc.2.nextFresh + 1 :=
          EncState.allocFresh_nextFresh b acc.2
        simp only [EncState.addClause, hAllocNF]
      have hFromTail := ih (eventWitnessStep b acc hd) v hv n hFresh
      rcases hFromTail with hInStep | hGe
      · -- v ∈ (eventWitnessStep b acc hd).1
        rw [hStep] at hInStep
        simp only [List.mem_append, List.mem_singleton] at hInStep
        rcases hInStep with hInAcc | hNew
        · exact Or.inl hInAcc
        · -- v = Var.Fresh acc.2.nextFresh
          rw [hFresh] at hNew
          have hn : acc.2.nextFresh = n := Var.Fresh.inj hNew.symm
          right; omega
      · -- n ≥ (eventWitnessStep b acc hd).2.nextFresh
        right
        rw [hStepState] at hGe
        omega

/-- For the event case witness vars: all vars in the output list are Fresh
    with ids ≥ st.nextFresh. Needed for the event case of
    encodeFormula_new_clause_fresh_ge_nextFresh. -/
lemma foldl_eventWitnessStep_witnessVars_fresh_ge_empty (b : Bounds S)
    (pairs : List (Var b × Var b)) (st : EncState b)
    (v : Var b) (hv : v ∈ (pairs.foldl (eventWitnessStep b) ([], st)).1) (n : Nat)
    (hFresh : v = Var.Fresh n) :
    n ≥ st.nextFresh := by
  -- Use a generalized form with any accumulator
  have hGen := foldl_eventWitnessStep_witnessVars_fresh_ge b pairs ([], st) v hv n hFresh
  simp only [List.not_mem_nil] at hGen
  exact hGen.resolve_left (by simp)

/-- eventWitnessStep increases nextFresh by exactly 1 (addClause doesn't change nextFresh). -/
lemma eventWitnessStep_nextFresh' (b : Bounds S) (acc : List (Var b) × EncState b)
    (pair : Var b × Var b) :
    (eventWitnessStep b acc pair).2.nextFresh = acc.2.nextFresh + 1 := by
  simp only [eventWitnessStep, EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]

/-- eventWitnessStep adds exactly one Fresh var with id = acc.nextFresh. -/
lemma eventWitnessStep_vars (b : Bounds S) (acc : List (Var b) × EncState b)
    (pair : Var b × Var b) :
    (eventWitnessStep b acc pair).1 = acc.1 ++ [FVar.toVar b ⟨acc.2.nextFresh⟩] := by
  simp only [eventWitnessStep, FVar.toVar, EncState.allocFresh]

/-- General fold lemma: vars in result have Fresh id < final nextFresh,
    given that vars in initial accumulator have Fresh id < initial nextFresh. -/
lemma eventWitnessStep_foldl_vars_fresh_below_aux (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b)
    (hNonFresh : ∀ p ∈ pairs, ∀ n, p.1 ≠ Var.Fresh n ∧ p.2 ≠ Var.Fresh n)
    (hAccVars : ∀ v ∈ acc.1, ∀ n, v = Var.Fresh n → n < acc.2.nextFresh) :
    ∀ v ∈ (pairs.foldl (eventWitnessStep b) acc).1, ∀ n, v = Var.Fresh n →
      n < (pairs.foldl (eventWitnessStep b) acc).2.nextFresh := by
  induction pairs generalizing acc with
  | nil =>
    intro v hv n hEq
    simp only [List.foldl_nil]
    exact hAccVars v hv n hEq
  | cons p ps ih =>
    intro v hv n hEq
    simp only [List.foldl_cons] at hv ⊢
    have hpsNF : ∀ q ∈ ps, ∀ n, q.1 ≠ Var.Fresh n ∧ q.2 ≠ Var.Fresh n := by
      intro q hq n'
      exact hNonFresh q (List.mem_cons_of_mem p hq) n'
    -- The new accumulator after one step
    let acc' := eventWitnessStep b acc p
    -- Property of acc'.1: it's acc.1 ++ [new Fresh var with id = acc.nextFresh]
    have hAcc'Vars : acc'.1 = acc.1 ++ [FVar.toVar b ⟨acc.2.nextFresh⟩] :=
      eventWitnessStep_vars b acc p
    -- Property of acc'.2.nextFresh: it's acc.nextFresh + 1
    have hAcc'Next : acc'.2.nextFresh = acc.2.nextFresh + 1 :=
      eventWitnessStep_nextFresh' b acc p
    -- Vars in acc'.1 have Fresh id < acc'.2.nextFresh
    have hAcc'VarsBound : ∀ v ∈ acc'.1, ∀ n, v = Var.Fresh n → n < acc'.2.nextFresh := by
      intro v' hv' n' hEq'
      simp only [hAcc'Vars, List.mem_append, List.mem_singleton] at hv'
      cases hv' with
      | inl hOld =>
        -- v' was in original acc.1, so n' < acc.nextFresh < acc'.nextFresh
        have hLt := hAccVars v' hOld n' hEq'
        simp only [hAcc'Next]
        exact Nat.lt_of_lt_of_le hLt (Nat.le_succ _)
      | inr hNew =>
        -- v' is the new Fresh var with id = acc.nextFresh
        simp only [FVar.toVar] at hNew
        subst hNew
        simp only [hAcc'Next] at hEq' ⊢
        cases hEq'
        exact Nat.lt_succ_self _
    exact ih acc' hpsNF hAcc'VarsBound v hv n hEq

/-- eventWitnessStep preserves well-formedness.
    It allocates a fresh var and adds 3 clauses, all with Fresh vars within bounds.
    The input pair must have non-Fresh vars for the proof to work. -/
lemma eventWitnessStep_wf (b : Bounds S) (acc : List (Var b) × EncState b)
    (pair : Var b × Var b) (hwf : acc.2.WellFormed)
    (hNonFresh : ∀ n, pair.1 ≠ Var.Fresh n ∧ pair.2 ≠ Var.Fresh n) :
    (eventWitnessStep b acc pair).2.WellFormed := by
  simp only [eventWitnessStep]
  obtain ⟨vars, stAcc⟩ := acc
  obtain ⟨preEq, mem⟩ := pair
  have hAllocWF := EncState.allocFresh_wf hwf
  have hZId : (EncState.allocFresh b stAcc).1.id = stAcc.nextFresh := by
    simp only [EncState.allocFresh]
  have hAllocNext : (EncState.allocFresh b stAcc).2.nextFresh = stAcc.nextFresh + 1 :=
    EncState.allocFresh_nextFresh b stAcc
  -- Clause 1: [neg Fresh(z), pos preEq]
  have hC1 : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b stAcc).1),
      SAT.Lit.pos preEq] (EncState.allocFresh b stAcc).2.nextFresh := by
    intro lit hLit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h =>
      subst h
      simp only [litFreshBelow, FVar.toVar, hZId, hAllocNext]
      exact Nat.lt_succ_self _
    | inr h =>
      subst h
      simp only [litFreshBelow]
      -- preEq is non-Fresh by hypothesis; case split to reduce the match
      cases preEq with
      | Fresh n => exact absurd rfl ((hNonFresh n).1)
      | _ => trivial
  have hWF1 := EncState.addClause_wf hAllocWF _ hC1
  -- Clause 2: [neg Fresh(z), pos mem]
  have hC2 : clauseFreshBelow
      [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b stAcc).1), SAT.Lit.pos mem]
      (EncState.addClause b (EncState.allocFresh b stAcc).2
        [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b stAcc).1),
          SAT.Lit.pos preEq]).nextFresh := by
    intro lit hLit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
    simp only [EncState.addClause_nextFresh]
    cases hLit with
    | inl h =>
      subst h
      simp only [litFreshBelow, FVar.toVar, hZId, hAllocNext]
      exact Nat.lt_succ_self _
    | inr h =>
      subst h
      simp only [litFreshBelow]
      -- mem is non-Fresh by hypothesis; case split to reduce the match
      cases mem with
      | Fresh n => exact absurd rfl ((hNonFresh n).2)
      | _ => trivial
  have hWF2 := EncState.addClause_wf hWF1 _ hC2
  -- Clause 3: [neg preEq, neg mem, pos Fresh(z)]
  have hC3 : clauseFreshBelow
      [SAT.Lit.neg preEq, SAT.Lit.neg mem,
        SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b stAcc).1)]
      (EncState.addClause b (EncState.addClause b (EncState.allocFresh b stAcc).2
        [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b stAcc).1), SAT.Lit.pos preEq])
        [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b stAcc).1),
          SAT.Lit.pos mem]).nextFresh := by
    intro lit hLit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
    simp only [EncState.addClause_nextFresh]
    rcases hLit with rfl | rfl | rfl
    · -- neg preEq
      simp only [litFreshBelow]
      cases preEq with
      | Fresh n => exact absurd rfl ((hNonFresh n).1)
      | _ => trivial
    · -- neg mem
      simp only [litFreshBelow]
      cases mem with
      | Fresh n => exact absurd rfl ((hNonFresh n).2)
      | _ => trivial
    · -- pos Fresh(z)
      simp only [litFreshBelow, FVar.toVar, hZId, hAllocNext]
      exact Nat.lt_succ_self _
  have hWF3 := EncState.addClause_wf hWF2 _ hC3
  exact hWF3

/-- Fold of eventWitnessStep preserves well-formedness. -/
lemma eventWitnessStep_foldl_wf (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b)
    (hwf : acc.2.WellFormed)
    (hNonFresh : ∀ p ∈ pairs, ∀ n, p.1 ≠ Var.Fresh n ∧ p.2 ≠ Var.Fresh n) :
    (pairs.foldl (eventWitnessStep b) acc).2.WellFormed := by
  induction pairs generalizing acc with
  | nil => exact hwf
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hpNF : ∀ n, p.1 ≠ Var.Fresh n ∧ p.2 ≠ Var.Fresh n := by
      intro n
      exact hNonFresh p List.mem_cons_self n
    have hpsNF : ∀ q ∈ ps, ∀ n, q.1 ≠ Var.Fresh n ∧ q.2 ≠ Var.Fresh n := by
      intro q hq n
      exact hNonFresh q (List.mem_cons_of_mem p hq) n
    exact ih (eventWitnessStep b acc p) (eventWitnessStep_wf b acc p hwf hpNF) hpsNF

/-- eventWitnessStep_foldl produces Fresh vars below final nextFresh. -/
lemma eventWitnessStep_foldl_vars_fresh_below (b : Bounds S)
    (pairs : List (Var b × Var b)) (st : EncState b)
    (hNonFresh : ∀ p ∈ pairs, ∀ n, p.1 ≠ Var.Fresh n ∧ p.2 ≠ Var.Fresh n) :
    ∀ v ∈ (pairs.foldl (eventWitnessStep b) ([], st)).1, ∀ n, v = Var.Fresh n →
      n < (pairs.foldl (eventWitnessStep b) ([], st)).2.nextFresh := by
  apply eventWitnessStep_foldl_vars_fresh_below_aux
  · exact hNonFresh
  · intro v hv; simp only [List.not_mem_nil] at hv


variable [DecidableEq S.EventType]

/-- All pairs in eventWitnessPairs have notFresh components -/
lemma eventWitnessPairs_notFresh (b : Bounds S) (w : WId b) (evt : S.EventType)
    (pair : Var b × Var b) (hPair : pair ∈ eventWitnessPairs b w evt) :
    Var.notFresh b pair.1 ∧ Var.notFresh b pair.2 := by
  simp only [eventWitnessPairs, List.mem_filterMap] at hPair
  obtain ⟨w', _, hOpt⟩ := hPair
  -- hOpt tells us the filterMap produced pair from w'
  -- The filterMap condition is: if w'.p == w.p then match ... else none
  split at hOpt
  · -- w'.p == w.p is true
    rename_i hPEq
    split at hOpt
    · -- decodeMaybeEvent is some e'
      rename_i e' hDecode
      split at hOpt
      · -- e' = evt
        simp only [Option.some.injEq] at hOpt
        rw [← hOpt]
        constructor <;> simp only [Var.notFresh]
      · -- e' ≠ evt: contradiction (hOpt would be none = some pair)
        cases hOpt
    · -- decodeMaybeEvent is none: contradiction
      cases hOpt
  · -- w'.p ≠ w.p: contradiction
    cases hOpt

/-- encodeFormulaEvent increases nextFresh.
    encodeFormulaEvent does a fold with eventWitnessStep (allocates Fresh vars)
    then mkBigOrIff (allocates one more Fresh var). -/
lemma encodeFormulaEvent_nextFresh_mono (b : Bounds S) (w : WId b) (evt : S.EventType)
    (st : EncState b) :
    st.nextFresh ≤ (encodeFormulaEvent b w evt st).2.nextFresh := by
  simp only [encodeFormulaEvent]
  -- eventWitnessStep fold followed by mkBigOrIff
  -- Each eventWitnessStep allocates a Fresh var, and mkBigOrIff allocates one more
  -- So overall nextFresh increases by at least 1
  have hBigOr := mkBigOrIff_nextFresh b
    ((eventWitnessPairs b w evt).foldl (eventWitnessStep b) ([], st)).1
    ((eventWitnessPairs b w evt).foldl (eventWitnessStep b) ([], st)).2
  -- The foldl returns (vars, state) where state.nextFresh ≥ st.nextFresh
  -- because each step increases nextFresh by 1 (via allocFresh in eventWitnessStep)
  have hFold : st.nextFresh ≤ ((eventWitnessPairs b w evt).foldl
      (eventWitnessStep b) ([], st)).2.nextFresh :=
    foldl_eventWitnessStep_nextFresh_mono b _ ([], st)
  calc st.nextFresh
    _ ≤ ((eventWitnessPairs b w evt).foldl (eventWitnessStep b) ([], st)).2.nextFresh := hFold
    _ ≤ (mkBigOrIff b _ _).2.nextFresh := by simp only [hBigOr]; omega

/-- eventWitnessPairs produces only non-Fresh vars (PreEq and Mem). -/
lemma eventWitnessPairs_nonFresh (b : Bounds S) (w : WId b) (evt : Signature.EventType S) :
    ∀ p ∈ eventWitnessPairs b w evt, ∀ n, p.1 ≠ Var.Fresh n ∧ p.2 ≠ Var.Fresh n := by
  intro p hp n
  simp only [eventWitnessPairs, List.mem_filterMap] at hp
  obtain ⟨w', _, hSome⟩ := hp
  split at hSome
  · split at hSome
    · split at hSome
      · simp only [Option.some.injEq] at hSome
        subst hSome
        constructor <;> intro h <;> cases h
      · exact absurd hSome (Option.noConfusion)
    · exact absurd hSome (Option.noConfusion)
  · exact absurd hSome (Option.noConfusion)

variable [DecidableEq S.Value]

omit [DecidableEq S.EventType] in
/-- encodeTupleControl increases nextFresh by exactly 1.
    encodeTupleControl does allocFresh once then folds with addClause.
    Since addClause preserves nextFresh, the result is st.nextFresh + 1. -/
lemma encodeTupleControl_nextFresh (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars : List (Var b)) (st : EncState b) :
    (encodeTupleControl b learners tuple witnessVars st).2.nextFresh = st.nextFresh + 1 := by
  simp only [encodeTupleControl]
  have hAlloc := EncState.allocFresh_nextFresh b st
  -- The folds all use addClause which preserves nextFresh
  rw [foldl_nextFresh_eq, foldl_nextFresh_eq, EncState.addClause, hAlloc]
  · intro s _; simp [EncState.addClause]
  · intro s _; simp [EncState.addClause]

omit [DecidableEq S.EventType] in
/-- encodeTupleControl increases nextFresh. -/
lemma encodeTupleControl_nextFresh_mono (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars : List (Var b)) (st : EncState b) :
    st.nextFresh ≤ (encodeTupleControl b learners tuple witnessVars st).2.nextFresh := by
  rw [encodeTupleControl_nextFresh]; omega

/-! ## Structural Determinism for eventWitnessStep -/

/-- A single eventWitnessStep produces clauses that satisfy structural determinism.

The clauses are:
- [¬z, preEq] where z = Fresh(acc.nextFresh) and preEq is non-Fresh
- [¬z, mem] where mem is non-Fresh
- [¬preEq, ¬mem, z]

For st' with offset, z' = Fresh(acc.nextFresh + offset). The shifted assignment σ' maps
Fresh(n+offset) → σ(Fresh(n)) when n+offset ≥ threshold.

Key insight: non-Fresh vars evaluate the same under σ' and σ, and Fresh vars shift correctly. -/
lemma eventWitnessStep_structural_determinism (b : Bounds S)
    (acc acc' : List (Var b) × EncState b)
    (pair : Var b × Var b)
    (offset : Nat) (threshold : Nat)
    (hOffset : acc'.2.nextFresh = acc.2.nextFresh + offset)
    (hMono : acc.2.nextFresh ≤ acc'.2.nextFresh)
    (hPairNotFresh : Var.notFresh b pair.1 ∧ Var.notFresh b pair.2)
    (hThreshold : threshold ≤ acc.2.nextFresh + offset)
    (hWF : EncState.WellFormed acc.2)
    (σ : SAT.Assignment (Var b))
    (hSat : ∀ c ∈ (eventWitnessStep b acc pair).2.clauses,
            c ∉ acc.2.clauses → SAT.Clause.eval σ c = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < threshold then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v
    ∀ c ∈ (eventWitnessStep b acc' pair).2.clauses,
        c ∉ acc'.2.clauses → SAT.Clause.eval σ' c = true := by
  intro σ' c hcMem hcNew
  -- Unfold eventWitnessStep
  simp only [eventWitnessStep] at hcMem hSat
  simp only [EncState.addClause] at hcMem

  -- z = Fresh(acc.nextFresh), z' = Fresh(acc'.nextFresh) = Fresh(acc.nextFresh + offset)
  have hZId : (EncState.allocFresh b acc.2).1.id = acc.2.nextFresh := EncState.allocFresh_fst (b := b) acc.2
  have hZ'Id : (EncState.allocFresh b acc'.2).1.id = acc'.2.nextFresh := EncState.allocFresh_fst (b := b) acc'.2
  have hZ'Shift : (EncState.allocFresh b acc'.2).1.id = acc.2.nextFresh + offset := by
    rw [hZ'Id, hOffset]

  -- σ'(z') = σ(z) because z'.id = acc.nextFresh + offset ≥ threshold
  have hZ'Eval : σ' (FVar.toVar b (EncState.allocFresh b acc'.2).1) =
      σ (FVar.toVar b (EncState.allocFresh b acc.2).1) := by
    simp only [σ', FVar.toVar]
    -- acc'.2.nextFresh = acc.2.nextFresh + offset, so z'.id = acc.2.nextFresh + offset
    -- threshold ≤ acc.2.nextFresh + offset by hThreshold
    -- So z'.id ≥ threshold, meaning we use the else branch
    have hGe : ¬((EncState.allocFresh b acc'.2).1.id < threshold) := by
      rw [hZ'Id, hOffset]; omega
    simp only [hGe, ↓reduceIte]
    -- Now we need acc'.2.nextFresh - offset = acc.2.nextFresh
    -- Goal: σ (Var.Fresh ((EncState.allocFresh b acc'.2).1.id - offset)) =
    --       σ (Var.Fresh (EncState.allocFresh b acc.2).1.id)
    -- Use hZ'Id: (EncState.allocFresh b acc'.2).1.id = acc'.2.nextFresh
    -- Use hZId: (EncState.allocFresh b acc.2).1.id = acc.2.nextFresh
    -- Use hOffset: acc'.2.nextFresh = acc.2.nextFresh + offset
    -- So: acc'.2.nextFresh - offset = acc.2.nextFresh + offset - offset = acc.2.nextFresh
    have hEq : (EncState.allocFresh b acc'.2).1.id - offset =
               (EncState.allocFresh b acc.2).1.id := by
      rw [hZ'Id, hZId, hOffset]; omega
    simp only [hEq]

  -- σ'(pair.1) = σ(pair.1) and σ'(pair.2) = σ(pair.2) (non-Fresh vars)
  have hPair1Eval : σ' pair.1 = σ pair.1 := by
    simp only [σ']
    cases hp : pair.1 with
    | Fresh n =>
        rw [hp] at hPairNotFresh
        simp only [Var.notFresh] at hPairNotFresh
        exact False.elim hPairNotFresh.1
    | _ => rfl
  have hPair2Eval : σ' pair.2 = σ pair.2 := by
    simp only [σ']
    cases hp : pair.2 with
    | Fresh n =>
        rw [hp] at hPairNotFresh
        simp only [Var.notFresh] at hPairNotFresh
        exact False.elim hPairNotFresh.2
    | _ => rfl

  -- The three new clauses at st' correspond to three clauses at st
  -- Clause 3 (head): [¬pair.1, ¬pair.2, z']
  -- Clause 2: [¬z', pair.2]
  -- Clause 1: [¬z', pair.1]
  -- Old clauses from acc'.2.clauses

  -- Check old clauses first
  have hAllocClauses : (EncState.allocFresh b acc'.2).2.clauses = acc'.2.clauses :=
    EncState.allocFresh_clauses_eq (b := b) acc'.2

  cases hcMem with
  | head =>
      -- c = [¬pair.1, ¬pair.2, pos z']
      -- Corresponding at st: [¬pair.1, ¬pair.2, pos z]
      have hCorr : [SAT.Lit.neg pair.1, SAT.Lit.neg pair.2,
          SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b acc.2).1)] ∈
          (eventWitnessStep b acc pair).2.clauses := by
        -- Destruct acc and pair first to resolve let-bindings in eventWitnessStep
        obtain ⟨vars, stAcc⟩ := acc
        obtain ⟨preEq, mem⟩ := pair
        simp only [eventWitnessStep, EncState.addClause, List.mem_cons]
        left; trivial
      have hNotOld : [SAT.Lit.neg pair.1, SAT.Lit.neg pair.2,
          SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b acc.2).1)] ∉ acc.2.clauses := by
        -- This clause contains Fresh(acc.nextFresh) which is new
        intro hIn
        -- If the clause were in acc.clauses, WF would require Fresh vars < acc.nextFresh
        -- But this clause has Fresh(acc.nextFresh) which violates that
        have hWFClause := hWF _ hIn
        unfold clauseFreshBelow litFreshBelow at hWFClause
        have hLitMem : SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b acc.2).1) ∈
            [SAT.Lit.neg pair.1, SAT.Lit.neg pair.2,
             SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b acc.2).1)] := by simp
        have hBound := hWFClause _ hLitMem
        simp only [FVar.toVar] at hBound
        -- hBound : (EncState.allocFresh b acc.2).1.id < acc.2.nextFresh
        -- hZId : (EncState.allocFresh b acc.2).1.id = acc.2.nextFresh
        -- This gives acc.2.nextFresh < acc.2.nextFresh, contradiction
        exact Nat.lt_irrefl _ (hZId ▸ hBound)
      have hSatCorr := hSat _ hCorr hNotOld
      -- The clause at st' is [¬pair.1, ¬pair.2, pos z']
      -- The clause at st is [¬pair.1, ¬pair.2, pos z]
      -- They evaluate the same under σ'/σ because:
      -- - pair.1, pair.2 are non-Fresh → same value
      -- - z' maps to z via the shift
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hSatCorr
      simp only [hPair1Eval, hPair2Eval, hZ'Eval, hSatCorr]
  | tail _ h1 =>
      cases h1 with
      | head =>
          -- c = [¬z', pair.2]
          have hCorr : [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1),
              SAT.Lit.pos pair.2] ∈ (eventWitnessStep b acc pair).2.clauses := by
            obtain ⟨vars, stAcc⟩ := acc
            obtain ⟨preEq, mem⟩ := pair
            simp only [eventWitnessStep, EncState.addClause, List.mem_cons]
            right; left; trivial
          have hNotOld : [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1),
              SAT.Lit.pos pair.2] ∉ acc.2.clauses := by
            intro hIn
            have hWFClause := hWF _ hIn
            unfold clauseFreshBelow litFreshBelow at hWFClause
            have hLitMem : SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1) ∈
                [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1),
                 SAT.Lit.pos pair.2] := by simp
            have hBound := hWFClause _ hLitMem
            simp only [FVar.toVar] at hBound
            exact Nat.lt_irrefl _ (hZId ▸ hBound)
          have hSatCorr := hSat _ hCorr hNotOld
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hSatCorr
          simp only [hPair2Eval, hZ'Eval, hSatCorr]
      | tail _ h2 =>
          cases h2 with
          | head =>
              -- c = [¬z', pair.1] (the first clause added)
              -- The clause list structure after unfolding is:
              -- [clause3, clause2, clause1, ...allocFresh.clauses]
              -- where clause1 = [¬z, pair.1], clause2 = [¬z, pair.2], clause3 = [¬pair.1, ¬pair.2, z]
              have hCorr : [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1),
                  SAT.Lit.pos pair.1] ∈ (eventWitnessStep b acc pair).2.clauses := by
                obtain ⟨vars, stAcc⟩ := acc
                obtain ⟨preEq, mem⟩ := pair
                simp only [eventWitnessStep, EncState.addClause, List.mem_cons]
                right; right; left; trivial
              have hNotOld : [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1),
                  SAT.Lit.pos pair.1] ∉ acc.2.clauses := by
                intro hIn
                have hWFClause := hWF _ hIn
                unfold clauseFreshBelow litFreshBelow at hWFClause
                have hLitMem : SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1) ∈
                    [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b acc.2).1),
                     SAT.Lit.pos pair.1] := by simp
                have hBound := hWFClause _ hLitMem
                simp only [FVar.toVar] at hBound
                exact Nat.lt_irrefl _ (hZId ▸ hBound)
              have hSatCorr := hSat _ hCorr hNotOld
              simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
              simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or] at hSatCorr
              simp only [hPair1Eval, hZ'Eval, hSatCorr]
          | tail _ hOld =>
              -- c ∈ allocFresh.2.clauses = acc'.2.clauses
              rw [hAllocClauses] at hOld
              exact absurd hOld hcNew

/-! ## Fold Structural Determinism -/

/-- The length of witness vars from the fold equals the number of pairs. -/
lemma foldl_eventWitnessStep_length (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b) :
    (pairs.foldl (eventWitnessStep b) acc).1.length = acc.1.length + pairs.length := by
  induction pairs generalizing acc with
  | nil => simp
  | cons p ps ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, eventWitnessStep_vars]
      simp only [List.length_append, List.length_singleton]
      ring

/-- Clauses from eventWitnessStep fold are a subset of the final result. -/
lemma foldl_eventWitnessStep_clauses_subset (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b)
    (c : SAT.Clause (Var b)) (hc : c ∈ acc.2.clauses) :
    c ∈ (pairs.foldl (eventWitnessStep b) acc).2.clauses := by
  induction pairs generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hc
  | cons p ps ih =>
      simp only [List.foldl_cons]
      apply ih
      simp only [eventWitnessStep, EncState.addClause, EncState.allocFresh, List.mem_cons]
      right; right; right; exact hc

/-- Helper: folding only appends, preserving earlier elements -/
lemma foldl_eventWitnessStep_getElem_preserved (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b)
    (i : Nat) (hi : i < acc.1.length) :
    (pairs.foldl (eventWitnessStep b) acc).1[i]? = acc.1[i]? := by
  induction pairs generalizing acc i hi with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.foldl_cons]
      have hStep : (eventWitnessStep b acc p).1 = acc.1 ++ [Var.Fresh acc.2.nextFresh] := by
        simp only [eventWitnessStep, FVar.toVar, EncState.allocFresh]
      have hLenStep : (eventWitnessStep b acc p).1.length = acc.1.length + 1 := by
        rw [hStep]; simp
      have hi' : i < (eventWitnessStep b acc p).1.length := by rw [hLenStep]; omega
      rw [ih (eventWitnessStep b acc p) i hi', hStep]
      simp only [List.getElem?_append_left hi]

/-- The i-th witness var from the fold is Fresh(st.nextFresh + i).
    Uses get with a proof of bounds. -/
lemma foldl_eventWitnessStep_vars_indexed (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b)
    (i : Nat) (hi : i < pairs.length) :
    (pairs.foldl (eventWitnessStep b) acc).1[acc.1.length + i]? =
      some (Var.Fresh (acc.2.nextFresh + i)) := by
  induction pairs generalizing acc i with
  | nil => simp at hi
  | cons p ps ih =>
      simp only [List.foldl_cons]
      cases i with
      | zero =>
          simp only [Nat.add_zero]
          have hStep : (eventWitnessStep b acc p).1 = acc.1 ++ [Var.Fresh acc.2.nextFresh] := by
            simp only [eventWitnessStep, FVar.toVar, EncState.allocFresh]
          have hLenStep : (eventWitnessStep b acc p).1.length = acc.1.length + 1 := by
            rw [hStep]; simp
          rw [foldl_eventWitnessStep_getElem_preserved b ps (eventWitnessStep b acc p) acc.1.length
              (by rw [hLenStep]; omega)]
          rw [hStep]
          have hGe : acc.1.length ≥ acc.1.length := le_refl _
          simp only [List.getElem?_append_right hGe, Nat.sub_self]
          rfl
      | succ j =>
          simp only [List.length_cons] at hi
          have hj : j < ps.length := Nat.lt_of_succ_lt_succ hi
          have hIH := ih (eventWitnessStep b acc p) j hj
          have hLenStep : (eventWitnessStep b acc p).1.length = acc.1.length + 1 := by
            rw [eventWitnessStep_vars]; simp
          have hNextStep : (eventWitnessStep b acc p).2.nextFresh = acc.2.nextFresh + 1 :=
            eventWitnessStep_nextFresh_eq b acc p
          simp only [hLenStep, hNextStep] at hIH
          -- Goal: result[acc.1.length + (j + 1)]? = some (Var.Fresh (acc.2.nextFresh + (j + 1)))
          -- IH:  result[(acc.1.length + 1) + j]? = some (Var.Fresh ((acc.2.nextFresh + 1) + j))
          -- These are equal (both indices and values match)
          have hIdxEq : acc.1.length + (j + 1) = (acc.1.length + 1) + j := by omega
          have hValEq : acc.2.nextFresh + (j + 1) = (acc.2.nextFresh + 1) + j := by omega
          rw [hIdxEq, hValEq]
          exact hIH

/-- Structural determinism for the fold of eventWitnessStep.

For clauses that are NEW (not in the base accumulator), if σ satisfies them at st,
then σ' (shifted) satisfies the corresponding clauses at st'. -/
lemma foldl_eventWitnessStep_structural_determinism (b : Bounds S)
    (pairs : List (Var b × Var b))
    (acc acc' : List (Var b) × EncState b)
    (offset : Nat) (threshold : Nat)
    (hOffset : acc'.2.nextFresh = acc.2.nextFresh + offset)
    (hMono : acc.2.nextFresh ≤ acc'.2.nextFresh)
    (hPairsNotFresh : ∀ p ∈ pairs, Var.notFresh b p.1 ∧ Var.notFresh b p.2)
    (hThreshold : threshold ≤ acc.2.nextFresh + offset)
    (hWF : EncState.WellFormed acc.2)
    (σ : SAT.Assignment (Var b))
    (hSat : ∀ c ∈ (pairs.foldl (eventWitnessStep b) acc).2.clauses,
            c ∉ acc.2.clauses → SAT.Clause.eval σ c = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < threshold then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v
    ∀ c ∈ (pairs.foldl (eventWitnessStep b) acc').2.clauses,
        c ∉ acc'.2.clauses → SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  induction pairs generalizing acc acc' c with
  | nil =>
      -- No iterations: fold_st' = acc', fold_st = acc
      -- c ∈ acc'.clauses but c ∉ acc'.clauses by hcNew - contradiction
      simp only [List.foldl_nil] at hc
      exact absurd hc hcNew
  | cons p ps ih =>
      simp only [List.foldl_cons] at hc hSat
      -- One step: acc -> step_acc, acc' -> step_acc'
      -- Then fold ps starting from step_acc, step_acc'
      let step_acc := eventWitnessStep b acc p
      let step_acc' := eventWitnessStep b acc' p
      -- Offset is preserved through the step
      have hStepOffset : step_acc'.2.nextFresh = step_acc.2.nextFresh + offset := by
        simp only [step_acc', step_acc, eventWitnessStep_nextFresh_eq, hOffset]; omega
      have hStepMono : step_acc.2.nextFresh ≤ step_acc'.2.nextFresh := by
        simp only [step_acc', step_acc, eventWitnessStep_nextFresh_eq, hOffset]; omega
      have hPsNotFresh : ∀ q ∈ ps, Var.notFresh b q.1 ∧ Var.notFresh b q.2 := fun q hq =>
        hPairsNotFresh q (List.mem_cons_of_mem p hq)
      have hPNotFresh := hPairsNotFresh p (List.mem_cons.mpr (Or.inl rfl))
      have hStepThreshold : threshold ≤ step_acc.2.nextFresh + offset := by
        simp only [step_acc, eventWitnessStep_nextFresh_eq]; omega
      have hStepWF : EncState.WellFormed step_acc.2 := by
        apply eventWitnessStep_wf b acc p hWF
        intro n
        exact ⟨Var.notFresh_ne_Fresh b p.1 hPNotFresh.1 n,
               Var.notFresh_ne_Fresh b p.2 hPNotFresh.2 n⟩
      -- Case split: is c from the step or from the tail fold?
      by_cases hcStep : c ∈ step_acc'.2.clauses
      · -- c is from the first step (eventWitnessStep at acc')
        -- Need to show c ∉ acc'.clauses (we have hcNew) implies we can use step SD
        by_cases hcAcc' : c ∈ acc'.2.clauses
        · exact absurd hcAcc' hcNew
        · -- c is NEW in step_acc'.clauses (not in acc'.clauses)
          -- Use eventWitnessStep_structural_determinism
          have hStepSat : ∀ c ∈ step_acc.2.clauses,
              c ∉ acc.2.clauses → SAT.Clause.eval σ c = true := by
            intro c' hc' hcNotAcc
            -- c' is in step_acc.clauses but not in acc.clauses
            have hFoldMem : c' ∈ (ps.foldl (eventWitnessStep b) step_acc).2.clauses :=
              foldl_eventWitnessStep_clauses_subset b ps step_acc c' hc'
            exact hSat c' hFoldMem hcNotAcc
          exact eventWitnessStep_structural_determinism b acc acc' p offset threshold
            hOffset hMono hPNotFresh hThreshold hWF σ hStepSat c hcStep hcAcc'
      · -- c is from the tail fold (ps) starting from step_acc'
        -- Use IH with step_acc, step_acc' as new accumulators
        have hTailSat : ∀ c ∈ (ps.foldl (eventWitnessStep b) step_acc).2.clauses,
            c ∉ step_acc.2.clauses → SAT.Clause.eval σ c = true := by
          intro c' hc' hcNotStep
          by_cases hcAcc : c' ∈ acc.2.clauses
          · -- c' ∈ acc.clauses → c' ∈ step_acc.clauses by subset
            have hSubset : acc.2.clauses ⊆ step_acc.2.clauses := by
              intro x hx
              simp only [step_acc, eventWitnessStep, EncState.addClause, EncState.allocFresh,
                List.mem_cons]
              right; right; right; exact hx
            exact absurd (hSubset hcAcc) hcNotStep
          · exact hSat c' hc' hcAcc
        have hcNotStep' : c ∉ step_acc'.2.clauses := hcStep
        exact ih step_acc step_acc' hStepOffset hStepMono hPsNotFresh hStepThreshold
          hStepWF hTailSat c hc hcNotStep'

/-! ## Structural Determinism for encodeFormulaEvent -/

/-- Helper: clauses from addClause foldl are monotonic -/
lemma foldl_addClause_clauses_subset' (b : Bounds S) (u : Var b)
    (vs : List (Var b)) (acc : EncState b) :
    acc.clauses ⊆ (vs.foldl (fun stCur w =>
        EncState.addClause b stCur [SAT.Lit.neg w, SAT.Lit.pos u]) acc).clauses := by
  induction vs generalizing acc with
  | nil => exact fun _ h => h
  | cons v vs ih =>
      intro c hc
      simp only [List.foldl_cons]
      apply ih
      simp only [EncState.addClause, List.mem_cons]
      right; exact hc

/-- If c is in foldl result but not in base, then c is one of the added clauses -/
lemma foldl_addClause_clause_from_list (b : Bounds S) (u : Var b)
    (vs : List (Var b)) (acc : EncState b) (c : SAT.Clause (Var b))
    (hMem : c ∈ (vs.foldl (fun stCur w =>
        EncState.addClause b stCur [SAT.Lit.neg w, SAT.Lit.pos u]) acc).clauses)
    (hNotBase : c ∉ acc.clauses) :
    ∃ w ∈ vs, c = [SAT.Lit.neg w, SAT.Lit.pos u] := by
  induction vs generalizing acc with
  | nil =>
      simp only [List.foldl_nil] at hMem
      exact absurd hMem hNotBase
  | cons v vs ih =>
      simp only [List.foldl_cons] at hMem
      let acc' := EncState.addClause b acc [SAT.Lit.neg v, SAT.Lit.pos u]
      by_cases hAcc' : c ∈ acc'.clauses
      · -- c is in acc'.clauses = [new] :: acc.clauses
        simp only [acc', EncState.addClause, List.mem_cons] at hAcc'
        rcases hAcc' with rfl | hOld
        · exact ⟨v, List.mem_cons.mpr (Or.inl rfl), rfl⟩
        · exact absurd hOld hNotBase
      · -- c is not in acc'.clauses, use IH
        obtain ⟨w, hw, hEq⟩ := ih acc' hMem hAcc'
        exact ⟨w, List.mem_cons_of_mem v hw, hEq⟩

/-- Short clause structure lemma: clauses in mkBigOrIff's tail are either from base or short clauses -/
lemma mkBigOrIff_short_clauses_structure (b : Bounds S) (vs : List (Var b)) (st : EncState b)
    (c : SAT.Clause (Var b))
    (hTail : c ∈ (vs.foldl (fun stCur w =>
        EncState.addClause b stCur [SAT.Lit.neg w,
          SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)])
      (EncState.allocFresh b st).2).clauses) :
    c ∈ st.clauses ∨ ∃ v ∈ vs, c = [SAT.Lit.neg v,
        SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)] := by
  induction vs generalizing c st with
  | nil =>
      simp only [List.foldl_nil] at hTail
      rw [EncState.allocFresh_clauses_eq] at hTail
      left; exact hTail
  | cons v vs ih =>
      simp only [List.foldl_cons] at hTail
      -- After adding the first clause, we fold over vs
      let u := FVar.toVar b (EncState.allocFresh b st).1
      let st1 := EncState.addClause b (EncState.allocFresh b st).2 [SAT.Lit.neg v, SAT.Lit.pos u]
      -- The fold over vs with st1 as base
      have hFold : c ∈ (vs.foldl (fun stCur w =>
          EncState.addClause b stCur [SAT.Lit.neg w, SAT.Lit.pos u]) st1).clauses := hTail
      -- c is either in st1.clauses, or a new clause from the fold
      by_cases hc1 : c ∈ st1.clauses
      · -- c is in st1.clauses = [new_clause] ++ st.clauses (via allocFresh)
        simp only [st1, EncState.addClause, List.mem_cons] at hc1
        rcases hc1 with rfl | hOld
        · -- c is the newly added clause
          right; exact ⟨v, List.mem_cons.mpr (Or.inl rfl), rfl⟩
        · -- c is in (allocFresh st).clauses = st.clauses
          rw [EncState.allocFresh_clauses_eq] at hOld
          left; exact hOld
      · -- c is NOT in st1.clauses, so it was added by the fold over vs
        -- This means c = [¬w, u] for some w ∈ vs
        -- We need to trace through the fold
        -- Use induction on vs with the same pattern
        have hFromFold : c ∉ st1.clauses ∧ c ∈
            (vs.foldl (fun stCur w => EncState.addClause b stCur
              [SAT.Lit.neg w, SAT.Lit.pos u]) st1).clauses :=
          ⟨hc1, hFold⟩
        -- Prove by strong induction on vs that if c is in the fold but not in base,
        -- then c is one of the added clauses
        have := foldl_addClause_clause_from_list b u vs st1 c hFold hc1
        obtain ⟨w, hw, hcEq⟩ := this
        right; exact ⟨w, List.mem_cons_of_mem v hw, hcEq⟩

/-- Short clause membership in mkBigOrIff -/
lemma mkBigOrIff_short_clause_mem (b : Bounds S) (vs : List (Var b)) (st : EncState b)
    (v : Var b) (hv : v ∈ vs) :
    [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b ⟨st.nextFresh⟩)] ∈
      (mkBigOrIff b vs st).2.clauses := by
  have hU : (mkBigOrIff b vs st).1 = ⟨st.nextFresh⟩ := mkBigOrIff_fst b vs st
  have h := mkBigOrIff_unit_clause_mem b vs st hv
  simp only [hU] at h
  exact h

/-- The entire encodeFormulaEvent produces clauses that satisfy structural determinism.

encodeFormulaEvent structure:
1. eventWitnessPairs.foldl (eventWitnessStep b) ([], st) produces (witnessVars, st1)
2. mkBigOrIff b witnessVars st1 produces (u, stFinal)

All Fresh vars in clauses are:
- From eventWitnessStep: z_i at st.nextFresh + i
- From mkBigOrIff: u at st1.nextFresh = st.nextFresh + numPairs

These all shift uniformly by offset between st and st'. -/
lemma encodeFormulaEvent_structural_determinism (b : Bounds S)
    (w : WId b) (evt : Signature.EventType S)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st)
    (σ : SAT.Assignment (Var b))
    (hSat : ∀ c ∈ (encodeFormulaEvent b w evt st).2.clauses,
            c ∉ st.clauses → SAT.Clause.eval σ c = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < st'.nextFresh then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v
    ∀ c ∈ (encodeFormulaEvent b w evt st').2.clauses,
        c ∉ st'.clauses → SAT.Clause.eval σ' c = true := by
  intro σ' c hc hcNew
  -- Unfold encodeFormulaEvent
  simp only [encodeFormulaEvent] at hc hSat

  -- Define intermediate states
  let pairs := eventWitnessPairs b w evt
  let fold_st := pairs.foldl (eventWitnessStep b) ([], st)
  let fold_st' := pairs.foldl (eventWitnessStep b) ([], st')

  -- Key facts about fold offsets
  have hFoldOffset : fold_st'.2.nextFresh = fold_st.2.nextFresh + offset := by
    simp only [fold_st', fold_st, foldl_eventWitnessStep_nextFresh_eq, hOffset]; ring
  have hFoldMono : fold_st.2.nextFresh ≤ fold_st'.2.nextFresh := by
    simp only [fold_st', fold_st, foldl_eventWitnessStep_nextFresh_eq, hOffset]; omega

  -- Check if c is from fold or mkBigOrIff
  by_cases hcFold : c ∈ fold_st'.2.clauses
  · -- c is from the fold
    by_cases hcBase : c ∈ st'.clauses
    · exact absurd hcBase hcNew
    · -- c is NEW from the fold (not in st'.clauses)
      have hPairsNotFresh := eventWitnessPairs_notFresh b w evt
      have hFoldSat : ∀ c ∈ fold_st.2.clauses, c ∉ st.clauses → SAT.Clause.eval σ c = true := by
        intro c' hc' hcNotSt
        have hInFinal : c' ∈ (mkBigOrIff b fold_st.1 fold_st.2).2.clauses :=
          mkBigOrIff_clauses_subset b fold_st.1 fold_st.2 hc'
        exact hSat c' hInFinal hcNotSt
      have hThreshold : st'.nextFresh ≤ st.nextFresh + offset := by omega
      exact foldl_eventWitnessStep_structural_determinism b pairs ([], st) ([], st')
        offset st'.nextFresh hOffset hMono hPairsNotFresh hThreshold hWF σ hFoldSat c hcFold hcBase
  · -- c is NEW from mkBigOrIff (not in fold_st'.clauses)
    -- Use mkBigOrIff_clause_mem_iff to characterize c
    have hMem := mkBigOrIff_clause_mem_iff b fold_st'.1 fold_st'.2 c
    rw [hMem] at hc
    rcases hc with hcInFold | ⟨v', hV'Mem, hCEq⟩ | hBackward
    · -- c ∈ fold_st'.clauses - contradiction
      exact absurd hcInFold hcFold
    · -- c is a short clause [¬v', u'] where v' ∈ fold_st'.1
      -- Find the index of v' and the corresponding v in fold_st.1
      have hIdx := List.mem_iff_get.mp hV'Mem
      obtain ⟨⟨i, hi'⟩, hGet'⟩ := hIdx
      have hLen : fold_st.1.length = fold_st'.1.length := by
        simp only [fold_st, fold_st', foldl_eventWitnessStep_length]
      have hi : i < fold_st.1.length := hLen.symm ▸ hi'
      let v := fold_st.1.get ⟨i, hi⟩
      have hVMem : v ∈ fold_st.1 := List.get_mem _ ⟨i, hi⟩
      -- The short clause at st is [¬v, u]
      have hShortSt : [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (mkBigOrIff b fold_st.1 fold_st.2).1)] ∈
          (mkBigOrIff b fold_st.1 fold_st.2).2.clauses :=
        mkBigOrIff_unit_clause_mem b fold_st.1 fold_st.2 hVMem
      have hNotInBase : [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (mkBigOrIff b fold_st.1 fold_st.2).1)] ∉
          st.clauses := by
        intro hIn
        have hWFClause := hWF _ hIn
        have hUId := mkBigOrIff_fst b fold_st.1 fold_st.2
        have hLit : SAT.Lit.pos (FVar.toVar b (mkBigOrIff b fold_st.1 fold_st.2).1) ∈
            [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (mkBigOrIff b fold_st.1 fold_st.2).1)] := by simp
        have hBound := hWFClause _ hLit
        simp only [litFreshBelow, FVar.toVar] at hBound
        have hFoldMono' : st.nextFresh ≤ fold_st.2.nextFresh :=
          foldl_eventWitnessStep_nextFresh_mono b pairs ([], st)
        simp only [hUId] at hBound
        exact Nat.not_lt.mpr hFoldMono' hBound
      have hSatShort := hSat _ hShortSt hNotInBase

      -- v is Fresh(st.nextFresh + i), v' is Fresh(st'.nextFresh + i)
      have hFoldLen : fold_st.1.length = pairs.length := by
        simp only [fold_st, foldl_eventWitnessStep_length, List.length_nil, Nat.zero_add]
      have hFoldLen' : fold_st'.1.length = pairs.length := by
        simp only [fold_st', foldl_eventWitnessStep_length, List.length_nil, Nat.zero_add]
      have hiPairs : i < pairs.length := hFoldLen ▸ hi
      have hi'Pairs : i < pairs.length := hFoldLen' ▸ hi'
      have hVFresh : v = Var.Fresh (st.nextFresh + i) := by
        have hVarsEq := foldl_eventWitnessStep_vars_indexed b pairs ([], st) i hiPairs
        simp only [List.length_nil, Nat.zero_add] at hVarsEq
        have hGetEq : fold_st.1[i]? = some v := List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
        rw [hGetEq] at hVarsEq
        exact Option.some.inj hVarsEq
      have hV'Fresh : v' = Var.Fresh (st'.nextFresh + i) := by
        have hVarsEq := foldl_eventWitnessStep_vars_indexed b pairs ([], st') i hi'Pairs
        simp only [List.length_nil, Nat.zero_add] at hVarsEq
        have hGetEq : fold_st'.1[i]? = some v' := by
          rw [List.getElem?_eq_some_iff]
          refine ⟨hi', ?_⟩
          simp only [List.get_eq_getElem] at hGet'
          exact hGet'
        rw [hGetEq] at hVarsEq
        exact Option.some.inj hVarsEq
      have hU' := mkBigOrIff_fst b fold_st'.1 fold_st'.2
      have hU := mkBigOrIff_fst b fold_st.1 fold_st.2

      simp only [hCEq, SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, or_false, SAT.Lit.eval]
      simp only [SAT.Clause.eval_eq_any, List.any_cons, List.any_nil, or_false, SAT.Lit.eval,
        FVar.toVar, hU] at hSatShort

      simp only [σ', hV'Fresh, hU', FVar.toVar]
      have hV'Ge : ¬(st'.nextFresh + i < st'.nextFresh) := by omega
      have hU'Ge : ¬(fold_st'.2.nextFresh < st'.nextFresh) := by
        have hMono' : st'.nextFresh ≤ fold_st'.2.nextFresh :=
          foldl_eventWitnessStep_nextFresh_mono b pairs ([], st')
        omega
      simp only [hV'Ge, hU'Ge, ↓reduceIte]
      have hV'Shift : st'.nextFresh + i - offset = st.nextFresh + i := by
        rw [hOffset]; omega
      have hU'Shift : fold_st'.2.nextFresh - offset = fold_st.2.nextFresh := by
        rw [hFoldOffset]; omega
      rw [hV'Shift, hU'Shift, ← hVFresh]
      exact hSatShort
    · -- c is the long clause [¬u', v'_1, ..., v'_n]
      have hLongSt : (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b fold_st.1 fold_st.2).1) ::
          fold_st.1.map SAT.Lit.pos) ∈ (mkBigOrIff b fold_st.1 fold_st.2).2.clauses :=
        mkBigOrIff_long_clause_mem b fold_st.1 fold_st.2
      have hNotInBase : (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b fold_st.1 fold_st.2).1) ::
          fold_st.1.map SAT.Lit.pos) ∉ st.clauses := by
        intro hIn
        have hUId := mkBigOrIff_fst b fold_st.1 fold_st.2
        have hWFClause := hWF _ hIn
        have hLit : SAT.Lit.neg (FVar.toVar b (mkBigOrIff b fold_st.1 fold_st.2).1) ∈
            (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b fold_st.1 fold_st.2).1) ::
              fold_st.1.map SAT.Lit.pos) := List.Mem.head _
        have hBound := hWFClause _ hLit
        simp only [litFreshBelow, FVar.toVar, hUId] at hBound
        have hFoldMono' : st.nextFresh ≤ fold_st.2.nextFresh :=
          foldl_eventWitnessStep_nextFresh_mono b pairs ([], st)
        exact Nat.not_lt.mpr hFoldMono' hBound
      have hSatLong := hSat _ hLongSt hNotInBase

      simp only [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatLong ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatLong
      rcases hLitMem with ⟨⟩ | ⟨_, hMapMem⟩
      · -- lit = ¬u
        have hU' := mkBigOrIff_fst b fold_st'.1 fold_st'.2
        have hU := mkBigOrIff_fst b fold_st.1 fold_st.2
        refine ⟨SAT.Lit.neg (FVar.toVar b (mkBigOrIff b fold_st'.1 fold_st'.2).1), ?_, ?_⟩
        · rw [hBackward]; exact List.Mem.head _
        · simp only [SAT.Lit.eval, FVar.toVar, hU']
          simp only [SAT.Lit.eval, FVar.toVar, hU] at hLitTrue
          simp only [σ']
          have hGe : ¬(fold_st'.2.nextFresh < st'.nextFresh) := by
            have hMono' : st'.nextFresh ≤ fold_st'.2.nextFresh :=
              foldl_eventWitnessStep_nextFresh_mono b pairs ([], st')
            omega
          simp only [hGe, ↓reduceIte]
          have hEq : fold_st'.2.nextFresh - offset = fold_st.2.nextFresh := by
            rw [hFoldOffset]; omega
          rw [hEq]
          exact hLitTrue
      · -- lit = pos(v_i) for some v_i in fold_st.1
        obtain ⟨v, hVMem, hLitEq⟩ := List.mem_map.mp hMapMem
        have hLen : fold_st.1.length = fold_st'.1.length := by
          simp only [fold_st, fold_st', foldl_eventWitnessStep_length]
        have hIdx := List.mem_iff_get.mp hVMem
        obtain ⟨⟨i, hi⟩, hGet⟩ := hIdx
        have hi' : i < fold_st'.1.length := hLen ▸ hi
        let v' := fold_st'.1.get ⟨i, hi'⟩
        have hV'Mem : v' ∈ fold_st'.1 := List.get_mem _ ⟨i, hi'⟩
        have hPosV'Mem : SAT.Lit.pos v' ∈ fold_st'.1.map SAT.Lit.pos :=
          List.mem_map_of_mem (f := SAT.Lit.pos) hV'Mem
        refine ⟨SAT.Lit.pos v', ?_, ?_⟩
        · rw [hBackward]; exact List.mem_cons_of_mem _ hPosV'Mem
        · simp only [SAT.Lit.eval]
          simp only [← hLitEq, SAT.Lit.eval] at hLitTrue
          have hFoldLenV : fold_st.1.length = pairs.length := by
            simp only [fold_st, foldl_eventWitnessStep_length, List.length_nil, Nat.zero_add]
          have hFoldLenV' : fold_st'.1.length = pairs.length := by
            simp only [fold_st', foldl_eventWitnessStep_length, List.length_nil, Nat.zero_add]
          have hiPairsV : i < pairs.length := hFoldLenV ▸ hi
          have hi'PairsV : i < pairs.length := hFoldLenV' ▸ hi'
          have hVFresh : v = Var.Fresh (st.nextFresh + i) := by
            have hVarsEq := foldl_eventWitnessStep_vars_indexed b pairs ([], st) i hiPairsV
            simp only [List.length_nil, Nat.zero_add] at hVarsEq
            have hGetEq : fold_st.1[i]? = some v := by
              rw [List.getElem?_eq_some_iff]
              refine ⟨hi, ?_⟩
              simp only [List.get_eq_getElem] at hGet
              exact hGet
            rw [hGetEq] at hVarsEq
            exact Option.some.inj hVarsEq
          have hV'Fresh : v' = Var.Fresh (st'.nextFresh + i) := by
            have hVarsEq := foldl_eventWitnessStep_vars_indexed b pairs ([], st') i hi'PairsV
            simp only [List.length_nil, Nat.zero_add] at hVarsEq
            have hGetEq : fold_st'.1[i]? = some v' :=
              List.getElem?_eq_some_iff.mpr ⟨hi', rfl⟩
            rw [hGetEq] at hVarsEq
            exact Option.some.inj hVarsEq
          simp only [σ', hV'Fresh]
          have hGe : ¬(st'.nextFresh + i < st'.nextFresh) := by omega
          simp only [hGe, ↓reduceIte]
          have hShift : st'.nextFresh + i - offset = st.nextFresh + i := by
            rw [hOffset]; omega
          rw [hShift, ← hVFresh]
          exact hLitTrue

end Encoding
