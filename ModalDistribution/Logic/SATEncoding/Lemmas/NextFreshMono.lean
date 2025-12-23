import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Lemmas.Basic

/-!
# NextFresh Monotonicity Lemmas

This file contains lemmas about nextFresh counter monotonicity:
- `foldl_nextFresh_eq`: foldl preserves nextFresh if each step preserves it
- `foldl_nextFresh_mono`: foldl is monotonic if each step is monotonic
- `addPreEqFrom_nextFresh_mono`: addPreEqFrom is monotonic in nextFresh
- `addPreEqPair_newClause_fresh_ge`: Fresh vars in new clauses have index ≥ input nextFresh
- `addPreEqFrom_newClause_fresh_ge`: Fresh vars in new clauses have index ≥ input nextFresh
- `addPreEqReflAll_nextFresh`: addPreEqReflAll preserves nextFresh
- `addPreEqReflAll_wf`: addPreEqReflAll preserves well-formedness
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}

/-- Helper: foldl preserves nextFresh if each step preserves it. -/
lemma foldl_nextFresh_eq {α : Type*} (b : Bounds S)
    (xs : List α) (st : EncState b)
    (f : EncState b → α → EncState b)
    (hPres : ∀ s x, (f s x).nextFresh = s.nextFresh) :
    (xs.foldl f st).nextFresh = st.nextFresh := by
  induction xs generalizing st with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih, hPres]

/-- Helper: foldl is monotonic in nextFresh if each step is monotonic. -/
lemma foldl_nextFresh_mono {α : Type*} (b : Bounds S)
    (xs : List α) (st : EncState b)
    (f : EncState b → α → EncState b)
    (hMono : ∀ s x, s.nextFresh ≤ (f s x).nextFresh) :
    st.nextFresh ≤ (xs.foldl f st).nextFresh := by
  induction xs generalizing st with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (hMono st hd) (ih (f st hd))

/-- The control variable from mkBigOrIff has id < output state's nextFresh.
    This follows from: u.id = st.nextFresh and output.nextFresh = st.nextFresh + 1. -/
lemma mkBigOrIff_controlVar_lt_nextFresh (b : Bounds S) (vs : List (Var b)) (st : EncState b) :
    (mkBigOrIff b vs st).1.id < (mkBigOrIff b vs st).2.nextFresh := by
  have hFst := mkBigOrIff_fst (S := S) b vs st
  have hSnd := mkBigOrIff_nextFresh b vs st
  rw [hFst, hSnd]
  exact Nat.lt_succ_self _

/-- addPreEqReflAll preserves nextFresh. -/
lemma addPreEqReflAll_nextFresh (b : Bounds S) (st : EncState b) :
    (addPreEqReflAll b st).nextFresh = st.nextFresh := by
  simp only [addPreEqReflAll]
  rw [foldl_nextFresh_eq]
  intro s _; simp [EncState.addClause]

/-- addPreEqReflAll preserves well-formedness.
    It only adds clauses of the form [pos (PreEq t t)] which contain no Fresh vars. -/
lemma addPreEqReflAll_wf (b : Bounds S) (st : EncState b) (hwf : st.WellFormed) :
    (addPreEqReflAll b st).WellFormed := by
  simp only [addPreEqReflAll]
  apply (foldl_addClause_wf_mem (Bounds.timesL b) st
    (fun t => [SAT.Lit.pos (Var.PreEq t t)]) hwf _).1
  intro t _ lit hLit
  simp only [List.mem_singleton] at hLit
  subst hLit
  simp only [litFreshBelow]
  trivial

variable [DecidableEq S.EventType]

/-- addPreEqFrom is monotonic in nextFresh.
    addPreEqFrom uses allocFresh via mkY, mkOw, mkDw, preEqAccStep, etc.
    so nextFresh may increase. -/
lemma addPreEqFrom_nextFresh_mono (b : Bounds S) (ti : b.times) (st : EncState b) :
    st.nextFresh ≤ (addPreEqFrom b ti st).nextFresh := by
  simp only [addPreEqFrom]
  apply foldl_nextFresh_mono
  intro s H'
  exact addPreEqPair_nextFresh_mono b ti H' s

/-- Fresh vars in NEW clauses from addPreEqPair have index ≥ st.nextFresh.
    addPreEqPair allocates Fresh vars starting from st.nextFresh, so any
    Fresh var in a new clause will have index ≥ st.nextFresh. -/
lemma addPreEqPair_newClause_fresh_ge (b : Bounds S) (H0 H' : b.times) (st : EncState b)
    (c : SAT.Clause (Var b)) (hc : c ∈ (addPreEqPair b H0 H' st).clauses)
    (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ st.nextFresh := by
  -- addPreEqPair = addPreEqPair_core + optional reflexivity unit clause
  -- addPreEqPair_core uses preEqObligationStep folds, allocFresh, preEqAccStep folds,
  -- addPreEqExpose
  -- All of these allocate Fresh vars starting from the input nextFresh
  -- The reflexivity unit clause [pos (PreEq H0 H0)] has no Fresh vars
  classical
  unfold addPreEqPair at hc
  by_cases hEq : H0 = H'
  · -- Reflexive case: addClause [pos (PreEq H0 H0)] after addPreEqPair_core
    subst hEq
    simp only [↓reduceIte, EncState.addClause] at hc
    cases hc with
    | head =>
        -- c = [pos (PreEq H0 H0)] which has no Fresh vars
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
        rw [hLit] at hFresh; simp only [SAT.Lit.getVar] at hFresh
        exact Var.noConfusion hFresh
    | tail _ hTail =>
        -- c is from addPreEqPair_core
        have hNotStCore : c ∉ st.clauses := hcNotOld
        exact addPreEqPair_core_newClause_fresh_ge b H0 H0 st c hTail hNotStCore lit hLit n hFresh
  · -- Non-reflexive case: just addPreEqPair_core
    simp only [hEq, ↓reduceIte] at hc
    exact addPreEqPair_core_newClause_fresh_ge b H0 H' st c hc hcNotOld lit hLit n hFresh

/-- Fresh vars in NEW clauses from addPreEqFrom have index ≥ st.nextFresh.
    addPreEqFrom internally allocates Fresh vars for Tseytin gadgets, but any
    Fresh var in a new clause will have index ≥ the input nextFresh. -/
lemma addPreEqFrom_newClause_fresh_ge (b : Bounds S) (ti : b.times) (st : EncState b)
    (c : SAT.Clause (Var b)) (hc : c ∈ (addPreEqFrom b ti st).clauses) (hcNotOld : c ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ c) (n : Nat)
    (hFresh : SAT.Lit.getVar lit = Var.Fresh n) :
    n ≥ st.nextFresh := by
  -- addPreEqFrom b ti st = (Bounds.timesL b).foldl (fun acc H' => addPreEqPair b ti H' acc) st
  -- Use induction on the fold. Each step preserves WF and clauses are monotonic.
  simp only [addPreEqFrom] at hc
  -- Generalize over the fold list and prove for arbitrary accumulator
  suffices h : ∀ (times : List b.times) (acc : EncState b),
      st.nextFresh ≤ acc.nextFresh →
      c ∈ (times.foldl (fun stCur t => addPreEqPair b ti t stCur) acc).clauses →
      c ∉ acc.clauses →
      n ≥ st.nextFresh by
    exact h (Bounds.timesL b) st (Nat.le_refl _) hc hcNotOld
  intro times
  induction times with
  | nil =>
      intro acc _ hcIn hcNotAcc
      simp only [List.foldl_nil] at hcIn
      exact absurd hcIn hcNotAcc
  | cons t ts ih =>
      intro acc hAccGeSt hcIn hcNotAcc
      simp only [List.foldl_cons] at hcIn
      by_cases hcStep : c ∈ (addPreEqPair b ti t acc).clauses
      · -- c is in addPreEqPair output
        by_cases hcInAcc : c ∈ acc.clauses
        · exact absurd hcInAcc hcNotAcc
        · -- c is NEW from addPreEqPair
          have hFreshGeAcc := addPreEqPair_newClause_fresh_ge b ti t acc c hcStep hcInAcc
            lit hLit n hFresh
          omega
      · -- c ∉ (addPreEqPair output).clauses, so c is from tail fold
        have hStepMono : acc.nextFresh ≤ (addPreEqPair b ti t acc).nextFresh :=
          addPreEqPair_nextFresh_mono b ti t acc
        exact ih (addPreEqPair b ti t acc) (Nat.le_trans hAccGeSt hStepMono) hcIn hcStep

end Encoding
