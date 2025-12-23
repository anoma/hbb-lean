import ModalDistribution.Logic.SATEncoding.FormulaEncoding

/-!
# Basic Formula Encoding Lemmas

This file contains foundational lemmas about the formula encoding:
- Variable shifting definitions and lemmas
- Clause evaluation preservation under assignment modifications
- Basic foldl helpers for addClause
- Non-Fresh clause structural lemmas

These serve as building blocks for the structural determinism and
well-formedness preservation lemmas.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}

/-! ## Variable Shifting -/

/-- Shift a variable by an offset (only affects Fresh vars). -/
def Var.shift (b : Bounds S) (v : Var b) (offset : Nat) : Var b :=
  match v with
  | Var.Fresh n => Var.Fresh (n + offset)
  | v => v

/-- Unshift a variable by an offset (only affects Fresh vars). -/
def Var.unshift (b : Bounds S) (v : Var b) (offset : Nat) : Var b :=
  match v with
  | Var.Fresh n => Var.Fresh (n - offset)
  | v => v

/-- Shift and unshift are inverse for Fresh vars. -/
lemma Var.unshift_shift (b : Bounds S) (v : Var b) (offset : Nat) :
    Var.unshift b (Var.shift b v offset) offset = v := by
  cases v <;> simp [Var.shift, Var.unshift]

/-- Unshift then shift is identity for Fresh vars with n >= offset. -/
lemma Var.shift_unshift (b : Bounds S) (n : Nat) (offset : Nat) (h : offset ≤ n) :
    Var.shift b (Var.unshift b (Var.Fresh (S := S) n) offset) offset = Var.Fresh n := by
  simp [Var.shift, Var.unshift, Nat.sub_add_cancel h]

/-- The shifted assignment used in structural determinism proofs.
    Maps Fresh vars ≥ threshold to their unshifted counterparts. -/
def shiftedAssignment (b : Bounds S) (σ : SAT.Assignment (Var b)) (threshold : Nat) (offset : Nat) :
    SAT.Assignment (Var b) := fun v =>
  match v with
  | Var.Fresh n => if n < threshold then σ v else σ (Var.unshift b v offset)
  | _ => σ v

/-- Evaluating shiftedAssignment at the threshold itself gives the unshifted value. -/
lemma shiftedAssignment_at_threshold (b : Bounds S) (σ : SAT.Assignment (Var b))
    (threshold offset : Nat) :
    shiftedAssignment b σ threshold offset (Var.Fresh threshold) =
      σ (Var.Fresh (threshold - offset)) := by
  simp only [shiftedAssignment, Nat.lt_irrefl, ↓reduceIte, Var.unshift]

/-- Two shifted assignments with different thresholds agree on Fresh vars ≥ the higher threshold.
    This is the key lemma for composing IH results in recursive cases. -/
lemma shiftedAssignment_agree_ge (b : Bounds S) (σ : SAT.Assignment (Var b))
    (threshold1 threshold2 offset : Nat) (hLe : threshold1 ≤ threshold2)
    (n : Nat) (hGe : n ≥ threshold2) :
    shiftedAssignment b σ threshold1 offset (Var.Fresh n) =
    shiftedAssignment b σ threshold2 offset (Var.Fresh n) := by
  simp only [shiftedAssignment, Var.unshift]
  have hNotLt1 : ¬(n < threshold1) := by omega
  have hNotLt2 : ¬(n < threshold2) := by omega
  simp only [if_neg hNotLt1, if_neg hNotLt2]

/-- σ' agrees with σ on vars where Fresh index < bound. -/
lemma shifted_assignment_agrees_below (b : Bounds S) (σ : SAT.Assignment (Var b))
    (bound offset : Nat) (v : Var b)
    (hBelow : ∀ n, v = Var.Fresh n → n < bound) :
    let σ' := fun v' =>
      match v' with
      | Var.Fresh n => if n < bound then σ v' else σ (Var.unshift b v' offset)
      | _ => σ v'
    σ' v = σ v := by
  intro σ'
  cases v with
  | Fresh n =>
      have hLt := hBelow n rfl
      simp only [σ', hLt, ↓reduceIte]
  | _ => rfl

/-! ## Literal and Clause Evaluation -/

/-- Helper: get the variable from a literal. -/
def SAT.Lit.getVar {V} : SAT.Lit V → V
  | .pos v => v
  | .neg v => v

/-- A clause has no Fresh variables. -/
def clauseHasNoFresh {S : Signature} {b : Bounds S} (clause : SAT.Clause (Var b)) : Prop :=
  ∀ lit ∈ clause, ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n

/-- Non-Fresh clauses in st are preserved in st'.
    This is the appropriate clause compatibility condition for structural determinism:
    only non-Fresh clauses need to be preserved because Fresh clauses are handled
    via the well-formedness argument. -/
def nonFreshClausesCompat {S : Signature} {b : Bounds S}
    (st st' : EncState b) : Prop :=
  ∀ c ∈ st.clauses, clauseHasNoFresh c → c ∈ st'.clauses

/-- Full clause subset implies non-Fresh clause compatibility. -/
lemma subset_implies_nonFreshCompat {S : Signature} {b : Bounds S}
    (st st' : EncState b)
    (h : st.clauses ⊆ st'.clauses) : nonFreshClausesCompat st st' := by
  intro c hc _
  exact h hc

/-- Literal evaluation depends only on the var's assignment value. -/
lemma lit_eval_of_var_eq (b : Bounds S)
    (σ σ' : SAT.Assignment (Var b))
    (lit : SAT.Lit (Var b))
    (hEq : σ' (SAT.Lit.getVar lit) = σ (SAT.Lit.getVar lit)) :
    SAT.Lit.eval σ' lit = SAT.Lit.eval σ lit := by
  cases lit with
  | pos v => simp only [SAT.Lit.eval, SAT.Lit.getVar] at hEq ⊢; exact hEq
  | neg v => simp only [SAT.Lit.eval, SAT.Lit.getVar] at hEq ⊢; rw [hEq]

/-- Helper: foldl with || is preserved when literal evaluations agree. -/
private lemma foldl_or_lit_eval_congr (b : Bounds S)
    (σ σ' : SAT.Assignment (Var b))
    (C : List (SAT.Lit (Var b))) (init : Bool)
    (hAgree : ∀ lit ∈ C, σ' (SAT.Lit.getVar lit) = σ (SAT.Lit.getVar lit)) :
    List.foldl (fun acc lit => acc || SAT.Lit.eval σ' lit) init C =
    List.foldl (fun acc lit => acc || SAT.Lit.eval σ lit) init C := by
  induction C generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hHd := hAgree hd (List.mem_cons_self ..)
    have hTl := fun lit hLit => hAgree lit (List.mem_cons_of_mem hd hLit)
    rw [lit_eval_of_var_eq b σ σ' hd hHd]
    exact ih _ hTl

/-- Clause evaluation is preserved when assignment agrees on all clause vars. -/
lemma clause_eval_of_agreement (b : Bounds S)
    (σ σ' : SAT.Assignment (Var b))
    (clause : SAT.Clause (Var b))
    (hAgree : ∀ lit ∈ clause, σ' (SAT.Lit.getVar lit) = σ (SAT.Lit.getVar lit)) :
    SAT.Clause.eval σ' clause = SAT.Clause.eval σ clause := by
  simp only [SAT.Clause.eval]
  exact foldl_or_lit_eval_congr b σ σ' clause false hAgree

/-- For a well-formed state, σ' (which agrees with σ on vars below nextFresh)
    evaluates inherited clauses the same as σ. -/
lemma inherited_clause_eval (b : Bounds S) (st' : EncState b)
    (hWF : EncState.WellFormed st')
    (σ : SAT.Assignment (Var b)) (offset : Nat)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ st'.clauses)
    (hSatBase : st'.clauses.all (SAT.Clause.eval σ) = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < st'.nextFresh then σ v else σ (Var.unshift b v offset)
      | _ => σ v
    SAT.Clause.eval σ' clause = true := by
  intro σ'
  -- σ' agrees with σ on all vars in clause (by WF)
  have hAgree : ∀ lit ∈ clause, σ' (SAT.Lit.getVar lit) = σ (SAT.Lit.getVar lit) := by
    intro lit hLit
    -- By WF, all Fresh vars in clause have index < st'.nextFresh
    have hClauseWF := hWF clause hClause
    unfold clauseFreshBelow litFreshBelow at hClauseWF
    have hLitWF := hClauseWF lit hLit
    cases lit with
    | pos v =>
        simp only [SAT.Lit.getVar] at hLitWF ⊢
        cases v with
        | Fresh n =>
            -- σ'(Fresh n) = if n < nextFresh then σ(Fresh n) else ...
            -- hLitWF : n < st'.nextFresh
            simp only [σ']
            split
            · rfl
            · exact absurd hLitWF (by assumption)
        | _ => rfl
    | neg v =>
        simp only [SAT.Lit.getVar] at hLitWF ⊢
        cases v with
        | Fresh n =>
            simp only [σ']
            split
            · rfl
            · exact absurd hLitWF (by assumption)
        | _ => rfl
  rw [clause_eval_of_agreement b σ σ' clause hAgree]
  exact List.all_eq_true.mp hSatBase clause hClause

/-- A clause containing only non-Fresh vars is satisfied by σ' iff satisfied by σ,
    where σ' is the shifted assignment (σ' = σ on non-Fresh vars). -/
lemma nonFresh_clause_eval (b : Bounds S) (st' : EncState b)
    (σ : SAT.Assignment (Var b)) (offset : Nat)
    (clause : SAT.Clause (Var b))
    (hNoFresh : ∀ lit ∈ clause, ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < st'.nextFresh then σ v else σ (Var.unshift b v offset)
      | _ => σ v
    SAT.Clause.eval σ' clause = SAT.Clause.eval σ clause := by
  intro σ'
  apply clause_eval_of_agreement
  intro lit hLit
  have hNotFresh := hNoFresh lit hLit
  cases hv : SAT.Lit.getVar lit with
  | Fresh n => exact absurd hv (hNotFresh n)
  | _ => rfl

/-! ## AddClause Fold Helpers -/

/-- Helper: all clauses added by foldl with addClause satisfy a predicate if each clause does. -/
lemma foldl_addClause_all_satisfy {α : Type} (b : Bounds S)
    (P : SAT.Clause (Var b) → Prop)
    (mkClause : α → SAT.Clause (Var b)) (xs : List α) (st : EncState b)
    (hBase : ∀ c ∈ st.clauses, P c)
    (hNew : ∀ x ∈ xs, P (mkClause x)) :
    ∀ c ∈ (xs.foldl (fun stCur x => EncState.addClause b stCur (mkClause x)) st).clauses, P c := by
  induction xs generalizing st with
  | nil => exact hBase
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro c hc
        simp only [EncState.addClause] at hc
        cases hc with
        | head => exact hNew hd (List.mem_cons_self ..)
        | tail _ hTail => exact hBase c hTail
      · intro x hx
        exact hNew x (List.mem_cons_of_mem hd hx)

/-- Helper: clauses in foldl with addClause are either from base or added. -/
lemma foldl_addClause_mem {α : Type*} (b : Bounds S)
    (xs : List α) (st : EncState b) (mkClause : α → SAT.Clause (Var b))
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈
      (xs.foldl (fun stCur x => EncState.addClause b stCur (mkClause x)) st).clauses) :
    clause ∈ st.clauses ∨ ∃ x ∈ xs, clause = mkClause x := by
  induction xs generalizing st with
  | nil =>
    left
    exact hClause
  | cons hd tl ih =>
    simp only [List.foldl_cons] at hClause
    rcases ih _ hClause with hBase | ⟨x, hx, hEq⟩
    · simp only [EncState.addClause] at hBase
      cases hBase with
      | head =>
        right
        exact ⟨hd, List.mem_cons_self .., rfl⟩
      | tail _ hTail =>
        left
        exact hTail
    · right
      exact ⟨x, List.mem_cons_of_mem hd hx, hEq⟩

/-- Nested foldl clause membership: clauses in output are either from base state
or equal to one of the generated clauses. -/
lemma nested_foldl_addClause_mem {α β : Type*} (b : Bounds S)
    (outer : List α) (inner : List β) (st : EncState b)
    (mkClause : α → β → SAT.Clause (Var b))
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (outer.foldl (fun stAcc a =>
        inner.foldl (fun stAcc' x => EncState.addClause b stAcc' (mkClause a x)) stAcc)
        st).clauses) :
    clause ∈ st.clauses ∨ ∃ a ∈ outer, ∃ x ∈ inner, clause = mkClause a x := by
  induction outer generalizing st with
  | nil =>
    left
    exact hClause
  | cons a tl ih =>
    simp only [List.foldl_cons] at hClause
    rcases ih _ hClause with hBase | ⟨a', ha', x, hx, hEq⟩
    · -- clause is from inner fold at head
      rcases foldl_addClause_mem b inner st (mkClause a) clause hBase with hSt | ⟨x, hx, hEqInner⟩
      · left; exact hSt
      · right; exact ⟨a, List.mem_cons_self .., x, hx, hEqInner⟩
    · -- clause is from tail of outer fold
      right; exact ⟨a', List.mem_cons_of_mem a ha', x, hx, hEq⟩

/-- Helper for inner fold with 2 addClauses per step. -/
lemma foldl_addClause2_mem {α : Type*} (b : Bounds S)
    (xs : List α) (st : EncState b)
    (mkClause1 mkClause2 : α → SAT.Clause (Var b))
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (xs.foldl (fun stAcc x =>
        let stAcc := EncState.addClause b stAcc (mkClause1 x)
        EncState.addClause b stAcc (mkClause2 x)) st).clauses) :
    clause ∈ st.clauses ∨ ∃ x ∈ xs, clause = mkClause1 x ∨ clause = mkClause2 x := by
  induction xs generalizing st with
  | nil => left; exact hClause
  | cons hd tl ih =>
    simp only [List.foldl_cons] at hClause
    rcases ih _ hClause with hBase | ⟨x, hx, hEq⟩
    · -- clause is from the two addClauses at head
      simp only [EncState.addClause] at hBase
      cases hBase with
      | head => right; exact ⟨hd, List.mem_cons_self .., Or.inr rfl⟩
      | tail _ hTail =>
        cases hTail with
        | head => right; exact ⟨hd, List.mem_cons_self .., Or.inl rfl⟩
        | tail _ hTail' => left; exact hTail'
    · -- clause is from tail
      right; exact ⟨x, List.mem_cons_of_mem hd hx, hEq⟩

/-- Nested foldl clause membership with 2 addClauses per inner step. -/
lemma nested_foldl_addClause2_mem {α β : Type*} (b : Bounds S)
    (outer : List α) (inner : List β) (st : EncState b)
    (mkClause1 mkClause2 : α → β → SAT.Clause (Var b))
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (outer.foldl (fun stAcc a =>
        inner.foldl (fun stAcc' x =>
          let stAcc' := EncState.addClause b stAcc' (mkClause1 a x)
          EncState.addClause b stAcc' (mkClause2 a x)) stAcc) st).clauses) :
    clause ∈ st.clauses ∨
      ∃ a ∈ outer, ∃ x ∈ inner, clause = mkClause1 a x ∨ clause = mkClause2 a x := by
  induction outer generalizing st with
  | nil => left; exact hClause
  | cons a tl ih =>
    simp only [List.foldl_cons] at hClause
    rcases ih _ hClause with hBase | ⟨a', ha', x, hx, hEq⟩
    · -- clause is from inner fold at head
      rcases foldl_addClause2_mem b inner st (mkClause1 a) (mkClause2 a) clause hBase with
        hSt | ⟨x, hx, hEqInner⟩
      · left; exact hSt
      · right; exact ⟨a, List.mem_cons_self .., x, hx, hEqInner⟩
    · -- clause is from tail
      right; exact ⟨a', List.mem_cons_of_mem a ha', x, hx, hEq⟩

/-- Forward direction: if x ∈ xs, then mkClause1 x is in the fold result. -/
lemma foldl_addClause2_elem_mem1 {α : Type*} (b : Bounds S)
    (xs : List α) (st : EncState b)
    (mkClause1 mkClause2 : α → SAT.Clause (Var b))
    (x : α) (hx : x ∈ xs) :
    mkClause1 x ∈ (xs.foldl (fun stAcc a =>
        let stAcc := EncState.addClause b stAcc (mkClause1 a)
        EncState.addClause b stAcc (mkClause2 a)) st).clauses := by
  induction xs generalizing st with
  | nil => cases hx
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with hEq | hTail
    · -- x = hd: the clause is added at head, then preserved through tail
      subst hEq
      have hAddedHere : mkClause1 x ∈ (EncState.addClause b
          (EncState.addClause b st (mkClause1 x)) (mkClause2 x)).clauses := by
        simp only [EncState.addClause, List.mem_cons, true_or, or_true]
      have hStep : ∀ (st' : EncState b) (a : α),
          st'.clauses ⊆ (let stAcc := EncState.addClause b st' (mkClause1 a);
            EncState.addClause b stAcc (mkClause2 a)).clauses := by
        intro st' a
        simp only [EncState.addClause]
        intro c hc
        right; right; exact hc
      exact foldl_subset_state (f := fun stAcc a =>
        let stAcc := EncState.addClause b stAcc (mkClause1 a)
        EncState.addClause b stAcc (mkClause2 a)) (hStep := hStep) tl _ hAddedHere
    · -- x ∈ tl: use IH
      exact ih _ hTail

/-- Forward direction: if x ∈ xs, then mkClause2 x is in the fold result. -/
lemma foldl_addClause2_elem_mem2 {α : Type*} (b : Bounds S)
    (xs : List α) (st : EncState b)
    (mkClause1 mkClause2 : α → SAT.Clause (Var b))
    (x : α) (hx : x ∈ xs) :
    mkClause2 x ∈ (xs.foldl (fun stAcc a =>
        let stAcc := EncState.addClause b stAcc (mkClause1 a)
        EncState.addClause b stAcc (mkClause2 a)) st).clauses := by
  induction xs generalizing st with
  | nil => cases hx
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with hEq | hTail
    · -- x = hd: the clause is added at head, then preserved through tail
      subst hEq
      have hAddedHere : mkClause2 x ∈ (EncState.addClause b
          (EncState.addClause b st (mkClause1 x)) (mkClause2 x)).clauses := by
        simp only [EncState.addClause, List.mem_cons, true_or]
      have hStep : ∀ (st' : EncState b) (a : α),
          st'.clauses ⊆ (let stAcc := EncState.addClause b st' (mkClause1 a);
            EncState.addClause b stAcc (mkClause2 a)).clauses := by
        intro st' a
        simp only [EncState.addClause]
        intro c hc
        right; right; exact hc
      exact foldl_subset_state (f := fun stAcc a =>
        let stAcc := EncState.addClause b stAcc (mkClause1 a)
        EncState.addClause b stAcc (mkClause2 a)) (hStep := hStep) tl _ hAddedHere
    · -- x ∈ tl: use IH
      exact ih _ hTail

/-- Forward direction for nested folds with 2 clauses per step: mkClause1 a x is in result. -/
lemma nested_foldl_addClause2_elem_mem1 {α β : Type*} (b : Bounds S)
    (outer : List α) (inner : List β) (st : EncState b)
    (mkClause1 mkClause2 : α → β → SAT.Clause (Var b))
    (a : α) (ha : a ∈ outer) (x : β) (hx : x ∈ inner) :
    mkClause1 a x ∈ (outer.foldl (fun stAcc a =>
        inner.foldl (fun stAcc' y =>
          let stAcc' := EncState.addClause b stAcc' (mkClause1 a y)
          EncState.addClause b stAcc' (mkClause2 a y)) stAcc) st).clauses := by
  induction outer generalizing st with
  | nil => cases ha
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with hEq | hTail
    · -- a = hd: clause added in inner fold, then preserved
      subst hEq
      have hInner : mkClause1 a x ∈ (inner.foldl (fun stAcc' y =>
          let stAcc' := EncState.addClause b stAcc' (mkClause1 a y)
          EncState.addClause b stAcc' (mkClause2 a y)) st).clauses :=
        foldl_addClause2_elem_mem1 b inner st (mkClause1 a) (mkClause2 a) x hx
      have hStep : ∀ (st' : EncState b) (a' : α),
          st'.clauses ⊆ (inner.foldl (fun stAcc' y =>
            let stAcc' := EncState.addClause b stAcc' (mkClause1 a' y)
            EncState.addClause b stAcc' (mkClause2 a' y)) st').clauses := by
        intro st' a'
        apply foldl_subset_state
        intro stAcc y
        simp only [EncState.addClause]
        intro c hc
        right; right; exact hc
      exact foldl_subset_state (f := fun stAcc a' =>
        inner.foldl (fun stAcc' y =>
          let stAcc' := EncState.addClause b stAcc' (mkClause1 a' y)
          EncState.addClause b stAcc' (mkClause2 a' y)) stAcc)
        (hStep := hStep) tl _ hInner
    · -- a ∈ tl: use IH
      exact ih _ hTail

/-- Forward direction for nested folds with 2 clauses per step: mkClause2 a x is in result. -/
lemma nested_foldl_addClause2_elem_mem2 {α β : Type*} (b : Bounds S)
    (outer : List α) (inner : List β) (st : EncState b)
    (mkClause1 mkClause2 : α → β → SAT.Clause (Var b))
    (a : α) (ha : a ∈ outer) (x : β) (hx : x ∈ inner) :
    mkClause2 a x ∈ (outer.foldl (fun stAcc a =>
        inner.foldl (fun stAcc' y =>
          let stAcc' := EncState.addClause b stAcc' (mkClause1 a y)
          EncState.addClause b stAcc' (mkClause2 a y)) stAcc) st).clauses := by
  induction outer generalizing st with
  | nil => cases ha
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with hEq | hTail
    · -- a = hd: clause added in inner fold, then preserved
      subst hEq
      have hInner : mkClause2 a x ∈ (inner.foldl (fun stAcc' y =>
          let stAcc' := EncState.addClause b stAcc' (mkClause1 a y)
          EncState.addClause b stAcc' (mkClause2 a y)) st).clauses :=
        foldl_addClause2_elem_mem2 b inner st (mkClause1 a) (mkClause2 a) x hx
      have hStep : ∀ (st' : EncState b) (a' : α),
          st'.clauses ⊆ (inner.foldl (fun stAcc' y =>
            let stAcc' := EncState.addClause b stAcc' (mkClause1 a' y)
            EncState.addClause b stAcc' (mkClause2 a' y)) st').clauses := by
        intro st' a'
        apply foldl_subset_state
        intro stAcc y
        simp only [EncState.addClause]
        intro c hc
        right; right; exact hc
      exact foldl_subset_state (f := fun stAcc a' =>
        inner.foldl (fun stAcc' y =>
          let stAcc' := EncState.addClause b stAcc' (mkClause1 a' y)
          EncState.addClause b stAcc' (mkClause2 a' y)) stAcc)
        (hStep := hStep) tl _ hInner
    · -- a ∈ tl: use IH
      exact ih _ hTail

/-- Clauses from addPreEqReflAll contain only non-Fresh vars. -/
lemma addPreEqReflAll_clauses_nonFresh (b : Bounds S) (st : EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (addPreEqReflAll b st).clauses)
    (hNotBase : clause ∉ st.clauses) :
    ∀ lit ∈ clause, ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n := by
  -- addPreEqReflAll adds [pos (Var.PreEq ti ti)] for each ti via foldl
  simp only [addPreEqReflAll] at hClause
  -- Use foldl_addClause_mem to show clause is either from st or one of the added clauses
  rcases foldl_addClause_mem b (Bounds.timesL b) st
      (fun t => [SAT.Lit.pos (Var.PreEq t t)]) clause hClause with hBase | ⟨t, _, hEq⟩
  · -- clause ∈ st.clauses contradicts hNotBase
    exact absurd hBase hNotBase
  · -- clause = [pos (Var.PreEq t t)] for some t
    intro lit hLit n hFresh
    rw [hEq] at hLit
    simp only [List.mem_singleton] at hLit
    rw [hLit] at hFresh
    simp only [SAT.Lit.getVar] at hFresh
    -- PreEq t t ≠ Fresh n
    cases hFresh

/-- Structural determinism for clauses that only contain non-Fresh vars:
    If σ satisfies such clauses, then σ' (which equals σ on non-Fresh) also does. -/
lemma nonFresh_clauses_structural (b : Bounds S) (st' : EncState b)
    (σ : SAT.Assignment (Var b)) (offset : Nat)
    (clauses : List (SAT.Clause (Var b)))
    (hNoFresh : ∀ c ∈ clauses, ∀ lit ∈ c, ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n)
    (hSat : clauses.all (SAT.Clause.eval σ) = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < st'.nextFresh then σ v else σ (Var.unshift b v offset)
      | _ => σ v
    clauses.all (SAT.Clause.eval σ') = true := by
  intro σ'
  rw [List.all_eq_true] at hSat ⊢
  intro c hc
  have hNoFreshC := hNoFresh c hc
  rw [nonFresh_clause_eval b st' σ offset c hNoFreshC]
  exact hSat c hc

end Encoding
