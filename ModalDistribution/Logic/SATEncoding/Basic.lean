import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Vector.Basic

/-!
# SAT Encoding Infrastructure

This file provides the basic SAT/CNF data structures and evaluation functions
for the bounded model checker.

## Main Definitions

- `SAT.Lit`: Propositional literals (positive or negative)
- `SAT.Clause`: Disjunction of literals (list)
- `SAT.CNF`: Conjunction of clauses (list of clauses)
- `SAT.Assignment`: Variable assignment function (Var → Bool)
- Evaluation functions for literals, clauses, and CNF formulas

## Key Properties

- All evaluation functions are fully computable (return `Bool`)
- No dependence on `Prop`-level semantics
- Uses Lean 4 boolean operators: `&&`, `||`, `!`

-/

namespace SAT

/-! ## Basic SAT Types -/

/-- Propositional literal: either a positive or negative variable. -/
inductive Lit (Var : Type) : Type where
  | pos : Var → Lit Var
  | neg : Var → Lit Var
deriving DecidableEq, Repr

/-- A clause is a disjunction of literals (represented as a list). -/
abbrev Clause (Var : Type) := List (Lit Var)

/-- CNF formula: conjunction of clauses. -/
structure CNF (Var : Type) where
  clauses : List (Clause Var)
deriving Repr

/-- Assignment: maps variables to boolean values. -/
abbrev Assignment (Var : Type) := Var → Bool

/-! ## Evaluation Functions (Computable) -/

namespace Lit

/-- Evaluate a literal under an assignment. -/
@[simp]
def eval {Var} (σ : Assignment Var) : Lit Var → Bool
  | .pos v => σ v
  | .neg v => !(σ v)

/-- Extract the variable from a literal. -/
def getVar {Var} : Lit Var → Var
  | .pos v => v
  | .neg v => v

end Lit

namespace Clause

/-- Evaluate a clause (disjunction) under an assignment.
    Returns `true` if at least one literal evaluates to `true`. -/
@[simp]
def eval {Var} (σ : Assignment Var) (C : Clause Var) : Bool :=
  C.foldl (fun acc lit => acc || Lit.eval σ lit) false

/-- Helper: clause evaluation is equivalent to `any` over literal evaluations. -/
theorem eval_eq_any {Var} (σ : Assignment Var) (C : Clause Var) :
    C.eval σ = C.any (fun lit => Lit.eval σ lit) := by
  unfold eval
  have aux :
      ∀ (C : Clause Var) (acc : Bool),
        List.foldl (fun acc lit => acc || Lit.eval σ lit) acc C =
          (acc || C.any (fun lit => Lit.eval σ lit)) := by
    intro C
    induction C with
    | nil =>
        intro acc
        simp
    | cons lit rest ih =>
        intro acc
        have := ih (acc := acc || Lit.eval σ lit)
        simpa [List.foldl_cons, List.any_cons, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm, this]
  simpa [Bool.false_or] using aux C false

/-- Evaluation of a two-literal clause [l1 ∨ l2]. -/
theorem eval_two_lit {Var} (σ : Assignment Var) (l1 l2 : Lit Var) :
    Clause.eval σ [l1, l2] = (Lit.eval σ l1 || Lit.eval σ l2) := by
  unfold Clause.eval
  simp [List.foldl]

/-- If a clause contains a literal that evaluates to true, the clause is satisfied. -/
theorem eval_true_of_mem {Var} (σ : Assignment Var) (C : Clause Var) (lit : Lit Var)
    (hMem : lit ∈ C) (hTrue : Lit.eval σ lit = true) :
    C.eval σ = true := by
  rw [eval_eq_any]
  apply List.any_eq_true.mpr
  exact ⟨lit, hMem, hTrue⟩

/-- If a clause contains a positive literal that evaluates to true, the clause is satisfied. -/
theorem eval_true_of_pos_mem {Var} (σ : Assignment Var) (C : Clause Var) (v : Var)
    (hMem : Lit.pos v ∈ C) (hTrue : σ v = true) :
    C.eval σ = true := by
  rw [eval_eq_any]
  apply List.any_eq_true.mpr
  exact ⟨Lit.pos v, hMem, by simp [Lit.eval, hTrue]⟩

/-- If a clause contains a negative literal whose variable is false, the clause is satisfied. -/
theorem eval_true_of_neg_mem {Var} (σ : Assignment Var) (C : Clause Var) (v : Var)
    (hMem : Lit.neg v ∈ C) (hFalse : σ v = false) :
    C.eval σ = true := by
  rw [eval_eq_any]
  apply List.any_eq_true.mpr
  exact ⟨Lit.neg v, hMem, by simp [Lit.eval, hFalse]⟩

end Clause

namespace CNF

/-- Evaluate a CNF formula (conjunction of clauses) under an assignment.
    Returns `true` if all clauses evaluate to `true`. -/
@[simp]
def eval {Var} (σ : Assignment Var) (F : CNF Var) : Bool :=
  F.clauses.all (Clause.eval σ)

/-- Unit clause: single positive literal. -/
@[simp]
def unit {Var} (v : Var) : CNF Var :=
  ⟨[[Lit.pos v]]⟩

/-- Negative unit clause: single negative literal. -/
@[simp]
def unitNeg {Var} (v : Var) : CNF Var :=
  ⟨[[Lit.neg v]]⟩

/-- Conjunction of two CNF formulas. -/
def and {Var} (F G : CNF Var) : CNF Var :=
  ⟨F.clauses ++ G.clauses⟩

/-- Empty CNF (always satisfied). -/
def empty {Var} : CNF Var := ⟨[]⟩

/-! ## Evaluation Lemmas -/

theorem eval_empty {Var} (σ : Assignment Var) :
    (empty (Var := Var)).eval σ = true := by
  simp [eval, empty]

theorem eval_unit {Var} (σ : Assignment Var) (v : Var) :
    (unit v).eval σ = σ v := by
  simp [eval, unit, Clause.eval, List.foldl, Lit.eval]

theorem eval_unitNeg {Var} (σ : Assignment Var) (v : Var) :
    (unitNeg v).eval σ = !(σ v) := by
  simp [eval, unitNeg, Clause.eval, List.foldl, Lit.eval]

theorem eval_and {Var} (σ : Assignment Var) (F G : CNF Var) :
    (F.and G).eval σ = (F.eval σ && G.eval σ) := by
  simp [eval, and, List.all_append]

/-- Conjoin a list of CNF formulas. -/
def band {Var} : List (CNF Var) → CNF Var
  | [] => empty
  | F :: Fs => F.and (band Fs)

theorem eval_band_nil {Var} (σ : Assignment Var) :
    (band (Var := Var) []).eval σ = true := by
  rw [band]
  exact eval_empty σ

theorem eval_band_cons {Var} (σ : Assignment Var) (F : CNF Var) (Fs : List (CNF Var)) :
    (band (F :: Fs)).eval σ = (F.eval σ && (band Fs).eval σ) := by
  rw [band]
  exact eval_and σ F (band Fs)

/-- Evaluation of a big conjunction is true iff all components are true. -/
theorem eval_band_true {Var} (σ : Assignment Var) (Fs : List (CNF Var)) :
    (band Fs).eval σ = true ↔ ∀ F ∈ Fs, F.eval σ = true := by
  induction Fs with
  | nil =>
      simp [band, empty]
  | cons F Fs ih =>
      constructor
      · intro h
        have hAll :
            (F.clauses ++ (band Fs).clauses).all (Clause.eval σ) = true := by
          simpa [band, eval, and] using h
        have hClauses :
            ∀ C ∈ F.clauses ++ (band Fs).clauses,
              Clause.eval σ C = true :=
          List.all_eq_true.mp hAll
        obtain ⟨hFClauses, hBandClauses⟩ :=
          List.forall_mem_append.1 hClauses
        have hFAll : F.clauses.all (Clause.eval σ) = true :=
          List.all_eq_true.mpr hFClauses
        have hF : F.eval σ = true := by
          simpa [eval] using hFAll
        have hBandAll : (band Fs).clauses.all (Clause.eval σ) = true :=
          List.all_eq_true.mpr hBandClauses
        have hBandEval : (band Fs).eval σ = true := by
          simpa [eval] using hBandAll
        have hTail : ∀ G ∈ Fs, G.eval σ = true := ih.mp hBandEval
        exact List.forall_mem_cons.2 ⟨hF, hTail⟩
      · intro h
        obtain ⟨hF, hTail⟩ := List.forall_mem_cons.1 h
        have hTailEval : (band Fs).eval σ = true := ih.mpr hTail
        have hFAll : F.clauses.all (Clause.eval σ) = true := by
          simpa [eval] using hF
        have hFClauses :
            ∀ C ∈ F.clauses, Clause.eval σ C = true :=
          List.all_eq_true.mp hFAll
        have hBandAll :
            (band Fs).clauses.all (Clause.eval σ) = true := by
          simpa [eval] using hTailEval
        have hBandClauses :
            ∀ C ∈ (band Fs).clauses, Clause.eval σ C = true :=
          List.all_eq_true.mp hBandAll
        have hClauses :
            ∀ C ∈ F.clauses ++ (band Fs).clauses,
              Clause.eval σ C = true :=
          List.forall_mem_append.2 ⟨hFClauses, hBandClauses⟩
        have hAll :
            (F.clauses ++ (band Fs).clauses).all (Clause.eval σ) = true :=
          List.all_eq_true.mpr hClauses
        simpa [band, eval, and] using hAll

/-- Convenience alias matching the suggested name. -/
theorem eval_and_true {Var} (σ : Assignment Var) (F G : CNF Var) :
    (F.and G).eval σ = true ↔ (F.eval σ = true ∧ G.eval σ = true) := by
  constructor
  · intro h
    have hAll : (F.clauses ++ G.clauses).all (Clause.eval σ) = true := by
      simpa [eval_and, eval, and] using h
    have hClauses :
        ∀ C ∈ F.clauses ++ G.clauses, Clause.eval σ C = true :=
      List.all_eq_true.mp hAll
    obtain ⟨hFClauses, hGClauses⟩ :=
      List.forall_mem_append.1 hClauses
    have hFAll : F.clauses.all (Clause.eval σ) = true :=
      List.all_eq_true.mpr hFClauses
    have hGAll : G.clauses.all (Clause.eval σ) = true :=
      List.all_eq_true.mpr hGClauses
    exact ⟨by simpa [eval] using hFAll, by simpa [eval] using hGAll⟩
  · intro h
    have hFAll : F.clauses.all (Clause.eval σ) = true := by
      simpa [eval] using h.left
    have hGAll : G.clauses.all (Clause.eval σ) = true := by
      simpa [eval] using h.right
    have hFClauses :
        ∀ C ∈ F.clauses, Clause.eval σ C = true :=
      List.all_eq_true.mp hFAll
    have hGClauses :
        ∀ C ∈ G.clauses, Clause.eval σ C = true :=
      List.all_eq_true.mp hGAll
    have hClauses :
        ∀ C ∈ F.clauses ++ G.clauses, Clause.eval σ C = true :=
      List.forall_mem_append.2 ⟨hFClauses, hGClauses⟩
    have hAll : (F.clauses ++ G.clauses).all (Clause.eval σ) = true :=
      List.all_eq_true.mpr hClauses
    simpa [eval_and, eval, and] using hAll

end CNF

/-! ## Tseytin-style Encoding Helpers -/

/-- Encode `u ↔ (x ∧ y)` using Tseytin transformation.
    Clauses: (¬u ∨ x), (¬u ∨ y), (¬x ∨ ¬y ∨ u) -/
def iff_and {Var} (u x y : Var) : CNF Var :=
  ⟨[ [Lit.neg u, Lit.pos x],
     [Lit.neg u, Lit.pos y],
     [Lit.neg x, Lit.neg y, Lit.pos u] ]⟩

/-- Encode `u ↔ (x ∨ y)` using Tseytin transformation.
    Clauses: (¬x ∨ u), (¬y ∨ u), (¬u ∨ x ∨ y) -/
def iff_or {Var} (u x y : Var) : CNF Var :=
  ⟨[ [Lit.neg x, Lit.pos u],
     [Lit.neg y, Lit.pos u],
     [Lit.neg u, Lit.pos x, Lit.pos y] ]⟩

/-- Encode `u ↔ (x → y)` using Tseytin transformation.
    Equivalent to `u ↔ (¬x ∨ y)`
    Clauses: (x ∨ u), (¬y ∨ u), (¬u ∨ ¬x ∨ y) -/
def iff_imp {Var} (u x y : Var) : CNF Var :=
  ⟨[ [Lit.pos x, Lit.pos u],
     [Lit.neg y, Lit.pos u],
     [Lit.neg u, Lit.neg x, Lit.pos y] ]⟩

/-! ## At-Least-One and At-Most-One Constraints -/

/-- At-least-one constraint: at least one variable must be true. -/
@[simp]
def alo {Var} (xs : List Var) : CNF Var :=
  ⟨[xs.map Lit.pos]⟩

/-- At-most-one constraint: at most one variable can be true (pairwise).
    For each pair (x, y) with x ≠ y, add clause (¬x ∨ ¬y). -/
@[simp]
def amo {Var} [DecidableEq Var] (xs : List Var) : CNF Var :=
  let pairs := xs.flatMap (fun x => xs.map (fun y => (x, y)))
  let strict := pairs.filter (fun (x, y) => x ≠ y)
  ⟨strict.map (fun (x, y) => [Lit.neg x, Lit.neg y])⟩

/-- Exactly-one constraint: exactly one variable must be true. -/
@[simp]
def exo {Var} [DecidableEq Var] (xs : List Var) : CNF Var :=
  (alo xs).and (amo xs)

/-! ## CNF Clause Reasoning -/

/-- Unit propagation: If a clause is in a satisfied CNF and all but one literal are false,
    then the remaining literal must be true.

    This is the key lemma for extracting consequences from CNF constraints. -/
theorem clause_unit_propagation {Var : Type} (σ : Assignment Var)
    (cnf : CNF Var) (clause : Clause Var)
    (h_clause_in : clause ∈ cnf.clauses)
    (h_cnf_sat : cnf.eval σ = true) :
    Clause.eval σ clause = true := by
  -- If the CNF is satisfied, all clauses in it are satisfied
  unfold CNF.eval at h_cnf_sat
  have h_all := List.all_eq_true.mp h_cnf_sat
  exact h_all clause h_clause_in

/-- If a 3-literal clause [¬A, ¬B, C] is satisfied and A and B are true, then C must be true. -/
theorem clause_three_unit {Var : Type} (σ : Assignment Var)
    (cnf : CNF Var) (v1 v2 v3 : Var)
    (h_clause_in : [Lit.neg v1, Lit.neg v2, Lit.pos v3] ∈ cnf.clauses)
    (h_cnf_sat : cnf.eval σ = true)
    (h1 : σ v1 = true)
    (h2 : σ v2 = true) :
    σ v3 = true := by
  -- Get that the clause is satisfied
  have h_clause := clause_unit_propagation σ cnf [Lit.neg v1, Lit.neg v2, Lit.pos v3]
    h_clause_in h_cnf_sat
  -- Unfold clause evaluation
  unfold Clause.eval at h_clause
  simp [Lit.eval, h1, h2] at h_clause
  exact h_clause

/-- If `iff_and u x y` is satisfied and both x and y are true, then u is true.
    Uses the clause [¬x, ¬y, u] from the Tseytin encoding. -/
theorem iff_and_forward {Var : Type} (σ : Assignment Var)
    (u x y : Var)
    (h_sat : (iff_and u x y).eval σ = true)
    (hx : σ x = true)
    (hy : σ y = true) :
    σ u = true := by
  -- The third clause [¬x, ¬y, u] is in iff_and
  have h_clause_in : [Lit.neg x, Lit.neg y, Lit.pos u] ∈ (iff_and u x y).clauses := by
    unfold iff_and
    simp
  exact clause_three_unit σ (iff_and u x y) x y u h_clause_in h_sat hx hy

/-- If `iff_and u x y` is satisfied and u is true, then x is true.
    Uses the clause [¬u, x] from the Tseytin encoding. -/
theorem iff_and_back_left {Var : Type} (σ : Assignment Var)
    (u x y : Var)
    (h_sat : (iff_and u x y).eval σ = true)
    (hu : σ u = true) :
    σ x = true := by
  have h_clause_in : [Lit.neg u, Lit.pos x] ∈ (iff_and u x y).clauses := by
    unfold iff_and
    simp
  have h_clause := clause_unit_propagation σ (iff_and u x y)
    [Lit.neg u, Lit.pos x] h_clause_in h_sat
  unfold Clause.eval at h_clause
  simp [Lit.eval, hu] at h_clause
  exact h_clause

/-- If `iff_and u x y` is satisfied and u is true, then y is true.
    Uses the clause [¬u, y] from the Tseytin encoding. -/
theorem iff_and_back_right {Var : Type} (σ : Assignment Var)
    (u x y : Var)
    (h_sat : (iff_and u x y).eval σ = true)
    (hu : σ u = true) :
    σ y = true := by
  have h_clause_in : [Lit.neg u, Lit.pos y] ∈ (iff_and u x y).clauses := by
    unfold iff_and
    simp
  have h_clause := clause_unit_propagation σ (iff_and u x y)
    [Lit.neg u, Lit.pos y] h_clause_in h_sat
  unfold Clause.eval at h_clause
  simp [Lit.eval, hu] at h_clause
  exact h_clause

end SAT
