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
# Tseytin Correctness for Implication (imp)

This file proves that the Tseytin encoding correctly captures the semantics of
implication formulas.

## Strategy

The implication encoding uses three clauses for u ↔ (φ1 → φ2):
- [u1, u]: ensures u1 = false → u = true
- [¬u2, u]: ensures u2 = true → u = true
- [¬u, ¬u1, u2]: ensures u = true → (u1 → u2)

Together these enforce u ↔ (u1 → u2).
-/

open ModalDistribution Encoding Logic

namespace Encoding

variable {S : Signature}

/-! ## Implication Tseytin Encoding -/

/-- The three Tseytin clauses for implication: u ↔ (u1 → u2).
    - [u1, u]: if u1 = false, then u = true
    - [¬u2, u]: if u2 = true, then u = true
    - [¬u, ¬u1, u2]: if u = true, then (u1 → u2) -/
def encode_imp (b : Bounds S) (u1 u2 u : FVar b) : List (SAT.Clause (Var b)) :=
  [[SAT.Lit.pos (FVar.toVar b u1), SAT.Lit.pos (FVar.toVar b u)],
   [SAT.Lit.neg (FVar.toVar b u2), SAT.Lit.pos (FVar.toVar b u)],
   [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b u1),
    SAT.Lit.pos (FVar.toVar b u2)]]

/-! ## Tseytin Correctness for Implication -/

/-- The implication encoding produces u ↔ (u1 → u2).

    Backward direction case 1: if u1 = false, then u = true. -/
lemma encode_imp_backward_u1_false (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u u1 u2 : FVar b) (clauses : List (SAT.Clause (Var b)))
    (hEncoding : clauses =
      [[SAT.Lit.pos (FVar.toVar b u1), SAT.Lit.pos (FVar.toVar b u)],
       [SAT.Lit.neg (FVar.toVar b u2), SAT.Lit.pos (FVar.toVar b u)],
       [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b u1),
        SAT.Lit.pos (FVar.toVar b u2)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true)
    (hU1 : σ (FVar.toVar b u1) = false) :
    σ (FVar.toVar b u) = true := by
  -- The first clause is [u1, u]
  -- If σ(u1) = false, then σ(u) = true
  have hClauseIn :
      [SAT.Lit.pos (FVar.toVar b u1), SAT.Lit.pos (FVar.toVar b u)] ∈ clauses := by
    rw [hEncoding]
    simp

  have hClauseTrue : SAT.Clause.eval σ
      [SAT.Lit.pos (FVar.toVar b u1), SAT.Lit.pos (FVar.toVar b u)] = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Evaluate the clause with u1 = false
  unfold SAT.Clause.eval at hClauseTrue
  simp [SAT.Lit.eval, hU1] at hClauseTrue
  exact hClauseTrue

/-- The implication encoding produces u ↔ (u1 → u2).

    Backward direction case 2: if u2 = true, then u = true. -/
lemma encode_imp_backward_u2_true (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u u1 u2 : FVar b) (clauses : List (SAT.Clause (Var b)))
    (hEncoding : clauses =
      [[SAT.Lit.pos (FVar.toVar b u1), SAT.Lit.pos (FVar.toVar b u)],
       [SAT.Lit.neg (FVar.toVar b u2), SAT.Lit.pos (FVar.toVar b u)],
       [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b u1),
        SAT.Lit.pos (FVar.toVar b u2)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true)
    (hU2 : σ (FVar.toVar b u2) = true) :
    σ (FVar.toVar b u) = true := by
  -- The second clause is [¬u2, u]
  -- If σ(u2) = true, then ¬σ(u2) = false, so σ(u) = true
  have hClauseIn :
      [SAT.Lit.neg (FVar.toVar b u2), SAT.Lit.pos (FVar.toVar b u)] ∈ clauses := by
    rw [hEncoding]
    simp

  have hClauseTrue : SAT.Clause.eval σ
      [SAT.Lit.neg (FVar.toVar b u2), SAT.Lit.pos (FVar.toVar b u)] = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Evaluate the clause with u2 = true
  unfold SAT.Clause.eval at hClauseTrue
  simp [SAT.Lit.eval, hU2] at hClauseTrue
  exact hClauseTrue

variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]
variable [DecidableEq S.Value]

/-! ## Implication Bridge Lemmas -/

/-! ## Helper Lemmas for EncState Operations -/


/-! ## Implication Clause Extraction -/

/-- The control variable for implication is the fresh variable allocated
    after encoding subformulas. -/
lemma encodeFormula_imp_control_var (b : Bounds S) (φ₁ φ₂ : Formula S)
    (w : WId b) (st : EncState b) :
    (encodeFormula b (.imp φ₁ φ₂) w st).1 =
    { id := (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).2.nextFresh } := by
  -- Match on the encoding results to avoid unfolding φ₁ and φ₂
  cases h1 : encodeFormula b φ₁ w st with
  | mk u1 st1 =>
    cases h2 : encodeFormula b φ₂ w st1 with
    | mk u2 st2 =>
      -- Now unfold the implication encoding
      unfold encodeFormula
      simp [h1, h2, EncState.allocFresh]

/-- The three clauses added during implication encoding are in the final
    clause list. -/
lemma encodeFormula_imp_clauses_in (b : Bounds S) (φ₁ φ₂ : Formula S)
    (w : WId b) (st : EncState b) :
    let (u1, st1) := encodeFormula b φ₁ w st
    let (u2, st2) := encodeFormula b φ₂ w st1
    let u := { id := st2.nextFresh : FVar b }
    let c1 := [SAT.Lit.pos (FVar.toVar b u1), SAT.Lit.pos (FVar.toVar b u)]
    let c2 := [SAT.Lit.neg (FVar.toVar b u2), SAT.Lit.pos (FVar.toVar b u)]
    let c3 := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b u1),
               SAT.Lit.pos (FVar.toVar b u2)]
    c1 ∈ (encodeFormula b (.imp φ₁ φ₂) w st).2.clauses ∧
    c2 ∈ (encodeFormula b (.imp φ₁ φ₂) w st).2.clauses ∧
    c3 ∈ (encodeFormula b (.imp φ₁ φ₂) w st).2.clauses := by
  -- Match on the encoding results
  cases h1 : encodeFormula b φ₁ w st with
  | mk u1 st1 =>
    cases h2 : encodeFormula b φ₂ w st1 with
    | mk u2 st2 =>
      -- Now we have u1, st1, u2, st2 in context
      -- Define u, c1, c2, c3
      let u := { id := st2.nextFresh : FVar b }
      let c1 := [SAT.Lit.pos (FVar.toVar b u1), SAT.Lit.pos (FVar.toVar b u)]
      let c2 := [SAT.Lit.neg (FVar.toVar b u2), SAT.Lit.pos (FVar.toVar b u)]
      let c3 := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b u1),
                 SAT.Lit.pos (FVar.toVar b u2)]
      -- Show c1, c2, c3 ∈ result.clauses
      -- Rewrite the goal using h1 and h2
      simp only [h2]
      constructor
      · -- c1 ∈ result.clauses
        unfold encodeFormula
        simp [h1, h2, EncState.allocFresh, EncState.addClause]
      constructor
      · -- c2 ∈ result.clauses
        unfold encodeFormula
        simp [h1, h2, EncState.allocFresh, EncState.addClause]
      · -- c3 ∈ result.clauses
        unfold encodeFormula
        simp [h1, h2, EncState.allocFresh, EncState.addClause]

/-- Extract the three implication clauses from the full encoding and show they
    evaluate to true under σ. -/
lemma encodeFormula_imp_clauses (b : Bounds S) (φ₁ φ₂ : Formula S)
    (w : WId b) (st : EncState b) (σ : SAT.Assignment (Var b))
    (hClauses : (encodeFormula b (.imp φ₁ φ₂) w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    (encode_imp b
      (encodeFormula b φ₁ w st).1
      (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).1
      (encodeFormula b (.imp φ₁ φ₂) w st).1).all (SAT.Clause.eval σ) = true := by
  classical
  have hAll := List.all_eq_true.mp hClauses
  refine List.all_eq_true.mpr ?_
  intro clause hMem
  apply hAll
  -- Show clause ∈ (encodeFormula b (.imp φ₁ φ₂) w st).2.clauses
  unfold encode_imp at hMem
  -- Rewrite the control variable to match the encoding structure
  rw [encodeFormula_imp_control_var] at hMem
  -- Get the membership facts
  obtain ⟨hC1, hC2, hC3⟩ := encodeFormula_imp_clauses_in b φ₁ φ₂ w st
  -- Case split on which clause we have from the list [c1, c2, c3]
  simp only [List.mem_cons] at hMem
  rcases hMem with h | h | h | h
  · rw [h]; exact hC1
  · rw [h]; exact hC2
  · rw [h]; exact hC3
  · cases h

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- From the third implication clause plus σ(u)=true and σ(u1)=true, derive σ(u2)=true. -/
lemma imp_bridge_u2_true (b : Bounds S) (u1 u2 u : FVar b) (σ : SAT.Assignment (Var b))
    (hImp : (encode_imp b u1 u2 u).all (SAT.Clause.eval σ) = true)
    (hU : σ (FVar.toVar b u) = true)
    (hU1 : σ (FVar.toVar b u1) = true) :
    σ (FVar.toVar b u2) = true := by
  classical
  -- Pick the third clause [¬u, ¬u1, u2]
  have hAll := List.all_eq_true.mp hImp
  have hMem :
    [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b u1),
     SAT.Lit.pos (FVar.toVar b u2)] ∈ encode_imp b u1 u2 u := by
    simp [encode_imp]
  have hClause := hAll _ hMem
  -- Evaluate under σ(u)=true and σ(u1)=true
  unfold SAT.Clause.eval at hClause
  simp [SAT.Lit.eval, hU, hU1] at hClause
  exact hClause

/-! ## Implication Adequacy -/

/-- Adequacy for encodeFormula implication case: σ(u) = true ↔ implication holds.

Proves **bi-directional adequacy** using iff IHs for both subformulas. -/
lemma encodeFormula_imp_adequate
    (b : Bounds S) (φ₁ φ₂ : Formula S) (w : WId b) (st : EncState b)
    (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    -- Iff IH for antecedent
    (ihLeft_iff : ∀ st₀ : EncState b,
      let res := encodeFormula b φ₁ w st₀
      let uLeft := res.1
      let st₁ := res.2
      st₁.clauses.all (SAT.Clause.eval σ) = true →
      (σ (FVar.toVar b uLeft) = true ↔
       Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti) φ₁))
    -- Iff IH for consequent
    (ihRight_iff : ∀ st₀ : EncState b,
      let res := encodeFormula b φ₂ w st₀
      let uRight := res.1
      let st₂ := res.2
      st₂.clauses.all (SAT.Clause.eval σ) = true →
      (σ (FVar.toVar b uRight) = true ↔
       Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti) φ₂))
    (hClauses : (encodeFormula b (.imp φ₁ φ₂) w st).2.clauses.all
      (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b (encodeFormula b (.imp φ₁ φ₂) w st).1) = true) ↔
    Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti) (.imp φ₁ φ₂) := by
  classical
  -- Get the three imp clauses
  have hImpClauses :=
    encodeFormula_imp_clauses b φ₁ φ₂ w st σ hClauses

  -- Get "all=true" for both sub-encodings
  have hAll_after_left :
      (encodeFormula b φ₁ w st).2.clauses.all (SAT.Clause.eval σ) = true := by
    -- Use existing lemma: st1.clauses ⊆ final.clauses
    apply all_true_of_subset _ hClauses
    intro c hMem
    -- c ∈ st1.clauses → c ∈ final.clauses
    cases h1 : encodeFormula b φ₁ w st with
    | mk u1 st1 =>
      simp [h1] at hMem
      -- First, c ∈ st2.clauses (by encodeFormula_clauses_subset for φ₂)
      have hSub2 := encodeFormula_clauses_subset b φ₂ w st1
      have hInSt2 : c ∈ (encodeFormula b φ₂ w st1).2.clauses := hSub2 hMem
      -- Then, c ∈ final.clauses (by unfolding .imp encoding)
      unfold encodeFormula
      simp [h1, EncState.allocFresh, EncState.addClause]
      right; right; right
      exact hInSt2

  have hAll_after_right :
      (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).2.clauses.all
        (SAT.Clause.eval σ) = true := by
    -- Use existing lemma: st2.clauses ⊆ final.clauses
    apply all_true_of_subset _ hClauses
    intro c hMem
    -- c ∈ st2.clauses → c ∈ final.clauses
    cases h1 : encodeFormula b φ₁ w st with
    | mk u1 st1 =>
      cases h2 : encodeFormula b φ₂ w st1 with
      | mk u2 st2 =>
        simp [h1, h2] at hMem
        -- c ∈ st2.clauses → c ∈ final.clauses
        unfold encodeFormula
        simp [h1, h2, EncState.allocFresh, EncState.addClause]
        right; right; right
        exact hMem

  -- Unfold Sat for implication
  unfold Sat

  -- Prove the iff
  constructor
  · -- Forward: σ(uImp) = true → (Sat φ₁ → Sat φ₂)
    intro hUImp hSat1
    -- From adequacy (←) for φ₁: Sat φ₁ ⇒ σ(uLeft)=true
    have hU1_true : σ (FVar.toVar b (encodeFormula b φ₁ w st).1) = true := by
      have hIff := ihLeft_iff st hAll_after_left
      exact hIff.mpr hSat1
    -- From the third imp-clause + uImp=true + uLeft=true, get uRight=true
    have hU2_true : σ (FVar.toVar b (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).1) = true :=
      imp_bridge_u2_true b (encodeFormula b φ₁ w st).1
        (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).1
        (encodeFormula b (.imp φ₁ φ₂) w st).1
        σ hImpClauses hUImp hU1_true
    -- Forward IH for φ₂ finishes
    have hIff := ihRight_iff (encodeFormula b φ₁ w st).2 hAll_after_right
    exact hIff.mp hU2_true

  · -- Backward: (Sat φ₁ → Sat φ₂) → σ(uImp) = true
    intro hSatImp
    -- Case analysis on σ(uLeft)
    by_cases hU1 : σ (FVar.toVar b (encodeFormula b φ₁ w st).1) = true
    · -- Case σ(uLeft) = true
      -- By iff IH for φ₁, get Sat φ₁
      have hSat1
        : Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti) φ₁ := by
        have hIff := ihLeft_iff st hAll_after_left
        exact hIff.mp hU1
      -- By assumption, get Sat φ₂
      have hSat2 := hSatImp hSat1
      -- By iff IH for φ₂, get σ(uRight) = true
      have hU2 : σ (FVar.toVar b (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).1) = true := by
        have hIff := ihRight_iff (encodeFormula b φ₁ w st).2 hAll_after_right
        exact hIff.mpr hSat2
      -- By second Tseytin clause [¬uRight, uImp], get σ(uImp) = true
      exact encode_imp_backward_u2_true b σ
        (encodeFormula b (.imp φ₁ φ₂) w st).1
        (encodeFormula b φ₁ w st).1
        (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).1
        (encode_imp b (encodeFormula b φ₁ w st).1
          (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).1
          (encodeFormula b (.imp φ₁ φ₂) w st).1)
        rfl hImpClauses hU2
    · -- Case σ(uLeft) = false
      -- By first Tseytin clause [uLeft, uImp], get σ(uImp) = true
      -- Convert ¬(σ u1 = true) to σ u1 = false
      have hU1_false : σ (FVar.toVar b (encodeFormula b φ₁ w st).1) = false := by
        cases h : σ (FVar.toVar b (encodeFormula b φ₁ w st).1)
        · rfl
        · contradiction
      exact encode_imp_backward_u1_false b σ
        (encodeFormula b (.imp φ₁ φ₂) w st).1
        (encodeFormula b φ₁ w st).1
        (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).1
        (encode_imp b (encodeFormula b φ₁ w st).1
          (encodeFormula b φ₂ w (encodeFormula b φ₁ w st).2).1
          (encodeFormula b (.imp φ₁ φ₂) w st).1)
        rfl hImpClauses hU1_false

end Encoding
