import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Common

/-!
# Shifted Assignment Threshold Helpers

Helper lemmas for reasoning about `shiftedAssignment` across different thresholds.
These are crucial for composing inductive hypotheses in recursive formula cases.

## Main Lemmas

- `shiftedAssignment_threshold_agree`: Two shifted assignments agree on Fresh vars >= higher threshold
- `lit_eval_shiftedAssignment_threshold_agree`: Literal evaluation agreement
- `clause_eval_shiftedAssignment_threshold_agree`: Clause evaluation agreement
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- Helper: shiftedAssignment with different thresholds agrees on Fresh vars >= higher threshold.
    This is key for recursion: when we increase the threshold, the assignment still works. -/
lemma shiftedAssignment_threshold_agree (b : Bounds S) (σ : SAT.Assignment (Var b))
    (threshold1 threshold2 : Nat) (offset : Nat)
    (hThresholdLe : threshold1 ≤ threshold2) (n : Nat) (hn : n ≥ threshold2) :
    shiftedAssignment b σ threshold1 offset (Var.Fresh n) =
    shiftedAssignment b σ threshold2 offset (Var.Fresh n) := by
  have hGe1 : ¬(n < threshold1) := by omega
  have hGe2 : ¬(n < threshold2) := by omega
  simp only [shiftedAssignment, hGe1, hGe2, ↓reduceIte, Var.unshift]

/-- Helper: Lit.eval with shiftedAssignment agrees across threshold changes for Fresh vars. -/
lemma lit_eval_shiftedAssignment_threshold_agree (b : Bounds S) (σ : SAT.Assignment (Var b))
    (threshold1 threshold2 : Nat) (offset : Nat)
    (hThresholdLe : threshold1 ≤ threshold2)
    (lit : SAT.Lit (Var b))
    (hFreshGe : ∀ n, SAT.Lit.getVar lit = Var.Fresh n → n ≥ threshold2) :
    SAT.Lit.eval (shiftedAssignment b σ threshold1 offset) lit =
    SAT.Lit.eval (shiftedAssignment b σ threshold2 offset) lit := by
  cases lit with
  | pos v =>
    simp only [SAT.Lit.eval]
    cases v with
    | Fresh n =>
      simp only [SAT.Lit.getVar] at hFreshGe
      have hn := hFreshGe n rfl
      exact shiftedAssignment_threshold_agree b σ threshold1 threshold2 offset hThresholdLe n hn
    | _ => rfl
  | neg v =>
    simp only [SAT.Lit.eval]
    cases v with
    | Fresh n =>
      simp only [SAT.Lit.getVar] at hFreshGe
      have hn := hFreshGe n rfl
      have hEq := shiftedAssignment_threshold_agree b σ threshold1 threshold2 offset hThresholdLe n hn
      simp only [hEq]
    | _ => rfl

/-- Helper: clause eval with shiftedAssignment agrees across threshold changes for Fresh vars.
    If all Fresh vars in a clause have index >= threshold2 >= threshold1, then
    evaluating the clause with σ' at threshold1 equals evaluating at threshold2. -/
lemma clause_eval_shiftedAssignment_threshold_agree (b : Bounds S) (σ : SAT.Assignment (Var b))
    (threshold1 threshold2 : Nat) (offset : Nat)
    (hThresholdLe : threshold1 ≤ threshold2)
    (c : SAT.Clause (Var b))
    (hFreshGe : ∀ lit, lit ∈ c → ∀ n, SAT.Lit.getVar lit = Var.Fresh n → n ≥ threshold2) :
    SAT.Clause.eval (shiftedAssignment b σ threshold1 offset) c =
    SAT.Clause.eval (shiftedAssignment b σ threshold2 offset) c := by
  simp only [SAT.Clause.eval_eq_any]
  induction c with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.any_cons]
    have hHdFresh : ∀ n, SAT.Lit.getVar hd = Var.Fresh n → n ≥ threshold2 :=
      hFreshGe hd List.mem_cons_self
    have hLitEq := lit_eval_shiftedAssignment_threshold_agree b σ threshold1 threshold2 offset
      hThresholdLe hd hHdFresh
    rw [hLitEq]
    have hTlFresh : ∀ l, l ∈ tl → ∀ n, SAT.Lit.getVar l = Var.Fresh n → n ≥ threshold2 :=
      fun l hl => hFreshGe l (List.mem_cons_of_mem hd hl)
    have hRestEq := ih hTlFresh
    rw [hRestEq]

end Encoding
