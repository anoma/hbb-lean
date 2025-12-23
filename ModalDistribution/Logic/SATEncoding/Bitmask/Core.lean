import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.FinRange

/-!
# Bitmask ↔ Finset Conversions (Core)

This module provides the basic, dependency-light API for converting between bitmasks
and finite index sets. These definitions sit in their own file so they can be reused
without introducing a dependency on the SAT variable enumeration.
-/

namespace ModalDistribution
namespace Encoding

/-! ## Conversion Functions -/

/-- Convert a `Finset (Fin n)` to its bitmask representation.
Each element `i ∈ Q` sets bit `i.` -/
def finsetToBitmask {n : Nat} (Q : Finset (Fin n)) : Nat :=
  Q.fold (· ||| ·) 0 (fun i => Nat.shiftLeft 1 i.val)

/-- Convert a bitmask to a `Finset (Fin n)`.
Element `i` is included iff bit `i` is set. -/
def bitmaskToFinset (n : Nat) (mask : Nat) : Finset (Fin n) :=
  (List.finRange n).filter (fun i => (mask >>> i.val) &&& 1 = 1) |>.toFinset

@[simp] lemma bitmaskToFinset_filter (n : Nat) (mask : Nat) :
    ((List.finRange n).filter (fun i => (mask >>> i.val) &&& 1 = 1)).toFinset =
      bitmaskToFinset n mask :=
  rfl

/-! ## Bit Manipulation Helpers -/

lemma testBit_shiftRight_zero (n k : Nat) :
    (n >>> k).testBit 0 = n.testBit k := by
  unfold Nat.testBit
  simp

lemma land_one_eq_one_iff_testBit (n k : Nat) :
    ((n >>> k) &&& 1 = 1) ↔ n.testBit k = true := by
  classical
  have h := Nat.and_two_pow (n >>> k) 0
  have h' : (n >>> k) &&& 1 = ((n >>> k).testBit 0).toNat := by
    simpa [pow_zero] using h
  constructor
  · intro hEq
    have hToNat : ((n >>> k).testBit 0).toNat = 1 := by
      simpa [h'] using hEq
    cases hVal : (n >>> k).testBit 0 with
    | false =>
        simp [Bool.toNat, hVal] at hToNat
    | true =>
        simpa [testBit_shiftRight_zero, hVal]
  · intro hBit
    have hVal : (n >>> k).testBit 0 = true := by
      simpa [testBit_shiftRight_zero] using hBit
    have hToNat : ((n >>> k).testBit 0).toNat = 1 := by
      simp [hVal]
    simp [h', hVal]

lemma bitmaskToFinset_mem_iff (n mask : Nat) (i : Fin n) :
    i ∈ bitmaskToFinset n mask ↔ mask.testBit i.val = true := by
  classical
  constructor
  · intro hi
    have hiList :
        i ∈ (List.finRange n).filter (fun j => (mask >>> j.val) &&& 1 = 1) :=
      (List.mem_toFinset).1 hi
    obtain ⟨hiRange, hiCond⟩ := List.mem_filter.1 hiList
    have hiCondProp : (mask >>> i.val) &&& 1 = 1 :=
      of_decide_eq_true hiCond
    exact (land_one_eq_one_iff_testBit mask i.val).mp hiCondProp
  · intro hbit
    have hiCond : (mask >>> i.val) &&& 1 = 1 :=
      (land_one_eq_one_iff_testBit mask i.val).mpr hbit
    have hiCondBool :
        decide ((mask >>> i.val) &&& 1 = 1) = true :=
      decide_eq_true_iff.mpr hiCond
    have hiRange :
        i ∈ List.finRange n := by
      simp [List.mem_finRange]
    have hiList :
        i ∈ (List.finRange n).filter (fun j => (mask >>> j.val) &&& 1 = 1) :=
      List.mem_filter.2 ⟨hiRange, hiCondBool⟩
    exact (List.mem_toFinset).2 hiList

@[simp] lemma bitmaskToFinset_coe_set (n : Nat) (mask : Nat) :
    {x : Fin n | mask.testBit x.val = true}
      = (bitmaskToFinset n mask : Set (Fin n)) := by
  ext i
  change mask.testBit i.val = true ↔ i ∈ bitmaskToFinset n mask
  simp [bitmaskToFinset_mem_iff]

@[simp] lemma testBit_shiftLeft_one (m k : Nat) :
    (Nat.shiftLeft 1 m).testBit k = decide (m = k) := by
  classical
  by_cases h : m = k
  · subst h
    simp [Nat.shiftLeft_eq]
  · simp [Nat.shiftLeft_eq, h]

/-- Helper: `Nat.testBit` of `1` at positive indices is false. -/
lemma testBit_one_pos {k : Nat} (hk : 0 < k) : Nat.testBit 1 k = false := by
  cases k with
  | zero => exact (Nat.lt_asymm hk hk).elim
  | succ k' =>
    rw [Nat.testBit_succ]
    simp

/-! ## Characterisation Lemmas -/

lemma finsetToBitmask_testBit {n : Nat} (Q : Finset (Fin n)) (k : Nat) :
    (finsetToBitmask Q).testBit k = decide (∃ i ∈ Q, i.val = k) := by
  classical
  refine Q.induction_on ?base ?step
  · simp [finsetToBitmask]
  · intro a s ha ih
    have hfold :
        finsetToBitmask (insert a s)
          = Nat.shiftLeft 1 a.val ||| finsetToBitmask s := by
      simp [finsetToBitmask, ha]
    have hmem :
        (∃ i ∈ insert a s, i.val = k) ↔
          (a.val = k ∨ ∃ i ∈ s, i.val = k) := by
      constructor
      · rintro ⟨i, hi, hiVal⟩
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inl hiVal
        · exact Or.inr ⟨i, hi, hiVal⟩
      · rintro (h | ⟨i, hi, hiVal⟩)
        · exact ⟨a, Finset.mem_insert_self _ _, h⟩
        · exact ⟨i, Finset.mem_insert_of_mem hi, hiVal⟩
    by_cases hk : a.val = k
    · have hBit :
          (finsetToBitmask (insert a s)).testBit k = true := by
        rw [hfold, Nat.testBit_lor, testBit_shiftLeft_one]
        simp [hk]
      have hMem : decide (∃ i ∈ insert a s, i.val = k) = true := by
        simp [hk]
      exact hBit.trans hMem.symm
    · have hBit :
          (finsetToBitmask (insert a s)).testBit k =
            (finsetToBitmask s).testBit k := by
        rw [hfold, Nat.testBit_lor, testBit_shiftLeft_one]
        simp [hk]
      have hMem :
          decide (∃ i ∈ insert a s, i.val = k) =
            decide (∃ i ∈ s, i.val = k) := by
        simp [hk]
      exact hBit.trans (ih.trans hMem.symm)

lemma finsetToBitmask_testBit_high {n : Nat} (Q : Finset (Fin n))
    {k : Nat} (hk : n ≤ k) :
    (finsetToBitmask Q).testBit k = false := by
  rw [finsetToBitmask_testBit]
  simp only [decide_eq_false_iff_not]
  intro ⟨i, _, hiVal⟩
  have : i.val < n := i.isLt
  exact (not_lt_of_ge hk) (hiVal ▸ this)

lemma finsetToBitmask_lt {n : Nat} (Q : Finset (Fin n)) :
    finsetToBitmask Q < Nat.shiftLeft 1 n := by
  have hMaskBit :
      (finsetToBitmask Q).testBit n = false :=
    finsetToBitmask_testBit_high Q (Nat.le_refl _)
  have hPowBit :
      (Nat.shiftLeft 1 n).testBit n = true := by
    simp
  have hAbove :
      ∀ j, n < j →
        (finsetToBitmask Q).testBit j = (Nat.shiftLeft 1 n).testBit j := by
    intro j hj
    have hMask := finsetToBitmask_testBit_high Q (le_of_lt hj)
    have hPow : (Nat.shiftLeft 1 n).testBit j = false := by
      rw [testBit_shiftLeft_one]
      simp [ne_of_lt hj]
    exact hMask.trans hPow.symm
  exact Nat.lt_of_testBit n hMaskBit hPowBit hAbove

/-! ## Inverse Lemmas -/

lemma bitmaskToFinset_inverse (n : Nat) (mask : Fin (Nat.shiftLeft 1 n)) :
    finsetToBitmask (bitmaskToFinset n mask.val) = mask.val := by
  classical
  have hMaskBound : mask.val < 2 ^ n := by
    simpa [Nat.shiftLeft_eq] using mask.is_lt
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · have hExists :
      (∃ i ∈ bitmaskToFinset n mask.val, i.val = k) ↔
        mask.val.testBit k = true := by
      constructor
      · intro hex
        rcases hex with ⟨i, hi, hiVal⟩
        have hiBit : mask.val.testBit i.val = true := by
          simpa [bitmaskToFinset, Nat.testBit, i.is_lt] using hi
        simpa [hiVal] using hiBit
      · intro hbit
        refine ⟨⟨k, hk⟩, ?_, ?_⟩
        · simpa [bitmaskToFinset, Nat.testBit, hk] using hbit
        · simp
    cases hbit : mask.val.testBit k with
    | false =>
        have hNo : ¬ ∃ i ∈ bitmaskToFinset n mask.val, i.val = k := by
          intro hex
          have h := (hExists.mp) hex
          simp [hbit] at h
        simp [finsetToBitmask_testBit, hExists, hbit]
    | true =>
        simp [finsetToBitmask_testBit, hExists, hbit]
  · have hk_le : n ≤ k := Nat.le_of_not_lt hk
    have hNo : ¬ ∃ i ∈ bitmaskToFinset n mask.val, i.val = k := by
      intro hex
      rcases hex with ⟨i, _, hiVal⟩
      exact hk (hiVal ▸ i.is_lt)
    have hPowMono : 2 ^ n ≤ 2 ^ k := by
      have hk' : n + (k - n) = k := Nat.add_sub_of_le hk_le
      have hOne : 1 ≤ 2 ^ (k - n) := Nat.one_le_pow _ _ (by decide)
      have hMul : 2 ^ n ≤ 2 ^ n * 2 ^ (k - n) := by
        have := Nat.mul_le_mul_left (2 ^ n) hOne
        simpa using this
      have hPowAdd := Nat.pow_add 2 n (k - n)
      have hPowEq : 2 ^ n * 2 ^ (k - n) = 2 ^ k := by
        simpa [hk', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hPowAdd.symm
      simpa [hPowEq] using hMul
    have hBit : mask.val.testBit k = false := by
      have : mask.val < 2 ^ k := lt_of_lt_of_le hMaskBound hPowMono
      exact Nat.testBit_eq_false_of_lt this
    simp [finsetToBitmask_testBit, hNo, hBit]

lemma finsetToBitmask_inverse {n : Nat} (Q : Finset (Fin n)) :
    bitmaskToFinset n (finsetToBitmask Q) = Q := by
  classical
  ext i
  constructor
  · intro hi
    have hBit : (finsetToBitmask Q).testBit i.val = true :=
      (bitmaskToFinset_mem_iff n (finsetToBitmask Q) i).1 hi
    have hDec :
        decide (∃ j ∈ Q, j.val = i.val) = true := by
      simpa [finsetToBitmask_testBit] using hBit
    have hExists : ∃ j ∈ Q, j.val = i.val := of_decide_eq_true hDec
    rcases hExists with ⟨j, hj, hjVal⟩
    have hjEq : j = i := Fin.ext (by simp [hjVal])
    simpa [hjEq] using hj
  · intro hi
    have hDec :
        decide (∃ j ∈ Q, j.val = i.val) = true :=
      decide_eq_true_iff.mpr ⟨i, hi, rfl⟩
    have hBit : (finsetToBitmask Q).testBit i.val = true := by
      simpa [finsetToBitmask_testBit] using hDec
    exact (bitmaskToFinset_mem_iff n (finsetToBitmask Q) i).2 hBit

end Encoding
end ModalDistribution
