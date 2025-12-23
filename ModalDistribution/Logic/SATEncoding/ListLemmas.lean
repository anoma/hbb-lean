import Mathlib.Data.List.Basic

/-!
# List Helper Lemmas

This file contains general-purpose lemmas about List operations,
particularly for `List.mapIdxFrom` which is used in the SAT encoding
for enumeration and indexing with a custom starting index.

These lemmas are not specific to the adequacy proof and may be
useful in other parts of the encoding.
-/

namespace List

/-- Helper: map a list with indices starting from a given index.
    This is different from Mathlib's `List.mapIdx` which starts from 0
    and has a different parameter order. -/
def mapIdxFrom {α β} (f : Nat → α → β) : List α → Nat → List β
  | [], _ => []
  | x :: xs, i => f i x :: mapIdxFrom f xs (i+1)

/-- Convenience alias for List.get with Nat index and proof. -/
def nthLe {α} (xs : List α) (idx : Nat) (h : idx < xs.length) : α :=
  xs.get ⟨idx, h⟩

/-- Evaluate `List.get` on a mapped list. -/
@[simp] lemma get_map {α β} (f : α → β) (xs : List α) (idx : Nat)
    (h : idx < xs.length) :
    (xs.map f).get ⟨idx, by simpa [length_map] using h⟩
      = f (xs.get ⟨idx, h⟩) := by
  induction xs generalizing idx with
  | nil => cases h
  | cons x xs ih =>
      cases idx with
      | zero =>
          simp
      | succ idx =>
          have h' : idx < xs.length := Nat.lt_of_succ_lt_succ h
          simp

/-- The length of mapIdxFrom is the same as the original list. -/
lemma length_mapIdxFrom {α β} (f : Nat → α → β) (xs : List α) (start : Nat) :
    (xs.mapIdxFrom f start).length = xs.length := by
  induction xs generalizing start with
  | nil => simp [mapIdxFrom]
  | cons x xs ih =>
      simp [mapIdxFrom, ih]

/-- Getting from mapIdxFrom gives the function applied to the correct index. -/
lemma get_mapIdxFrom {α β} (f : Nat → α → β) (xs : List α) (start idx : Nat)
    (h : idx < xs.length) :
    (xs.mapIdxFrom f start).get ⟨idx, by simpa [length_mapIdxFrom] using h⟩
      = f (start + idx) (xs.get ⟨idx, h⟩) := by
  induction xs generalizing start idx with
  | nil => cases h
  | cons x xs ih =>
      cases idx with
      | zero =>
          simp [mapIdxFrom]
      | succ idx =>
          have : idx < xs.length := Nat.lt_of_succ_lt_succ h
          have := ih (start + 1) idx this
          simpa [mapIdxFrom, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
            List.get_cons_succ]
            using this

/-- nthLe version of get_mapIdxFrom. -/
lemma nthLe_mapIdxFrom {α β} (f : Nat → α → β) (xs : List α) (start idx : Nat)
    (h : idx < xs.length) :
    (xs.mapIdxFrom f start).nthLe idx (by simpa [length_mapIdxFrom] using h)
      = f (start + idx) (xs.nthLe idx h) := by
  unfold nthLe
  simpa using
    (get_mapIdxFrom (f := f) (xs := xs) (start := start) (idx := idx) (h := h))

end List
