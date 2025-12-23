import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Lemmas.Basic
import ModalDistribution.Logic.SATEncoding.Lemmas.NextFreshMono

/-!
# Nested Fold Well-Formedness Lemmas

This file contains lemmas about well-formedness preservation for nested foldl operations
that add clauses. These are used for predicate encoding's guard clause generation.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}

/-- Nested foldl with addClause preserves WF when all clauses contain only non-Fresh vars. -/
lemma nested_foldl_addClause_nonFresh_wf (b : Bounds S) {α β : Type*}
    (outer : List α) (inner : List β) (st : EncState b) (hwf : st.WellFormed)
    (mkClause : β → SAT.Clause (Var b))
    (hNonFresh : ∀ x ∈ inner, ∀ lit ∈ mkClause x, litFreshBelow lit st.nextFresh) :
    (outer.foldl (fun stAcc _ => inner.foldl (fun stAcc' y =>
      EncState.addClause b stAcc' (mkClause y)) stAcc) st).WellFormed := by
  induction outer generalizing st with
  | nil => exact hwf
  | cons _ tl ih =>
    simp only [List.foldl_cons]
    -- First prove inner fold WF
    let st' := inner.foldl (fun stAcc' y => EncState.addClause b stAcc' (mkClause y)) st
    have hInnerWF : st'.WellFormed := (foldl_addClause_wf_mem inner st mkClause hwf (by
      intro y hy lit hLit
      exact hNonFresh y hy lit hLit)).1
    have hInnerNext : st'.nextFresh = st.nextFresh := by
      simp only [st']
      apply foldl_nextFresh_eq
      intro s _; simp [EncState.addClause]
    -- Now apply ih with the new state
    have hNonFresh' : ∀ x ∈ inner, ∀ lit ∈ mkClause x, litFreshBelow lit st'.nextFresh := by
      intro y hy lit hLit
      have hFB := hNonFresh y hy lit hLit
      rw [hInnerNext]
      exact hFB
    exact ih st' hInnerWF hNonFresh'

/-- Inner foldl with addClause preserves WF for a fixed outer variable. -/
lemma inner_foldl_addClause_wf' (b : Bounds S) {α β : Type*}
    (a : α) (inner : List β) (st : EncState b)
    (mkClause : α → β → SAT.Clause (Var b)) (hwf : st.WellFormed)
    (hNonFresh : ∀ x, clauseFreshBelow (mkClause a x) st.nextFresh) :
    (inner.foldl (fun stAcc' x => EncState.addClause b stAcc' (mkClause a x)) st).WellFormed ∧
    (inner.foldl (fun stAcc' x => EncState.addClause b stAcc' (mkClause a x)) st).nextFresh =
      st.nextFresh := by
  induction inner generalizing st with
  | nil => exact ⟨hwf, rfl⟩
  | cons y ys ihInner =>
    simp only [List.foldl_cons]
    have hAddWF := EncState.addClause_wf hwf (mkClause a y) (hNonFresh y)
    have hAddNext : (EncState.addClause b st (mkClause a y)).nextFresh = st.nextFresh :=
      EncState.addClause_nextFresh b st (mkClause a y)
    have hNonFresh' : ∀ x, clauseFreshBelow (mkClause a x)
        (EncState.addClause b st (mkClause a y)).nextFresh := by
      intro x; rw [hAddNext]; exact hNonFresh x
    have ⟨hWF', hNext'⟩ := ihInner (EncState.addClause b st (mkClause a y)) hAddWF hNonFresh'
    exact ⟨hWF', by rw [hNext', hAddNext]⟩

/-- Nested foldl with addClause preserves WF when all clauses contain only non-Fresh vars.
    This version supports a clause maker that depends on both outer and inner loop variables. -/
lemma nested_foldl_addClause_nonFresh_wf' (b : Bounds S) {α β : Type*}
    (outer : List α) (inner : List β) (st : EncState b)
    (mkClause : α → β → SAT.Clause (Var b)) (hwf : st.WellFormed)
    (hNonFresh : ∀ a x, clauseFreshBelow (mkClause a x) st.nextFresh) :
    (outer.foldl (fun stAcc a => inner.foldl (fun stAcc' x =>
      EncState.addClause b stAcc' (mkClause a x)) stAcc) st).WellFormed := by
  induction outer generalizing st with
  | nil => exact hwf
  | cons a tl ih =>
    simp only [List.foldl_cons]
    have ⟨hInnerWF, hInnerNext⟩ := inner_foldl_addClause_wf' b a inner st mkClause hwf
      (fun x => hNonFresh a x)
    have hNonFresh' : ∀ a' x', clauseFreshBelow (mkClause a' x')
        (inner.foldl (fun stAcc' x =>
          EncState.addClause b stAcc' (mkClause a x)) st).nextFresh := by
      intro a' x'; rw [hInnerNext]; exact hNonFresh a' x'
    exact ih _ hInnerWF hNonFresh'

/-- Inner foldl adding pairs of clauses preserves WF for a fixed outer variable. -/
lemma inner_foldl_addClause_pair_wf (bounds : Bounds S) {α β : Type*}
    (a : α) (inner : List β) (st : EncState bounds)
    (mkPairClauses : α → β → SAT.Clause (Var bounds) × SAT.Clause (Var bounds))
    (hwf : st.WellFormed)
    (hNonFresh : ∀ x, clauseFreshBelow (mkPairClauses a x).1 st.nextFresh ∧
                      clauseFreshBelow (mkPairClauses a x).2 st.nextFresh) :
    (inner.foldl (fun stAcc x =>
        EncState.addClause bounds (EncState.addClause bounds stAcc (mkPairClauses a x).1)
          (mkPairClauses a x).2) st).WellFormed ∧
    (inner.foldl (fun stAcc x =>
        EncState.addClause bounds (EncState.addClause bounds stAcc (mkPairClauses a x).1)
          (mkPairClauses a x).2) st).nextFresh = st.nextFresh := by
  induction inner generalizing st with
  | nil => exact ⟨hwf, rfl⟩
  | cons y ys ihInner =>
    simp only [List.foldl_cons]
    have ⟨hNF1, hNF2⟩ := hNonFresh y
    have hAdd1WF := EncState.addClause_wf hwf (mkPairClauses a y).1 hNF1
    have hAdd1Next : (EncState.addClause bounds st (mkPairClauses a y).1).nextFresh =
        st.nextFresh := EncState.addClause_nextFresh bounds st _
    have hNF2' : clauseFreshBelow (mkPairClauses a y).2
        (EncState.addClause bounds st (mkPairClauses a y).1).nextFresh := by
      rw [hAdd1Next]; exact hNF2
    have hAdd2WF := EncState.addClause_wf hAdd1WF (mkPairClauses a y).2 hNF2'
    have hAdd2Next : (EncState.addClause bounds
        (EncState.addClause bounds st (mkPairClauses a y).1) (mkPairClauses a y).2).nextFresh =
        st.nextFresh := by simp [EncState.addClause]
    have hNonFresh' : ∀ x, clauseFreshBelow (mkPairClauses a x).1
        (EncState.addClause bounds (EncState.addClause bounds st (mkPairClauses a y).1)
          (mkPairClauses a y).2).nextFresh ∧
        clauseFreshBelow (mkPairClauses a x).2
        (EncState.addClause bounds (EncState.addClause bounds st (mkPairClauses a y).1)
          (mkPairClauses a y).2).nextFresh := by
      intro x; rw [hAdd2Next]; exact hNonFresh x
    have ⟨hWF', hNext'⟩ := ihInner _ hAdd2WF hNonFresh'
    exact ⟨hWF', by rw [hNext', hAdd2Next]⟩

/-- Nested foldl adding pairs of clauses preserves WF when all clauses
    contain only non-Fresh vars. -/
lemma nested_foldl_addClause_pair_nonFresh_wf (bounds : Bounds S) {α β : Type*}
    (outer : List α) (inner : List β) (st : EncState bounds)
    (mkPairClauses : α → β → SAT.Clause (Var bounds) × SAT.Clause (Var bounds))
    (hwf : st.WellFormed)
    (hNonFresh : ∀ a x, clauseFreshBelow (mkPairClauses a x).1 st.nextFresh ∧
                        clauseFreshBelow (mkPairClauses a x).2 st.nextFresh) :
    (outer.foldl (fun stCur a => inner.foldl (fun stAcc x =>
        EncState.addClause bounds (EncState.addClause bounds stAcc (mkPairClauses a x).1)
          (mkPairClauses a x).2) stCur) st).WellFormed := by
  induction outer generalizing st with
  | nil => exact hwf
  | cons a tl ih =>
    simp only [List.foldl_cons]
    have ⟨hInnerWF, hInnerNext⟩ := inner_foldl_addClause_pair_wf bounds a inner st mkPairClauses
      hwf (fun x => hNonFresh a x)
    have hNonFresh' : ∀ a' x', clauseFreshBelow (mkPairClauses a' x').1
        (inner.foldl (fun stAcc x =>
          EncState.addClause bounds (EncState.addClause bounds stAcc (mkPairClauses a x).1)
            (mkPairClauses a x).2) st).nextFresh ∧
        clauseFreshBelow (mkPairClauses a' x').2
        (inner.foldl (fun stAcc x =>
          EncState.addClause bounds (EncState.addClause bounds stAcc (mkPairClauses a x).1)
            (mkPairClauses a x).2) st).nextFresh := by
      intro a' x'; rw [hInnerNext]; exact hNonFresh a' x'
    exact ih _ hInnerWF hNonFresh'

end Encoding
