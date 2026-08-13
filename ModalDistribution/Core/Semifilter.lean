import ModalDistribution.Core.Set
import ModalDistribution.Core.History

open Set
open History

/-!
# Semifilter Structures

This file introduces semifilters as the set-theoretic foundation for quorums, following
Notation and definition for semifilters. Semifilters capture nonempty,
up-closed families of pairwise intersecting quorums on a set of participants.

## Main definitions

* `Semifilter.intersects` (`≬`): quorum-intersection predicate.
* `Semifilter`: structure of nonempty up-closed pairwise-intersecting families of quorums.

## References

* Paper notation for quorum intersection.
* Paper definition for semifilters.
-/

universe u

namespace Semifilter

variable {P : Type u}

/-- Quorum intersection: `O ≬ O'` when two quorums intersect (their intersection is nonempty). -/
@[simp] def intersects (O O' : Set P) : Prop := (O ∩ O').Nonempty

scoped infix:50 " ≬ " => Semifilter.intersects

end Semifilter

open scoped Semifilter

/-- A semifilter is: A semifilter is a nonempty up-closed family of pairwise
intersecting quorums over a participant set `P`. -/
structure Semifilter (P : Type u) where
  /-- Carrier set of quorums. -/
  quorums : Set (Set P)
  /-- Property 1: the family of quorums is nonempty. -/
  nonempty : quorums.Nonempty
  /-- Property 2: the family is up-closed under supersets inside `P`. -/
  upwardClosed : ∀ ⦃O O' : Set P⦄, O ∈ quorums → O ⊆ O' → O' ∈ quorums
  /-- Property 3: quorums pairwise intersect. -/
  pairwiseInter : ∀ ⦃O O' : Set P⦄, O ∈ quorums → O' ∈ quorums → O ≬ O'

namespace Semifilter

variable {P : Type u}

/-/ Intersections are symmetric. -/
lemma intersects_comm {O O' : Set P} :
    (O ≬ O') ↔ (O' ≬ O) := by
  classical
  simp [Semifilter.intersects, inter_comm]

/-- A quorum intersects itself exactly when it is nonempty. -/
lemma intersects_self_iff_nonempty {O : Set P} :
    (O ≬ O) ↔ O.Nonempty := by
  classical
  simp [Semifilter.intersects, inter_self]

/-- Intersections distribute over a shared witness. -/
lemma intersects_of_mem {p : P} {O O' : Set P}
    (hpO : p ∈ O) (hpO' : p ∈ O') :
    O ≬ O' := by
  classical
  refine ⟨p, ?_⟩
  exact ⟨hpO, hpO'⟩

/-- Intersections are witnessed precisely by shared members. -/
lemma intersects_iff {O O' : Set P} :
    (O ≬ O') ↔ ∃ p, p ∈ O ∧ p ∈ O' := by
  classical
  constructor
  · intro hint
    rcases hint with ⟨p, hp⟩
    exact ⟨p, hp.1, hp.2⟩
  · rintro ⟨p, hpO, hpO'⟩
    exact intersects_of_mem (P := P) hpO hpO'

/-- Intersecting quorums are themselves nonempty on the left. -/
lemma intersects_nonempty_left {O O' : Set P} :
    O ≬ O' → O.Nonempty :=
  by
    intro hint
    rcases hint with ⟨p, hp⟩
    exact ⟨p, hp.1⟩

/-- Intersecting quorums are themselves nonempty on the right. -/
lemma intersects_nonempty_right {O O' : Set P} :
    O ≬ O' → O'.Nonempty :=
  by
    intro hint
    rcases hint with ⟨p, hp⟩
    exact ⟨p, hp.2⟩

/-- Intersections are monotone in their arguments. -/
lemma intersects_mono {O O' O₁ O₂ : Set P}
    (h₁ : O ⊆ O₁) (h₂ : O' ⊆ O₂) (hint : O ≬ O') :
    O₁ ≬ O₂ := by
  classical
  rcases hint with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  exact ⟨h₁ hp.1, h₂ hp.2⟩

/-- Property 2: Supersets of quorums remain quorums. -/
lemma upwards_of_subset {L : Semifilter P} {O O' : Set P}
    (hO : O ∈ L.quorums) (h_subset : O ⊆ O') :
    O' ∈ L.quorums := by
  exact L.upwardClosed hO h_subset

/-- Property 3: Quorums intersect pairwise. -/
lemma intersects_mem {L : Semifilter P} {O O' : Set P}
    (hO : O ∈ L.quorums) (hO' : O' ∈ L.quorums) :
    O ≬ O' := by
  exact L.pairwiseInter hO hO'

/-- Property 1: Every quorum in a semifilter is nonempty. -/
lemma quorum_nonempty {L : Semifilter P} {O : Set P}
    (hO : O ∈ L.quorums) :
    O.Nonempty := by
  have := L.pairwiseInter hO hO
  simpa [intersects_self_iff_nonempty] using this

/-- Any two quorums in a semifilter intersect. -/
lemma intersects_of_mem_quorums {L : Semifilter P} {O₁ O₂ : Set P}
    (h₁ : O₁ ∈ L.quorums) (h₂ : O₂ ∈ L.quorums) :
    O₁ ≬ O₂ :=
  L.pairwiseInter h₁ h₂

/-- Property 1: A semifilter contains at least one quorum. -/
lemma exists_quorum (L : Semifilter P) :
    ∃ O : Set P, O ∈ L.quorums := by
  exact L.nonempty

/-- If a property cannot be witnessed on every quorum, some quorum forces its negation. -/
lemma exists_quorum_forall_not {L : Semifilter P} {R : P → Prop}
    (h : ¬ ∀ O ∈ L.quorums, ∃ q ∈ O, R q) :
    ∃ O ∈ L.quorums, ∀ q ∈ O, ¬ R q := by
  classical
  have : ∃ O ∈ L.quorums, ¬ (∃ q ∈ O, R q) := by
    refine Classical.byContradiction ?_
    intro hcon
    exact h fun O hO => Classical.byContradiction fun hq => hcon ⟨O, hO, hq⟩
  rcases this with ⟨O, hO, hNone⟩
  refine ⟨O, hO, ?_⟩
  intro q hq
  have : ¬ (R q) := by
    have hno := not_exists.mp hNone q
    exact (not_and.mp hno) hq
  simpa using this

/-- Intersections grow monotonically with supersets on the left. -/
lemma intersects_mono_left {O O' O'' : Set P}
    (h_subset : O ⊆ O') (hint : O ≬ O'') :
    O' ≬ O'' := by
  classical
  have hmono :=
    intersects_mono (P := P) (O := O) (O' := O'') (O₁ := O') (O₂ := O'')
      h_subset subset_rfl hint
  simpa using hmono

/-- Intersections grow monotonically with supersets on the right. -/
lemma intersects_mono_right {O O' O'' : Set P}
    (h_subset : O' ⊆ O'') (hint : O ≬ O') :
    O ≬ O'' := by
  classical
  have hmono :=
    intersects_mono (P := P) (O := O) (O' := O') (O₁ := O) (O₂ := O'')
      subset_rfl h_subset hint
  simpa using hmono

/-- The empty set fails to intersect any quorum. -/
@[simp] lemma intersects_empty_left {O : Set P} :
    (∅ : Set P) ≬ O ↔ False := by
  classical
  simp [Semifilter.intersects]

/-- Any quorum fails to intersect the empty set. -/
@[simp] lemma intersects_empty_right {O : Set P} :
    O ≬ (∅ : Set P) ↔ False := by
  classical
  simp [Semifilter.intersects]

/-- Extensionality: semifilters coincide when they have the same quorums. -/
@[ext] lemma ext {L₁ L₂ : Semifilter P}
    (h : ∀ O : Set P, O ∈ L₁.quorums ↔ O ∈ L₂.quorums) :
    L₁ = L₂ := by
  classical
  cases L₁ with
  | mk Q₁ n₁ u₁ p₁ =>
    cases L₂ with
    | mk Q₂ n₂ u₂ p₂ =>
      have hQ : Q₁ = Q₂ := by
        ext O
        exact (h O)
      subst hQ
      have : n₁ = n₂ := Subsingleton.elim _ _
      subst this
      have : u₁ = u₂ := Subsingleton.elim _ _
      subst this
      have : p₁ = p₂ := Subsingleton.elim _ _
      subst this
      rfl

end Semifilter
