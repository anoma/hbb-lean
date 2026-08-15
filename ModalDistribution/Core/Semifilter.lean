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

theorem intersects_self_iff_nonempty {O : Set P} :
    (O ≬ O) ↔ O.Nonempty := by
  classical
  simp [Semifilter.intersects, inter_self]

/-- Intersections distribute over a shared witness. -/
theorem intersects_of_mem {p : P} {O O' : Set P}
    (hpO : p ∈ O) (hpO' : p ∈ O') :
    O ≬ O' := by
  classical
  refine ⟨p, ?_⟩
  exact ⟨hpO, hpO'⟩

/-- Intersections are witnessed precisely by shared members. -/
theorem intersects_iff {O O' : Set P} :
    (O ≬ O') ↔ ∃ p, p ∈ O ∧ p ∈ O' := by
  classical
  constructor
  · intro hint
    rcases hint with ⟨p, hp⟩
    exact ⟨p, hp.1, hp.2⟩
  · rintro ⟨p, hpO, hpO'⟩
    exact intersects_of_mem (P := P) hpO hpO'


theorem quorum_nonempty {L : Semifilter P} {O : Set P}
    (hO : O ∈ L.quorums) :
    O.Nonempty := by
  have := L.pairwiseInter hO hO
  simpa [intersects_self_iff_nonempty] using this

/-- Any two quorums in a semifilter intersect. -/
theorem intersects_of_mem_quorums {L : Semifilter P} {O₁ O₂ : Set P}
    (h₁ : O₁ ∈ L.quorums) (h₂ : O₂ ∈ L.quorums) :
    O₁ ≬ O₂ :=
  L.pairwiseInter h₁ h₂

@[ext] theorem ext {L₁ L₂ : Semifilter P}
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
