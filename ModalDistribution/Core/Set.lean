import ModalDistribution.Core.Tactics

/-!
# Sets

A set over `α` is identified with its membership predicate.  This file provides
the set-builder notation, the operations (`⊆`, `∩`, `∅`, `univ`) and the
membership lemmas used throughout the development.

## Main definitions

* `Set α`: sets over `α`, presented as predicates.
* `setOf` together with the set-builder notation `{ x | p x }`.
* `Set.univ`, `Set.Nonempty`, and the `HasSubset`, `Inter`, `EmptyCollection`
  instances.
-/

universe u

/-- A set over `α` is determined by its membership predicate. -/
def Set (α : Type u) := α → Prop

/-- The set of elements of `α` satisfying `p`. -/
def setOf {α : Type u} (p : α → Prop) : Set α := p

@[inherit_doc setOf]
syntax "{" ident (" : " term)? " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x:ident => $p)
  | `({ $x:ident : $t | $p }) => `(setOf fun $x:ident : $t => $p)

namespace Set

variable {α : Type u}

instance : Membership α (Set α) where
  mem s a := s a

@[simp] theorem mem_setOf_eq {a : α} {p : α → Prop} : (a ∈ { x | p x }) = p a := rfl

/-- Sets with the same members are equal. -/
@[ext] theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext fun x => propext (h x)

/-- Inclusion of sets: every member of `s` is a member of `t`. -/
protected def Subset (s t : Set α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ s → a ∈ t

instance : HasSubset (Set α) := ⟨Set.Subset⟩

/-- Inclusion is reflexive. -/
@[refl] theorem Subset.refl (s : Set α) : s ⊆ s := fun _ h => h

/-- Inclusion is transitive. -/
theorem Subset.trans {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  fun _ h => htu (hst h)

/-- The empty set has no members. -/
instance : EmptyCollection (Set α) := ⟨fun _ => False⟩

@[simp] theorem mem_empty_iff_false {a : α} : a ∈ (∅ : Set α) ↔ False := Iff.rfl

/-- The set of all elements of `α`. -/
def univ : Set α := fun _ => True

@[simp] theorem mem_univ (a : α) : a ∈ (univ : Set α) := trivial

/-- Intersection of two sets. -/
protected def inter (s t : Set α) : Set α := fun a => a ∈ s ∧ a ∈ t

instance : Inter (Set α) := ⟨Set.inter⟩

@[simp] theorem mem_inter_iff {a : α} {s t : Set α} : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := Iff.rfl

/-- A set is nonempty when it has a member. -/
protected def Nonempty (s : Set α) : Prop := ∃ x, x ∈ s

@[simp] theorem not_nonempty_empty : ¬ (∅ : Set α).Nonempty := fun ⟨_, h⟩ => h

theorem mem_of_mem_inter_left {a : α} {s t : Set α} (h : a ∈ s ∩ t) : a ∈ s := h.1

theorem mem_of_mem_inter_right {a : α} {s t : Set α} (h : a ∈ s ∩ t) : a ∈ t := h.2

theorem inter_comm (s t : Set α) : s ∩ t = t ∩ s :=
  Set.ext fun _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

@[simp] theorem inter_self (s : Set α) : s ∩ s = s :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem inter_assoc (s t u : Set α) : s ∩ t ∩ u = s ∩ (t ∩ u) :=
  Set.ext fun _ => ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem inter_left_comm (s t u : Set α) : s ∩ (t ∩ u) = t ∩ (s ∩ u) :=
  Set.ext fun _ => ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

@[simp] theorem inter_univ (s : Set α) : s ∩ univ = s :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

@[simp] theorem univ_inter (s : Set α) : univ ∩ s = s :=
  Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

@[simp] theorem empty_inter (s : Set α) : ∅ ∩ s = (∅ : Set α) :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => h.elim⟩

@[simp] theorem inter_empty (s : Set α) : s ∩ ∅ = (∅ : Set α) :=
  Set.ext fun _ => ⟨fun h => h.2, fun h => h.elim⟩

end Set

/-- Inclusion of sets is reflexive. -/
theorem subset_rfl {α : Type u} {s : Set α} : s ⊆ s := Set.Subset.refl s
