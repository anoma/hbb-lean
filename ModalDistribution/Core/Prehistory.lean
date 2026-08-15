import ModalDistribution.Core.Set
import ModalDistribution.Core.Equiv

/-!
# Prehistory Structures

This file formalizes prehistory structures for HBB.
A prehistory represents the finite set of events and their causal relationships
in a distributed system.

## Main definitions

* `World P Event History`: Type for event tuples (p, E, H) where p ∈ P, E ∈ Event†,
  H is a history type
* `MaybeEvent Event`: Type Event† = Event ∪ {†} for maybe-events
* `PreHistory P Event`: Inductive type for prehistories as finite sets of event tuples

## Main theorems

* Structural induction principle for prehistories
* Basic properties of the happens-before relations
-/

universe u v

variable {P : Type u} {Event : Type v}

-- Definition of maybe-events (Event†)
/-- Paper: Notation 2.2.2 (maybe-sets). -/
inductive MaybeEvent (Event : Type v) where
  | some : Event → MaybeEvent Event  -- Regular events
  | none : MaybeEvent Event          -- The non-event †

notation:max "†" => MaybeEvent.none

-- Prehistory inductive type.
-- Note: We use List instead of a finite-set type due to Lean's positivity restrictions.
-- The paper acknowledges this approach (pages 4-5), noting that while it introduces
-- redundancy (multiple lists can represent the same logical prehistory), all the
-- mathematical development works with this representation.
-- The paper's requirement that prehistories are finite (⊆fin) is automatically
-- satisfied because: (1) inductive types in Lean are well-founded by construction,
-- preventing infinite recursion, and (2) Lists have finite length.
/-- Paper: Definition 2.2.4 (Prehistories).

Representation note: this is list-backed, so it realises the paper's
inductive-datatype presentation (its Section 2.1) rather than the quotiented
set-theoretic definition — distinct terms (reorderings, duplicates) can denote
the same intended prehistory. All results are stated through membership, never
through equality of prehistories, so the redundancy is harmless, as the paper
itself notes for the datatype view. -/
inductive PreHistory (P : Type u) (Event : Type v) where
  | mk : List (P × MaybeEvent Event × PreHistory P Event) → PreHistory P Event

-- Event tuple type alias.
-- An event tuple is (p, E, H) ∈ P × Event† × PreHistory(P, Event)
-- Note: World must be defined after PreHistory due to dependency
/-- Paper: Definition 2.2.6(1) (event-tuples). -/
abbrev World (P : Type u) (Event : Type v) := P × MaybeEvent Event × PreHistory P Event

namespace World

variable {P : Type u} {Event : Type v}

/-!
### Projection functions for event tuples

The specification refers to the *place*, *(maybe-)event*, and *time* of
an event tuple. We expose exactly those projections.
-/
/-- Paper: Definition 2.2.6(2). -/
@[simp] def place (t : World P Event) : P := t.1

/-- Paper: Definition 2.2.6(2). -/
@[simp] def event (t : World P Event) : MaybeEvent Event := t.2.1

/-- Paper: Definition 2.2.6(2). -/
@[simp] def time (t : World P Event) : PreHistory P Event := t.2.2

-- Constructor for event tuples (for convenience)
def mk (p : P) (e : MaybeEvent Event) (h : PreHistory P Event) : World P Event :=
  (p, e, h)

-- Simp lemmas for projections on constructed tuples




end World
namespace PreHistory
def empty : PreHistory P Event := mk []

-- Singleton prehistory
def singleton (t : World P Event) : PreHistory P Event :=
  mk [t]

-- Construct from a list (allows duplicates)
/-- Paper: Definition 2.2.6(5) (the "knows of" relation). -/
def mem (tuple : World P Event) (h : PreHistory P Event) : Prop :=
  match h with
  | mk l => tuple ∈ l

-- The paper phrases this as "H knows of the
-- event-tuple (p, E, H′)”, i.e. membership in the prehistory.

instance : Membership (World P Event) (PreHistory P Event) where
  mem := fun h t => PreHistory.mem t h

/-! ## Simp lemmas for PreHistory membership and operations -/

-- Basic membership lemma

-- Empty prehistory membership
def subset (h1 h2 : PreHistory P Event) : Prop :=
  ∀ t, t ∈ h1 → t ∈ h2

instance : HasSubset (PreHistory P Event) where
  Subset := PreHistory.subset

-- Subset in terms of membership

end PreHistory

namespace World

/-!
### Accessibility relations on event tuples

Accessibility defines accessibility
between worlds as membership of the predecessor tuple in the enclosing history.
We expose that relation directly on event tuples so that worlds can be modelled
without introducing additional wrappers.
-/

/-- Paper: Definition 3.4.2(3) (accessibility, ≪). Strict accessibility: `t' ≪ t` when `t'` belongs to the time component of `t`. -/
def accessible (t' t : World P Event) : Prop :=
  t' ∈ World.time t

/-- Paper: Definition 3.4.2(4) (in-place accessibility, ≪⁻). Same-place accessibility (`≪^{-}` in Accessibility(4)). -/
def accessibleLe (t' t : World P Event) : Prop :=
  accessible t' t ∧ World.place t' = World.place t

end World
namespace PreHistory
scoped infix:50 " ≪ " => World.accessible
scoped infix:50 " ≪⁻ " => World.accessibleLe
end PreHistory
namespace World
open scoped PreHistory
end World
namespace PreHistory
/-- Paper: Definition 3.4.7 (H at p). -/
def historyAt (H : PreHistory P Event) (p : P) : Set (World P Event) :=
  { t | t ∈ H ∧ World.place t = p }

/-- Paper: Definition 2.3.1(1) (element-of, ≺−). -/
def happensBefore (h1 h2 : PreHistory P Event) : Prop :=
  ∃ (p : P) (e : MaybeEvent Event),
    (p, e, h1) ∈ h2

-- H' ⪯ H: H' happens non-strictly before H
-- iff H' ≺− H ∨ H' = H
/-- Paper: Definition 2.3.1(2) (non-strict element-of, ⪯). -/
def happensBeforeEq (h1 h2 : PreHistory P Event) : Prop :=
  happensBefore h1 h2 ∨ h1 = h2

-- Notation for happens-before relations
infixl:50 " ≺− " => happensBefore
infixl:50 " ⪯ " => happensBeforeEq

-- Happens-before membership characterization

/-- Paper: Lemma 3.4.3. Combining accessibility and happens-before:
strict accessibility forces the predecessor time to happen before the
successor. -/
theorem happensBefore_of_accessible {t' t : World P Event}
    (h : t' ≪ t) :
    happensBefore (World.time t') (World.time t) := by
  rcases t' with ⟨p, e, h'⟩
  exact ⟨p, e, by simpa [happensBefore] using h⟩

/-- Accessibility: the non-strict happens-before relation absorbs
the strict case obtained from accessibility. -/
theorem happensBeforeEq_of_accessible {t' t : World P Event}
    (h : t' ≪ t) :
    happensBeforeEq (World.time t') (World.time t) :=
  Or.inl (happensBefore_of_accessible (P := P) (Event := Event) h)

-- Basic Properties and Lemmas (from acceptance criteria)

-- Induction principle (structural induction for prehistories).
-- The result is
-- implicit in the inductive definition.
-- "Let PreHistory(P, Event), the set of prehistories over P and Event,
-- be the least set closed under..."
@[simp] theorem happensBeforeEq_iff (h1 h2 : PreHistory P Event) :
    h1 ⪯ h2 ↔ h1 ≺− h2 ∨ h1 = h2 := by
  rfl

-- ⪯ is a preorder (reflexivity and transitivity)
theorem happensBeforeEq_refl (h : PreHistory P Event) : h ⪯ h := by
  -- By definition, h ⪯ h means h ≺− h ∨ h = h
  -- We use the right disjunct since h = h is trivially true
  right
  rfl

-- Happens-before is well-founded (no infinite descending chains)
-- Derived from prehistories being finite
-- (Accessibility)

open List

-- Height of a prehistory: 1 + max height of immediate sub-prehistories
mutual
  private def heightList {P Event} :
      List (World P Event) → Nat
    | []      => 0
    | t :: ts => Nat.max (height t.2.2) (heightList ts)

  def height {P Event} : PreHistory P Event → Nat
    | mk l => heightList l + 1
end

-- Key list lemma: any member's subheight ≤ foldr max
private theorem heightList_ge_of_mem {P Event}
    {l : List (World P Event)} {t : World P Event}
    (hmem : t ∈ l) :
    height t.2.2 ≤ heightList l := by
  induction l with
  | nil =>
      cases hmem
  | cons x xs ih =>
      rw [heightList]
      rcases (List.mem_cons.mp hmem) with h | h
      · -- t = x
        rw [←h]
        apply Nat.le_max_left
      · -- t ∈ xs
        exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

-- The measure strictly decreases along ≺−
theorem height_lt_of_happensBefore {P Event}
    {h₁ h₂ : PreHistory P Event}
    (h : happensBefore (P := P) (Event := Event) h₁ h₂) :
    height h₁ < height h₂ := by
  rcases h with ⟨p,e,hin⟩
  cases h₂ with
  | mk l =>
      have hle : height h₁ ≤ heightList (P := P) (Event := Event) l :=
        heightList_ge_of_mem (l := l) (t := (p,e,h₁)) hin
      have : heightList (P := P) (Event := Event) l < heightList l + 1 :=
        Nat.lt_succ_self _
      -- combine and unfold `height`
      calc height h₁
        ≤ heightList (P := P) (Event := Event) l := hle
        _ < heightList l + 1 := this
        _ = height (mk l) := by rfl

/-- accessible predecessors have strictly smaller
times, reflected here by the height measure. -/
theorem height_lt_of_accessible {t' t : World P Event}
    (h : t' ≪ t) :
    height (World.time t') < height (World.time t) := by
  exact height_lt_of_happensBefore
    (P := P) (Event := Event)
    (happensBefore_of_accessible (P := P) (Event := Event) h)

theorem accessible_subset
    {t' t : World P Event}
    (h : t' ≪ t)
    (htrans : ∀ h', h' ≺− World.time t → h' ⊆ World.time t) :
    World.time t' ⊆ World.time t := by
  intro s hs
  have hBefore :=
    happensBefore_of_accessible (P := P) (Event := Event) h
  have hSubset := htrans (World.time t') hBefore
  exact hSubset s hs

theorem happensBefore_wellFounded : WellFounded (@happensBefore P Event) := by
  -- pull well-foundedness of `<` on Nat back along `height`
  have wfHeight :
      WellFounded (InvImage (fun a b : Nat => a < b) (height (P := P) (Event := Event))) :=
    InvImage.wf _ Nat.lt_wfRel.wf
  refine Subrelation.wf ?_ wfHeight
  intro a b hab
  -- exactly the strict height decrease we proved
  exact height_lt_of_happensBefore (P := P) (Event := Event) hab

-- ≺− is irreflexive and transitive
theorem happensBefore_irrefl (h : PreHistory P Event) : ¬(h ≺− h) := by
  intro h_self
  -- If h ≺− h, then height h < height h by our existing theorem
  have : height h < height h := height_lt_of_happensBefore h_self
  -- But this is impossible (n < n is false for any n)
  exact Nat.lt_irrefl (height h) this

/-- Paper: Proposition 3.4.5 (irreflexivity). accessibility is irreflexive. -/
theorem accessible_irrefl (t : World P Event) :
    ¬ t ≪ t := by
  intro hacc
  have : happensBefore (P := P) (Event := Event)
      (World.time t) (World.time t) :=
    happensBefore_of_accessible (P := P) (Event := Event) hacc
  exact happensBefore_irrefl (P := P) (Event := Event) (h := World.time t) this

-- Knowledge-of reflexivity ((p, H) knows of itself when appropriate)
-- Subset relation properties (basic set-theoretic facts)
theorem subset_refl (h : PreHistory P Event) : h ⊆ h := by
  intro t ht
  exact ht

-- Standard set theory

theorem happensBefore_trans {h₁ h₂ h₃ : PreHistory P Event} :
    (h₁ ≺− h₂) → (h₂ ⊆ h₃) → (h₁ ≺− h₃) := by
  intro h₁₂ h₂₃
  rcases h₁₂ with ⟨p, e, hmem⟩
  exact ⟨p, e, h₂₃ _ hmem⟩

/-- Membership of a tuple yields non-strict happens-before for its time component. -/
theorem happensBeforeEq_of_mem {p : P} {e : MaybeEvent Event}
    {h₁ h₂ : PreHistory P Event}
    (hmem : (p, e, h₁) ∈ h₂) :
    h₁ ⪯ h₂ := by
  exact Or.inl ⟨p, e, hmem⟩

theorem subset_of_happensBeforeEq {h₁ h₂ : PreHistory P Event}
    (htrans : ∀ ⦃h⦄, h ≺− h₂ → h ⊆ h₂) :
    (h₁ ⪯ h₂) → h₁ ⊆ h₂ := by
  intro h₁₂ t ht
  rcases h₁₂ with h₁₂ | h₁₂
  · have hsubset : h₁ ⊆ h₂ := htrans h₁₂
    exact hsubset t ht
  · subst h₁₂
    exact ht

-- Mutual non-strict happens-before forces equality of prehistories.

/-- Paper: Remark 2.2.7 (fixpoint characterisation). -/
def prehistory_fixpoint : PreHistory P Event ≃ List (World P Event) where
  toFun := fun h => match h with | mk l => l
  invFun := mk
  left_inv := by intro ⟨l⟩; rfl
  right_inv := by intro l; rfl

-- Utility Functions

-- Constructor helpers (smart constructors for common patterns)

instance [ToString Event] : ToString (MaybeEvent Event) where
  toString
  | MaybeEvent.some e => toString e
  | MaybeEvent.none => "†"
instance [ToString P] [ToString Event] : ToString (World P Event) where
  toString t := s!"({World.place t}, {World.event t}, <prehistory>)"
instance [ToString P] [ToString Event] : ToString (PreHistory P Event) where
  toString h := match h with | mk l => s!"PreHistory(size={l.length})"
section Examples
variable (P : Type u) (Event : Type v) [ToString P] [ToString Event]
end Examples
end PreHistory
