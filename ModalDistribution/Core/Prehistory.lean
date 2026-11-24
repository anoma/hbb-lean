import ModalDistribution.Core.Set
import ModalDistribution.Core.Equiv

/-!
# Prehistories

Prehistories (paper Section 2.2) are finite sets of event-tuples
`(p, E, H)`: participant `p` saw maybe-event `E` with prehistory `H` in its
past. This file defines them, the element-of relation `≺−` on them
(Section 2.3) and the accessibility relation `≪` on event-tuples
(Section 3.4).

## Main definitions

* `MaybeEvent Event`: `Event† = Event ∪ {†}`.
* `PreHistory P Event`: prehistories, as an inductive type of lists.
* `World P Event`: event-tuples `(p, E, H)`, with projections `place`,
  `event` and `time`.
* `PreHistory.HappensBefore` (`≺−`) and `PreHistory.HappensBeforeEq` (`⪯`).
* `World.Accessible` (`≪`) and `World.AccessibleLe` (`≪⁻`).

## Main results

* `PreHistory.happensBefore_wellFounded`: `≺−` is well-founded.
* `PreHistory.accessible_irrefl`: `≪` is irreflexive.
-/

universe u v

variable {P : Type u} {Event : Type v}

/-- Paper: Notation 2.2.2 (maybe-sets). -/
inductive MaybeEvent (Event : Type v) where
  /-- A genuine event. -/
  | some : Event → MaybeEvent Event
  /-- The non-event `†`. -/
  | none : MaybeEvent Event

notation:max "†" => MaybeEvent.none

/-- Paper: Definition 2.2.4 (Prehistories).

Representation note: this is list-backed, so it realises the paper's
inductive-datatype presentation (its Section 2.1) rather than the quotiented
set-theoretic definition — distinct terms (reorderings, duplicates) can denote
the same intended prehistory. All results are stated through membership, never
through equality of prehistories, so the redundancy is harmless, as the paper
itself notes for the datatype view. Lists are finite, so every prehistory is
finite as the paper requires. -/
inductive PreHistory (P : Type u) (Event : Type v) where
  | mk : List (P × MaybeEvent Event × PreHistory P Event) → PreHistory P Event

/-- Paper: Definition 2.2.6(1) (event-tuples). -/
abbrev World (P : Type u) (Event : Type v) := P × MaybeEvent Event × PreHistory P Event

namespace World

variable {P : Type u} {Event : Type v}

/-- Paper: Definition 2.2.6(2). The participant of an event-tuple. -/
@[simp] def place (t : World P Event) : P := t.1

/-- Paper: Definition 2.2.6(2). The maybe-event of an event-tuple. -/
@[simp] def event (t : World P Event) : MaybeEvent Event := t.2.1

/-- Paper: Definition 2.2.6(2). The prehistory of an event-tuple. -/
@[simp] def time (t : World P Event) : PreHistory P Event := t.2.2

end World

namespace PreHistory

/-- The empty prehistory. -/
def empty : PreHistory P Event := mk []

/-- Paper: Definition 2.2.6(5) (the "knows of" relation). `H` knows of the
event-tuple `t` when `t` is a member of `H`. -/
def Mem (tuple : World P Event) (h : PreHistory P Event) : Prop :=
  match h with
  | mk l => tuple ∈ l

instance : Membership (World P Event) (PreHistory P Event) where
  mem := fun h t => PreHistory.Mem t h

/-- Inclusion of prehistories: every member of `h1` is a member of `h2`. -/
def Subset (h1 h2 : PreHistory P Event) : Prop :=
  ∀ t, t ∈ h1 → t ∈ h2

instance : HasSubset (PreHistory P Event) where
  Subset := PreHistory.Subset

/-- Inclusion of prehistories is reflexive. -/
theorem subset_refl (h : PreHistory P Event) : h ⊆ h := fun _ ht => ht

/-- Paper: Remark 2.2.7 (fixpoint characterisation). -/
def prehistoryFixpoint : PreHistory P Event ≃ List (World P Event) where
  toFun := fun h => match h with | mk l => l
  invFun := mk
  left_inv := by intro ⟨l⟩; rfl
  right_inv := by intro l; rfl

/-! ## The element-of relation (paper Section 2.3) -/

/-- Paper: Definition 2.3.1(1) (element-of, ≺−). `h1 ≺− h2` when `h1` is the
prehistory of a member of `h2`. -/
def HappensBefore (h1 h2 : PreHistory P Event) : Prop :=
  ∃ (p : P) (e : MaybeEvent Event),
    (p, e, h1) ∈ h2

/-- Paper: Definition 2.3.1(2) (non-strict element-of, ⪯). -/
def HappensBeforeEq (h1 h2 : PreHistory P Event) : Prop :=
  HappensBefore h1 h2 ∨ h1 = h2

infixl:50 " ≺− " => HappensBefore
infixl:50 " ⪯ " => HappensBeforeEq

@[simp] theorem happensBeforeEq_iff (h1 h2 : PreHistory P Event) :
    h1 ⪯ h2 ↔ h1 ≺− h2 ∨ h1 = h2 := Iff.rfl

theorem happensBeforeEq_refl (h : PreHistory P Event) : h ⪯ h := Or.inr rfl

/-- The prehistory of a member weakly precedes the prehistory containing it. -/
theorem happensBeforeEq_of_mem {p : P} {e : MaybeEvent Event}
    {h₁ h₂ : PreHistory P Event}
    (hmem : (p, e, h₁) ∈ h₂) :
    h₁ ⪯ h₂ := Or.inl ⟨p, e, hmem⟩

/-- A prehistory weakly before a transitive prehistory is included in it. -/
theorem subset_of_happensBeforeEq {h₁ h₂ : PreHistory P Event}
    (htrans : ∀ ⦃h⦄, h ≺− h₂ → h ⊆ h₂) :
    (h₁ ⪯ h₂) → h₁ ⊆ h₂
  | .inl hBefore => htrans hBefore
  | .inr rfl => subset_refl _

/-! ### Well-foundedness of `≺−` -/

mutual
  /-- The largest height of the prehistories of a list of event-tuples. -/
  private def heightList {P Event} :
      List (World P Event) → Nat
    | []      => 0
    | t :: ts => Nat.max (height t.2.2) (heightList ts)

  /-- The nesting depth of a prehistory; it strictly decreases along `≺−`. -/
  def height {P Event} : PreHistory P Event → Nat
    | mk l => heightList l + 1
end

private theorem heightList_ge_of_mem {P Event}
    {l : List (World P Event)} {t : World P Event}
    (hmem : t ∈ l) :
    height t.2.2 ≤ heightList l := by
  induction l with
  | nil => cases hmem
  | cons x xs ih =>
      rw [heightList]
      rcases List.mem_cons.mp hmem with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- `≺−` strictly decreases `height`. -/
theorem height_lt_of_happensBefore {P Event}
    {h₁ h₂ : PreHistory P Event}
    (h : h₁ ≺− h₂) :
    height h₁ < height h₂ := by
  obtain ⟨p, e, hin⟩ := h
  cases h₂ with
  | mk l => exact Nat.lt_succ_of_le (heightList_ge_of_mem (t := (p, e, h₁)) hin)

/-- `≺−` is well-founded: prehistories are finite. -/
theorem happensBefore_wellFounded : WellFounded (@HappensBefore P Event) :=
  Subrelation.wf height_lt_of_happensBefore (InvImage.wf height Nat.lt_wfRel.wf)

theorem happensBefore_irrefl (h : PreHistory P Event) : ¬(h ≺− h) := fun h_self =>
  Nat.lt_irrefl _ (height_lt_of_happensBefore h_self)

end PreHistory

/-! ## Accessibility (paper Section 3.4) -/

namespace World

/-- Paper: Definition 3.4.2(3) (accessibility, ≪). `t' ≪ t` when `t'` is a
member of the time of `t`. -/
def Accessible (t' t : World P Event) : Prop :=
  t' ∈ World.time t

/-- Paper: Definition 3.4.2(4) (in-place accessibility, ≪⁻). `t' ≪⁻ t` when
`t' ≪ t` at the same place. -/
def AccessibleLe (t' t : World P Event) : Prop :=
  Accessible t' t ∧ World.place t' = World.place t

end World

namespace PreHistory

scoped infix:50 " ≪ " => World.Accessible
scoped infix:50 " ≪⁻ " => World.AccessibleLe

/-- Paper: Lemma 3.4.3. If `t' ≪ t` then the time of `t'` is element-of the
time of `t`. -/
theorem happensBefore_of_accessible {t' t : World P Event}
    (h : t' ≪ t) :
    HappensBefore (World.time t') (World.time t) :=
  ⟨t'.1, t'.2.1, h⟩

/-- `happensBefore_of_accessible`, weakened to `⪯`. -/
theorem happensBeforeEq_of_accessible {t' t : World P Event}
    (h : t' ≪ t) :
    HappensBeforeEq (World.time t') (World.time t) :=
  Or.inl (happensBefore_of_accessible h)

/-- Paper: Proposition 3.4.5 (irreflexivity). Accessibility is irreflexive: `¬ t ≪ t`. -/
theorem accessible_irrefl (t : World P Event) :
    ¬ t ≪ t := fun hacc =>
  happensBefore_irrefl _ (happensBefore_of_accessible hacc)

/-- Paper: Definition 3.4.7 (H at p). The event-tuples of `H` at `p`. -/
def historyAt (H : PreHistory P Event) (p : P) : Set (World P Event) :=
  { t | t ∈ H ∧ World.place t = p }

end PreHistory
