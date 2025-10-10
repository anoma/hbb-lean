import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Prehistory Structures

This file formalizes the prehistory structure from
Definition~\ref{defn.prehistory.structure} of the paper.
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

## References

* Definition~\ref{defn.prehistory.structure}
-/

variable {P Event : Type*}

-- Definition of maybe-events (Event†)
inductive MaybeEvent (Event : Type*) where
  | some : Event → MaybeEvent Event  -- Regular events
  | none : MaybeEvent Event          -- The non-event †

notation:max "†" => MaybeEvent.none

-- Prehistory inductive type following Definition~\ref{defn.prehistory.structure}
-- Note: We use List instead of Finset due to Lean's positivity restrictions.
-- The paper acknowledges this approach (pages 4-5), noting that while it introduces
-- redundancy (multiple lists can represent the same logical prehistory), all the
-- mathematical development works with this representation.
-- The paper's requirement that prehistories are finite (⊆fin) is automatically
-- satisfied because: (1) inductive types in Lean are well-founded by construction,
-- preventing infinite recursion, and (2) Lists have finite length.
inductive PreHistory (P Event : Type*) where
  | mk : List (P × MaybeEvent Event × PreHistory P Event) → PreHistory P Event

-- Event tuple type alias following Definition~\ref{defn.happens.at}
-- An event tuple is (p, E, H) ∈ P × Event† × PreHistory(P, Event)
-- Note: World must be defined after PreHistory due to dependency
abbrev World (P Event : Type*) := P × MaybeEvent Event × PreHistory P Event

namespace World

variable {P Event : Type*}

/-!
### Projection functions for event tuples

The revised specification refers to the *place*, *(maybe-)event*, and *time* of
an event tuple (Definition~\ref{defn.happens.at}).  We expose exactly those projections.
-/
@[simp] def place (t : World P Event) : P := t.1

@[simp] def event (t : World P Event) : MaybeEvent Event := t.2.1

@[simp] def time (t : World P Event) : PreHistory P Event := t.2.2

-- Constructor for event tuples (for convenience)
def mk (p : P) (e : MaybeEvent Event) (h : PreHistory P Event) : World P Event :=
  (p, e, h)

-- Simp lemmas for projections on constructed tuples
@[simp] lemma place_mk (p : P) (e : MaybeEvent Event) (h : PreHistory P Event) :
    place (mk p e h) = p := rfl

@[simp] lemma event_mk (p : P) (e : MaybeEvent Event) (h : PreHistory P Event) :
    event (mk p e h) = e := rfl

@[simp] lemma time_mk (p : P) (e : MaybeEvent Event) (h : PreHistory P Event) :
    time (mk p e h) = h := rfl

-- Simp lemmas for projections on tuple syntax
@[simp] lemma place_tuple (p : P) (e : MaybeEvent Event) (h : PreHistory P Event) :
    place (p, e, h) = p := rfl

@[simp] lemma event_tuple (p : P) (e : MaybeEvent Event) (h : PreHistory P Event) :
    event (p, e, h) = e := rfl

@[simp] lemma time_tuple (p : P) (e : MaybeEvent Event) (h : PreHistory P Event) :
    time (p, e, h) = h := rfl

end World

namespace PreHistory

-- Empty prehistory
def empty : PreHistory P Event := mk []

-- Singleton prehistory
def singleton (t : World P Event) : PreHistory P Event :=
  mk [t]

-- Construct from a list (allows duplicates)
def fromList (l : List (World P Event)) : PreHistory P Event :=
  mk l

-- Construct from a finite set (removes duplicates)
noncomputable def fromFinset (s : Finset (World P Event)) : PreHistory P Event :=
  mk s.toList

-- Membership relation for event tuples in prehistories
def mem (tuple : World P Event) (h : PreHistory P Event) : Prop :=
  match h with
  | mk l => tuple ∈ l

-- Definition \ref{defn.happens.at} phrases this as “H knows of the
-- event-tuple (p, E, H′)”, i.e. membership in the prehistory.

instance : Membership (World P Event) (PreHistory P Event) where
  mem := fun h t => PreHistory.mem t h

/-! ## Simp lemmas for PreHistory membership and operations -/

-- Basic membership lemma
@[simp] lemma mem_mk {e : World P Event} {l : List (World P Event)} :
  e ∈ PreHistory.mk l ↔ e ∈ l := by
  rfl

-- Empty prehistory membership
@[simp] lemma not_mem_empty {e : World P Event} :
  e ∉ PreHistory.empty := by
  simp [empty, mem_mk]

-- Singleton membership
@[simp] lemma mem_singleton {e e' : World P Event} :
  e ∈ PreHistory.singleton e' ↔ e = e' := by
  simp [singleton, mem_mk]

-- For filtered lists
@[simp] lemma mem_mk_filter
  {l : List (World P Event)} {p : World P Event → Bool} {e : World P Event} :
  e ∈ PreHistory.mk (l.filter p) ↔ e ∈ PreHistory.mk l ∧ p e := by
  simp [mem_mk, List.mem_filter]

-- Subset relation
def subset (h1 h2 : PreHistory P Event) : Prop :=
  ∀ t, t ∈ h1 → t ∈ h2

instance : HasSubset (PreHistory P Event) where
  Subset := PreHistory.subset

-- Subset in terms of membership
@[simp] lemma subset_iff {h1 h2 : PreHistory P Event} :
  h1 ⊆ h2 ↔ ∀ e, e ∈ h1 → e ∈ h2 := by
  rfl

end PreHistory

namespace World

/-!
### Accessibility relations on event tuples

Definition~\ref{defn.world}(\ref{item.world.accessible}) defines accessibility
between worlds as membership of the predecessor tuple in the enclosing history.
We expose that relation directly on event tuples so that worlds can be modelled
without introducing additional wrappers.
-/

/-- Strict accessibility: `t' ≪ t` when `t'` belongs to the time component of `t`. -/
def accessible (t' t : World P Event) : Prop :=
  t' ∈ World.time t

/-- Same-place accessibility (`≪^{-}` in Definition~\ref{defn.world}(4)). -/
def accessibleLe (t' t : World P Event) : Prop :=
  accessible t' t ∧ World.place t' = World.place t

@[simp] lemma accessible_iff (t' t : World P Event) :
    accessible t' t ↔ t' ∈ World.time t := Iff.rfl

@[simp] lemma accessibleLe_iff (t' t : World P Event) :
    accessibleLe t' t ↔
      accessible t' t ∧ World.place t' = World.place t := Iff.rfl

scoped[PreHistory] infix:50 " ≪ " => World.accessible
scoped[PreHistory] infix:50 " ≪⁻ " => World.accessibleLe

open scoped PreHistory

/-- Definition~\ref{defn.world}(4): in-place accessibility refines the strict
accessibility relation. -/
lemma accessible_of_accessibleLe {t' t : World P Event} :
    t' ≪⁻ t → t' ≪ t := fun h => h.1

/-- Definition~\ref{defn.world}(4): in-place accessibility forces equality of
places. -/
lemma place_eq_of_accessibleLe {t' t : World P Event} :
    t' ≪⁻ t → World.place t' = World.place t := fun h => h.2

/-- Definition~\ref{defn.world}(4): strict accessibility at the same place
produces an in-place accessible successor. -/
lemma accessibleLe_of_accessible {t' t : World P Event}
    (h : t' ≪ t) (hplace : World.place t' = World.place t) :
    t' ≪⁻ t := ⟨h, hplace⟩

end World

namespace PreHistory

/-!
### History-at helpers

Definition~\ref{defn.historyat} isolates the events owned by a participant.  We
phrase it directly in terms of event-tuples to avoid redundant interfaces.
-/

/-- Definition~\ref{defn.historyat}: the collection of event-tuples in `H` whose
place matches `p`. -/
def historyAt (H : PreHistory P Event) (p : P) : Set (World P Event) :=
  { t | t ∈ H ∧ World.place t = p }

@[simp] lemma mem_historyAt {H : PreHistory P Event} {p : P} {t : World P Event} :
    t ∈ historyAt (P := P) (Event := Event) H p ↔
      t ∈ H ∧ World.place t = p := Iff.rfl

/-- Definitions~\ref{defn.world}(4) and~\ref{defn.historyat} identify
in-place accessibility with membership of the history at the current
participant. -/
@[simp] lemma accessibleLe_iff_mem_historyAt {t' t : World P Event} :
    t' ≪⁻ t ↔
      t' ∈ historyAt (P := P) (Event := Event)
        (World.time t) (World.place t) := by
  simp [historyAt]

-- Happens-before relations as introduced alongside Definition~\ref{defn.Hin}

-- H' ≺− H: H' happens strictly before H
-- iff ∃p', E'.(p', E', H') ∈ H
def happensBefore (h1 h2 : PreHistory P Event) : Prop :=
  ∃ (p : P) (e : MaybeEvent Event),
    (p, e, h1) ∈ h2

-- H' ⪯ H: H' happens non-strictly before H
-- iff H' ≺− H ∨ H' = H
def happensBeforeEq (h1 h2 : PreHistory P Event) : Prop :=
  happensBefore h1 h2 ∨ h1 = h2

-- Notation for happens-before relations
infixl:50 " ≺− " => happensBefore
infixl:50 " ⪯ " => happensBeforeEq

-- Happens-before membership characterization
@[simp] lemma happensBefore_iff {h1 h2 : PreHistory P Event} :
  h1 ≺− h2 ↔ ∃ (p : P) (e : MaybeEvent Event), (p, e, h1) ∈ h2 := by
  rfl

/-- Combining Definitions~\ref{defn.world}(3) and~\ref{defn.Hin}:
strict accessibility forces the predecessor time to happen before the
successor. -/
lemma happensBefore_of_accessible {t' t : World P Event}
    (h : t' ≪ t) :
    happensBefore (World.time t') (World.time t) := by
  rcases t' with ⟨p, e, h'⟩
  exact ⟨p, e, by simpa [happensBefore] using h⟩

/-- Definition~\ref{defn.Hin}: the non-strict happens-before relation absorbs
the strict case obtained from accessibility. -/
lemma happensBeforeEq_of_accessible {t' t : World P Event}
    (h : t' ≪ t) :
    happensBeforeEq (World.time t') (World.time t) :=
  Or.inl (happensBefore_of_accessible (P := P) (Event := Event) h)

-- Basic Properties and Lemmas (from acceptance criteria)

-- Induction principle (structural induction for prehistories).
-- Paper Reference: Definition~\ref{defn.prehistory.structure}; the result is
-- implicit in the inductive definition.
-- "Let PreHistory(P, Event), the set of prehistories over P and Event,
-- be the least set closed under..."
theorem prehistory_induction (P_prop : PreHistory P Event → Prop)
    (h_empty : P_prop empty)
    (h_extend : ∀ (l : List (World P Event)), P_prop (mk l) →
      ∀ (t : World P Event), P_prop (mk (t :: l))) :
    ∀ (h : PreHistory P Event), P_prop h := by
  intro h
  cases h with
  | mk l =>
    induction l with
    | nil => exact h_empty
    | cons t l' ih => exact h_extend l' ih t

-- Empty prehistory properties (∅ is minimal element)
-- Paper Reference: Definition~\ref{defn.prehistory.structure} - direct consequence
-- "Any finite (possibly empty) set of place-event-prehistory tuples, is a prehistory"
theorem empty_minimal (h : PreHistory P Event) : empty ⊆ h := by
  intro t h_mem
  simp [empty] at h_mem

-- Definition of ⪯ from the paper
-- Paper Reference: see the discussion following Definition~\ref{defn.Hin}
-- "H′ ⪯ H means H′ ≺− H ∨ H′ = H"
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
-- Paper Reference: Not explicitly stated - derived from prehistories being finite
-- (Definition~\ref{defn.prehistory.structure})

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
private lemma heightList_ge_of_mem {P Event}
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
        exact le_trans (ih h) (Nat.le_max_right _ _)

-- The measure strictly decreases along ≺−
lemma height_lt_of_happensBefore {P Event}
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

/-- Lemma~\ref{lemm.world.time}: accessible predecessors have strictly smaller
times, reflected here by the height measure. -/
lemma height_lt_of_accessible {t' t : World P Event}
    (h : t' ≪ t) :
    height (World.time t') < height (World.time t) := by
  exact height_lt_of_happensBefore
    (P := P) (Event := Event)
    (happensBefore_of_accessible (P := P) (Event := Event) h)

/-- Definition~\ref{defn.world}(4): in-place accessibility also induces the
strict happens-before relation between times. -/
lemma happensBefore_of_accessibleLe {t' t : World P Event}
    (h : t' ≪⁻ t) :
    happensBefore (World.time t') (World.time t) :=
  happensBefore_of_accessible (P := P) (Event := Event)
    (World.accessible_of_accessibleLe (P := P) (Event := Event) h)

/-- Lemma~\ref{lemm.world.time}: the height measure decreases along
in-place accessibility. -/
lemma height_lt_of_accessibleLe {t' t : World P Event}
    (h : t' ≪⁻ t) :
    height (World.time t') < height (World.time t) :=
  height_lt_of_accessible (P := P) (Event := Event)
    (World.accessible_of_accessibleLe (P := P) (Event := Event) h)

/-- Lemma~\ref{lemm.world.time}: accessibility preserves membership of the
underlying time component provided the ambient time is transitive. -/
lemma accessible_subset
    {t' t : World P Event}
    (h : t' ≪ t)
    (htrans : ∀ h', h' ≺− World.time t → h' ⊆ World.time t) :
    World.time t' ⊆ World.time t := by
  intro s hs
  have hBefore :=
    happensBefore_of_accessible (P := P) (Event := Event) h
  have hSubset := htrans (World.time t') hBefore
  exact hSubset s hs

/-- The height of the empty prehistory is the base height `1`. -/
@[simp] lemma height_empty :
    height (P := P) (Event := Event) PreHistory.empty = 1 := by
  simp [PreHistory.empty, height, heightList]

/-- The height of a singleton prehistory is the successor of the embedded time. -/
lemma height_singleton (t : World P Event) :
    height (P := P) (Event := Event) (PreHistory.singleton t) =
      Nat.succ (height (P := P) (Event := Event) t.2.2) := by
  have hzero : 0 ≤ height (P := P) (Event := Event) t.2.2 := Nat.zero_le _
  have hlist : heightList (P := P) (Event := Event) [t] =
      Nat.max (height (P := P) (Event := Event) t.2.2) 0 := by
    simp [heightList]
  calc
    height (P := P) (Event := Event) (PreHistory.singleton t)
        = heightList (P := P) (Event := Event) [t] + 1 := by
            simp [PreHistory.singleton, height]
    _ = Nat.max (height (P := P) (Event := Event) t.2.2) 0 + 1 := by
            simp [hlist]
    _ = height (P := P) (Event := Event) t.2.2 + 1 := by
            simp
    _ = Nat.succ (height (P := P) (Event := Event) t.2.2) := by
            simp [Nat.succ_eq_add_one]

/-- Prehistory height is monotone with respect to the subset relation. -/
lemma height_le_of_subset {h₁ h₂ : PreHistory P Event}
    (hsubset : h₁ ⊆ h₂) :
    height (P := P) (Event := Event) h₁ ≤
      height (P := P) (Event := Event) h₂ := by
  classical
  cases h₁ with
  | mk l₁ =>
      cases h₂ with
      | mk l₂ =>
          have hsubset_list : ∀ t, t ∈ l₁ → t ∈ l₂ := by
            intro t ht
            have ht' : t ∈ PreHistory.mk l₁ := by
              simpa [mem_mk] using ht
            have : t ∈ PreHistory.mk l₂ := hsubset t ht'
            simpa [mem_mk] using this
          have heightList_le :
              heightList (P := P) (Event := Event) l₁ ≤
                heightList (P := P) (Event := Event) l₂ := by
            have aux : ∀ {l : List (World P Event)},
                (∀ t ∈ l, t ∈ l₂) →
                  heightList (P := P) (Event := Event) l ≤
                    heightList (P := P) (Event := Event) l₂ := by
              intro l hsub
              induction l with
              | nil =>
                  simp [heightList]
              | cons t ts ih =>
                  have ht_mem : t ∈ l₂ := hsub t (by simp)
                  have ht_le :
                      height (P := P) (Event := Event) t.2.2 ≤
                        heightList (P := P) (Event := Event) l₂ :=
                    heightList_ge_of_mem (l := l₂) (t := t) ht_mem
                  have hts_le :
                      heightList (P := P) (Event := Event) ts ≤
                        heightList (P := P) (Event := Event) l₂ :=
                    ih (fun s hs => hsub s (by simp [hs]))
                  simpa [heightList] using (max_le_iff).2 ⟨ht_le, hts_le⟩
            exact aux hsubset_list
          simpa [height] using add_le_add_right heightList_le 1

-- Final well-foundedness proof using onFun + mono
theorem happensBefore_wellFounded : WellFounded (@happensBefore P Event) := by
  -- well-foundedness of `<` on Nat
  have wfNat : WellFounded (fun a b : Nat => a < b) := Nat.lt_wfRel.wf
  -- pull back along `height`
  have wfOnHeight :
      WellFounded (Function.onFun (fun a b : Nat => a < b) (height (P := P) (Event := Event))) :=
    WellFounded.onFun wfNat
  -- show ≺− ⊆ onFun(<, height)
  refine WellFounded.mono wfOnHeight ?mono
  intro a b hab
  -- exactly the strict height decrease we proved
  simpa [Function.onFun] using
    (height_lt_of_happensBefore (P := P) (Event := Event) hab)

-- ≺− is irreflexive and transitive
-- Paper Reference: see the discussion following Definition~\ref{defn.Hin}
theorem happensBefore_irrefl (h : PreHistory P Event) : ¬(h ≺− h) := by
  intro h_self
  -- If h ≺− h, then height h < height h by our existing theorem
  have : height h < height h := height_lt_of_happensBefore h_self
  -- But this is impossible (n < n is false for any n)
  exact Nat.lt_irrefl (height h) this

/-- Proposition~\ref{prop.accessible.trans}: accessibility is irreflexive. -/
lemma accessible_irrefl (t : World P Event) :
    ¬ t ≪ t := by
  intro hacc
  have : happensBefore (P := P) (Event := Event)
      (World.time t) (World.time t) :=
    happensBefore_of_accessible (P := P) (Event := Event) hacc
  exact happensBefore_irrefl (P := P) (Event := Event) (h := World.time t) this

-- Knowledge-of reflexivity ((p, H) knows of itself when appropriate)
-- Paper Reference: Definition~\ref{defn.known.to}, which supplies the self-knowledge disjunct.
-- Subset relation properties (basic set-theoretic facts)
theorem subset_refl (h : PreHistory P Event) : h ⊆ h := by
  intro t ht
  exact ht

-- Paper Reference: Standard set theory - used throughout implicitly
theorem subset_trans (h1 h2 h3 : PreHistory P Event) :
    h1 ⊆ h2 → h2 ⊆ h3 → h1 ⊆ h3 := by
  intro h12 h23 t ht1
  apply h23
  apply h12
  exact ht1

/-- A prehistory can only be contained in the empty prehistory if it is empty. -/
@[simp] lemma subset_empty_iff (h : PreHistory P Event) :
    h ⊆ empty ↔ h = empty := by
  constructor
  · intro hsubset
    cases h with
    | mk l =>
        classical
        cases l with
        | nil => rfl
        | cons t l' =>
            have : False :=
              (not_mem_empty (P := P) (Event := Event) (e := t))
                (hsubset t (by simp [mem_mk]))
            exact False.elim this
  · intro h_eq
    subst h_eq
    exact subset_refl _

/-- Mutual inclusion of prehistories yields equivalent membership predicates. -/
lemma subset_antisymm {h₁ h₂ : PreHistory P Event} :
    h₁ ⊆ h₂ → h₂ ⊆ h₁ → ∀ t, t ∈ h₁ ↔ t ∈ h₂ := by
  intro h₁₂ h₂₁ t
  constructor
  · exact h₁₂ t
  · exact h₂₁ t

/-- Strict happens-before composes along inclusions of the target prehistory. -/
theorem happensBefore_trans {h₁ h₂ h₃ : PreHistory P Event} :
    (h₁ ≺− h₂) → (h₂ ⊆ h₃) → (h₁ ≺− h₃) := by
  intro h₁₂ h₂₃
  rcases h₁₂ with ⟨p, e, hmem⟩
  exact ⟨p, e, h₂₃ _ hmem⟩

/-- Membership of a tuple yields non-strict happens-before for its time component. -/
lemma happensBeforeEq_of_mem {p : P} {e : MaybeEvent Event}
    {h₁ h₂ : PreHistory P Event}
    (hmem : (p, e, h₁) ∈ h₂) :
    h₁ ⪯ h₂ := by
  exact Or.inl ⟨p, e, hmem⟩

/-- Strict happens-before of the empty prehistory is impossible. -/
@[simp] lemma happensBefore_empty_iff (h : PreHistory P Event) :
    h ≺− empty ↔ False :=
  by
    constructor
    · intro hbefore
      rcases hbefore with ⟨p, e, hmem⟩
      have : False := by simp [empty, mem_mk] at hmem
      exact this
    · intro hfalse
      cases hfalse

-- Non-strict happens-before composes provided every predecessor of the target
-- prehistory lies inside it.
theorem happensBeforeEq_trans {h₁ h₂ h₃ : PreHistory P Event}
    (htrans : ∀ ⦃h⦄, h ≺− h₃ → h ⊆ h₃) :
    (h₁ ⪯ h₂) → (h₂ ⪯ h₃) → (h₁ ⪯ h₃) := by
  intro h₁₂ h₂₃
  rcases h₁₂ with h₁₂ | h₁₂
  · rcases h₂₃ with h₂₃ | h₂₃
    · have hsubset : h₂ ⊆ h₃ := htrans h₂₃
      have : h₁ ≺− h₃ :=
        happensBefore_trans (P := P) (Event := Event) h₁₂ hsubset
      exact Or.inl this
    · subst h₂₃
      exact Or.inl h₁₂
  · subst h₁₂
    rcases h₂₃ with h₂₃ | h₂₃
    · exact Or.inl h₂₃
    · subst h₂₃
      exact Or.inr rfl

-- Non-strict happens-before exposes the underlying subset relation when the
-- target prehistory absorbs its predecessors.
lemma subset_of_happensBeforeEq {h₁ h₂ : PreHistory P Event}
    (htrans : ∀ ⦃h⦄, h ≺− h₂ → h ⊆ h₂) :
    (h₁ ⪯ h₂) → h₁ ⊆ h₂ := by
  intro h₁₂ t ht
  rcases h₁₂ with h₁₂ | h₁₂
  · have hsubset : h₁ ⊆ h₂ := htrans h₁₂
    exact hsubset t ht
  · subst h₁₂
    exact ht

-- Mutual non-strict happens-before forces equality of prehistories.
theorem happensBeforeEq_antisymm {h₁ h₂ : PreHistory P Event} :
    (h₁ ⪯ h₂) → (h₂ ⪯ h₁) → h₁ = h₂ :=
  by
    intro h₁₂ h₂₁
    rcases h₁₂ with h₁₂ | h₁₂
    · rcases h₂₁ with h₂₁ | h₂₁
      · have : False :=
          Nat.lt_asymm
            (height_lt_of_happensBefore (P := P) (Event := Event) h₁₂)
            (height_lt_of_happensBefore (P := P) (Event := Event) h₂₁)
        cases this
      · have hself : h₁ ≺− h₁ := by simpa [h₂₁] using h₁₂
        cases (happensBefore_irrefl (P := P) (Event := Event) h₁) hself
    · rcases h₂₁ with h₂₁ | h₂₁
      · have hself : h₂ ≺− h₂ := by simpa [h₁₂] using h₂₁
        cases (happensBefore_irrefl (P := P) (Event := Event) h₂) hself
      · exact h₁₂

/-- Describes when the empty prehistory happens non-strictly before another. -/
@[simp] lemma empty_happensBeforeEq (h : PreHistory P Event) :
    empty ⪯ h ↔
      (∃ (p : P) (e : MaybeEvent Event), (p, e, empty) ∈ h) ∨ empty = h := by
  constructor <;> intro hrel
  · simpa [happensBeforeEq, happensBefore_iff]
  · simpa [happensBeforeEq, happensBefore_iff]

/-- Strict happens-before is monotone in the right argument. -/
lemma happensBefore_mono_right
    {h₁ h₂ h₃ : PreHistory P Event}
    (h_before : h₁ ≺− h₂) (h_subset : h₂ ⊆ h₃) :
    h₁ ≺− h₃ := by
  rcases h_before with ⟨p, e, hmem⟩
  exact ⟨p, e, h_subset _ hmem⟩

/-- Non-strict happens-before decreases the height measure. -/
lemma happensBeforeEq_height_le
    {h₁ h₂ : PreHistory P Event}
    (h_before : h₁ ⪯ h₂) :
    height (P := P) (Event := Event) h₁ ≤ height h₂ := by
  rcases h_before with h_before | h_eq
  · have h_lt := height_lt_of_happensBefore (P := P) (Event := Event) h_before
    exact (Nat.lt_succ_iff).1 (Nat.lt_succ_of_lt h_lt)
  · subst h_eq
    exact le_rfl

/-- No prehistory happens strictly before the empty prehistory. -/
lemma not_happensBefore_empty (h : PreHistory P Event) :
    ¬ h ≺− empty := by
  intro h_before
  rcases h_before with ⟨p, e, hmem⟩
  simp [empty, mem_mk] at hmem

/-- Non-strict happens-before with `∅` forces equality. -/
lemma happensBeforeEq_empty_iff (h : PreHistory P Event) :
    h ⪯ empty ↔ h = empty := by
  constructor
  · intro h_before
    have h_cases :=
      (happensBeforeEq_iff (P := P) (Event := Event) h empty).1 h_before
    cases h_cases with
    | inl h_strict =>
        have : False :=
          (not_happensBefore_empty (P := P) (Event := Event) (h := h)) h_strict
        cases this
    | inr h_eq => exact h_eq
  · intro h_eq
    subst h_eq
    exact happensBeforeEq_refl (P := P) (Event := Event) empty

/-- Equality implies non-strict happens-before. -/
lemma happensBeforeEq_of_eq {h₁ h₂ : PreHistory P Event}
    (h_eq : h₁ = h₂) :
    h₁ ⪯ h₂ := by
  subst h_eq
  exact happensBeforeEq_refl (P := P) (Event := Event) _

-- Fixpoint characterization (Remark 2.2.7)
-- Paper Reference: Remark 2.2.7 - explicitly stated
-- "PreHistory(P, Event) can be characterised as the least set such that
-- PreHistory(P, Event) = Pfin(P × Event† × PreHistory(P, Event))"
-- In Lean, this is an equivalence between PreHistory and List of Worlds
def prehistory_fixpoint : PreHistory P Event ≃ List (World P Event) where
  toFun := fun h => match h with | mk l => l
  invFun := mk
  left_inv := by intro ⟨l⟩; rfl
  right_inv := by intro l; rfl

-- Utility Functions

-- Constructor helpers (smart constructors for common patterns)
def from_list (tuples : List (World P Event)) : PreHistory P Event :=
  fromList tuples

def insert (tuple : World P Event) (h : PreHistory P Event) : PreHistory P Event :=
  match h with
  | mk l => mk (tuple :: l)

-- Pretty printing (string representation for debugging)
instance [ToString Event] : ToString (MaybeEvent Event) where
  toString
  | MaybeEvent.some e => toString e
  | MaybeEvent.none => "†"

instance [ToString P] [ToString Event] : ToString (World P Event) where
  toString t := s!"({World.place t}, {World.event t}, <prehistory>)"

instance [ToString P] [ToString Event] : ToString (PreHistory P Event) where
  toString h := match h with | mk l => s!"PreHistory(size={l.length})"

-- Examples from the paper

section Examples

variable (P : Type*) (Event : Type*) [ToString P] [ToString Event]

-- Example 1: Empty prehistory
-- Represents: ∅
def example_empty : PreHistory P Event := empty

-- Example 2: Single participant sequential events
-- This builds the prehistory for p executing "hello" then "world"
-- Paper notation (similar to Example 2.2.5):
--   H₀ = ∅
--   H₁ = {(p, †, ∅)}                      -- p initializes
--   H₂ = {(p, hello, H₁)}                 -- p says hello after initializing
--   H₃ = {(p, world, H₂)}                 -- p says world after hello
-- The final prehistory H₃ represents the complete sequential execution
def example_sequential (p : P) (hello world : Event) : PreHistory P Event :=
  let h0 := empty                                  -- H₀ = ∅
  let t0 := World.mk p MaybeEvent.none h0    -- (p, †, ∅)
  let h1 := singleton t0                          -- H₁ = {(p, †, ∅)}
  let t1 := World.mk p (MaybeEvent.some hello) h1  -- (p, hello, H₁)
  let h2 := singleton t1                          -- H₂ = {(p, hello, H₁)}
  let t2 := World.mk p (MaybeEvent.some world) h2  -- (p, world, H₂)
  singleton t2                                     -- H₃ = {(p, world, H₂)}

-- Example 3: Two participant message passing
-- This represents p sending message m to q (similar to broadcast scenarios)
-- Paper notation matching the Section 2.2 message-passing discussion:
--   H₀ = ∅
--   H₁ = {(p, †, ∅), (q, †, ∅)}          -- both p and q initialize
--   H₂ = H₁ ∪ {(p, send(m), H₁)}         -- p sends message m
--   H₃ = H₂ ∪ {(q, recv(m), H₂)}         -- q receives message m
-- This shows the causal dependency: q's receive depends on p's send
-- Note: The List representation means we're building the full history,
-- not just the final event set
def example_message_passing (p q : P) (m : Event) : PreHistory P Event :=
  let h0 := empty                                  -- H₀ = ∅
  let tp_init := World.mk p MaybeEvent.none h0    -- (p, †, ∅)
  let tq_init := World.mk q MaybeEvent.none h0    -- (q, †, ∅)
  let h1 := mk [tp_init, tq_init]                 -- H₁ = both initialize
  let tp_send := World.mk p (MaybeEvent.some m) h1  -- (p, m, H₁)
  let h2 := mk [tp_init, tq_init, tp_send]        -- H₂ = H₁ ∪ {p sends}
  let tq_recv := World.mk q (MaybeEvent.some m) h2  -- (q, m, H₂)
  mk [tp_init, tq_init, tp_send, tq_recv]         -- H₃ = H₂ ∪ {q receives}

end Examples

end PreHistory
