import ModalDistribution.Core.Prehistory
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic

open scoped PreHistory

/-!
# History Structures

This file formalizes the History structure from Definition 2.3.5 of the HBB paper.
A history is a hereditarily transitive element of PreHistory(P, Event).

## Main definitions

* `History P Event`: Type for history structures with hereditary transitivity
* `TransitiveSubset`: Transitive subset relation (⊆trn) from Definition 2.3.13
* Local view operations and sequentiality properties

## Main theorems

* Hereditary transitivity proofs
* Basic properties of history structures
* Local view properties and sequentiality lemmas

## References

* Definition 2.3.5 in "Logical Analysis of Heterogeneous Broadcasts"
* Definition 2.3.13 (Transitive subset relation)
* Definition 3.2.7 (Local view)
* Definition 3.3.2 (Sequential participant)
-/

variable {P Event : Type*}

/-- Definition 2.3.2: A prehistory is transitive when `H′ ≺− H` implies `H′ ⊆ H`. -/
def isTransitive (h : PreHistory P Event) : Prop :=
  ∀ h' : PreHistory P Event, h' ≺− h → h' ⊆ h

/-- Definition 2.3.5 (auxiliary): hereditary transitivity demands every
    predecessor be transitive and itself satisfy hereditary transitivity. We
    construct this predicate by well-founded recursion on ≺−. -/
noncomputable def isHereditarilyTransitive : PreHistory P Event → Prop :=
  PreHistory.happensBefore_wellFounded.fix
    (fun h rec =>
      isTransitive h ∧
      ∀ h' : PreHistory P Event,
        ∀ h_before : h' ≺− h, rec h' h_before)

lemma isHereditarilyTransitive_unfold (h : PreHistory P Event) :
  isHereditarilyTransitive h ↔
    isTransitive h ∧
    ∀ h' : PreHistory P Event,
      ∀ _ : h' ≺− h, isHereditarilyTransitive h' := by
  classical
  unfold isHereditarilyTransitive
  simpa using
    (PreHistory.happensBefore_wellFounded.fix_eq
      (fun h rec =>
        isTransitive h ∧
        ∀ h' : PreHistory P Event,
          ∀ h_before : h' ≺− h, rec h' h_before)
      h)

lemma isHereditarilyTransitive.trans
    {h : PreHistory P Event} :
    isHereditarilyTransitive h → isTransitive h := by
  intro h_hered
  have := (isHereditarilyTransitive_unfold h).mp h_hered
  exact this.1

lemma isHereditarilyTransitive.desc
    {h h' : PreHistory P Event}
    (hh : isHereditarilyTransitive h)
    (hb : h' ≺− h) :
    isHereditarilyTransitive h' := by
  classical
  have := (isHereditarilyTransitive_unfold h).mp hh
  exact this.2 h' hb

/-- Definition 2.3.5 (2025-09-17 draft): histories are the prehistories that are
    hereditarily transitive. The transitivity of the history follows from the
    hereditary property itself. -/
structure History (P Event : Type*) where
  val : PreHistory P Event
  hered : isHereditarilyTransitive val

namespace History

/-- Coerce a history to its underlying prehistory. -/
instance : Coe (History P Event) (PreHistory P Event) := ⟨History.val⟩

/-- Extract the underlying prehistory from a history -/
def toPreHistory (h : History P Event) : PreHistory P Event := h.val

/-- Extensionality for histories: equality follows from equality of underlying
    prehistories. -/
@[ext] theorem ext {h₁ h₂ : History P Event}
    (hval : h₁.val = h₂.val) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hval
  rfl

/-- A history is transitive -/
theorem transitive (h : History P Event) : isTransitive h.val :=
  (isHereditarilyTransitive.trans (P := P) (Event := Event) h.hered)

/-- A history is hereditarily transitive -/
theorem hereditarilyTransitive (h : History P Event) : isHereditarilyTransitive h.val :=
  h.hered

/-- Helper: data carried by the hereditary property for a specific predecessor. -/
lemma predecessor_data {H : History P Event} {h' : PreHistory P Event}
    (h_before : h' ≺− H.val) :
    isTransitive h' ∧ isHereditarilyTransitive h' := by
  have h_hered := History.hereditarilyTransitive H
  have h_desc := isHereditarilyTransitive.desc
      (P := P) (Event := Event) (h := H.val) (h' := h') h_hered h_before
  exact ⟨isHereditarilyTransitive.trans h_desc, h_desc⟩

/-- Package a predecessor of a history as a history. -/
def predecessorHistory {H : History P Event} {h' : PreHistory P Event}
    (h_before : h' ≺− H.val) : History P Event :=
  { val := h'
    hered := (predecessor_data (H := H) (h_before := h_before)).2 }

/-- A predecessor packaged as a history embeds into the ambient history. -/
lemma predecessorHistory_subset {H : History P Event}
    {h' : PreHistory P Event} (h_before : h' ≺− H.val) :
    (predecessorHistory (H := H) h_before).val ⊆ H.val := by
  exact History.transitive H h' h_before

/-- Main characterization theorem from Definition 2.3.2:
    if `H` is a history, then it is transitive, and every immediate predecessor
    is itself a history. -/
theorem history_characterization (h : History P Event) :
  isTransitive h.val ∧
    ∀ {h' : PreHistory P Event}, h' ≺− h.val → ∃ H' : History P Event, H'.val = h' := by
  constructor
  · exact History.transitive h
  · intro h' h_before
    exact ⟨predecessorHistory (H := h) h_before, rfl⟩

/-- The empty prehistory forms a history (no predecessors). -/
def emptyHistory (P Event : Type*) : History P Event :=
{
  val := PreHistory.empty,
  hered := by
    classical
    refine (isHereditarilyTransitive_unfold (P := P) (Event := Event) PreHistory.empty).mpr ?_
    constructor
    · intro h' hbefore
      rcases hbefore with ⟨p, e, mem⟩
      simp [PreHistory.empty, PreHistory.mem_mk] at mem
    · intro h' hbefore
      rcases hbefore with ⟨p, e, mem⟩
      simp [PreHistory.empty, PreHistory.mem_mk] at mem
}

end History

section Examples

/-- The raw prehistory for minimal history -/
def minimalHistory_val : PreHistory Unit Unit :=
  PreHistory.mk [((), MaybeEvent.none, PreHistory.empty)]

/-- minimalHistory_val is transitive -/
lemma minimalHistory_transitive : isTransitive minimalHistory_val := by
  intro h' hbefore
  rcases hbefore with ⟨p, e, hmem⟩
  simp only [minimalHistory_val, PreHistory.mem_mk, List.mem_singleton] at hmem
  -- hmem is now: (p, e, h') = ((), MaybeEvent.none, PreHistory.empty)
  have : h' = PreHistory.empty := by simp only [Prod.ext_iff] at hmem; exact hmem.2.2
  rw [this]
  exact PreHistory.empty_minimal minimalHistory_val

/-- minimalHistory_val is hereditarily transitive -/
lemma minimalHistory_hered : isHereditarilyTransitive minimalHistory_val := by
  classical
  refine (isHereditarilyTransitive_unfold (P := Unit) (Event := Unit) minimalHistory_val).mpr ?_
  constructor
  · exact minimalHistory_transitive
  · intro h' hbefore
    rcases hbefore with ⟨p, e, hmem⟩
    simp only [minimalHistory_val, PreHistory.mem_mk, List.mem_singleton] at hmem
    have : h' = PreHistory.empty := by
      simp only [Prod.ext_iff] at hmem
      exact hmem.2.2
    subst this
    exact History.hereditarilyTransitive (History.emptyHistory Unit Unit)

/-- Example: A minimal history with one participant -/
def minimalHistory : History Unit Unit :=
  { val := minimalHistory_val
    hered := minimalHistory_hered }

/-- A history that extends minimalHistory with a new event but where
    minimalHistory doesn't happen-before it -/
def extendedHistory_val : PreHistory Unit Unit :=
  PreHistory.mk [((), MaybeEvent.some (), PreHistory.empty),
                 ((), MaybeEvent.none, PreHistory.empty)]

/-- extendedHistory_val is transitive -/
lemma extendedHistory_transitive : isTransitive extendedHistory_val := by
  intro h' hbefore
  rcases hbefore with ⟨p, e, hmem⟩
  simp only [extendedHistory_val, PreHistory.mem_mk, List.mem_cons] at hmem
  cases hmem with
  | inl h_eq =>
    -- First element: ((), MaybeEvent.some (), PreHistory.empty)
    have : h' = PreHistory.empty := by simp only [Prod.ext_iff] at h_eq; exact h_eq.2.2
    rw [this]
    exact PreHistory.empty_minimal extendedHistory_val
  | inr h_tail =>
    -- h_tail means (p, e, h') is in the tail [((), MaybeEvent.none, PreHistory.empty)]
    -- which after simp becomes:
    -- (p, e, h') = ((), MaybeEvent.none, PreHistory.empty) ∨ (p, e, h') ∈ []
    cases h_tail with
    | inl h_eq =>
      -- (p, e, h') = ((), MaybeEvent.none, PreHistory.empty)
      have : h' = PreHistory.empty := by
        simp only [Prod.ext_iff] at h_eq
        exact h_eq.2.2
      rw [this]
      exact PreHistory.empty_minimal extendedHistory_val
    | inr h_empty =>
      -- (p, e, h') ∈ [], which is impossible
      simp at h_empty

/-- extendedHistory_val is hereditarily transitive -/
lemma extendedHistory_hered : isHereditarilyTransitive extendedHistory_val := by
  classical
  refine (isHereditarilyTransitive_unfold (P := Unit) (Event := Unit) extendedHistory_val).mpr ?_
  constructor
  · exact extendedHistory_transitive
  · intro h' hbefore
    rcases hbefore with ⟨p, e, hmem⟩
    simp only [extendedHistory_val, PreHistory.mem_mk, List.mem_cons] at hmem
    cases hmem with
    | inl h_eq =>
      have : h' = PreHistory.empty := by
        simp only [Prod.ext_iff] at h_eq
        exact h_eq.2.2
      subst this
      exact History.hereditarilyTransitive (History.emptyHistory Unit Unit)
    | inr h_tail =>
      cases h_tail with
      | inl h_eq =>
        have : h' = PreHistory.empty := by
          simp only [Prod.ext_iff] at h_eq
          exact h_eq.2.2
        subst this
        exact History.hereditarilyTransitive (History.emptyHistory Unit Unit)
      | inr h_empty =>
        cases h_empty

/-- Extended history -/
def extendedHistory : History Unit Unit :=
  { val := extendedHistory_val
    hered := extendedHistory_hered }

end Examples

/-- Definition 2.3.13: Transitive subset relation (⊆trn).
    `H' ⊆trn H` when `H' ⊆ H` and `H'` is hereditarily transitive; the
    September 2025 draft clarifies that an explicit transitivity hypothesis is
    redundant. -/
def TransitiveSubset (h1 h2 : PreHistory P Event) : Prop :=
  h1 ⊆ h2 ∧ isHereditarilyTransitive h1

infixl:50 " ⊆trn " => TransitiveSubset

/-- Any transitive subset inclusion exposes an underlying subset inclusion. -/
lemma transitiveSubset_subset {h₁ h₂ : PreHistory P Event}
    (h : h₁ ⊆trn h₂) : h₁ ⊆ h₂ := by
  exact h.1

/-- Participant happens-before persists under transitive supersets of the target. -/
lemma happensBeforeAt_of_subsetTrn {p : P}
    {h₁ h₂ h₃ : PreHistory P Event}
    (hBefore : h₁ ≺ₚ[p]h₂) (hSubset : h₂ ⊆trn h₃) :
    h₁ ≺ₚ[p] h₃ := by
  exact
    PreHistory.happensBeforeAt_mono (P := P) (Event := Event)
      hBefore (transitiveSubset_subset (P := P) (Event := Event) hSubset)

/-- Transitive subsets carry hereditary transitivity along the inclusion. -/
lemma transitiveSubset_hereditarily {h₁ h₂ : PreHistory P Event}
    (h : h₁ ⊆trn h₂) :
    isHereditarilyTransitive h₁ := by
  exact h.2

/-- A hereditarily transitive substructure yields a transitive-subset inclusion. -/
lemma transitiveSubset_of_subset
    {h₁ h₂ : PreHistory P Event}
    (hsubset : h₁ ⊆ h₂)
    (hhered : isHereditarilyTransitive (P := P) (Event := Event) h₁) :
    h₁ ⊆trn h₂ := by
  exact ⟨hsubset, hhered⟩

/-- Mutual transitive-subset inclusions yield equivalent membership predicates. -/
theorem transitiveSubset_antisymm {h₁ h₂ : PreHistory P Event} :
    h₁ ⊆trn h₂ → h₂ ⊆trn h₁ → ∀ t, t ∈ h₁ ↔ t ∈ h₂ := by
  intro h₁₂ h₂₁ t
  refine PreHistory.subset_antisymm (P := P) (Event := Event)
    h₁₂.1 h₂₁.1 t

/-- Definition 3.2.7 (2025-09-17 draft): the local view of a history simply
    returns the chosen transitive subset. -/
def localView (_H_bar : History P Event) (H : History P Event) :
  History P Event := H

infixl:70 " ∣ᵥ " => localView

@[simp] lemma localView_eq (H_bar H : History P Event) : H_bar ∣ᵥ H = H := rfl

/-- Local views at the end of time return the entire history (Lemma 3.2.8(1)). -/
@[simp] lemma localView_end (H : History P Event) : H ∣ᵥ H = H := rfl

/-- Local views compose as expected when taking a transitive subset (Lemma 3.2.8(2)). -/
@[simp] lemma localView_comp
    {H_bar H H' : History P Event}
    (_hsub : H' ⊆trn H.val) :
    (H_bar ∣ᵥ H) ∣ᵥ H' = H' := by
  simp [localView]

/-- A corollary of Lemma 3.2.8(2). -/
@[simp] lemma localView_idempotent (H_bar H : History P Event) :
    (H_bar ∣ᵥ H) ∣ᵥ H = H := by
  simp [localView]

/-- Definition 2.3.11: Elementwise transitivity – elements of elements are also
    elements. -/
def isElementwiseTransitive (H : PreHistory P Event) : Prop :=
  ∀ ⦃H' H'' : History P Event⦄,
    H''.val ≺− H'.val →
    H'.val ≺− H →
    H''.val ≺− H

/-- Lemma 2.3.12(1): Transitivity implies elementwise transitivity. -/
lemma isTransitive.elementwise {H : PreHistory P Event}
    (htrans : isTransitive (P := P) (Event := Event) H) :
    isElementwiseTransitive (P := P) (Event := Event) H := by
  intro H' H'' hH'' hH'
  rcases hH'' with ⟨p, e, mem⟩
  have hsubset : H'.val ⊆ H := htrans H'.val hH'
  exact ⟨p, e, hsubset _ mem⟩

/-- Lemma 2.3.12(2): Elementwise transitivity does not imply transitivity. -/
lemma elementwise_not_transitive :
  ∃ (P Event : Type) (H : PreHistory P Event),
    isElementwiseTransitive H ∧ ¬ isTransitive H := by
  classical
  let H₀ : PreHistory Bool Unit :=
    PreHistory.mk [((false : Bool), MaybeEvent.none, PreHistory.empty)]
  let H : PreHistory Bool Unit :=
    PreHistory.mk
      [ ((false : Bool), MaybeEvent.none, H₀)
      , ((true : Bool), MaybeEvent.none, PreHistory.empty) ]
  refine ⟨Bool, Unit, H, ?_, ?_⟩
  · intro H' H'' hH'' hH'
    classical
    rcases hH' with ⟨p, e, mem⟩
    have mem_cases :
        (p = (false : Bool) ∧ e = MaybeEvent.none ∧ H'.val = H₀) ∨
        (p = (true : Bool) ∧ e = MaybeEvent.none ∧ H'.val = PreHistory.empty) := by
      simpa [H, PreHistory.mem_mk, List.mem_cons] using mem
    rcases mem_cases with ⟨hp, he, hval⟩ | ⟨hp, he, hval⟩
    · subst hp; subst he
      rcases hH'' with ⟨p', e', mem'⟩
      have mem₀ : p' = (false : Bool) ∧ e' = MaybeEvent.none ∧ H''.val = PreHistory.empty := by
        have := mem'
        simp [H₀, PreHistory.mem_mk, hval, Prod.ext_iff] at this
        exact this
      rcases mem₀ with ⟨hp', he', hval'⟩
      subst hp'
      subst he'
      refine ⟨(true : Bool), MaybeEvent.none, ?_⟩
      simp [H, hval', PreHistory.mem_mk]
    · subst hp; subst he
      rcases hH'' with ⟨p', e', mem'⟩
      have mem_empty : (p', e', H''.val) ∈ PreHistory.empty := by
        simp [hval] at mem'
      have : False := by
        simp [PreHistory.empty, PreHistory.mem_mk] at mem_empty
      cases this
  · intro htrans
    have h_before : H₀ ≺− H := by
      refine ⟨(false : Bool), MaybeEvent.none, ?_⟩
      simp [H, PreHistory.mem_mk]
    have hsubset := htrans H₀ h_before
    have : (false, MaybeEvent.none, PreHistory.empty) ∈ H₀ := by
      simp [H₀, PreHistory.mem_mk]
    have : (false, MaybeEvent.none, PreHistory.empty) ∈ H := hsubset _ this
    simp [H, H₀, PreHistory.mem_mk, List.mem_cons] at this
    cases this

/-- Lemma 2.3.12(3): Histories are elementwise-transitive. -/
lemma History.elementwise (H : History P Event) :
    isElementwiseTransitive (P := P) (Event := Event) H.val :=
  (isTransitive.elementwise (P := P) (Event := Event)
    (History.transitive H))

/-- Lemma 2.3.14(1): `H′ ≺− H` implies `H′ ⊆trn H`. -/
theorem happensBefore_implies_transitiveSubset (h1 h2 : History P Event) :
  h1.val ≺− h2.val → h1.val ⊆trn h2.val := by
  intro h_before
  constructor
  · -- h1.val ⊆ h2.val
    exact History.transitive h2 h1.val h_before
  · -- isHereditarilyTransitive h1.val
    exact History.hereditarilyTransitive h1

theorem happensBeforeAt_implies_transitiveSubset (h1 h2 : History P Event) (p : P) :
  (h1.val ≺ₚ[p] h2.val) → h1.val ⊆trn h2.val := by
  intro h_before
  constructor
  · -- h1.val ⊆ h2.val
    exact History.transitive h2 h1.val (PreHistory.happensBefore_of_happensBeforeAt h_before)
  · -- isHereditarilyTransitive h1.val
    exact History.hereditarilyTransitive h1

/-- Lemma 2.3.14(1): `H′ ⪯ H` implies `H′ ⊆trn H`. -/
theorem happensBeforeEq_implies_transitiveSubset (h1 h2 : History P Event) :
  h1.val ⪯ h2.val → h1.val ⊆trn h2.val := by
  intro h_before_eq
  -- Use the characterization: h1.val ⪯ h2.val ↔ h1.val ≺− h2.val ∨ h1.val = h2.val
  rw [PreHistory.happensBeforeEq_iff] at h_before_eq
  cases h_before_eq with
  | inl h_before =>
    -- Case: h1.val ≺− h2.val
    exact happensBefore_implies_transitiveSubset h1 h2 h_before
  | inr h_eq =>
    -- Case: h1.val = h2.val
    rw [h_eq]
    constructor
    · -- h2.val ⊆ h2.val
      exact PreHistory.subset_refl h2.val
    · -- isHereditarilyTransitive h2.val
      exact History.hereditarilyTransitive h2

/-- Definition 2.3.15(1): a globally initial event-tuple. -/
def isInitialTuple (t : EventTuple P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ ¬ ∃ H' : PreHistory P Event, H' ≺− t.2.2

/-- Definition 2.3.15(1): a globally final event-tuple. -/
def isFinalTuple (t : EventTuple P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ ¬ ∃ H' : PreHistory P Event, t.2.2 ≺− H'

/-- Definition 2.3.15(2): `(p, E, H)` is `p`-initial when no earlier `p`-event exists. -/
def isInitialAt (p : P) (t : EventTuple P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ t.1 = p ∧ ¬ ∃ H' : PreHistory P Event, H' ≺ₚ[p] t.2.2

/-- Definition 2.3.15(3): `(p, E, H)` is `p`-final when no later `p`-event exists. -/
def isFinalAt (p : P) (t : EventTuple P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ t.1 = p ∧ ¬ ∃ H' : PreHistory P Event, t.2.2 ≺ₚ[p] H'

/-- Lemma 2.3.14(2): The reverse implication need not hold.
    There exist histories H' and H where H' ⊆trn H but not H' ⪯ H -/
theorem transitiveSubset_not_implies_happensBeforeEq :
  ∃ (P Event : Type) (H' H : History P Event),
    H'.val ⊆trn H.val ∧ ¬(H'.val ⪯ H.val) := by
  -- Use minimalHistory as H' and extendedHistory as H
  use Unit, Unit, minimalHistory, extendedHistory
  constructor
  · -- Show minimalHistory.val ⊆trn extendedHistory.val
    constructor
    · -- minimalHistory.val ⊆ extendedHistory.val
      intro e he
      simp only [minimalHistory, minimalHistory_val, PreHistory.mem_mk, List.mem_singleton] at he
      simp only [extendedHistory, extendedHistory_val, PreHistory.mem_mk, List.mem_cons]
      right
      -- he is (e = ((), MaybeEvent.none, PreHistory.empty) ∨ e ∈ [])
      -- We need e ∈ [((), MaybeEvent.none, PreHistory.empty)]
      simp
      exact he
    · -- isHereditarilyTransitive minimalHistory.val
      exact minimalHistory_hered
  · -- Show ¬(minimalHistory.val ⪯ extendedHistory.val)
    intro h_le
    rw [PreHistory.happensBeforeEq_iff] at h_le
    cases h_le with
    | inl h_before =>
      -- Case: minimalHistory.val ≺− extendedHistory.val
      -- This would mean ∃ p e, (p, e, minimalHistory.val) ∈ extendedHistory.val
      rcases h_before with ⟨p, e, hmem⟩
      simp only [extendedHistory, extendedHistory_val, PreHistory.mem_mk,
                 List.mem_cons] at hmem
      cases hmem with
      | inl h_eq =>
        -- (p, e, minimalHistory.val) = ((), MaybeEvent.some (), PreHistory.empty)
        simp only [Prod.ext_iff] at h_eq
        have : minimalHistory.val = PreHistory.empty := h_eq.2.2
        -- But minimalHistory.val is not empty!
        have not_empty : ((), MaybeEvent.none, PreHistory.empty) ∈ minimalHistory.val := by
          simp [minimalHistory, minimalHistory_val, PreHistory.mem_mk]
        rw [this] at not_empty
        simp [PreHistory.empty] at not_empty
      | inr h_tail =>
        -- h_tail means (p, e, minimalHistory.val) is in the tail
        cases h_tail with
        | inl h_eq =>
          -- (p, e, minimalHistory.val) = ((), MaybeEvent.none, PreHistory.empty)
          simp only [Prod.ext_iff] at h_eq
          have : minimalHistory.val = PreHistory.empty := h_eq.2.2
          -- But minimalHistory.val is not empty!
          have not_empty : ((), MaybeEvent.none, PreHistory.empty) ∈ minimalHistory.val := by
            simp [minimalHistory, minimalHistory_val, PreHistory.mem_mk]
          rw [this] at not_empty
          simp [PreHistory.empty] at not_empty
        | inr h_empty =>
          -- (p, e, minimalHistory.val) ∈ [], which is impossible
          simp at h_empty
    | inr h_eq =>
      -- Case: minimalHistory.val = extendedHistory.val
      -- But they have different elements!
      have h1 : ((), MaybeEvent.some (), PreHistory.empty) ∈ extendedHistory.val := by
        simp [extendedHistory, extendedHistory_val, PreHistory.mem_mk]
      rw [← h_eq] at h1
      simp only [minimalHistory, minimalHistory_val, PreHistory.mem_mk, List.mem_singleton] at h1
      -- This gives us ((), MaybeEvent.some (), PreHistory.empty) =
      --             ((), MaybeEvent.none, PreHistory.empty)
      simp only [Prod.ext_iff] at h1
      -- MaybeEvent.some () = MaybeEvent.none, which is false
      cases h1.2.1

/-- Transitivity Closure (Knowledge preservation):
    The "knows of" relation is transitive in histories -/
theorem transitivity_closure (H : History P Event) :
  ∀ e1 e2 e3 : EventTuple P Event,
    e1 ∈ H.val → e2 ∈ H.val → e3 ∈ H.val →
    (∃ p, e2 = (p, e2.2.1, e1.2.2)) →
    (∃ q, e3 = (q, e3.2.1, e2.2.2)) →
    (∃ r, (r, e3.2.1, e1.2.2) ∈ H.val) := by
  intro e1 e2 e3 _ _ he3 hp hq
  -- Extract the witnesses and equalities
  rcases hp with ⟨_, hp_eq⟩
  rcases hq with ⟨q, hq_eq⟩
  -- From hp_eq: e2 = (p, e2.2.1, e1.2.2), so e2.2.2 = e1.2.2
  have h_time : e2.2.2 = e1.2.2 := by rw [hp_eq]
  -- Substitute this time equality into hq_eq
  -- Since e3 = (q, e3.2.1, e2.2.2) and e2.2.2 = e1.2.2,
  -- we have e3 = (q, e3.2.1, e1.2.2)
  use q
  -- Show that (q, e3.2.1, e1.2.2) ∈ H.val
  -- This follows from e3 = (q, e3.2.1, e2.2.2) and e2.2.2 = e1.2.2
  rw [hq_eq] at he3
  rw [h_time] at he3
  exact he3

/-- Corollary: For histories, ≺− transitivity within the history -/
theorem happensBefore_trans_in_history (H : History P Event) :
  ∀ h1 h2 h3 : PreHistory P Event,
    h1 ≺− h2 → h2 ≺− h3 → h3 ⪯ H.val → h1 ≺− h3 := by
  intro h1 h2 h3 h12 h23 h3_le_H
  -- h3 is transitive: either h3 ≺− H.val (hereditary transitivity) or h3 = H.val (H is transitive)
  have h3_transitive : isTransitive h3 := by
    rw [PreHistory.happensBeforeEq_iff] at h3_le_H
    cases h3_le_H with
    | inl h3_before_H =>
      -- Case: h3 ≺− H.val, use hereditary transitivity
      exact (History.predecessor_data (H := H) (h_before := h3_before_H)).1
    | inr h3_eq_H =>
      -- Case: h3 = H.val, use that H is transitive
      rw [h3_eq_H]
      exact History.transitive H
  -- From h2 ≺− h3 and h3 being transitive, we get h2 ⊆ h3
  have h2_subset_h3 : h2 ⊆ h3 := h3_transitive h2 h23
  -- From h1 ≺− h2, by definition of ≺−, ∃ p e. (p, e, h1) ∈ h2
  rcases h12 with ⟨p, e, h1_in_h2⟩
  -- Since h2 ⊆ h3, we have (p, e, h1) ∈ h3
  have h1_in_h3 : (p, e, h1) ∈ h3 := h2_subset_h3 (p, e, h1) h1_in_h2
  -- Therefore h1 ≺− h3 by definition
  exact ⟨p, e, h1_in_h3⟩

/-- Corollary: For histories, ⪯ transitivity within the history -/
theorem happensBeforeEq_trans_in_history (H : History P Event) :
  ∀ h1 h2 h3 : PreHistory P Event,
    h1 ⪯ h2 → h2 ⪯ h3 → h3 ⪯ H.val → h1 ⪯ h3 := by
  intro h1 h2 h3 h12 h23 h3_le_H
  -- Use the characterization: ⪯ means ≺− ∨ =
  rw [PreHistory.happensBeforeEq_iff] at h12 h23 ⊢
  cases h12 with
  | inl h12_before =>
    cases h23 with
    | inl h23_before =>
      -- Case: h1 ≺− h2 and h2 ≺− h3
      left
      exact happensBefore_trans_in_history H h1 h2 h3 h12_before h23_before h3_le_H
    | inr h23_eq =>
      -- Case: h1 ≺− h2 and h2 = h3
      left
      rw [←h23_eq]
      exact h12_before
  | inr h12_eq =>
    cases h23 with
    | inl h23_before =>
      -- Case: h1 = h2 and h2 ≺− h3
      left
      rw [h12_eq]
      exact h23_before
    | inr h23_eq =>
      -- Case: h1 = h2 and h2 = h3
      right
      rw [h12_eq, h23_eq]

/-- Simple corollary: Transitivity for three histories -/
theorem happensBefore_trans (h1 h2 h3 : History P Event) :
  h1.val ≺− h2.val → h2.val ≺− h3.val → h1.val ≺− h3.val := by
  intro h12 h23
  -- Apply the general theorem with H = h3, using h3.val ⪯ h3.val (which is reflexive)
  exact happensBefore_trans_in_history h3 h1.val h2.val h3.val h12 h23
    (PreHistory.happensBeforeEq_refl h3.val)

/-- Transitivity of ⪯ for histories -/
theorem happensBeforeEq_trans (h1 h2 h3 : History P Event) :
  h1.val ⪯ h2.val →
  h2.val ⪯ h3.val →
  h1.val ⪯ h3.val := by
  intro h12 h23
  -- Apply the general theorem with H = h3, using h3.val ⪯ h3.val (which is reflexive)
  exact happensBeforeEq_trans_in_history h3 h1.val h2.val h3.val h12 h23
    (PreHistory.happensBeforeEq_refl h3.val)

/-- Antisymmetry of ⪯ for histories -/
theorem happensBeforeEq_antisymm (h1 h2 : History P Event) :
  h1.val ⪯ h2.val → h2.val ⪯ h1.val → h1 = h2 := by
  intro h12 h21
  -- Use the characterization: ⪯ means ≺− ∨ =
  rw [PreHistory.happensBeforeEq_iff] at h12 h21
  cases h12 with
  | inl h12_before =>
    cases h21 with
    | inl h21_before =>
      -- Case: h1.val ≺− h2.val and h2.val ≺− h1.val
      -- This contradicts well-foundedness of ≺−
      have h12_trans : h1.val ≺− h1.val :=
        happensBefore_trans h1 h2 h1 h12_before h21_before
      -- But ≺− is irreflexive
      exact absurd h12_trans (PreHistory.happensBefore_irrefl h1.val)
    | inr h21_eq =>
      -- Case: h1.val ≺− h2.val and h2.val = h1.val
      rw [h21_eq] at h12_before
      -- This gives h1.val ≺− h1.val, contradicting irreflexivity
      exact absurd h12_before (PreHistory.happensBefore_irrefl h1.val)
  | inr h12_eq =>
    cases h21 with
    | inl h21_before =>
      -- Case: h1.val = h2.val and h2.val ≺− h1.val
      rw [←h12_eq] at h21_before
      -- This gives h1.val ≺− h1.val, contradicting irreflexivity
      exact absurd h21_before (PreHistory.happensBefore_irrefl h1.val)
    | inr h21_eq =>
      -- Case: h1.val = h2.val and h2.val = h1.val
      -- Both are equal, so h1 = h2
      exact History.ext h12_eq

/-- Partial order instance for happens-before relation on histories -/
instance : PartialOrder (History P Event) where
  le h1 h2 := h1.val ⪯ h2.val
  le_refl h := PreHistory.happensBeforeEq_refl h.val
  le_trans h1 h2 h3 := happensBeforeEq_trans h1 h2 h3
  le_antisymm h1 h2 := happensBeforeEq_antisymm h1 h2

/-- Strict happens-before implies the corresponding order relation. -/
theorem le_of_happensBefore {h₁ h₂ : History P Event} :
    h₁.val ≺− h₂.val → h₁ ≤ h₂ :=
  by
    intro hbefore
    exact Or.inl hbefore

/-- Strict happens-before yields a strict inequality of histories. -/
theorem lt_of_happensBefore {h₁ h₂ : History P Event} :
    h₁.val ≺− h₂.val → h₁ < h₂ :=
  by
    intro hbefore
    refine ⟨le_of_happensBefore (P := P) (Event := Event) hbefore, ?_⟩
    intro h₂₁
    have hcases :=
      (PreHistory.happensBeforeEq_iff (P := P) (Event := Event)
        h₂.val h₁.val).1 h₂₁
    cases hcases with
    | inl h₂before =>
        have : False :=
          Nat.lt_asymm
            (PreHistory.height_lt_of_happensBefore (P := P) (Event := Event) hbefore)
            (PreHistory.height_lt_of_happensBefore (P := P) (Event := Event) h₂before)
        cases this
    | inr h_eq =>
        have : h₁.val ≺− h₁.val := by simpa [h_eq] using hbefore
        exact (PreHistory.happensBefore_irrefl (P := P) (Event := Event) h₁.val) this

/-- Comparable histories that bound each other coincide. -/
theorem eq_of_le_of_le_history {h₁ h₂ : History P Event} :
    h₁ ≤ h₂ → h₂ ≤ h₁ → h₁ = h₂ :=
  by
    intro h₁₂ h₂₁
    exact le_antisymm h₁₂ h₂₁

/-- Predecessor histories sit strictly below the ambient history. -/
theorem predecessorHistory_lt {H : History P Event}
    {h' : PreHistory P Event}
    (h_before : h' ≺− H.val) :
    History.predecessorHistory (H := H) h_before < H :=
  lt_of_happensBefore (P := P) (Event := Event) h_before

/-- Local views inherit the ambient subset relation. -/
theorem localView_subset_history (H : History P Event)
    (h' : PreHistory P Event) (hsub : h' ⊆trn H.val) :
    (History.mk h' hsub.2).val ⊆ H.val :=
  hsub.1

/-- Predecessors of a history are contained in the ambient history. -/
lemma happensBefore_subset {H : History P Event} {h' : PreHistory P Event} :
    (h' ≺− H.val) → h' ⊆ H.val := by
  intro h_before
  exact History.transitive H h' h_before

/-- Order-theoretic monotonicity for histories: `h₁ ≤ h₂` yields `h₁.val ⊆ h₂.val`. -/
lemma subset_of_le {h₁ h₂ : History P Event} :
    (h₁ ≤ h₂) → h₁.val ⊆ h₂.val := by
  intro h_le
  have h := (PreHistory.happensBeforeEq_iff (h₁.val) (h₂.val)).mp h_le
  cases h with
  | inl h_before =>
      exact History.transitive h₂ h₁.val h_before
  | inr h_eq =>
      intro t ht
      simpa [h_eq] using ht

/-- The transitive-subset relation is reflexive on histories. -/
lemma transitiveSubset_refl (H : History P Event) :
    H.val ⊆trn H.val := by
  constructor
  · exact PreHistory.subset_refl H.val
  · exact History.hereditarilyTransitive H

/-- The transitive-subset relation composes transitively. -/
lemma transitiveSubset_trans {h₁ h₂ h₃ : PreHistory P Event} :
    (h₁ ⊆trn h₂) → (h₂ ⊆trn h₃) → h₁ ⊆trn h₃ := by
  intro h₁₂ h₂₃
  rcases h₁₂ with ⟨h₁₂_subset, h₁₂_trn⟩
  rcases h₂₃ with ⟨h₂₃_subset, _⟩
  constructor
  · exact PreHistory.subset_trans h₁ h₂ h₃ h₁₂_subset h₂₃_subset
  · exact h₁₂_trn

/-- Definition 3.3.2 (September 17, 2025 draft): a participant is sequential when
    any two of its event-tuples appear in sequence. -/
def isSequential (p : P) (h : PreHistory P Event) : Prop :=
  ∀ {t₁ t₂ : EventTuple P Event},
    t₁ ∈ h →
    t₂ ∈ h →
    EventTuple.participant t₁ = p →
    EventTuple.participant t₂ = p →
      (t₁ ∈ EventTuple.time t₂ ∨
        t₂ ∈ EventTuple.time t₁ ∨
        t₁ = t₂)

/-! ## Helper lemmas for sequentiality preservation -/

/-- If an event is in H, its time component happens before H -/
lemma happensBefore_of_mem {H : PreHistory P Event} {e : EventTuple P Event}
  (he : e ∈ H) :
  e.2.2 ≺− H :=
  ⟨e.1, e.2.1, he⟩

/-- If `H' ≺− H` then there exists a participant that knows the possible world
`H'` at `(p, H)` (Lemma 2.4.3). -/
lemma exists_knowsOfPossibleWorld_of_happensBefore
    {H : History P Event} {H' : PreHistory P Event}
    (h_before : H' ≺− H.val) :
    ∃ p : P, (p,H') ↢[H.val] p,H.val := by
  classical
  rcases h_before with ⟨p, e, mem⟩
  exact ⟨p, ⟨e, Or.inr mem⟩⟩

/-- If a participant knows the possible world `H'` at `(p, H)` then
`H' ⪯ H` (Lemma 2.4.3/2.4.4, reverse direction). -/
lemma happensBeforeEq_of_exists_knowsOfPossibleWorld
    {H : History P Event} {H' : PreHistory P Event}
    (h_know : ∃ p : P, (p,H')↢[H.val]p,H.val) :
    H' ⪯ H.val := by
  classical
  rcases h_know with ⟨p, ⟨e, hmem⟩⟩
  cases hmem with
  | inl hself =>
      rcases hself with ⟨_, hh, _⟩
      subst hh
      exact Or.inr rfl
  | inr mem' =>
      exact Or.inl ⟨p, e, mem'⟩

/-- Forward direction: sequentiality is preserved by local views (now the
identity). -/
lemma sequentiality_forward {p : P} {H : History P Event} {H_bar : History P Event}
  (seqH : isSequential p H.val) :
  isSequential p (H_bar ∣ᵥ H).val := by
  intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
  simpa [localView] using seqH ht₁ ht₂ hp₁ hp₂

/-- Backward direction: sequentiality on the local view implies sequentiality
on the original history. -/
lemma sequentiality_backward {p : P} {H : History P Event} {H_bar : History P Event}
  (_hsubtrn : H ⊆trn H_bar.val)
  (seqLV : isSequential p (H_bar ∣ᵥ H).val) :
  isSequential p H.val := by
  intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
  simpa [localView] using seqLV ht₁ ht₂ hp₁ hp₂

/-- Lemma 3.2.8 (sequentiality preservation): the new local view leaves
sequentiality unchanged. -/
theorem sequentiality_preservation (p : P) (H : History P Event) (H_bar : History P Event)
  (_hsubtrn : H ⊆trn H_bar.val) :
  isSequential p H.val ↔ isSequential p (H_bar ∣ᵥ H).val := by
  constructor <;> intro h
  · intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
    simpa [localView] using h ht₁ ht₂ hp₁ hp₂
  · intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
    simpa [localView] using h ht₁ ht₂ hp₁ hp₂

/-- Lemma 5.1.1: Sequentiality is monotone -/
theorem sequentiality_monotone (p : P) (h h' : History P Event) :
  h' ⊆trn h.val →
  isSequential p h.val →
  isSequential p h'.val := by
  intro hsubtrn seq_h
  -- Extract the plain subset relation from ⊆trn
  have hsub : h'.val ⊆ h.val := hsubtrn.1
  intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
  have ht₁_in : t₁ ∈ h.val := hsub _ ht₁
  have ht₂_in : t₂ ∈ h.val := hsub _ ht₂
  exact seq_h ht₁_in ht₂_in hp₁ hp₂

/-- Sequentiality is inherited by immediate predecessors of a history. -/
lemma sequentiality_of_predecessor {p : P} {H : History P Event}
    {h' : PreHistory P Event}
    (h_before : h' ≺− H.val)
    (hseq : isSequential (P := P) (Event := Event) p H.val) :
    isSequential p h' := by
  have hsubset : h' ⊆ H.val := History.transitive H h' h_before
  intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
  have ht₁' : t₁ ∈ H.val := hsubset _ ht₁
  have ht₂' : t₂ ∈ H.val := hsubset _ ht₂
  exact hseq ht₁' ht₂' hp₁ hp₂
