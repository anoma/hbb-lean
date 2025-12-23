import ModalDistribution.Core.Prehistory
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic

open scoped PreHistory
open PreHistory
open Set

/-!
# History Structures

This file formalizes the history structure from
Definition~\ref{defn.history.structure} of the paper.
A history is a hereditarily transitive element of PreHistory(P, Event).

## Main definitions

* `History P Event`: Type for history structures with hereditary transitivity
* `TransitiveSubset`: Transitive subset relation (⊆trn) from Definition~\ref{defn.hsubseteq}
* Local view operations and sequentiality properties

## Main theorems

* Hereditary transitivity proofs
* Basic properties of history structures
* Local view properties and sequentiality lemmas

## References

* Definition~\ref{defn.history.structure}
* Definition~\ref{defn.hsubseteq}
* Definition~\ref{defn.views}
* Definition~\ref{defn.sequential.p}
-/

variable {P Event : Type*}

/-- Definition\ref{defn.transitive}: a prehistory is transitive when every
strict predecessor is a subset. -/
def isTransitive (h : PreHistory P Event) : Prop :=
  ∀ h' : PreHistory P Event, h' ≺− h → h' ⊆ h

/-- Definition~\ref{defn.history.structure}: hereditary transitivity demands every
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

/-- Definition~\ref{defn.history.structure}: histories are the prehistories that are
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

lemma subset_of_happensBefore {H : History P Event} {h' : PreHistory P Event}
    (h_before : h' ≺− H.val) : h' ⊆ H.val :=
  History.transitive H h' h_before

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
  exact History.subset_of_happensBefore (H := H) h_before

/-- If `H` is a history and `h' ≺− H`, then `h'` is also a history. -/
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

section HistoryAt

variable {P Event : Type*}

namespace History

/-- Specialise Definition~\ref{defn.historyat} to history structures. -/
def historyAt (H : History P Event) (p : P) : Set (World P Event) :=
  PreHistory.historyAt (P := P) (Event := Event) H.val p

@[simp] lemma mem_historyAt {H : History P Event} {p : P} {t : World P Event} :
    t ∈ historyAt (P := P) (Event := Event) H p ↔
      t ∈ H.val ∧ World.place t = p := Iff.rfl

end History

end HistoryAt

/-- Definition~\ref{defn.sequential.p}(\ref{item.p.sequential}):
    participant `p` is sequential in `h` when its event-tuples are linearly
    ordered by accessibility. -/
def isSequential (p : P) (h : PreHistory P Event) : Prop :=
  ∀ {t₁ t₂ : World P Event},
    t₁ ∈ h →
    t₂ ∈ h →
    World.place t₁ = p →
    World.place t₂ = p →
      (t₁ ≪ t₂ ∨
        t₂ ≪ t₁ ∨
        worldEq t₁ t₂)

-- TODO: This lemma needs to be reproven or redesigned for the new bisimulation-style histEq.
-- The new histEq allows histories to differ in representation while being extensionally equal.
-- We need to show that isSequential is preserved under worldEq and the bisimulation.
lemma isSequential_congr_histEq
    {p : P} {h h' : PreHistory P Event}
    (hHist : PreHistory.histEq h h') :
    isSequential (Event := Event) p h ↔
      isSequential (Event := Event) p h' := by
  classical
  have transfer :
      ∀ {h₁ h₂ : PreHistory P Event},
        PreHistory.histEq h₁ h₂ →
          isSequential (Event := Event) p h₁ →
            isSequential (Event := Event) p h₂ := by
    intro h₁ h₂ hSame hSeq
    refine fun {t₁ t₂} ht₁ ht₂ hp₁ hp₂ => ?_
    obtain ⟨s₁, hs₁_mem, hs₁_eq⟩ :=
      PreHistory.histEq_bwd hSame t₁ ht₁
    obtain ⟨s₂, hs₂_mem, hs₂_eq⟩ :=
      PreHistory.histEq_bwd hSame t₂ ht₂
    have hp₁' : World.place s₁ = p := by
      have := PreHistory.worldEq_place hs₁_eq
      simp [World.place] at this
      simpa [World.place] using this.trans hp₁
    have hp₂' : World.place s₂ = p := by
      have := PreHistory.worldEq_place hs₂_eq
      simp [World.place] at this
      simpa [World.place] using this.trans hp₂
    have hSeq_s := hSeq hs₁_mem hs₂_mem hp₁' hp₂'
    rcases hSeq_s with hAcc | hAcc | hEq
    · left
      exact
        PreHistory.accessible_of_worldEq_accessible
          (PreHistory.worldEq_symm hs₁_eq) hAcc
          (PreHistory.worldEq_symm hs₂_eq)
    · right; left
      exact
        PreHistory.accessible_of_worldEq_accessible
          (PreHistory.worldEq_symm hs₂_eq) hAcc
          (PreHistory.worldEq_symm hs₁_eq)
    · right; right
      exact
        PreHistory.worldEq_trans
          (PreHistory.worldEq_symm hs₁_eq)
          (PreHistory.worldEq_trans hEq hs₂_eq)
  refine ⟨transfer hHist, ?_⟩
  exact transfer (PreHistory.histEq_symm hHist)

namespace History

/-- Definition~\ref{defn.hsubseteq}: transitive subset relation (⊆trn).
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

/-- Strict happens-before forces the predecessor history to sit inside the
transitive-subset relation of Definition~\ref{defn.hsubseteq}. -/
theorem happensBefore_implies_transitiveSubset (h1 h2 : History P Event) :
  h1.val ≺− h2.val → h1.val ⊆trn h2.val := by
  intro h_before
  constructor
  · -- h1.val ⊆ h2.val
    exact History.subset_of_happensBefore (H := h2) h_before
  · -- isHereditarilyTransitive h1.val
    exact History.hereditarilyTransitive h1

/-- Non-strict happens-before collapses to the same transitive-subset
inclusion. -/
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

/-- Definition~\ref{defn.initial.final.event-tuple}: a globally initial event-tuple. -/
def isInitialTuple (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ ¬ ∃ H' : PreHistory P Event, H' ≺− t.2.2

/-- Definition~\ref{defn.initial.final.event-tuple}: a globally final event-tuple. -/
def isFinalTuple (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ ¬ ∃ H' : PreHistory P Event, t.2.2 ≺− H'

/-- `(p, E, H)` is `p`-initial when no earlier `p`-event exists.
    See Definition~\ref{defn.initial.final.event-tuple}. -/
def isInitialAt (p : P) (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ World.place t = p ∧
    ¬ ∃ t' : World P Event,
        t' ∈ H ∧ World.place t' = p ∧ World.time t' ≺− World.time t

/-- `(p, E, H)` is `p`-final when no later `p`-event exists.
    See Definition~\ref{defn.initial.final.event-tuple}. -/
def isFinalAt (p : P) (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ World.place t = p ∧
    ¬ ∃ t' : World P Event,
        t' ∈ H ∧ World.place t' = p ∧ World.time t ≺− World.time t'

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
  exact (History.transitive H) h' h_before

/-- Order-theoretic monotonicity for histories: `h₁ ≤ h₂` yields `h₁.val ⊆ h₂.val`. -/
lemma subset_of_le {h₁ h₂ : History P Event} :
    (h₁ ≤ h₂) → h₁.val ⊆ h₂.val := by
  intro h_le
  have h := (PreHistory.happensBeforeEq_iff (h₁.val) (h₂.val)).mp h_le
  cases h with
  | inl h_before =>
      exact (History.transitive h₂) h₁.val h_before
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

/-- Definition~\ref{defn.sequential.p} expressed using the `historyAt`
projection from Definition~\ref{defn.historyat}. -/
lemma isSequential_iff_historyAt (p : P) (h : PreHistory P Event) :
    isSequential (P := P) (Event := Event) p h ↔
      ∀ {t t' : World P Event},
        t ∈ PreHistory.historyAt (P := P) (Event := Event) h p →
        t' ∈ PreHistory.historyAt (P := P) (Event := Event) h p →
          (t ≪ t' ∨ t' ≪ t ∨ worldEq t t') := by
  constructor
  · intro hSeq t t' ht ht'
    obtain ⟨ht_mem, ht_place⟩ := ht
    obtain ⟨ht'_mem, ht'_place⟩ := ht'
    exact hSeq ht_mem ht'_mem ht_place ht'_place
  · intro hSeq t₁ t₂ ht₁ ht₂ hp₁ hp₂
    have ht₁_history :
        t₁ ∈ PreHistory.historyAt (P := P) (Event := Event) h p := ⟨ht₁, hp₁⟩
    have ht₂_history :
        t₂ ∈ PreHistory.historyAt (P := P) (Event := Event) h p := ⟨ht₂, hp₂⟩
    exact hSeq ht₁_history ht₂_history

/-! ## Helper lemmas for sequentiality preservation -/

/-- If an event is in H, its time component happens before H -/
lemma happensBefore_of_mem {H : PreHistory P Event} {e : World P Event}
  (he : e ∈ H) :
  e.2.2 ≺− H :=
  ⟨e.1, e.2.1, he⟩

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
  have hsubset : h' ⊆ H.val := History.subset_of_happensBefore (H := H) h_before
  intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
  have ht₁' : t₁ ∈ H.val := hsubset _ ht₁
  have ht₂' : t₂ ∈ H.val := hsubset _ ht₂
  exact hseq ht₁' ht₂' hp₁ hp₂

end History
