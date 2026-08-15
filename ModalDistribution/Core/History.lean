import ModalDistribution.Core.Prehistory

open scoped PreHistory
open Set

/-!
# History Structures

This file formalizes history structures for HBB.
A history is a hereditarily transitive element of PreHistory(P, Event).

## Main definitions

* `History P Event`: Type for history structures with hereditary transitivity
* `TransitiveSubset`: Transitive subset relation (⊆trn)
* Local view operations and sequentiality properties

## Main theorems

* Hereditary transitivity proofs
* Basic properties of history structures
* Local view properties and sequentiality lemmas
-/

universe u v

variable {P : Type u} {Event : Type v}

/-- Paper: Definition 2.3.2 (transitive prehistories). A prehistory is transitive when every strict predecessor is a subset. -/
def isTransitive (h : PreHistory P Event) : Prop :=
  ∀ h' : PreHistory P Event, h' ≺− h → h' ⊆ h

/-- Paper: Definition 2.3.5. Hereditary transitivity demands every predecessor be transitive and itself
    satisfy hereditary transitivity. We construct this predicate by well-founded
    recursion on ≺−. -/
noncomputable def isHereditarilyTransitive : PreHistory P Event → Prop :=
  PreHistory.happensBefore_wellFounded.fix
    (fun h rec =>
      isTransitive h ∧
      ∀ h' : PreHistory P Event,
        ∀ h_before : h' ≺− h, rec h' h_before)

theorem isHereditarilyTransitive_unfold (h : PreHistory P Event) :
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

theorem isHereditarilyTransitive.trans
    {h : PreHistory P Event} :
    isHereditarilyTransitive h → isTransitive h := by
  intro h_hered
  have := (isHereditarilyTransitive_unfold h).mp h_hered
  exact this.1

theorem isHereditarilyTransitive.desc
    {h h' : PreHistory P Event}
    (hh : isHereditarilyTransitive h)
    (hb : h' ≺− h) :
    isHereditarilyTransitive h' := by
  classical
  have := (isHereditarilyTransitive_unfold h).mp hh
  exact this.2 h' hb

/-- Paper: Definition 2.3.5 (history structures). Histories are the prehistories that are hereditarily transitive.
    The transitivity of the history follows from the hereditary property itself. -/
structure History (P : Type u) (Event : Type v) where
  val : PreHistory P Event
  hered : isHereditarilyTransitive val

namespace History

/-- Coerce a history to its underlying prehistory. -/
instance : Coe (History P Event) (PreHistory P Event) := ⟨History.val⟩

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

theorem subset_of_happensBefore {H : History P Event} {h' : PreHistory P Event}
    (h_before : h' ≺− H.val) : h' ⊆ H.val :=
  History.transitive H h' h_before

/-- A history is hereditarily transitive -/
theorem hereditarilyTransitive (h : History P Event) : isHereditarilyTransitive h.val :=
  h.hered

/-- Helper: data carried by the hereditary property for a specific predecessor. -/
theorem predecessor_data {H : History P Event} {h' : PreHistory P Event}
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
theorem predecessorHistory_subset {H : History P Event}
    {h' : PreHistory P Event} (h_before : h' ≺− H.val) :
    (predecessorHistory (H := H) h_before).val ⊆ H.val := by
  exact History.subset_of_happensBefore (H := H) h_before

end History

section HistoryAt

variable {P : Type u} {Event : Type v}

namespace History

/-- History at p for history structures. -/
def historyAt (H : History P Event) (p : P) : Set (World P Event) :=
  PreHistory.historyAt (P := P) (Event := Event) H.val p

end History

end HistoryAt

/-- Paper: Definition 3.4.9(1) (p sequential at H). Participant `p` is sequential in `h` when its event-tuples are linearly
    ordered by accessibility. -/
def isSequential (p : P) (h : PreHistory P Event) : Prop :=
  ∀ t₁ t₂ : World P Event,
    t₁ ∈ h →
    t₂ ∈ h →
    World.place t₁ = p →
    World.place t₂ = p →
      (t₁ ≪ t₂ ∨
        t₂ ≪ t₁ ∨
        t₁ = t₂)

namespace History

/-- Transitive subset relation (⊆trn). `H' ⊆trn H` when `H' ⊆ H` and `H'`
    is hereditarily transitive. -/
def TransitiveSubset (h1 h2 : PreHistory P Event) : Prop :=
  h1 ⊆ h2 ∧ isHereditarilyTransitive h1

infixl:50 " ⊆trn " => TransitiveSubset

/-- Any transitive subset inclusion exposes an underlying subset inclusion. -/
theorem transitiveSubset_subset {h₁ h₂ : PreHistory P Event}
    (h : h₁ ⊆trn h₂) : h₁ ⊆ h₂ := by
  exact h.1

/-- A hereditarily transitive substructure yields a transitive-subset inclusion. -/
theorem transitiveSubset_of_subset
    {h₁ h₂ : PreHistory P Event}
    (hsubset : h₁ ⊆ h₂)
    (hhered : isHereditarilyTransitive (P := P) (Event := Event) h₁) :
    h₁ ⊆trn h₂ := by
  exact ⟨hsubset, hhered⟩

/-- Strict happens-before forces the predecessor history to sit inside the
    transitive-subset relation. -/
theorem happensBefore_implies_transitiveSubset (h1 h2 : History P Event) :
  h1.val ≺− h2.val → h1.val ⊆trn h2.val := by
  intro h_before
  constructor
  · -- h1.val ⊆ h2.val
    exact History.subset_of_happensBefore (H := h2) h_before
  · -- isHereditarilyTransitive h1.val
    exact History.hereditarilyTransitive h1

/-- Paper: Definition 2.3.13(2). A globally initial event-tuple. -/
def isInitialTuple (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ ¬ ∃ H' : PreHistory P Event, H' ≺− t.2.2

/-- Paper: Definition 2.3.13(3). A globally final event-tuple. -/
def isFinalTuple (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ ¬ ∃ H' : PreHistory P Event, t.2.2 ≺− H'

/-- Paper: Definition 2.3.13(2). `(p, E, H)` is `p`-initial when no earlier `p`-event exists. -/
def isInitialAt (p : P) (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ World.place t = p ∧
    ¬ ∃ t' : World P Event,
        t' ∈ H ∧ World.place t' = p ∧ World.time t' ≺− World.time t

/-- Paper: Definition 2.3.13(3). `(p, E, H)` is `p`-final when no later `p`-event exists. -/
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

/-- Simple corollary: Transitivity for three histories -/
theorem happensBefore_trans (h1 h2 h3 : History P Event) :
  h1.val ≺− h2.val → h2.val ≺− h3.val → h1.val ≺− h3.val := by
  intro h12 h23
  -- Apply the general theorem with H = h3, using h3.val ⪯ h3.val (which is reflexive)
  exact happensBefore_trans_in_history h3 h1.val h2.val h3.val h12 h23
    (PreHistory.happensBeforeEq_refl h3.val)

/-- Order relation for the happens-before relation on histories.  Reflexivity,
transitivity and antisymmetry are `PreHistory.happensBeforeEq_refl`,
`happensBeforeEq_trans` and `happensBeforeEq_antisymm`. -/
instance : LE (History P Event) where
  le h1 h2 := h1.val ⪯ h2.val

/-- Strict order relation for the happens-before relation on histories. -/
instance : LT (History P Event) where
  lt h1 h2 := h1 ≤ h2 ∧ ¬ h2 ≤ h1

/-- The transitive-subset relation is reflexive on histories. -/
theorem transitiveSubset_refl (H : History P Event) :
    H.val ⊆trn H.val := by
  constructor
  · exact PreHistory.subset_refl H.val
  · exact History.hereditarilyTransitive H

/-! ## Helper lemmas for sequentiality preservation -/

/-- If an event is in H, its time component happens before H -/
theorem happensBefore_of_mem {H : PreHistory P Event} {e : World P Event}
  (he : e ∈ H) :
  e.2.2 ≺− H :=
  ⟨e.1, e.2.1, he⟩

/-- Paper: Proposition 5.1.4 (variant). Sequentiality is monotone. -/
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
  exact seq_h t₁ t₂ ht₁_in ht₂_in hp₁ hp₂

/-- Sequentiality is inherited by immediate predecessors of a history. -/
theorem sequentiality_of_predecessor {p : P} {H : History P Event}
    {h' : PreHistory P Event}
    (h_before : h' ≺− H.val)
    (hseq : isSequential (P := P) (Event := Event) p H.val) :
    isSequential p h' := by
  have hsubset : h' ⊆ H.val := History.subset_of_happensBefore (H := H) h_before
  intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
  have ht₁' : t₁ ∈ H.val := hsubset _ ht₁
  have ht₂' : t₂ ∈ H.val := hsubset _ ht₂
  exact hseq t₁ t₂ ht₁' ht₂' hp₁ hp₂

end History

/-! ## Element-transitivity (paper Definition 2.3.11 and Lemma 2.3.12) -/

/-- Paper: Definition 2.3.11 (element-transitive). A prehistory is element-transitive when `≺−` is transitive into it. This is
an alternative, strictly weaker notion than `isTransitive`. -/
def isElementTransitive (h : PreHistory P Event) : Prop :=
  ∀ h'' h' : PreHistory P Event, h'' ≺− h' → h' ≺− h → h'' ≺− h

/-- Paper: Lemma 2.3.12(1). Transitive prehistories are element-transitive. -/
theorem isTransitive.isElementTransitive {h : PreHistory P Event}
    (ht : isTransitive h) : isElementTransitive h := by
  intro h'' h' h''h' h'h
  obtain ⟨p, x, hmem⟩ := h''h'
  exact ⟨p, x, ht h' h'h _ hmem⟩

/-- Paper: Lemma 2.3.12(3). Every history structure is element-transitive. -/
theorem History.isElementTransitive (H : History P Event) :
    isElementTransitive H.val :=
  (History.transitive H).isElementTransitive

/-- Paper: Lemma 2.3.12(2). The reverse implication fails: an element-transitive prehistory need not be
transitive. The witness is the paper's `H₂ = {(p, †, H₁), (q, †, ∅)}` with
`H₁ = {(p, †, ∅)}`. -/
theorem exists_elementTransitive_not_transitive :
    ∃ h : PreHistory Bool Empty,
      isElementTransitive h ∧ ¬ isTransitive h := by
  classical
  set H₁ : PreHistory Bool Empty :=
    PreHistory.mk [(true, MaybeEvent.none, PreHistory.empty)] with hH₁
  set H₂ : PreHistory Bool Empty :=
    PreHistory.mk
      [ (true, MaybeEvent.none, H₁)
      , (false, MaybeEvent.none, PreHistory.empty) ] with hH₂
  refine ⟨H₂, ?_, ?_⟩
  · intro h'' h' h''h' h'h
    obtain ⟨p, x, hmem'⟩ := h'h
    have hmemL :
        (p, x, h') ∈
          [ ((true : Bool), (MaybeEvent.none : MaybeEvent Empty), H₁)
          , (false, MaybeEvent.none, PreHistory.empty) ] := hmem'
    have hcases : h' = H₁ ∨ h' = PreHistory.empty := by
      rcases List.mem_cons.1 hmemL with heq | htail
      · exact Or.inl (congrArg (fun t => t.2.2) heq)
      · rcases List.mem_cons.1 htail with heq | hnil
        · exact Or.inr (congrArg (fun t => t.2.2) heq)
        · cases hnil
    obtain ⟨q, y, hmem''⟩ := h''h'
    rcases hcases with rfl | rfl
    · have hmemL' :
          (q, y, h'') ∈
            [ ((true : Bool), (MaybeEvent.none : MaybeEvent Empty),
                PreHistory.empty) ] := hmem''
      have h''eq : h'' = PreHistory.empty := by
        rcases List.mem_cons.1 hmemL' with heq | hnil
        · exact congrArg (fun t => t.2.2) heq
        · cases hnil
      subst h''eq
      exact ⟨false, MaybeEvent.none,
        List.Mem.tail _ (List.Mem.head _)⟩
    · cases hmem''
  · intro ht
    have hH₁_mem : H₁ ≺− H₂ :=
      ⟨true, MaybeEvent.none, List.Mem.head _⟩
    have hsub := ht H₁ hH₁_mem
    have hmem : ((true : Bool), (MaybeEvent.none : MaybeEvent Empty),
        PreHistory.empty) ∈ H₁ :=
      List.Mem.head _
    have hbad :
        ((true : Bool), (MaybeEvent.none : MaybeEvent Empty),
          PreHistory.empty) ∈
          [ ((true : Bool), (MaybeEvent.none : MaybeEvent Empty), H₁)
          , (false, MaybeEvent.none, PreHistory.empty) ] :=
      hsub _ hmem
    rcases List.mem_cons.1 hbad with heq | htail
    · have hstruct : PreHistory.empty = H₁ :=
        congrArg (fun t => t.2.2) heq
      rw [hH₁] at hstruct
      simp [PreHistory.empty] at hstruct
    · rcases List.mem_cons.1 htail with heq | hnil
      · have : (true : Bool) = false := congrArg (fun t => t.1) heq
        cases this
      · cases hnil

/-! ## Accessibility on the worlds of a history
(paper Lemma 3.4.4 and the transitivity half of Proposition 3.4.5) -/

/-- Paper: Lemma 3.4.4. If `w` is a world of the model (its time weakly precedes the end of time)
and `w' ≪ w`, then the time of `w'` strictly precedes the end of time. -/
theorem accessible_happensBefore_history
    {H : History P Event} {w w' : World P Event}
    (hW : World.time w ⪯ H.val)
    (hAcc : w' ≪ w) :
    World.time w' ≺− H.val := by
  have hstep : World.time w' ≺− World.time w :=
    PreHistory.happensBefore_of_accessible (P := P) (Event := Event) hAcc
  rcases (PreHistory.happensBeforeEq_iff
      (P := P) (Event := Event) (World.time w) H.val).1 hW with hlt | heq
  · exact History.isElementTransitive H _ _ hstep hlt
  · rw [heq] at hstep
    exact hstep

/-- Paper: Proposition 3.4.5 (transitivity). Accessibility is transitive on the worlds of a history. Together with
`PreHistory.accessible_irrefl` this is the paper's Proposition 3.4.5. -/
theorem accessible_trans
    {H : History P Event} {w w' w'' : World P Event}
    (hW : World.time w ⪯ H.val)
    (h₂ : w'' ≪ w') (h₁ : w' ≪ w) :
    w'' ≪ w := by
  have hbefore : World.time w' ≺− World.time w :=
    PreHistory.happensBefore_of_accessible (P := P) (Event := Event) h₁
  have htrans : isTransitive (World.time w) := by
    rcases (PreHistory.happensBeforeEq_iff
        (P := P) (Event := Event) (World.time w) H.val).1 hW with hlt | heq
    · exact (History.predecessor_data (H := H) hlt).1
    · rw [heq]
      exact History.transitive H
  have hsub : World.time w' ⊆ World.time w := htrans _ hbefore
  have hmem : w'' ∈ World.time w' := by
    simpa [World.accessible] using h₂
  have hmem' : w'' ∈ World.time w := hsub _ hmem
  simpa [World.accessible] using hmem'

/-- Paper: Definition 3.4.9(2) (H sequential). A whole time is sequential when all of its event-tuples are linearly
ordered by accessibility, regardless of place. -/
def isSequentialAll (h : PreHistory P Event) : Prop :=
  ∀ t₁ t₂ : World P Event,
    t₁ ∈ h → t₂ ∈ h →
      (t₁ ≪ t₂ ∨ t₂ ≪ t₁ ∨ t₁ = t₂)
