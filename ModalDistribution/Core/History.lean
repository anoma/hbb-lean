import ModalDistribution.Core.Prehistory

open scoped PreHistory
open Set

/-!
# History structures

A history structure (paper Definition 2.3.5) is a hereditarily transitive
prehistory: every prehistory reachable from it by `≺−` contains the
prehistories of its own members.

## Main definitions

* `IsTransitive`, `IsHereditarilyTransitive` and `History P Event`.
* `IsElementTransitive`, the weaker alternative of paper Definition 2.3.11.
* `History.TransitiveSubset` (`⊆trn`): inclusion of a hereditarily transitive
  prehistory.
* `IsSequential` and `IsSequentialAll` (paper Definition 3.4.9).

## Main results

* `exists_isElementTransitive_not_isTransitive`: element-transitivity is
  strictly weaker than transitivity (paper Lemma 2.3.12).
* `accessible_trans`: accessibility is transitive on the worlds of a history
  (paper Proposition 3.4.5).
-/

universe u v

variable {P : Type u} {Event : Type v}

/-- Paper: Definition 2.3.2 (transitive prehistories). A prehistory is
transitive when it includes every prehistory that is element-of it. -/
def IsTransitive (h : PreHistory P Event) : Prop :=
  ∀ h' : PreHistory P Event, h' ≺− h → h' ⊆ h

/-- Paper: Definition 2.3.5. A prehistory is hereditarily transitive when it
is transitive and so is everything element-of it, recursively. This is a
definition by well-founded recursion on `≺−`. -/
noncomputable def IsHereditarilyTransitive : PreHistory P Event → Prop :=
  PreHistory.happensBefore_wellFounded.fix
    (fun h rec =>
      IsTransitive h ∧
      ∀ h' : PreHistory P Event,
        ∀ h_before : h' ≺− h, rec h' h_before)

/-- The defining equation of `IsHereditarilyTransitive`. -/
theorem isHereditarilyTransitive_unfold (h : PreHistory P Event) :
  IsHereditarilyTransitive h ↔
    IsTransitive h ∧
    ∀ h' : PreHistory P Event,
      ∀ _ : h' ≺− h, IsHereditarilyTransitive h' := by
  rw [IsHereditarilyTransitive, WellFounded.fix_eq]

/-- A hereditarily transitive prehistory is transitive. -/
theorem IsHereditarilyTransitive.trans
    {h : PreHistory P Event} :
    IsHereditarilyTransitive h → IsTransitive h := fun hh =>
  ((isHereditarilyTransitive_unfold h).1 hh).1

/-- Hereditary transitivity passes to everything element-of the prehistory. -/
theorem IsHereditarilyTransitive.desc
    {h h' : PreHistory P Event}
    (hh : IsHereditarilyTransitive h)
    (hb : h' ≺− h) :
    IsHereditarilyTransitive h' :=
  ((isHereditarilyTransitive_unfold h).1 hh).2 h' hb

/-- Paper: Definition 2.3.5 (history structures). Histories are the
hereditarily transitive prehistories. -/
structure History (P : Type u) (Event : Type v) where
  /-- The underlying prehistory. -/
  val : PreHistory P Event
  /-- The prehistory is hereditarily transitive. -/
  hered : IsHereditarilyTransitive val

namespace History

instance : Coe (History P Event) (PreHistory P Event) := ⟨History.val⟩

/-- A history is transitive. -/
theorem transitive (h : History P Event) : IsTransitive h.val :=
  h.hered.trans

/-- A history is hereditarily transitive. -/
theorem hereditarily_transitive (h : History P Event) : IsHereditarilyTransitive h.val :=
  h.hered

/-- A history includes everything element-of it. -/
theorem subset_of_happensBefore {H : History P Event} {h' : PreHistory P Event}
    (h_before : h' ≺− H.val) : h' ⊆ H.val :=
  H.transitive h' h_before

/-- Everything element-of a history is transitive and hereditarily transitive. -/
theorem predecessor_data {H : History P Event} {h' : PreHistory P Event}
    (h_before : h' ≺− H.val) :
    IsTransitive h' ∧ IsHereditarilyTransitive h' :=
  ⟨(H.hered.desc h_before).trans, H.hered.desc h_before⟩

/-- Everything weakly before a history is hereditarily transitive. -/
theorem isHereditarilyTransitive_of_happensBeforeEq {H : History P Event}
    {h : PreHistory P Event} (hle : h ⪯ H.val) : IsHereditarilyTransitive h := by
  rcases hle with hBefore | rfl
  · exact H.hered.desc hBefore
  · exact H.hered

/-- A prehistory element-of a history, packaged as a history. -/
def predecessorHistory {H : History P Event} {h' : PreHistory P Event}
    (h_before : h' ≺− H.val) : History P Event :=
  { val := h'
    hered := H.hered.desc h_before }

/-- A predecessor history is included in the history it precedes. -/
theorem predecessorHistory_subset {H : History P Event}
    {h' : PreHistory P Event} (h_before : h' ≺− H.val) :
    (predecessorHistory (H := H) h_before).val ⊆ H.val :=
  subset_of_happensBefore h_before

/-- Transitive inclusion (`⊆trn`): `h1 ⊆ h2` and `h1` is hereditarily
transitive. -/
def TransitiveSubset (h1 h2 : PreHistory P Event) : Prop :=
  h1 ⊆ h2 ∧ IsHereditarilyTransitive h1

infixl:50 " ⊆trn " => TransitiveSubset

/-- A transitive inclusion is an inclusion. -/
theorem transitiveSubset_subset {h₁ h₂ : PreHistory P Event}
    (h : h₁ ⊆trn h₂) : h₁ ⊆ h₂ :=
  h.1

/-- An inclusion of a hereditarily transitive prehistory is a transitive
inclusion. -/
theorem transitiveSubset_of_subset
    {h₁ h₂ : PreHistory P Event}
    (hsubset : h₁ ⊆ h₂)
    (hhered : IsHereditarilyTransitive (P := P) (Event := Event) h₁) :
    h₁ ⊆trn h₂ :=
  ⟨hsubset, hhered⟩

/-- Between histories, element-of implies transitive inclusion. -/
theorem happensBefore_implies_transitiveSubset (h1 h2 : History P Event) :
    h1.val ≺− h2.val → h1.val ⊆trn h2.val := fun h_before =>
  ⟨subset_of_happensBefore h_before, h1.hered⟩

/-- A history is a transitive subset of itself. -/
theorem transitiveSubset_refl (H : History P Event) :
    H.val ⊆trn H.val :=
  ⟨PreHistory.subset_refl H.val, H.hered⟩

end History

/-- The prehistory of a member is element-of the prehistory containing it. -/
theorem History.happensBefore_of_mem {H : PreHistory P Event} {e : World P Event}
    (he : e ∈ H) :
    e.2.2 ≺− H :=
  ⟨e.1, e.2.1, he⟩

/-! ## Element-transitivity (paper Definition 2.3.11 and Lemma 2.3.12) -/

/-- Paper: Definition 2.3.11 (element-transitive). A prehistory is
element-transitive when `≺−` is transitive into it. This is strictly weaker
than `IsTransitive`. -/
def IsElementTransitive (h : PreHistory P Event) : Prop :=
  ∀ h'' h' : PreHistory P Event, h'' ≺− h' → h' ≺− h → h'' ≺− h

/-- Paper: Lemma 2.3.12(1). Transitive prehistories are element-transitive. -/
theorem IsTransitive.isElementTransitive {h : PreHistory P Event}
    (ht : IsTransitive h) : IsElementTransitive h :=
  fun _ h' ⟨p, x, hmem⟩ h'h => ⟨p, x, ht h' h'h _ hmem⟩

/-- Paper: Lemma 2.3.12(3). Every history structure is element-transitive. -/
theorem History.isElementTransitive (H : History P Event) :
    IsElementTransitive H.val :=
  H.transitive.isElementTransitive

/-- Paper: Lemma 2.3.12(2). An element-transitive prehistory need not be
transitive. The witness is the paper's `H₂ = {(p, †, H₁), (q, †, ∅)}` with
`H₁ = {(p, †, ∅)}`. -/
theorem exists_isElementTransitive_not_isTransitive :
    ∃ h : PreHistory Bool Empty,
      IsElementTransitive h ∧ ¬ IsTransitive h := by
  let H₁ : PreHistory Bool Empty := .mk [(true, †, .empty)]
  let H₂ : PreHistory Bool Empty := .mk [(true, †, H₁), (false, †, .empty)]
  refine ⟨H₂, ?_, ?_⟩
  · -- The member prehistories of `H₂` are `H₁` and `∅`; the only member
    -- prehistory of `H₁` is `∅`, which is also a member prehistory of `H₂`.
    rintro h'' h' ⟨_, _, hmem''⟩ ⟨_, _, hmem'⟩
    rcases List.mem_cons.1 hmem' with h | h
    · cases h
      rcases List.mem_singleton.1 hmem'' with ⟨⟩
      exact ⟨false, †, List.mem_cons_of_mem _ List.mem_cons_self⟩
    · rcases List.mem_singleton.1 h with ⟨⟩
      cases hmem''
  · -- `H₁ ≺− H₂`, but the member `(p, †, ∅)` of `H₁` is not a member of `H₂`.
    intro ht
    have hmem := ht H₁ ⟨true, †, List.mem_cons_self⟩ (true, †, .empty) List.mem_cons_self
    rcases List.mem_cons.1 hmem with h | h
    · simp [H₁, PreHistory.empty] at h
    · rcases List.mem_singleton.1 h with ⟨⟩

/-! ## Initial and final event-tuples (paper Definition 2.3.13) -/

namespace History

/-- Paper: Definition 2.3.13(2). A globally initial event-tuple. -/
def IsInitialTuple (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ ¬ ∃ H' : PreHistory P Event, H' ≺− t.2.2

/-- Paper: Definition 2.3.13(3). A globally final event-tuple. -/
def IsFinalTuple (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ ¬ ∃ H' : PreHistory P Event, t.2.2 ≺− H'

/-- Paper: Definition 2.3.13(2). `(p, E, H)` is `p`-initial when no earlier `p`-event exists. -/
def IsInitialAt (p : P) (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ World.place t = p ∧
    ¬ ∃ t' : World P Event,
        t' ∈ H ∧ World.place t' = p ∧ World.time t' ≺− World.time t

/-- Paper: Definition 2.3.13(3). `(p, E, H)` is `p`-final when no later `p`-event exists. -/
def IsFinalAt (p : P) (t : World P Event) (H : PreHistory P Event) : Prop :=
  t ∈ H ∧ World.place t = p ∧
    ¬ ∃ t' : World P Event,
        t' ∈ H ∧ World.place t' = p ∧ World.time t ≺− World.time t'

end History

/-! ## Accessibility on the worlds of a history
(paper Lemma 3.4.4 and the transitivity half of Proposition 3.4.5) -/

/-- Paper: Lemma 3.4.4. If `w` is a world of the model (its time weakly precedes the end of time)
and `w' ≪ w`, then the time of `w'` strictly precedes the end of time. -/
theorem accessible_happensBefore_history
    {H : History P Event} {w w' : World P Event}
    (hW : World.time w ⪯ H.val)
    (hAcc : w' ≪ w) :
    World.time w' ≺− H.val := by
  rcases hW with hlt | heq
  · exact H.isElementTransitive _ _ (PreHistory.happensBefore_of_accessible hAcc) hlt
  · exact heq ▸ PreHistory.happensBefore_of_accessible hAcc

/-- Paper: Proposition 3.4.5 (transitivity). Accessibility is transitive on the worlds of a history.
Together with `PreHistory.accessible_irrefl` this is the paper's Proposition 3.4.5. -/
theorem accessible_trans
    {H : History P Event} {w w' w'' : World P Event}
    (hW : World.time w ⪯ H.val)
    (h₂ : w'' ≪ w') (h₁ : w' ≪ w) :
    w'' ≪ w :=
  -- `w.time` is transitive, so it includes `w'.time`, which contains `w''`.
  (History.isHereditarilyTransitive_of_happensBeforeEq hW).trans _
    (PreHistory.happensBefore_of_accessible h₁) w'' h₂

/-! ## Sequentiality (paper Definition 3.4.9) -/

/-- Paper: Definition 3.4.9(1) (p sequential at H). Participant `p` is sequential in `h` when its
event-tuples are linearly ordered by accessibility. -/
def IsSequential (p : P) (h : PreHistory P Event) : Prop :=
  ∀ t₁ t₂ : World P Event,
    t₁ ∈ h →
    t₂ ∈ h →
    World.place t₁ = p →
    World.place t₂ = p →
      (t₁ ≪ t₂ ∨
        t₂ ≪ t₁ ∨
        t₁ = t₂)

/-- Paper: Definition 3.4.9(2) (H sequential). A whole time is sequential when all of its
event-tuples are linearly ordered by accessibility, regardless of place. -/
def IsSequentialAll (h : PreHistory P Event) : Prop :=
  ∀ t₁ t₂ : World P Event,
    t₁ ∈ h → t₂ ∈ h →
      (t₁ ≪ t₂ ∨ t₂ ≪ t₁ ∨ t₁ = t₂)

namespace History

/-- Paper: Proposition 5.1.4 (variant). Sequentiality passes to transitive
subsets: their event-tuples at `p` are event-tuples at `p` of the larger
history. -/
theorem sequentiality_monotone (p : P) (h h' : History P Event) :
    h' ⊆trn h.val →
    IsSequential p h.val →
    IsSequential p h'.val := fun hsub hseq t₁ t₂ ht₁ ht₂ =>
  hseq t₁ t₂ (hsub.1 _ ht₁) (hsub.1 _ ht₂)

/-- Sequentiality passes to everything element-of a history. -/
theorem sequentiality_of_predecessor {p : P} {H : History P Event}
    {h' : PreHistory P Event}
    (h_before : h' ≺− H.val)
    (hseq : IsSequential (P := P) (Event := Event) p H.val) :
    IsSequential p h' := fun t₁ t₂ ht₁ ht₂ =>
  hseq t₁ t₂ (subset_of_happensBefore h_before _ ht₁)
    (subset_of_happensBefore h_before _ ht₂)

end History
