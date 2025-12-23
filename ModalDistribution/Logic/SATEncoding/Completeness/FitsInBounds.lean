import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly

/-!
# Bounded Model Definition for Completeness

This file defines what it means for a semantic model to "fit within bounds" - the precondition
for the completeness theorem. We also define the EncodingView structure that provides the
witnesses needed to construct an assignment from a model.

## Main Definitions

- `reachablePreHistories`: The set of prehistories reachable from a root via happens-before
- `rankPre`: Well-founded rank of a prehistory (for termination/fuel alignment)
- `EncodingView`: Witnesses for indexing (time, event, predicate, value)
- `FitsInBounds`: A model fits within the given bounds

## Design Notes

The key insight is that completeness requires:
1. All reachable prehistories can be assigned distinct time indices
2. The happens-before relation is captured by strict ordering on indices
3. All semantic events, predicates, and values are enumerated in bounds

We use `histEq` (extensional equality) throughout rather than definitional equality,
since the decoder produces prehistories with potentially different list orderings.

## References

- Completeness/Main.lean for the main theorem
- Completeness/AssignmentOf.lean for the encoder construction
-/

open ModalDistribution Encoding
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Reachable Prehistories

The set of prehistories reachable from a root via the happens-before relation.
This is finite by well-foundedness of ≺−. -/

variable {P Event : Type*}

/-- Collect all prehistories reachable from `h` via happens-before, including `h` itself.
    This is well-founded because `≺−` is well-founded. -/
noncomputable def reachablePreHistories (h : PreHistory P Event) : Set (PreHistory P Event) :=
  { h' | PreHistory.happensBeforeEq h' h } ∪
  (⋃ w ∈ h, reachablePreHistories w.time)
termination_by PreHistory.height h
decreasing_by
  simp_wf
  exact PreHistory.height_of_mem ‹_›

/-- A prehistory is in its own reachable set. -/
lemma self_mem_reachablePreHistories (h : PreHistory P Event) :
    h ∈ reachablePreHistories h := by
  unfold reachablePreHistories
  left
  exact PreHistory.happensBeforeEq_refl h

/-- Predecessors are in the reachable set. -/
lemma happensBefore_mem_reachablePreHistories {h h' : PreHistory P Event}
    (hBefore : h' ≺− h) :
    h' ∈ reachablePreHistories h := by
  unfold reachablePreHistories
  left
  exact Or.inl hBefore

/-- World times in a reachable prehistory are also reachable. -/
lemma time_mem_reachablePreHistories {h : PreHistory P Event}
    {w : World P Event} (hw : w ∈ h) :
    w.time ∈ reachablePreHistories h := by
  unfold reachablePreHistories
  right
  simp only [Set.mem_iUnion]
  exact ⟨w, hw, self_mem_reachablePreHistories w.time⟩

/-- Helper for reachability transitivity in Histories. -/
lemma time_mem_reachablePreHistories_of_mem_history_aux
    (rootPre : PreHistory P Event)
    (rootHered : isHereditarilyTransitive rootPre)
    {h' : PreHistory P Event} {w : World P Event}
    (hReach : h' ∈ reachablePreHistories rootPre)
    (hw : w ∈ h') :
    w.time ∈ reachablePreHistories rootPre := by
  -- Induction on rootPre's height using well-founded recursion
  induction rootPre using (PreHistory.happensBefore_wellFounded (P := P) (Event := Event)).induction
      generalizing h' with
  | _ rootPre ih =>
    unfold reachablePreHistories at hReach
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion] at hReach
    cases hReach with
    | inl hBeforeEq =>
      rw [PreHistory.happensBeforeEq_iff] at hBeforeEq
      cases hBeforeEq with
      | inl hBefore =>
        -- h' ≺− rootPre, so h' ⊆ rootPre by transitivity
        -- and w ∈ h' implies w ∈ rootPre
        let rootHist : History P Event := ⟨rootPre, rootHered⟩
        have hSubset : h' ⊆ rootPre := History.subset_of_happensBefore (H := rootHist) hBefore
        have hwInRoot := hSubset w hw
        have hwTime := History.happensBefore_of_mem hwInRoot
        exact happensBefore_mem_reachablePreHistories hwTime
      | inr hEq =>
        rw [hEq] at hw
        have hwTime := History.happensBefore_of_mem hw
        exact happensBefore_mem_reachablePreHistories hwTime
    | inr hInUnion =>
      obtain ⟨w', hw'Mem, hReach'⟩ := hInUnion
      have hHB : w'.time ≺− rootPre := History.happensBefore_of_mem hw'Mem
      -- w'.time is a prehistory that happens-before rootPre
      -- By predecessor_data, w'.time is also hereditarily transitive
      let rootHist : History P Event := ⟨rootPre, rootHered⟩
      have ⟨_, hHered'⟩ := History.predecessor_data (H := rootHist) hHB
      have hxFromW' : w.time ∈ reachablePreHistories w'.time := ih w'.time hHB hHered' hReach' hw
      -- Now show w.time reachable from root given w.time reachable from w'.time and w' ∈ root
      unfold reachablePreHistories
      right
      simp only [Set.mem_iUnion]
      exact ⟨w', hw'Mem, hxFromW'⟩

/-- If h' is reachable from root and w ∈ h', then w.time is reachable from root.
    The proof exploits that root is a History (hereditarily transitive), so predecessors
    are subsets, enabling transitivity of happens-before. -/
lemma time_mem_reachablePreHistories_of_mem_history
    {root : History P Event}
    {h' : PreHistory P Event} {w : World P Event}
    (hReach : h' ∈ reachablePreHistories root.val)
    (hw : w ∈ h') :
    w.time ∈ reachablePreHistories root.val :=
  time_mem_reachablePreHistories_of_mem_history_aux root.val root.hered hReach hw

/-- Prehistories reachable from a history are hereditarily transitive.
    This is proven by induction on the root history's height. -/
lemma hereditarilyTransitive_of_reachable_aux
    (rootPre : PreHistory P Event)
    (rootHered : isHereditarilyTransitive rootPre)
    {h' : PreHistory P Event}
    (hReach : h' ∈ reachablePreHistories rootPre) :
    isHereditarilyTransitive h' := by
  induction rootPre using (PreHistory.happensBefore_wellFounded (P := P) (Event := Event)).induction
      generalizing h' with
  | _ rootPre ih =>
    unfold reachablePreHistories at hReach
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion] at hReach
    cases hReach with
    | inl hBeforeEq =>
      rw [PreHistory.happensBeforeEq_iff] at hBeforeEq
      cases hBeforeEq with
      | inl hBefore =>
        -- h' ≺− rootPre, use rootHered's desc
        exact isHereditarilyTransitive.desc (P := P) (Event := Event) rootHered hBefore
      | inr hEq =>
        rw [hEq]; exact rootHered
    | inr hInUnion =>
      obtain ⟨w', hw'Mem, hReach'⟩ := hInUnion
      have hHB : w'.time ≺− rootPre := History.happensBefore_of_mem hw'Mem
      let rootHist : History P Event := ⟨rootPre, rootHered⟩
      have ⟨_, hHered'⟩ := History.predecessor_data (H := rootHist) hHB
      exact ih w'.time hHB hHered' hReach'

/-- Prehistories reachable from a history are hereditarily transitive. -/
lemma hereditarilyTransitive_of_reachable
    {root : History P Event}
    {h' : PreHistory P Event}
    (hReach : h' ∈ reachablePreHistories root.val) :
    isHereditarilyTransitive h' :=
  hereditarilyTransitive_of_reachable_aux root.val root.hered hReach

/-- Package a reachable prehistory as a History. -/
noncomputable def historyOfReachable
    {root : History P Event}
    {h' : PreHistory P Event}
    (hReach : h' ∈ reachablePreHistories root.val) : History P Event :=
  ⟨h', hereditarilyTransitive_of_reachable hReach⟩

/-! ## Rank Function

We use `PreHistory.height` as our rank function for prehistories.
This measure strictly decreases along happens-before (already proven in Core.Prehistory). -/

/-- Rank of a prehistory for fuel alignment. We use `height` which is already proven
    to strictly decrease along happens-before. -/
abbrev rankPre (h : PreHistory P Event) : ℕ := PreHistory.height h

/-- The rank of empty prehistory is 1 (base height). -/
lemma rankPre_empty : rankPre (P := P) (Event := Event) PreHistory.empty = 1 :=
  PreHistory.height_empty

/-- Rank strictly decreases along happens-before. -/
lemma rankPre_lt_of_happensBefore {h h' : PreHistory P Event}
    (hBefore : h' ≺− h) :
    rankPre h' < rankPre h :=
  PreHistory.height_lt_of_happensBefore hBefore

/-! ## Encoding View

The EncodingView bundles all the indexing functions needed to construct an assignment
from a semantic model. These are witnesses that the model fits within bounds. -/

/-- An encoding view provides indexing functions from semantic objects to bound indices.
    This is the data needed to construct `assignmentOf`. -/
structure EncodingView (b : Bounds S) (M : Model S (Fin b.nParticipants)) where
  /-- Map reachable prehistories to time indices. -/
  timeIndexOf : PreHistory (Fin b.nParticipants) (Signature.EventType S) → b.times

  /-- The root prehistory maps to the root time index. -/
  timeIndex_root : timeIndexOf M.history.val = b.root

  /-- Time indexing is injective on reachable prehistories. -/
  timeIndex_inj :
    ∀ {h₁ h₂ : PreHistory (Fin b.nParticipants) (Signature.EventType S)},
      h₁ ∈ reachablePreHistories M.history.val →
      h₂ ∈ reachablePreHistories M.history.val →
      timeIndexOf h₁ = timeIndexOf h₂ → h₁ = h₂

  /-- Time indexing respects happens-before (strict order). -/
  timeIndex_hb :
    ∀ {h h' : PreHistory (Fin b.nParticipants) (Signature.EventType S)},
      h' ≺− h →
      h' ∈ reachablePreHistories M.history.val →
      h ∈ reachablePreHistories M.history.val →
      (timeIndexOf h').val < (timeIndexOf h).val

  /-- Map maybe-events to event selector indices. -/
  evSelOf : MaybeEvent (Signature.EventType S) → b.evIx

  /-- Event selector maps † to index 0. -/
  evSel_none : evSelOf MaybeEvent.none = ⟨0, Nat.zero_lt_succ _⟩

  /-- Event selector round-trips correctly. -/
  evSel_spec :
    ∀ e : MaybeEvent (Signature.EventType S),
      b.decodeMaybeEvent (evSelOf e) = e

  /-- Map atomic predicates to predicate indices. -/
  predIxOf : Signature.AtomicPredType S → b.predIx

  /-- Predicate indexing round-trips correctly. -/
  pred_spec :
    ∀ P : Signature.AtomicPredType S,
      b.preds.get (predIxOf P) = P

  /-- Map values to value indices. -/
  valIxOf : S.Value → b.valIx

  /-- Value indexing round-trips correctly. -/
  val_spec :
    ∀ v : S.Value, b.values.get (valIxOf v) = v

/-! ## FitsInBounds

The main predicate: a model fits within bounds if we can construct an EncodingView
for it and it satisfies additional structural requirements. -/

/-- A model M fits within bounds b if:
    1. There exists an encoding view (indexing functions)
    2. The history depth (rank) fits within nTimes

    Note: No global sequentiality requirement is needed. The `cnfSeq` encoding uses only
    conditional clauses, so models can have non-sequential participants. -/
structure FitsInBounds (b : Bounds S) (M : Model S (Fin b.nParticipants)) where
  /-- Encoding view providing indexing functions. -/
  view : EncodingView b M

  /-- The history rank fits within nTimes (needed for fuel alignment). -/
  height_bound : rankPre M.history.val < b.nTimes

/-! ## Helper: Inverse Time Index Lookup

Given a time index, find the corresponding semantic prehistory (if reachable). -/

/-- Look up the prehistory at a given time index using the encoding view.
    Returns the prehistory that maps to this index, or empty if not found. -/
noncomputable def prehistoryAt
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (ti : b.times) :
    PreHistory (Fin b.nParticipants) (Signature.EventType S) := by
  classical
  exact if h : ∃ H ∈ reachablePreHistories M.history.val, ev.timeIndexOf H = ti then
    Classical.choose h
  else
    PreHistory.empty

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If ti is the index of a reachable prehistory H, then prehistoryAt returns H. -/
lemma prehistoryAt_of_reachable
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    {H : PreHistory (Fin b.nParticipants) (Signature.EventType S)}
    (hReach : H ∈ reachablePreHistories M.history.val) :
    prehistoryAt ev (ev.timeIndexOf H) = H := by
  unfold prehistoryAt
  have hExists : ∃ H' ∈ reachablePreHistories M.history.val,
      ev.timeIndexOf H' = ev.timeIndexOf H := by
    exact ⟨H, hReach, rfl⟩
  simp only [hExists, ↓reduceDIte]
  have hChoose := Classical.choose_spec hExists
  obtain ⟨hReach', hEq⟩ := hChoose
  exact ev.timeIndex_inj hReach' hReach hEq

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If prehistoryAt returns a nonempty result, timeIndexOf maps it back to the original index. -/
lemma timeIndexOf_prehistoryAt
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (ti : b.times)
    (hNonempty : ∃ w, w ∈ prehistoryAt ev ti) :
    ev.timeIndexOf (prehistoryAt ev ti) = ti := by
  classical
  unfold prehistoryAt at hNonempty ⊢
  by_cases h : ∃ H ∈ reachablePreHistories M.history.val, ev.timeIndexOf H = ti
  · simp only [h, ↓reduceDIte]
    have hSpec := Classical.choose_spec h
    exact hSpec.2
  · simp only [h, ↓reduceDIte] at hNonempty
    obtain ⟨w, hwMem⟩ := hNonempty
    exact absurd hwMem PreHistory.not_mem_empty

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The root prehistory is at the root time index. -/
lemma prehistoryAt_root
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M) :
    prehistoryAt ev b.root = M.history.val := by
  classical
  have hRoot := ev.timeIndex_root
  have hReach := self_mem_reachablePreHistories M.history.val
  conv_rhs => rw [← prehistoryAt_of_reachable ev hReach]
  congr 1
  exact hRoot.symm

/-! ## Constructing EncodingView from Complete Bounds

When bounds enumerate all values/events/predicates (via values_complete, events_complete),
we can construct the encoding functions directly. -/

/-- Construct evSelOf using encodeMaybeEvent from Bounds. -/
noncomputable def mkEvSelOf (b : Bounds S) : MaybeEvent (Signature.EventType S) → b.evIx :=
  b.encodeMaybeEvent

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkEvSelOf maps † to 0. -/
lemma mkEvSelOf_none (b : Bounds S) : mkEvSelOf b MaybeEvent.none = ⟨0, Nat.zero_lt_succ _⟩ := by
  unfold mkEvSelOf Bounds.encodeMaybeEvent
  rfl

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkEvSelOf round-trips correctly (uses events_complete). -/
lemma mkEvSelOf_spec (b : Bounds S) (e : MaybeEvent (Signature.EventType S)) :
    b.decodeMaybeEvent (mkEvSelOf b e) = e := by
  unfold mkEvSelOf
  exact b.decodeMaybeEvent_encodeMaybeEvent e

/-- Construct valIxOf using findValueIndex from Bounds. -/
noncomputable def mkValIxOf (b : Bounds S) : S.Value → b.valIx :=
  b.findValueIndex

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- mkValIxOf round-trips correctly (uses values_complete). -/
lemma mkValIxOf_spec (b : Bounds S) (v : S.Value) : b.values.get (mkValIxOf b v) = v := by
  unfold mkValIxOf
  exact findValueIndex_value b v

end Encoding
