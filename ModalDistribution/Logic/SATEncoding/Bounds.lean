import Mathlib.Data.List.Range
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Finset.Basic
import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic

/-!
# Bounded Model Checking Parameters

This file defines the finite bounds for bounded model checking and the enumeration
of world identifiers.

## Main Definitions

- `Bounds`: Finite parameters for model checking (participants, times, events, etc.)
- `WId`: World identifier as a triple (participant, event index, time index)
- Helper functions for enumerating finite domains using `List.finRange`

## Design Notes

- Time indices represent preprocessed time slices, not the recursive PreHistory structure
- `decodePre` will reconstruct the actual PreHistory from these indices
- All enumerations use `List.finRange` from mathlib for finite types

-/

open ModalDistribution

namespace Encoding

variable {S : Signature}

/-! ## Bounds Structure -/

/-- Finite generation parameters for bounded model checking.
    These bounds determine the search space for the SAT solver. -/
structure Bounds (S : Signature) where
  /-- Number of participants in the system. -/
  nParticipants : Nat
  /-- Number of time steps (preprocessed time slices). -/
  nTimes        : Nat
  /-- Number of event types (excludes †). -/
  nEvents       : Nat
  /-- Enumerated event values. -/
  events        : Vector (Signature.Event S) nEvents
  /-- Number of values in the domain. -/
  nVals         : Nat
  /-- Enumerated values. -/
  values        : Vector (Signature.Value S) nVals
  /-- Number of atomic predicates. -/
  nPreds        : Nat
  /-- Enumerated atomic predicates. -/
  preds         : Vector (Signature.AtomicPred S) nPreds
  /-- Index of the root (final) time. -/
  root          : Fin nTimes
  /-- Positivity constraint: at least one participant for meaningful models. -/
  posParticipants : 0 < nParticipants
  /-- Positivity constraint: at least one time step for meaningful models. -/
  posTimes        : 0 < nTimes
  /-- Positivity constraint: at least one value for meaningful models. -/
  posVals         : 0 < nVals
  /-- Surjectivity of the value enumeration: every semantic value appears in `values`. -/
  values_complete :
    ∀ v : Signature.Value S, ∃ idx : Fin nVals, values.get idx = v
  /-- Surjectivity of the event enumeration: every semantic event appears in `events`. -/
  events_complete :
    ∀ e : Signature.Event S, ∃ idx : Fin nEvents, events.get idx = e
  /-- Injectivity of the event enumeration: no duplicate events in `events`.
      This ensures `decodeMaybeEvent` is injective and the Acc witness encoding is adequate. -/
  events_injective :
    ∀ i j : Fin nEvents, events.get i = events.get j → i = j

namespace Bounds

variable (b : Bounds S)

/-- Finite type of participants. -/
abbrev participants := Fin b.nParticipants

/-- Finite type of time indices. -/
abbrev times := Fin b.nTimes

/-- Finite type of event indices (includes † as index 0). -/
abbrev evIx := Fin (b.nEvents + 1)

/-- Finite type of predicate indices. -/
abbrev predIx := Fin b.nPreds

/-- Finite type of value indices. -/
abbrev valIx := Fin b.nVals

/-- Decode an event index to a `MaybeEvent`.
    Index 0 represents †, subsequent indices represent actual events. -/
def decodeMaybeEvent (ei : b.evIx) : MaybeEvent (Signature.EventType S) :=
  match ei with
  | ⟨0, _⟩ => MaybeEvent.none
  | ⟨Nat.succ k, hk⟩ =>
      let hk' : k < b.nEvents := Nat.lt_of_succ_lt_succ hk
      MaybeEvent.some (b.events.get ⟨k, hk'⟩)

/-- Encode a `MaybeEvent` to an event index.
    Returns 0 for †, and searches for matching events otherwise.
    Non-enumerated events map to 0 (will be handled in adequacy). -/
def encodeMaybeEvent [DecidableEq (Signature.Event S)]
    (E : MaybeEvent (Signature.EventType S)) : b.evIx :=
  match E with
  | .none => ⟨0, Nat.zero_lt_succ _⟩
  | .some e =>
      -- Linear search through enumerated events
      let rec go (i : Nat) (h : i < b.nEvents) : b.evIx :=
        if b.events.get ⟨i, h⟩ = e then
          ⟨i.succ, Nat.succ_lt_succ h⟩
        else
          if h' : i.succ < b.nEvents then
            go i.succ h'
          else
            ⟨0, Nat.zero_lt_succ _⟩
      if h0 : 0 < b.nEvents then
        go 0 h0
      else
        ⟨0, Nat.zero_lt_succ _⟩

/-- Helper: go finds an event that decodes correctly when one exists at index ≥ i. -/
private lemma encodeMaybeEvent_go_spec [DecidableEq (Signature.Event S)]
    (e : Signature.EventType S) (i : Nat) (hi : i < b.nEvents)
    (witnessIdx : Fin b.nEvents) (hWitnessGe : witnessIdx.val ≥ i)
    (hWitnessEq : b.events.get witnessIdx = e) :
    b.decodeMaybeEvent (encodeMaybeEvent.go b e i hi) = MaybeEvent.some e := by
  unfold encodeMaybeEvent.go
  split_ifs with hMatch hNext
  · -- Found match at i
    unfold decodeMaybeEvent
    simp only [MaybeEvent.some.injEq]
    exact hMatch
  · -- Continue searching
    have hWitnessGe' : witnessIdx.val ≥ i.succ := by
      by_cases hEq : witnessIdx.val = i
      · exfalso
        apply hMatch
        rw [← hWitnessEq]
        have : (⟨i, hi⟩ : Fin b.nEvents) = witnessIdx := by ext; exact hEq.symm
        rw [this]
      · omega
    exact encodeMaybeEvent_go_spec e i.succ hNext witnessIdx hWitnessGe' hWitnessEq
  · -- No more elements to check, but we know witnessIdx exists
    exfalso
    have hWitnessLt : witnessIdx.val < b.nEvents := witnessIdx.isLt
    by_cases hEq : witnessIdx.val = i
    · apply hMatch
      rw [← hWitnessEq]
      have : (⟨i, hi⟩ : Fin b.nEvents) = witnessIdx := by ext; exact hEq.symm
      rw [this]
    · omega

/-- Round-trip property: decoding an encoded event recovers the original.
    This relies on `events_complete` to ensure all events are in the enumeration. -/
lemma decodeMaybeEvent_encodeMaybeEvent [DecidableEq (Signature.Event S)]
    (E : MaybeEvent (Signature.EventType S)) :
    b.decodeMaybeEvent (b.encodeMaybeEvent E) = E := by
  cases E with
  | none =>
    unfold encodeMaybeEvent decodeMaybeEvent
    rfl
  | some e =>
    -- Get index from events_complete
    obtain ⟨idx, hIdx⟩ := b.events_complete e
    unfold encodeMaybeEvent
    have h0 : 0 < b.nEvents := Nat.lt_of_le_of_lt (Nat.zero_le _) idx.isLt
    simp only [h0, ↓reduceDIte]
    exact encodeMaybeEvent_go_spec b e 0 h0 idx (Nat.zero_le _) hIdx

/-- Injectivity of `decodeMaybeEvent`: distinct event indices decode to distinct `MaybeEvent`s.
    This relies on `events_injective` to ensure the underlying event vector has no duplicates. -/
lemma decodeMaybeEvent_injective (ei₁ ei₂ : b.evIx)
    (h : b.decodeMaybeEvent ei₁ = b.decodeMaybeEvent ei₂) : ei₁ = ei₂ := by
  -- Case split on both event indices based on whether they are 0 or succ
  rcases ei₁ with ⟨n₁, hn₁⟩
  rcases ei₂ with ⟨n₂, hn₂⟩
  match n₁, n₂ with
  | 0, 0 => rfl
  | 0, Nat.succ k₂ =>
    -- decodeMaybeEvent ⟨0, _⟩ = .none, decodeMaybeEvent ⟨k₂+1, _⟩ = .some _
    unfold decodeMaybeEvent at h
    exact absurd h MaybeEvent.noConfusion
  | Nat.succ k₁, 0 =>
    -- decodeMaybeEvent ⟨k₁+1, _⟩ = .some _, decodeMaybeEvent ⟨0, _⟩ = .none
    unfold decodeMaybeEvent at h
    exact absurd h MaybeEvent.noConfusion
  | Nat.succ k₁, Nat.succ k₂ =>
    -- Both are .some, extract event equality
    unfold decodeMaybeEvent at h
    simp only [MaybeEvent.some.injEq] at h
    -- h : events[k₁] = events[k₂]
    have hk₁' : k₁ < b.nEvents := Nat.lt_of_succ_lt_succ hn₁
    have hk₂' : k₂ < b.nEvents := Nat.lt_of_succ_lt_succ hn₂
    have hInjIdx : (⟨k₁, hk₁'⟩ : Fin b.nEvents) = ⟨k₂, hk₂'⟩ := b.events_injective _ _ h
    simp only [Fin.mk.injEq] at hInjIdx
    -- hInjIdx : k₁ = k₂
    simp only [Fin.mk.injEq, Nat.succ_inj]
    exact hInjIdx

/-- Find the index of a predicate in the enumerated predicate vector.
    Returns none if the predicate is not enumerated.
    Used for encoding Formula.predicate atoms. -/
def findPredIndex [DecidableEq (Signature.AtomicPred S)]
    (pred : Signature.AtomicPredType S) : Option b.predIx :=
  (List.finRange b.nPreds).find? (fun k => b.preds.get k = pred)

/-- Find the index of an event in the enumerated event vector.
    Returns none if the event is not enumerated.
    Used for encoding Formula.event atoms. -/
def findEventIndex [DecidableEq (Signature.Event S)]
    (evt : Signature.EventType S) : Option (Fin b.nEvents) :=
  (List.finRange b.nEvents).find? (fun k => b.events.get k = evt)

/-- Find the index of a value in the bounds vector.
    Returns the first value index if not found (which cannot happen under `values_complete`). -/
def findValueIndex [DecidableEq S.Value] (v : Signature.Value S) : b.valIx :=
  match (List.finRange b.nVals).find? (fun i => b.values.get i = v) with
  | some idx => idx
  | none => ⟨0, b.posVals⟩

/-! ## Canonical First Elements -/

/-- Canonical first participant (index 0).
    Uses positivity constraint to construct the Fin value. -/
def firstParticipant : b.participants := ⟨0, b.posParticipants⟩

/-- Canonical first time (index 0).
    Uses positivity constraint to construct the Fin value. -/
def firstTime : b.times := ⟨0, b.posTimes⟩

/-- Canonical first value index (index 0).
    Uses positivity constraint to construct the Fin value. -/
def firstValIx : b.valIx := ⟨0, b.posVals⟩

/-! ## Convenient Enumerations -/

/-- Enumerate all participants as a list. -/
def partsL : List b.participants :=
  List.finRange b.nParticipants

/-- Enumerate all time indices as a list. -/
def timesL : List b.times :=
  List.finRange b.nTimes

/-- Enumerate all event indices (including †) as a list. -/
def evIxL : List b.evIx :=
  List.finRange (b.nEvents + 1)

/-- Enumerate all predicate indices as a list. -/
def predIxL : List b.predIx :=
  List.finRange b.nPreds

/-- Enumerate all value indices as a list. -/
def valIxL : List b.valIx :=
  List.finRange b.nVals

end Bounds

/-! ## World Identifiers -/

/-- World identifier: a triple of (participant, event index, time index).
    Represents all possible worlds in the bounded search space. -/
structure WId (b : Bounds S) where
  /-- Participant component. -/
  p : b.participants
  /-- Event index component (0 = †, >0 = actual event). -/
  ei : b.evIx
  /-- Time index component (preprocessed time slice). -/
  ti : b.times
deriving DecidableEq, Repr

namespace WId

variable {b : Bounds S}

/-- Enumerate all possible world identifiers.
    Total count: nParticipants × (nEvents + 1) × nTimes. -/
def allWorlds (b : Bounds S) : List (WId b) :=
  (Bounds.partsL b).flatMap fun p =>
    (Bounds.evIxL b).flatMap fun ei =>
      (Bounds.timesL b).map fun ti =>
        { p, ei, ti : WId b }

/-- The number of worlds is the product of the three dimensions. -/
theorem allWorlds_length (b : Bounds S) :
    (allWorlds b).length = b.nParticipants * (b.nEvents + 1) * b.nTimes := by
  unfold allWorlds Bounds.partsL Bounds.evIxL Bounds.timesL
  -- Helper lemma: flatMap over lists with constant inner length multiplies lengths.
  have length_flatMap_const :
      ∀ {α β : Type} (l : List α) (f : α → List β) (n : Nat),
        (∀ x, (f x).length = n) →
        (l.flatMap f).length = l.length * n := by
    intro α β l
    induction l with
    | nil =>
        intro f n _
        simp
    | cons x xs ih =>
        intro f n h
        have hx : (f x).length = n := h x
        have hx' : (List.flatMap f xs).length = xs.length * n := ih f n h
        have hx_sum :
            (List.map (List.length ∘ f) xs).sum = xs.length * n := by
          simpa [List.length_flatMap] using hx'
        simp [List.flatMap, hx, hx_sum, Nat.succ_mul, Nat.add_comm]
  -- Length of the innermost map does not depend on `p` or `ei`.
  have innerLen :
      ∀ (p : Fin b.nParticipants) (ei : Fin (b.nEvents + 1)),
        ((List.finRange b.nTimes).map fun ti => { p, ei, ti : WId b }).length = b.nTimes := by
    intro p ei
    simp
  -- FlatMap over events multiplies by `b.nEvents + 1`.
  have midLen :
      ∀ p : Fin b.nParticipants,
        ((List.finRange (b.nEvents + 1)).flatMap fun ei =>
            (List.finRange b.nTimes).map fun ti => { p, ei, ti : WId b }).length
          = (b.nEvents + 1) * b.nTimes := by
    intro p
    have h := length_flatMap_const
      (l := List.finRange (b.nEvents + 1))
      (f := fun ei => (List.finRange b.nTimes).map fun ti => { p, ei, ti : WId b })
      (n := b.nTimes)
      (by
        intro ei
        exact innerLen p ei)
    calc
      ((List.finRange (b.nEvents + 1)).flatMap fun ei =>
          (List.finRange b.nTimes).map fun ti => { p, ei, ti : WId b }).length
          = (List.finRange (b.nEvents + 1)).length * b.nTimes := h
      _ = (b.nEvents + 1) * b.nTimes := by
        simp [List.length_finRange]
  -- FlatMap over participants multiplies by `b.nParticipants`.
  have outerLen :
      ((List.finRange b.nParticipants).flatMap fun p =>
          (List.finRange (b.nEvents + 1)).flatMap fun ei =>
            (List.finRange b.nTimes).map fun ti => { p, ei, ti : WId b }).length
        = b.nParticipants * ((b.nEvents + 1) * b.nTimes) := by
    have h := length_flatMap_const
      (l := List.finRange b.nParticipants)
      (f := fun p =>
        (List.finRange (b.nEvents + 1)).flatMap fun ei =>
          (List.finRange b.nTimes).map fun ti => { p, ei, ti : WId b })
      (n := (b.nEvents + 1) * b.nTimes)
      (by
        intro p
        exact midLen p)
    calc
      ((List.finRange b.nParticipants).flatMap fun p =>
        (List.finRange (b.nEvents + 1)).flatMap fun ei =>
          (List.finRange b.nTimes).map fun ti => { p, ei, ti : WId b }).length
        = (List.finRange b.nParticipants).length * ((b.nEvents + 1) * b.nTimes) := h
      _ = b.nParticipants * ((b.nEvents + 1) * b.nTimes) := by
        simp [List.length_finRange]
  calc
    ((List.finRange b.nParticipants).flatMap fun p =>
        (List.finRange (b.nEvents + 1)).flatMap fun ei =>
          (List.finRange b.nTimes).map fun ti => { p, ei, ti : WId b }).length
        = b.nParticipants * ((b.nEvents + 1) * b.nTimes) := outerLen
    _ = b.nParticipants * (b.nEvents + 1) * b.nTimes := by
      simp [Nat.mul_assoc]

lemma mem_allWorlds (b : Bounds S) (w : WId b) : w ∈ WId.allWorlds b := by
  rcases w with ⟨p, ei, ti⟩
  unfold WId.allWorlds Bounds.partsL Bounds.evIxL Bounds.timesL
  simp [List.mem_flatMap, List.mem_map, List.mem_finRange]

/-- allWorlds produces a list without duplicates -/
lemma allWorlds_nodup (b : Bounds S) : (WId.allWorlds b).Nodup := by
  unfold WId.allWorlds Bounds.partsL Bounds.evIxL Bounds.timesL
  -- flatMap over finRange of parts
  rw [List.nodup_flatMap]
  constructor
  · -- Each inner list is nodup
    intro p _
    rw [List.nodup_flatMap]
    constructor
    · intro ei _
      apply List.Nodup.map
      · intro ti1 ti2 heq
        simp only [WId.mk.injEq] at heq
        exact heq.2.2
      · exact List.nodup_finRange _
    · apply List.Pairwise.imp _ (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange _))
      intro ei ej hne
      simp only [Function.onFun, List.disjoint_iff_ne, List.mem_map, List.mem_finRange,
        true_and, forall_exists_index, ne_eq]
      intro w ti hw w' ti' hw' heq
      rw [← hw, ← hw'] at heq
      simp only [WId.mk.injEq] at heq
      exact hne heq.2.1
  · apply List.Pairwise.imp _ (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange _))
    intro p p' hne
    simp only [Function.onFun, List.disjoint_iff_ne, List.mem_flatMap, List.mem_map,
      List.mem_finRange, true_and, forall_exists_index, ne_eq]
    intro w1 ei1 ti1 hw1 w2 ei2 ti2 hw2 heq
    rw [← hw1, ← hw2] at heq
    simp only [WId.mk.injEq] at heq
    exact hne heq.1

end WId

/-! ## Value Class Helpers

These helpers are used by both Structure.lean (for CNF generation) and Decoder.lean
(for model extraction), so they're defined here to avoid circular dependencies.
-/

/-- All indices in b.values that map to the given value. -/
def valueIndices [DecidableEq (Signature.Value S)]
  (b : Bounds S) (v : Signature.Value S) : List (b.valIx) :=
  (List.finRange b.nVals).filterMap (fun i =>
    if b.values.get i = v then some i else none)

/-- All distinct values that appear in b.values (one per equivalence class). -/
def classValues [DecidableEq (Signature.Value S)] (b : Bounds S) : List (Signature.Value S) :=
  ((List.finRange b.nVals).map (b.values.get)).dedup

end Encoding
