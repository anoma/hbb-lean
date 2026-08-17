import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History

/-!
# ThyHBB1 Uniqueness of Proposals

This file contains lemmas proving the crucial property that at most one value can be proposed
in the ThyHBB1 broadcast protocol, and derives consequences about echo events.

The main results show that:
- Uniqueness of proposals forces observed proposal diamonds to agree on values
- Unique proposals guarantee eventual echoes with the same value
- At most one proposal implies every learner is safe

These lemmas are extracted from the main ThyHBB1 file to improve modularity and maintainability.
They support the proof of agreement and liveness properties.

## Key Lemmas

The file is organized into several categories:

- **Guard and value equality lemmas**: Extract and apply uniqueness constraints
  - `uniquePropose_guard_at_history`: Specializes uniqueness to a given history
  - `uniquePropose_equal_values`: Forces observed proposals to agree
  - `uniquePropose_guard_at_predecessor`: Restricts uniqueness to predecessor histories

- **Echo existence and equality lemmas**: Derive echo properties from unique proposals
  - `uniquePropose_exists_witness_echo`: Antecedent ensures echoes exist
  - `uniquePropose_eventually_echo_core`: Combines existence and equality
  - `uniquePropose_eventually_echo`: Main result

- **Helper lemmas for event-level reasoning**:
  - `sometime_echo_event_exists`: Witness explicit echo events
  - `echo_backward_diamond_from_sometime`: Convert echoes to proposal diamonds
  - `boxEcho_to_propose_diamond`: Box echoes imply proposal diamonds
  - `echoNonEquiv_diamond`: Echo non-equivalence constraint

- **Safety lemmas**:
  - `atMostOnePropose_safeFormula`: Uniqueness implies safety
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB1

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section Results

variable {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {w w' t : World P (Signature.EventType S)}

/-- Auxiliary: uniqueness at a fixed world yields the guarded at-most-one witness. -/
theorem uniquePropose_guard_at_history
    {w : World P (Signature.EventType S)}
    (hUnique :
      ⟪w⟫ ⊨[M]∃!ᶠ v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    ⟪w⟫ ⊨[M]
      ∃≤ᶠ1 v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) := by
  classical
  have hAnd :=
    (Sat.and (M := M) (w := w)
      (φ := ∃≤ᶠ1 v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
      (ψ := ∃ᶠ (fun witness =>
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩)))).1
      (by
        simpa [Formula.existsUnique]
          using hUnique)
  exact hAnd.1

/-- Auxiliary: uniqueness of proposals forces observed proposal diamonds to agree. -/
theorem uniquePropose_equal_values
    {w : World P (Signature.EventType S)}
    (value altValue : S.Value)
    (hAtMost : ⟪w⟫ ⊨[M]∃≤ᶠ1 v ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
    (hDiamond₁ : ⟪w⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
    (hDiamond₂ : ⟪w⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [altValue]⟩)) :
    value = altValue := by
  classical
  dsimp [Formula.existsAtMostOne] at hAtMost
  have hForValue :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun v =>
        ∀ᶠ fun altValue =>
          (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) ⇒ᶠ
            (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [altValue]⟩)) ⇒ᶠ
              (v ≃ᶠ altValue))
      (v := value) hAtMost
  have hForAlt :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun altValue =>
        (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [altValue]⟩)) ⇒ᶠ
            (value ≃ᶠ altValue))
      (v := altValue) hForValue
  have hEq : ⟪w⟫ ⊨[M] value ≃ᶠ altValue := by
    apply (Sat.imp (M := M) (w := w)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [altValue]⟩))
      (ψ := value ≃ᶠ altValue)).1
    · apply (Sat.imp (M := M) (w := w)
        (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
        (ψ := (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [altValue]⟩)) ⇒ᶠ
          (value ≃ᶠ altValue))).1
      · exact hForAlt
      · exact hDiamond₁
    · exact hDiamond₂
  simpa [Sat] using hEq

/-- Helper: extract a concrete witness from a modal existential at a fixed world. -/
theorem uniquePropose_exists_witness_at_world
    {w : World P (Signature.EventType S)}
    (hExists :
      ⟪w⟫ ⊨[M]∃ᶠ (fun witness =>
          ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩))) :
    ∃ value : Signature.Value S,
      ⟪w⟫ ⊨[M]
        ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  refine Classical.byContradiction fun hNoWitness => ?_
  have hNotForall : ∀ value : Signature.Value S,
      ¬ (⟪w⟫ ⊨[M] ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩)) :=
    not_exists.mp hNoWitness
  have hForallNot :
      ⟪w⟫ ⊨[M]
        ∀ᶠ (fun value => ¬ᶠ (↕ᶠ(ofEvent ⟨echoSymb, [value]⟩))) := by
    refine
      Sat.forall_intro (M := M) (w := w)
        (body := fun value => ¬ᶠ (↕ᶠ(ofEvent ⟨echoSymb, [value]⟩))) ?_
    intro v
    exact
      Sat.not_intro (M := M) (w := w)
        (φ := ↕ᶠ(ofEvent ⟨echoSymb, [v]⟩))
        (hNotForall v)
  have hNeg :
      ⟪w⟫ ⊨[M] ¬ᶠ (∀ᶠ (fun value => ¬ᶠ (↕ᶠ(ofEvent ⟨echoSymb, [value]⟩)))) := by
    simpa [Formula.exists_] using hExists
  exact
    (Sat.not (M := M) (w := w)
      (φ := ∀ᶠ (fun value => ¬ᶠ (↕ᶠ(ofEvent ⟨echoSymb, [value]⟩))))).1
        hNeg hForallNot

/-- Helper: equality implication yields value equality under a witness substitution. -/
theorem uniquePropose_witness_eq_at_world
    {w : World P (Signature.EventType S)}
    (value : S.Value)
    (hEq :
      ⟪w⟫ ⊨[M]∀ᶠ (fun witness =>
        (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
          (witness ≃ᶠ value)))
    (witness : Signature.Value S)
    (hEcho :
      ⟪w⟫ ⊨[M]↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) :
    witness = value := by
  classical
  have hImpl :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun witness =>
        (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
          (witness ≃ᶠ value))
      (v := witness) hEq
  have hEqFormula :=
    Sat.imp_elim (M := M) (w := w)
      (φ := ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩))
      (ψ := witness ≃ᶠ value)
      hImpl hEcho
  simpa [Sat] using hEqFormula

/-- Helper: transport sometime from a witness value back to the target value. -/
theorem uniquePropose_sometime_rewrite_value
    {w : World P (Signature.EventType S)}
    (value witness : Signature.Value S)
    (hEcho :
      ⟪w⟫ ⊨[M]↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩))
    (hVal : witness = value) :
    ⟪w⟫ ⊨[M]
      ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  subst hVal
  simpa using hEcho

theorem uniquePropose_eventually_echo_core_world
    {w : World P (Signature.EventType S)}
    (value : S.Value)
    (hExists :
      ⟪w⟫ ⊨[M](predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∃ᶠ (fun witness =>
            ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)))
    (hEq :
      ⟪w⟫ ⊨[M](predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∀ᶠ (fun witness =>
            (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
              (witness ≃ᶠ value))) :
    ⟪w⟫ ⊨[M]
      (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
        ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  refine Sat.imp_intro (M := M) (w := w)
      (φ := predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
      (ψ := ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩)) ?_
  intro hAnte
  obtain ⟨witness, hEchoWitness⟩ :=
    uniquePropose_exists_witness_at_world
      ((Sat.imp (M := M) (w := w)
        (φ := predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
        (ψ := ∃ᶠ (fun witness =>
          ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)))).1
        hExists hAnte)
  have hEq_inst :=
    (Sat.imp (M := M) (w := w)
      (φ := predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
      (ψ := ∀ᶠ (fun witness =>
        (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
          (witness ≃ᶠ value)))).1
      hEq hAnte
  have hWitnessEq :=
    uniquePropose_witness_eq_at_world
      (w := w) (value := value)
      (hEq := hEq_inst) (witness := witness)
      (hEcho := hEchoWitness)
  exact
    uniquePropose_sometime_rewrite_value
      (w := w) (value := value)
      (witness := witness)
      hEchoWitness hWitnessEq

/-- Auxiliary: combining existence and equality of echoes yields the target echo. -/
theorem uniquePropose_eventually_echo_core
    (value : S.Value)
    (hExists :
      □W⊨[M](predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∃ᶠ (fun witness =>
            ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)))
    (hEq :
      □W⊨[M](predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∀ᶠ (fun witness =>
            (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
              (witness ≃ᶠ value))) :
    □W⊨[M]
      (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
        ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  intro t ht
  have hExists_loc :
      ⟪t⟫ ⊨[M]
        (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∃ᶠ fun witness =>
            ↕ᶠ (ofEvent ⟨echoSymb, [witness]⟩) :=
    hExists ht
  have hEq_loc :
      ⟪t⟫ ⊨[M]
        (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∀ᶠ fun witness =>
            (↕ᶠ (ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
              (witness ≃ᶠ value) :=
    hEq ht
  exact
    uniquePropose_eventually_echo_core_world
      (w := t)
      (value := value)
      (hExists := hExists_loc)
      (hEq := hEq_loc)

/-- Auxiliary: the antecedent ensures echoes exist for some witness value. -/
theorem uniquePropose_exists_witness_echo
    (value : S.Value)
    (hEcho : □W⊨[M]echoForwardAxiom liveSymb proposeSymb echoSymb) :
    □W⊨[M]
      (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
        ∃ᶠ (fun witness =>
          ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) := by
  classical
  intro t ht
  have hLocal :
      ⟪t⟫ ⊨[M]
        echoForwardAxiom liveSymb proposeSymb echoSymb :=
    hEcho ht
  have hSpecialised :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun v =>
        (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) ⇒ᶠ
          ∃ᶠ (fun witness =>
            ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)))
      (v := value) hLocal
  simpa [echoForwardAxiom]
    using hSpecialised

/-- Witness an explicit echo event from a sometime echo. -/
theorem sometime_echo_event_exists
    {w : World P (Signature.EventType S)}
    (value : S.Value)
    (hEcho :
      ⟪w⟫ ⊨[M]↕ᶠ(ofEvent ⟨echoSymb, [value]⟩)) :
    ∃ wEcho : World P (Signature.EventType S),
      wEcho ∈ M.history.val ∧
      wEcho.place = w.place ∧
      ⟪wEcho⟫ ⊨[M] ofEvent ⟨echoSymb, [value]⟩ := by
  classical
  obtain ⟨wEcho, hMem, hPlace, hEvent⟩ :=
    (Sat.sometime (M := M) (w := w)
      (φ := Formula.ofEvent ⟨echoSymb, [value]⟩)).1
      (by simpa [Formula.sometime] using hEcho)
  refine ⟨wEcho, hMem, hPlace, ?_⟩
  simpa [Formula.ofEvent] using hEvent

/-- Convert an observed echo event into a proposal diamond via the backward axiom. -/
theorem echo_backward_diamond_from_sometime
    {w : World P (Signature.EventType S)}
    (value : S.Value)
    (hEchoBack :
      □W⊨[M]echoBackwardAxiom proposeSymb echoSymb)
    (hEvent :
      ⟪w⟫ ⊨[M]ofEvent ⟨echoSymb, [value]⟩) :
    ⟪w⟫ ⊨[M]
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) := by
  classical
  rcases w with ⟨p, evt, Hw⟩
  obtain ⟨hEvent_eq, ht⟩ :=
    (by
      simpa [Formula.ofEvent, Sat] using hEvent)
  have hw_mem : (p, evt, Hw) ∈ M.history.val := by
    simpa [hEvent_eq]
      using ht
  have hLocal :
      ⟪⟨p, evt, Hw⟩⟫ ⊨[M]
        echoBackwardAxiom proposeSymb echoSymb :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := echoBackwardAxiom proposeSymb echoSymb)
      hEchoBack hw_mem
  have hImp :=
    Sat.forall_elim (M := M) (w := ⟨p, evt, Hw⟩)
      (body := fun v =>
        ofEvent ⟨echoSymb, [v]⟩ ⇒ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
      (v := value) hLocal
  have hImp' :
      ⟪⟨p, evt, Hw⟩⟫ ⊨[M]
        ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) := by
    simpa [Formula.ofEvent, Sat, hEvent_eq]
      using hImp
  have hEvent' :
      ⟪⟨p, evt, Hw⟩⟫ ⊨[M]ofEvent ⟨echoSymb, [value]⟩ := by
    simpa [Formula.ofEvent, Sat, hEvent_eq]
      using hEvent
  exact (Sat.imp (M := M) (w := ⟨p, evt, Hw⟩)
    (φ := ofEvent ⟨echoSymb, [value]⟩)
    (ψ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))).1
    hImp' hEvent'

theorem boxEcho_to_propose_diamond
    {w : World P (Signature.EventType S)}
    (hSubset : w.time ⊆trn M.history.val)
    (hEchoBack :
      □W⊨[M]echoBackwardAxiom proposeSymb echoSymb)
    {learner : Signature.Value S}
    {value : S.Value}
    (hBox :
      ⟪w⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) :
    ⟪w⟫ ⊨[M]
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) := by
  classical
  rcases w with ⟨p, evt, Hw⟩
  have hHerHw : isHereditarilyTransitive Hw := hSubset.2

  -- Expand the guarded box to obtain a quorum and corresponding witnesses.
  have hBoxPast :
      ⟪⟨p, evt, Hw⟩⟫ ⊨[M]
        □ᶠ[[learner]] (Formula.past (ofEvent ⟨echoSymb, [value]⟩)) := by
    simpa [Formula.boxPast] using hBox
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
        (w := ⟨p, evt, Hw⟩) (l := learner)
        (φ := Formula.past (ofEvent ⟨echoSymb, [value]⟩))).1
      hBoxPast
  obtain ⟨qEcho, hqEcho⟩ :=
    (Semifilter.quorum_nonempty
      (P := P) (L := M.learner learner) (O := O) hO)
  have hPastEcho :
      ⟪⟨qEcho, †, Hw⟩⟫ ⊨[M]
        ↓ᶠ (Formula.ofEvent ⟨echoSymb, [value]⟩) := by
    simpa [Formula.past] using hAll qEcho hqEcho
  obtain ⟨wEcho, hEcho_memHw, hEcho_place, hEcho_local⟩ :=
    (Sat.past (M := M)
      (w := ⟨qEcho, †, Hw⟩)
      (φ := Formula.ofEvent ⟨echoSymb, [value]⟩)).1 hPastEcho

  have hEcho_event_mem :
      wEcho.event = MaybeEvent.some ⟨echoSymb, [value]⟩ ∧
        (wEcho.place, MaybeEvent.some ⟨echoSymb, [value]⟩, wEcho.time) ∈ M.history.val :=
    by
      simpa [Formula.ofEvent, Sat] using hEcho_local
  have hEcho_event :
      wEcho.event = MaybeEvent.some ⟨echoSymb, [value]⟩ :=
    hEcho_event_mem.1
  have hEchoMem :
      (wEcho.place, MaybeEvent.some ⟨echoSymb, [value]⟩, wEcho.time) ∈ M.history.val :=
    hEcho_event_mem.2
  have hEchoEvent :
      ⟪wEcho⟫ ⊨[M] ofEvent ⟨echoSymb, [value]⟩ :=
    hEcho_local
  -- Convert the echo information into a proposal diamond at `wEcho`.
  have hDiamondEcho :=
    echo_backward_diamond_from_sometime
      (M := M) (w := wEcho) (value := value)
      (hEchoBack := hEchoBack) (hEvent := hEchoEvent)

  -- Extract the proposal event produced by the diamond.
  obtain ⟨qProp, hPastProp⟩ :=
    (Sat.diamond_nil (M := M) (w := wEcho)
      (φ := ↓ᶠ (Formula.ofEvent ⟨proposeSymb, [value]⟩))).1
      (by
        simpa [Formula.diamondPast] using hDiamondEcho)
  obtain ⟨wProp, hProp_mem, hProp_place, hProp_event⟩ :=
    (Sat.past (M := M)
      (w := ⟨qProp, †, wEcho.time⟩)
      (φ := Formula.ofEvent ⟨proposeSymb, [value]⟩)).1 hPastProp

  have hPropEventSat :
      ⟪wProp⟫ ⊨[M]
        ofEvent ⟨proposeSymb, [value]⟩ :=
    by
      simpa [Sat] using hProp_event

  -- Show the witnessed proposal lies inside the base history `Hw`.
  have hAccEcho : wEcho ≪ ⟨qEcho, †, Hw⟩ :=
    by
      simpa [World.accessible] using hEcho_memHw
  have hBeforeEcho : wEcho.time ≺− Hw :=
    PreHistory.happensBefore_of_accessible
      (P := P) (Event := Signature.EventType S) hAccEcho
  let HW := History.mk Hw hHerHw
  have hEchoData :=
    History.predecessor_data (H := HW) hBeforeEcho
  have hSubsetHe_full : wEcho.time ⊆trn Hw :=
    History.happensBefore_implies_transitiveSubset
      (History.mk wEcho.time hEchoData.2) HW hBeforeEcho
  have hSubsetHe : wEcho.time ⊆ Hw :=
    History.transitiveSubset_subset
      (P := P) (Event := Signature.EventType S) hSubsetHe_full
  have hProp_inHw : wProp ∈ Hw :=
    hSubsetHe _ hProp_mem

  -- Transport the proposal witness back to the base world.
  have hPast_at_base :
      ⟪⟨qProp, †, Hw⟩⟫ ⊨[M]
        ↓ᶠ (Formula.ofEvent ⟨proposeSymb, [value]⟩) :=
    Sat.past_intro_of_prefix
      (M := M) (w := ⟨qProp, †, Hw⟩)
      (t := wProp)
      (φ := Formula.ofEvent ⟨proposeSymb, [value]⟩)
      (by simpa using hProp_inHw)
      (by simpa using hProp_place)
      hPropEventSat
  have hDiamond_witness :
      ∃ q : P,
        ⟪⟨q, †, Hw⟩⟫ ⊨[M]
          ↓ᶠ (Formula.ofEvent ⟨proposeSymb, [value]⟩) :=
    ⟨qProp, hPast_at_base⟩
  have hDiamond_base :
      ⟪⟨p, evt, Hw⟩⟫ ⊨[M]
        ♢ᶠ[[]] (↓ᶠ (Formula.ofEvent ⟨proposeSymb, [value]⟩)) :=
    (Sat.diamond_nil (M := M)
      (w := ⟨p, evt, Hw⟩)
      (φ := ↓ᶠ (Formula.ofEvent ⟨proposeSymb, [value]⟩))).2
      hDiamond_witness
  simpa [Formula.diamondPast]
    using hDiamond_base

/-- One-sided application of `EchoNE`: an echo followed by a past echo must
share the same value. -/
theorem echoNonEquiv_diamond
    (hEchoNE : AllWorldValid M (echoNonEquivAxiom echoSymb))
    {w : World P (Signature.EventType S)}
    (hSubset : w.time ⊆trn M.history.val)
    {valNow valPast : Signature.Value S}
    (hDiamond :
      ⟪w⟫ ⊨[M]♢ᶠ↓[[]]((ofEvent ⟨echoSymb, [valNow]⟩) ∧ᶠ
            ↓ᶠ (ofEvent ⟨echoSymb, [valPast]⟩))) :
    valNow = valPast := by
  classical
  rcases w with ⟨p, evt, Hw⟩
  have hSubsetPlain : Hw ⊆ M.history.val :=
    History.transitiveSubset_subset
      (P := P) (Event := Signature.EventType S) hSubset
  have hDiamondBase :
      ⟪⟨p, evt, Hw⟩⟫ ⊨[M]
        ♢ᶠ[[]]
          (↓ᶠ ((ofEvent ⟨echoSymb, [valNow]⟩) ∧ᶠ
            ↓ᶠ (ofEvent ⟨echoSymb, [valPast]⟩))) := by
    simpa [Formula.diamondPast]
      using hDiamond
  obtain ⟨qEcho, hPastPair⟩ :=
    (Sat.diamond_nil (M := M)
      (w := ⟨p, evt, Hw⟩)
      (φ := ↓ᶠ ((ofEvent ⟨echoSymb, [valNow]⟩) ∧ᶠ
        ↓ᶠ (ofEvent ⟨echoSymb, [valPast]⟩)))).1 hDiamondBase
  obtain ⟨wNow, hNow_memHw, hNow_place, hNow_local⟩ :=
    (Sat.past (M := M)
      (w := ⟨qEcho, †, Hw⟩)
      (φ := (ofEvent ⟨echoSymb, [valNow]⟩) ∧ᶠ
        ↓ᶠ (ofEvent ⟨echoSymb, [valPast]⟩))).1 hPastPair
  have hNow_split :=
    (Sat.and (M := M) (w := wNow)
      (φ := ofEvent ⟨echoSymb, [valNow]⟩)
      (ψ := ↓ᶠ (ofEvent ⟨echoSymb, [valPast]⟩))).1 hNow_local
  have hNow_eventSat :
      ⟪wNow⟫ ⊨[M]ofEvent ⟨echoSymb, [valNow]⟩ := hNow_split.1
  have hPast_local :
      ⟪wNow⟫ ⊨[M]↓ᶠ (ofEvent ⟨echoSymb, [valPast]⟩) :=
    hNow_split.2
  have hNow_mem : wNow ∈ M.history.val :=
    hSubsetPlain _ hNow_memHw
  have hEchoNE_local :
      ⟪wNow⟫ ⊨[M] echoNonEquivAxiom echoSymb :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := echoNonEquivAxiom echoSymb)
      hEchoNE hNow_mem
  have hForValues :=
    Sat.forall_elim (M := M) (w := wNow)
      (body := fun value =>
        ∀ᶠ fun altValue =>
          ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
            (↓ᶠ (ofEvent ⟨echoSymb, [altValue]⟩)) ⇒ᶠ
              (value ≃ᶠ altValue))
      (v := valNow) hEchoNE_local
  have hForAlt :=
    Sat.forall_elim (M := M) (w := wNow)
      (body := fun altValue =>
        ofEvent ⟨echoSymb, [valNow]⟩ ⇒ᶠ
          (↓ᶠ (ofEvent ⟨echoSymb, [altValue]⟩)) ⇒ᶠ
            (valNow ≃ᶠ altValue))
      (v := valPast) hForValues
  have hImp :=
    (Sat.imp (M := M) (w := wNow)
      (φ := ofEvent ⟨echoSymb, [valNow]⟩)
      (ψ := (↓ᶠ (ofEvent ⟨echoSymb, [valPast]⟩)) ⇒ᶠ
        (valNow ≃ᶠ valPast))).1 hForAlt hNow_eventSat
  have hEqFormula :=
    (Sat.imp (M := M) (w := wNow)
      (φ := ↓ᶠ (ofEvent ⟨echoSymb, [valPast]⟩))
      (ψ := valNow ≃ᶠ valPast)).1
      hImp hPast_local
  have hEq :=
    (Sat.eq (M := M) (w := wNow)
      (v₁ := valNow) (v₂ := valPast)).1 hEqFormula
  simpa [Sat] using hEq

theorem uniquePropose_guard_implies_eq
    {w : World P (Signature.EventType S)}
    (value witness : S.Value)
    (hGuard :
      ⟪w⟫ ⊨[M]∃≤ᶠ1 v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
    (hDiamond_value :
      ⟪w⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
    (hDiamond_witness :
      ⟪w⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩)) :
    ⟪w⟫ ⊨[M]
      witness ≃ᶠ value := by
  classical
  dsimp [Formula.existsAtMostOne] at hGuard
  have hForValue :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun v =>
        ∀ᶠ fun altValue =>
          (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) ⇒ᶠ
            (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [altValue]⟩)) ⇒ᶠ
              (v ≃ᶠ altValue))
      (v := value) hGuard
  have hForWitness :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun altValue =>
        (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [altValue]⟩)) ⇒ᶠ
            (value ≃ᶠ altValue))
      (v := witness) hForValue
  have hImp :=
    (Sat.imp (M := M) (w := w)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
      (ψ := (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩)) ⇒ᶠ
        (value ≃ᶠ witness))).1
      hForWitness hDiamond_value
  have hEqVal :=
    (Sat.imp (M := M) (w := w)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩))
      (ψ := value ≃ᶠ witness)).1
      hImp hDiamond_witness
  have hEq :=
    (Sat.eq (M := M) (w := w)
      (v₁ := value) (v₂ := witness)).1 hEqVal
  simpa [Sat] using hEq.symm

theorem uniquePropose_witness_eq_value
    (value : S.Value)
    (hEchoBack : □W⊨[M]echoBackwardAxiom proposeSymb echoSymb)
    (hUnique : ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    □W⊨[M]
      (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
        ∀ᶠ (fun witness =>
          (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
            (witness ≃ᶠ value)) := by
  classical
  dsimp [AllWorldValid]
  intro t ht
  set wPred : World P (Signature.EventType S) := t with hwPred_def
  set wTop : World P (Signature.EventType S) :=
    ⟨t.place, †, M.history.val⟩ with hwTop_def
  have hUnique_global :
      ⟪wTop⟫ ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) :=
    hUnique t.place
  have hGuard_global :
      ⟪wTop⟫ ⊨[M]
        ∃≤ᶠ1 v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) :=
    uniquePropose_guard_at_history (M := M) (w := wTop) hUnique_global
  refine
    Sat.imp_intro (M := M) (w := wPred)
      (φ :=
        predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
      (ψ := ∀ᶠ (fun witness =>
        (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
          (witness ≃ᶠ value))) ?_
  intro hAnte
  have hConj :=
    (Sat.and (M := M) (w := wPred)
      (φ := predicate0 liveSymb)
      (ψ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))).1 hAnte
  have hDiamond_value_loc := hConj.2
  refine
    Sat.forall_intro (M := M) (w := wPred)
      (body := fun witness =>
        (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
          (witness ≃ᶠ value)) ?_
  intro witness
  refine
    Sat.imp_intro (M := M) (w := wPred)
      (φ := ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩))
      (ψ := witness ≃ᶠ value) ?_
  intro hEcho
  obtain ⟨wEcho, hEcho_mem, _, hEcho_event⟩ :=
    sometime_echo_event_exists (M := M) (w := wPred)
      (value := witness) hEcho
  have hDiamond_witness_wEcho :
      ⟪wEcho⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩) :=
    echo_backward_diamond_from_sometime
      (M := M) (w := wEcho) (value := witness)
      (hEchoBack := hEchoBack) hEcho_event
  have hSubset_pred :
      wPred.time ⊆trn M.history.val :=
    by
      simpa [wPred, hwPred_def]
        using ModalDistribution.Logic.time_subset_trn_history
          (M := M) (t := t) ht
  have hDiamond_value_global :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) := by
    simpa [Formula.ofEvent]
      using
        (sat_diamondPast_nil_event_subset
          (M := M)
          (w := wTop)
          (w' := wPred)
          (symb := proposeSymb)
          (args := [value])
          (hSubset := hSubset_pred)
          hDiamond_value_loc)
  have hBefore_wEcho :
      wEcho.time ⪯ M.history.val :=
    PreHistory.happensBeforeEq_of_mem
      (Event := Signature.EventType S) hEcho_mem
  have hSubset_wEcho :
      wEcho.time ⊆trn M.history.val := by
    simpa using
      ModalDistribution.Logic.time_subset_trn_history
        (M := M) (t := wEcho) hBefore_wEcho
  have hDiamond_witness_global :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩) := by
    simpa [Formula.ofEvent]
      using
        (sat_diamondPast_nil_event_subset
          (M := M)
          (w := wTop)
          (w' := wEcho)
          (symb := proposeSymb)
          (args := [witness])
          (hSubset := hSubset_wEcho)
          hDiamond_witness_wEcho)
  have hEq_global :
      ⟪wTop⟫ ⊨[M] witness ≃ᶠ value :=
    uniquePropose_guard_implies_eq
      (M := M) (w := wTop)
      (value := value) (witness := witness)
      (hGuard := hGuard_global)
      (hDiamond_value := hDiamond_value_global)
      (hDiamond_witness := hDiamond_witness_global)
  have hEq_val : witness = value := by
    simpa [Sat] using hEq_global
  simp [Sat, hEq_val]

/-- Paper: Lemma 6.5.1. a unique proposal guarantees eventual echoes. -/
theorem uniquePropose_eventually_echo
    (value : S.Value)
    (hEcho : □W⊨[M]echoForwardAxiom liveSymb proposeSymb echoSymb)
    (hEchoBack : □W⊨[M]echoBackwardAxiom proposeSymb echoSymb)
    (hUnique : ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    □W⊨[M]
      (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
        ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  have hExists :
      □W⊨[M]
        (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∃ᶠ (fun witness =>
            ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) :=
    uniquePropose_exists_witness_echo (value := value) (hEcho := hEcho)
  have hEq :
      □W⊨[M]
        (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∀ᶠ (fun witness =>
            (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
              (witness ≃ᶠ value)) :=
    uniquePropose_witness_eq_value
      (value := value)
      (hEchoBack := hEchoBack) (hUnique := hUnique)
  exact
    (uniquePropose_eventually_echo_core
      (value := value)
      (hExists := hExists) (hEq := hEq) :
        □W⊨[M]
          (predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
            ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩))

/-- at most one proposal implies every learner is safe. -/
theorem atMostOnePropose_safeFormula
    (l : Signature.Value S) :
    ⊨[M](∃≤ᶠ1 v ↦
        (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        safeFormula proposeSymb l := by
  classical
  let uniqueCond : Formula S :=
    ∃≤ᶠ1 v ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)
  let seqGuard : Formula S :=
    ∀ᶠ (fun l' => ♢ᶠ[[l, l']] Formula.seq)
  intro p
  refine (Sat.imp (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := uniqueCond)
      (ψ := safeFormula proposeSymb l)).2 ?_
  intro hUniqueCond
  have hOr :=
    (Sat.or (M := M) (w := ⟨p, †, M.history.val⟩)
      (φ := uniqueCond) (ψ := seqGuard)).2
      (Or.inl hUniqueCond)
  simpa [uniqueCond, seqGuard, safeFormula]
    using hOr

/-- Paper: Lemma 6.5.2. If at most one value is proposed, then every learner is everywhere and
always safe. -/
theorem atMostOnePropose_safe
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (l : Signature.Value S) :
    ⊨[M](∃≤ᶠ1 v ↦
        (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hUnique
  refine Sat.not_intro (M := M) (w := wTop)
    (φ := ↕ᶠ (¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))) ?_
  intro hSome
  obtain ⟨s, hs_mem, hs_place, hNot⟩ :=
    (Sat.sometime (M := M) (w := wTop)
      (φ := ¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))).1 hSome
  have hs_mem' : s ∈ M.history.val := by
    simpa [wTop, World.time] using hs_mem
  have hs_le : s.time ⪯ M.history.val :=
    PreHistory.happensBeforeEq_of_mem
      (P := P) (Event := Signature.EventType S)
      (hmem := by
        simpa [World.place, World.event, World.time] using hs_mem')
  have hUnique_s :
      ⟪s⟫ ⊨[M]∃≤ᶠ1 v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) :=
    uniquePropose_monotone (M := M)
      (w := wTop) (w' := s)
      (hSubset := by
        simpa [wTop, World.time] using
          time_subset_trn_history (M := M) (t := s) hs_le)
      (hUnique := by simpa [wTop] using hUnique)
  have hSafeF_s : ⟪s⟫ ⊨[M] safeFormula proposeSymb l := by
    have hOr :=
      (Sat.or (M := M) (w := s)
        (φ := ∃≤ᶠ1 v ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
        (ψ := ∀ᶠ (fun l' => ♢ᶠ[[l, l']] Formula.seq))).2
        (Or.inl hUnique_s)
    simpa [safeFormula] using hOr
  have hSafe_s : ⟪s⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩ :=
    (safe_iff_safeFormula (M := M) (hTheory := hTheory)
      (w := s) hs_le l).2 hSafeF_s
  exact
    Sat.not_elim (M := M) (w := s)
      (φ := ofPredicate ⟨safeSymb, [l]⟩) hNot hSafe_s

end Results

end ThyHBB1
end Examples
end ModalDistribution
