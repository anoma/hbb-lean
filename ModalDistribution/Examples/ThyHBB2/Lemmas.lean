import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB2.Axioms
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History
import ModalDistribution.Core.Semifilter

/-!
# ThyHBB2 Helper Lemmas

This file bundles auxiliary lemmas for the ThyHBB2 development.  The first
group translates deliveries witnessed at end of time into the corresponding
vote quorums, instantiating the `Deliver?` axiom.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB2

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

namespace Deliver

/-- Instantiates the `Deliver?` axiom to extract the vote quorum that backs a
delivery observed at end of time. -/
theorem box_witness
    {p : P}
    {reporting learner value : Signature.Value S}
    (hDeliverAx : AllWorldValid M (deliverBackwardAxiom voteSymb deliverSymb))
    (hDeliver :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting, learner, value]⟩)) :
    ∃ t : World P (Signature.EventType S),
      t ∈ M.history.val ∧
        t.time ⊆ M.history.val ∧
        ⟪t⟫ ⊨[M]□ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hDiamond_nil :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩)) := by
    simpa [Formula.diamondPast, wTop] using hDeliver
  obtain ⟨qDeliver, hPastDeliver⟩ :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩))).1
      hDiamond_nil
  obtain ⟨tDeliver, ht_mem, ht_place, hDeliver_at⟩ :=
    (Sat.past (M := M)
      (w := ⟨qDeliver, †, wTop.time⟩)
      (φ := ofEvent ⟨deliverSymb, [reporting, learner, value]⟩)).1
      hPastDeliver
  have ht_mem_history : tDeliver ∈ M.history.val := by
    simpa [wTop, World.time] using ht_mem
  have hDeliverLocal :
      ⟪tDeliver⟫ ⊨[M]deliverBackwardAxiom voteSymb deliverSymb :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := deliverBackwardAxiom voteSymb deliverSymb)
      hDeliverAx ht_mem_history
  have hImp_reporting :=
    Sat.forall_elim (M := M) (w := tDeliver)
      (body := fun reporting' =>
        ∀ᶠ fun learner' =>
          ∀ᶠ fun value' =>
            ofEvent ⟨deliverSymb, [reporting', learner', value']⟩ ⇒ᶠ
              □ᶠ↓[[reporting']](ofEvent ⟨voteSymb, [learner', value']⟩))
      (v := reporting) hDeliverLocal
  have hImp_learner :=
    Sat.forall_elim (M := M) (w := tDeliver)
      (body := fun learner' =>
        ∀ᶠ fun value' =>
          ofEvent ⟨deliverSymb, [reporting, learner', value']⟩ ⇒ᶠ
            □ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner', value']⟩))
      (v := learner) hImp_reporting
  have hImp_value :=
    Sat.forall_elim (M := M) (w := tDeliver)
      (body := fun value' =>
        ofEvent ⟨deliverSymb, [reporting, learner, value']⟩ ⇒ᶠ
          □ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value']⟩))
      (v := value) hImp_learner
  have hBox_at_event :
      ⟪tDeliver⟫ ⊨[M]□ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value]⟩) :=
    (Sat.imp (M := M) (w := tDeliver)
      (φ := ofEvent ⟨deliverSymb, [reporting, learner, value]⟩)
      (ψ := □ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hImp_value hDeliver_at
  have hBefore_history : tDeliver.time ≺− M.history.val :=
    happensBefore_of_mem (P := P) (Event := Signature.EventType S)
      ht_mem_history
  have hSubset_history : tDeliver.time ⊆ M.history.val :=
    History.subset_of_happensBefore (H := M.history) hBefore_history
  exact ⟨tDeliver, ht_mem_history, hSubset_history, hBox_at_event⟩

/-- Lift a vote quorum box witnesses from a past world to end of time. -/
theorem lift_box_to_end
    {t : World P (Signature.EventType S)}
    {reporting learner value : Signature.Value S}
    (hSubset : t.time ⊆ M.history.val)
    (hBox : ⟪t⟫ ⊨[M]□ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value]⟩))
    {p : P} :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  have hBoxPast_at :
      ⟪t⟫ ⊨[M]□ᶠ[[reporting]]
          (↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    by simpa [Formula.boxPast] using hBox
  have hBoxPast_top :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ[[reporting]]
          (↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    sat_box_singleton_transfer (M := M)
      (w := t) (w' := ⟨p, †, M.history.val⟩)
      (l := reporting)
      (φ := ↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩))
      (hTransfer := fun q hPast =>
        sat_past_of_subset (M := M)
          (q := q)
          (H := t.time)
          (H' := M.history.val)
          (φ := ofEvent ⟨voteSymb, [learner, value]⟩)
          (hSubset := hSubset) hPast)
      hBoxPast_at
  simpa [Formula.boxPast]
    using hBoxPast_top

end Deliver

/-- Singleton past boxes yield a witness for the corresponding past diamond. -/
theorem boxPast_singleton_to_diamond_nil
    {w : World P (Signature.EventType S)}
    {learner : Signature.Value S}
    {φ : Formula S}
    (hBox : ⟪w⟫ ⊨[M]□ᶠ↓[[learner]]φ) :
    ⟪w⟫ ⊨[M]♢ᶠ↓[[]]φ := by
  classical
  have hBoxPlain :
      ⟪w⟫ ⊨[M]□ᶠ[[learner]](↓ᶠ φ) :=
    by simpa [Formula.boxPast] using hBox
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := w) (l := learner) (φ := ↓ᶠ φ)).1 hBoxPlain
  obtain ⟨q, hq⟩ :=
    (M.learner learner).quorum_nonempty hO
  have hPast :
      ⟪⟨q, †, w.time⟩⟫ ⊨[M] ↓ᶠ φ := hAll q hq
  have hDiamond :
      ⟪w⟫ ⊨[M]♢ᶠ[[]](↓ᶠ φ) :=
    (Sat.diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ φ)).2 ⟨q, hPast⟩
  simpa [Formula.diamondPast]
    using hDiamond

/-- Lift a learner-guarded past box along the end-of-time inclusion. -/
theorem lift_boxPast_to_end
    {t : World P (Signature.EventType S)}
    {learner : Signature.Value S}
    {φ : Formula S}
    (hSubset : t.time ⊆ M.history.val)
    (hBox : ⟪t⟫ ⊨[M]□ᶠ↓[[learner]]φ)
    {p : P} :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[learner]]φ := by
  classical
  have hBoxPast_at :
      ⟪t⟫ ⊨[M]□ᶠ[[learner]](↓ᶠ φ) :=
    by simpa [Formula.boxPast] using hBox
  have hBoxPast_top :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ[[learner]](↓ᶠ φ) :=
    sat_box_singleton_transfer (M := M)
      (w := t) (w' := ⟨p, †, M.history.val⟩)
      (l := learner)
      (φ := ↓ᶠ φ)
      (hTransfer := fun q hPast =>
        sat_past_of_subset (M := M)
          (q := q)
          (H := t.time)
          (H' := M.history.val)
          (φ := φ)
          (hSubset := hSubset) hPast)
      hBoxPast_at
  simpa [Formula.boxPast]
    using hBoxPast_top

namespace Vote

/-- Instantiates `Vote?` to extract echo quorums supporting a vote. -/
theorem box_witness
    {p : P}
    {learner value : Signature.Value S}
    (hVoteAx : AllWorldValid M (voteBackwardAxiom echoSymb voteSymb))
    (hVote :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ∃ t : World P (Signature.EventType S),
      t ∈ M.history.val ∧
        t.time ⊆ M.history.val ∧
        ⟪t⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hDiamond_nil :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)) := by
    simpa [Formula.diamondPast, wTop] using hVote
  obtain ⟨qVote, hPastVote⟩ :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hDiamond_nil
  obtain ⟨tVote, ht_mem, ht_place, hVote_at⟩ :=
    (Sat.past (M := M)
      (w := ⟨qVote, †, wTop.time⟩)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hPastVote
  have ht_mem_history : tVote ∈ M.history.val := by
    simpa [wTop, World.time] using ht_mem
  have hVoteLocal :
      ⟪tVote⟫ ⊨[M]voteBackwardAxiom echoSymb voteSymb :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := voteBackwardAxiom echoSymb voteSymb)
      hVoteAx ht_mem_history
  have hImp_learner :=
    Sat.forall_elim (M := M) (w := tVote)
      (body := fun learner' =>
        ∀ᶠ fun value' =>
          ofEvent ⟨voteSymb, [learner', value']⟩ ⇒ᶠ
            □ᶠ↓[[learner']](ofEvent ⟨echoSymb, [value']⟩))
      (v := learner) hVoteLocal
  have hImp_value :=
    Sat.forall_elim (M := M) (w := tVote)
      (body := fun value' =>
        ofEvent ⟨voteSymb, [learner, value']⟩ ⇒ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value']⟩))
      (v := value) hImp_learner
  have hBox_at_event :
      ⟪tVote⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
    (Sat.imp (M := M) (w := tVote)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)
      (ψ := □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).1
      hImp_value hVote_at
  have hBefore_history : tVote.time ≺− M.history.val :=
    happensBefore_of_mem (P := P) (Event := Signature.EventType S)
      ht_mem_history
  have hSubset_history : tVote.time ⊆ M.history.val :=
    History.subset_of_happensBefore (H := M.history) hBefore_history
  exact ⟨tVote, ht_mem_history, hSubset_history, hBox_at_event⟩

/-- At end of time, a vote for `(learner, value)` requires an `learner`-quorum of
echoes backing it. -/
theorem to_echo_box_end
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {learner value : Signature.Value S}
    {p : P}
    (hVote :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  have hVoteAx : AllWorldValid M (voteBackwardAxiom echoSymb voteSymb) := by
    apply hTheory
    simp [theory]
  obtain ⟨tVote, ht_mem, hSubset, hBox⟩ :=
    Vote.box_witness (M := M)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (hVoteAx := hVoteAx)
      (learner := learner) (value := value)
      (p := p) (hVote := hVote)
  exact
    lift_boxPast_to_end (M := M)
      (learner := learner)
      (φ := ofEvent ⟨echoSymb, [value]⟩)
      (t := tVote) (p := p)
      (hSubset := hSubset) (hBox := hBox)

end Vote

/-! Unique-proposal helpers specialised to the `ThyHBB2` axioms. -/
namespace Unique

/-- Auxiliary: the antecedent ensures echoes exist for some witness value under
`ThyHBB2`. -/
theorem exists_witness_echo
    (value : Signature.Value S)
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M](predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
        ∃ᶠ(fun witness =>
          ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) := by
  classical
  have hEchoAx : AllWorldValid M
      (echoForwardAxiom liveSymb proposeSymb echoSymb) := by
    apply hTheory
    simp [theory]
  intro t ht
  have hLocal : ⟪t⟫ ⊨[M]
      echoForwardAxiom liveSymb proposeSymb echoSymb :=
    hEchoAx ht
  have hSpecialised :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun v =>
        (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) ⇒ᶠ
          ∃ᶠ fun witness =>
            ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩))
      (v := value) hLocal
  simpa [echoForwardAxiom]
    using hSpecialised

/-- Auxiliary: uniqueness of proposals forces witnesses produced by
`Echo!` to agree with the target value. -/
theorem witness_eq_value
    (value : Signature.Value S)
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    (hUnique : ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    □W⊨[M](predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
        ∀ᶠ(fun witness =>
          (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
            (witness ≃ᶠ value)) := by
  classical
  have hEchoBackAx : AllWorldValid M
      (echoBackwardAxiom proposeSymb echoSymb) := by
    apply hTheory
    simp [theory]
  intro t ht
  set wPred : World P (Signature.EventType S) := t with hwPred_def
  set wTop : World P (Signature.EventType S) :=
    ⟨t.place, †, M.history.val⟩ with hwTop_def
  have hEchoBack :
      □W⊨[M]echoBackwardAxiom proposeSymb echoSymb :=
    hEchoBackAx
  have hUnique_global :
      ⟪wTop⟫ ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) :=
    hUnique t.place
  have hGuard_global :
      ⟪wTop⟫ ⊨[M]∃≤ᶠ1 v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) :=
    ThyHBB1.uniquePropose_guard_at_history
      (M := M) (proposeSymb := proposeSymb)
      (w := wTop) (hUnique := hUnique_global)
  refine
    Sat.imp_intro (M := M) (w := wPred)
      (φ :=
        predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
      (ψ := ∀ᶠ fun witness =>
        (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
          (witness ≃ᶠ value)) ?_
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
    ThyHBB1.sometime_echo_event_exists (M := M) (w := wPred)
      (value := witness) hEcho
  have hDiamond_witness_wEcho :
      ⟪wEcho⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩) :=
    ThyHBB1.echo_backward_diamond_from_sometime
      (M := M) (w := wEcho) (value := witness)
      (hEchoBack := hEchoBack) hEcho_event
  have hSubset_pred :
      wPred.time ⊆trn M.history.val := by
    simpa [wPred, hwPred_def, wTop, hwTop_def]
      using
        ModalDistribution.Logic.time_subset_trn_history
          (M := M) (t := t) ht
  have hDiamond_value_global :
      ⟪wTop⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) := by
    simpa [Formula.ofEvent]
      using
        (sat_diamondPast_nil_event_subset
          (M := M) (w := wTop)
          (w' := wPred)
          (symb := proposeSymb)
          (args := [value])
          (hSubset := hSubset_pred)
          hDiamond_value_loc)
  have hBefore_wEcho :
      wEcho.time ⪯ M.history.val :=
    PreHistory.happensBeforeEq_of_mem
      (P := P) (Event := Signature.EventType S)
      (hmem := by
        simpa [World.place, World.event, World.time] using hEcho_mem)
  have hSubset_wEcho :
      wEcho.time ⊆trn M.history.val := by
    simpa using
      ModalDistribution.Logic.time_subset_trn_history
        (M := M) (t := wEcho) hBefore_wEcho
  have hDiamond_witness_global :
      ⟪wTop⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [witness]⟩) := by
    simpa [Formula.ofEvent]
      using
        (sat_diamondPast_nil_event_subset
          (M := M) (w := wTop)
          (w' := wEcho)
          (symb := proposeSymb)
          (args := [witness])
          (hSubset := hSubset_wEcho)
          hDiamond_witness_wEcho)
  have hEq_global :
      ⟪wTop⟫ ⊨[M] witness ≃ᶠ value :=
    ThyHBB1.uniquePropose_guard_implies_eq
      (M := M) (proposeSymb := proposeSymb)
      (w := wTop) (value := value)
      (witness := witness)
      (hGuard := hGuard_global)
      (hDiamond_value := hDiamond_value_global)
      (hDiamond_witness := hDiamond_witness_global)
  have hEq_val : witness = value := by
    simpa [Sat] using hEq_global
  simp [Sat, hEq_val]

/-- Unique proposals in `ThyHBB2` guarantee eventual echoes for the chosen
value. -/
theorem eventually_echo
    (value : Signature.Value S)
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    (hUnique : ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    □W⊨[M](predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
        ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  have hExists' :
      □W⊨[M](predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∃ᶠ(fun witness =>
            ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) :=
    exists_witness_echo (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (voteSymb := voteSymb) (deliverSymb := deliverSymb)
      (value := value) (hTheory := hTheory)
  have hEq' :
      □W⊨[M](predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          ∀ᶠ(fun witness =>
            (↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)) ⇒ᶠ
              (witness ≃ᶠ value)) :=
    witness_eq_value (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (voteSymb := voteSymb) (deliverSymb := deliverSymb)
      (value := value) (hTheory := hTheory)
      (hUnique := hUnique)
  intro t ht
  exact
    (ThyHBB1.uniquePropose_eventually_echo_core
      (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (value := value)
      (hExists := hExists')
      (hEq := hEq')) ht

end Unique

/-- Quorum intersections transport a vote witnessed at `l₁'` to some live
member of the `l₂'` quorum. -/
theorem live_vote_transfer
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' learner : Signature.Value S}
    {value : Signature.Value S}
    {p : P}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb)
    (hVote :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[l₁']](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hThyLiveTheory : M ⊨ᵀ ThyLive liveSymb := by
    intro ax hAx
    exact hTheory (Or.inl hAx)
  have hIntersectTop :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ := by
    simpa [wTop] using hIntersect p
  have hLiveQuorumTop :
      ⟪wTop⟫ ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb := by
    simpa [wTop] using hLive p
  have hVoteBoxPlain :
      ⟪wTop⟫ ⊨[M]□ᶠ[[l₁']](↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    by simpa [Formula.boxPast] using hVote
  obtain ⟨Ovote, hOvote, hAllVote⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := wTop) (l := l₁')
      (φ := ↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hVoteBoxPlain
  obtain ⟨Olive, hOlive, hAllLive⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := wTop) (l := l₂')
      (φ := predicate0 liveSymb)).1
      hLiveQuorumTop
  have hIntersectWitness :=
    (sat_diamond_pair_iff (M := M)
      (w := wTop) (l := l₁') (l' := l₂') (φ := ⊤ᶠ)).1
      (by simpa using hIntersectTop)
      Ovote hOvote Olive hOlive
  obtain ⟨q, hqIntersect, -⟩ := hIntersectWitness
  have hqOvote : q ∈ Ovote := hqIntersect.1
  have hqOlive : q ∈ Olive := hqIntersect.2
  have hPastVote :
      ⟪⟨q, †, wTop.time⟩⟫ ⊨[M]↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩) :=
    hAllVote q hqOvote
  obtain ⟨tVote, ht_mem, ht_place, hVoteEvent⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, wTop.time⟩)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hPastVote
  have ht_mem_history : tVote ∈ M.history.val := by
    simpa [wTop, World.time] using ht_mem
  have hLiveEnd' :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb := by
    simpa [wTop]
      using hAllLive q hqOlive
  have hLiveGlobal :
      ⟪⟨tVote.place, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb :=
    Eq.subst (motive :=
        fun x => ⟪⟨x, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb)
      ht_place.symm hLiveEnd'
  have hLiveLocal :
      ⟪tVote⟫ ⊨[M]predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
      (liveSymb := liveSymb)
      (hTheory := hThyLiveTheory)
      (t := tVote) (ht := ht_mem_history)).mpr hLiveGlobal
  have hConjLocal :
      ⟪tVote⟫ ⊨[M]predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [learner, value]⟩ :=
    (Sat.and (M := M) (w := tVote)
      (φ := predicate0 liveSymb)
      (ψ := ofEvent ⟨voteSymb, [learner, value]⟩)).2
      ⟨hLiveLocal, hVoteEvent⟩
  have hConjPast :
      ⟪⟨q, †, wTop.time⟩⟫ ⊨[M]↓ᶠ (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [learner, value]⟩) :=
    (Sat.past (M := M)
      (w := ⟨q, †, wTop.time⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩)).2
        ⟨tVote, by simpa [wTop, World.time] using ht_mem,
          ht_place,
          hConjLocal⟩
  have hDiamond :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩))).2
      ⟨q, hConjPast⟩
  simpa [Formula.diamondPast]
    using hDiamond

/-- Refine a `live ∧ vote` diamond (at end of time) by exposing the supporting
echo quorum via `Vote?`. -/
theorem vote_live_to_echo_diamond
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {learner value : Signature.Value S}
    {p : P}
    (hVote :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hVoteAx : AllWorldValid M (voteBackwardAxiom echoSymb voteSymb) := by
    apply hTheory
    simp [theory]
  obtain ⟨qVote, hPastConj⟩ :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩))).1
      (by simpa [Formula.diamondPast, wTop] using hVote)
  obtain ⟨tVote, ht_mem, ht_place, hConjLocal⟩ :=
    (Sat.past (M := M)
      (w := ⟨qVote, †, wTop.time⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hPastConj
  have ht_mem_history : tVote ∈ M.history.val := by
    simpa [wTop, World.time] using ht_mem
  have hConjSplit :=
    (Sat.and (M := M) (w := tVote)
      (φ := predicate0 liveSymb)
      (ψ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hConjLocal
  have hLiveAt :
      ⟪tVote⟫ ⊨[M]predicate0 liveSymb := hConjSplit.1
  have hVoteAt :
      ⟪tVote⟫ ⊨[M] ofEvent ⟨voteSymb, [learner, value]⟩ := hConjSplit.2
  have hVoteLocal :
      ⟪tVote⟫ ⊨[M]voteBackwardAxiom echoSymb voteSymb :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := voteBackwardAxiom echoSymb voteSymb)
      hVoteAx ht_mem_history
  have hImpLearner :=
    Sat.forall_elim (M := M) (w := tVote)
      (body := fun learner' =>
        ∀ᶠ fun value' =>
          ofEvent ⟨voteSymb, [learner', value']⟩ ⇒ᶠ
            □ᶠ↓[[learner']]
              (ofEvent ⟨echoSymb, [value']⟩))
      (v := learner) hVoteLocal
  have hImpValue :=
    Sat.forall_elim (M := M) (w := tVote)
      (body := fun value' =>
        ofEvent ⟨voteSymb, [learner, value']⟩ ⇒ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value']⟩))
      (v := value) hImpLearner
  have hEchoBoxAt :
      ⟪tVote⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
    (Sat.imp (M := M) (w := tVote)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)
      (ψ := □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).1
      hImpValue hVoteAt
  have hConjEcho :
      ⟪tVote⟫ ⊨[M]predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
    (Sat.and (M := M) (w := tVote)
      (φ := predicate0 liveSymb)
      (ψ := □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).2
      ⟨hLiveAt, hEchoBoxAt⟩
  have hPastEcho :
      ⟪⟨qVote, †, wTop.time⟩⟫ ⊨[M]↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) :=
    (Sat.past (M := M)
      (w := ⟨qVote, †, wTop.time⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).2
      ⟨tVote, by simpa [wTop, World.time] using ht_mem,
        by simpa [World.place] using ht_place,
        hConjEcho⟩
  have hDiamond' :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))) :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)))).2
      ⟨qVote, hPastEcho⟩
  simpa [Formula.diamondPast, wTop]
    using hDiamond'

theorem live_vote_box_from_echo
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₂' learner : Signature.Value S} {value : Signature.Value S} {p : P}
    (hEchoBox :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[l₂']](predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[l₂']](predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hVoteAx : AllWorldValid M (voteForwardAxiom liveSymb echoSymb voteSymb) := by
    apply hTheory
    simp [theory]
  have hThyLive : M ⊨ᵀ ThyLive liveSymb := by
    intro ax hAx
    exact hTheory (Or.inl hAx)
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := wTop) (l := l₂')
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)))).1
      (by simpa [Formula.boxPast] using hEchoBox)
  refine
    (sat_box_singleton_exists (M := M)
      (w := wTop) (l := l₂')
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩))).2 ?_
  refine ⟨O, hO, ?_⟩
  intro q hqO
  have hPastLiveEcho :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) :=
    hAll q hqO
  obtain ⟨t, ht_mem, ht_place, hLiveEcho⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).1
      hPastLiveEcho
  have ht_mem_history : t ∈ M.history.val := by
    simpa [World.time] using ht_mem
  have hLiveEchoSplit :=
    (Sat.and (M := M) (w := t)
      (φ := predicate0 liveSymb)
      (ψ := □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).1
      hLiveEcho
  have hLiveLocal :
      ⟪t⟫ ⊨[M]predicate0 liveSymb := hLiveEchoSplit.1
  have hEchoLocal :
      ⟪t⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
    hLiveEchoSplit.2
  have hVoteLocal :
      ⟪t⟫ ⊨[M]voteForwardAxiom liveSymb echoSymb voteSymb :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := voteForwardAxiom liveSymb echoSymb voteSymb)
      hVoteAx ht_mem_history
  have hImpLearner :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun learner' =>
        ∀ᶠ fun value' =>
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[learner']](ofEvent ⟨echoSymb, [value']⟩)) ⇒ᶠ
              ↕ᶠ(ofEvent ⟨voteSymb, [learner', value']⟩))
      (v := learner) hVoteLocal
  have hImpValue :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun value' =>
        (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value']⟩)) ⇒ᶠ
              ↕ᶠ(ofEvent ⟨voteSymb, [learner, value']⟩))
      (v := value) hImpLearner
  have hVoteImp :=
    (Sat.imp (M := M) (w := t)
      (φ := predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))
      (ψ := ↕ᶠ(ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hImpValue
      ((Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).2
        ⟨hLiveLocal, hEchoLocal⟩)
  obtain ⟨t', ht'_mem, ht'_place, hVoteNow⟩ :=
    (Sat.sometime (M := M)
      (w := t)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hVoteImp
  have ht'_mem_history : t' ∈ M.history.val := ht'_mem
  have hLiveTop :
      ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
      (liveSymb := liveSymb)
      (hTheory := hThyLive)
      (t := t) (ht := ht_mem_history)).1
      hLiveLocal
  have ht'_place_q : t'.place = q :=
    ht'_place.trans ht_place
  have hLiveTop' :
      ⟪⟨t'.place, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb :=
    ht'_place ▸ hLiveTop
  have hLiveFuture :
      ⟪t'⟫ ⊨[M]predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
      (liveSymb := liveSymb)
      (hTheory := hThyLive)
      (t := t') (ht := ht'_mem_history)).2
      hLiveTop'
  exact
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩)).2
      ⟨t', ht'_mem_history, ht'_place_q,
        (Sat.and (M := M) (w := t')
          (φ := predicate0 liveSymb)
          (ψ := ofEvent ⟨voteSymb, [learner, value]⟩)).2
          ⟨hLiveFuture, hVoteNow⟩⟩

/-- Forget the left conjunct in an empty-guard past diamond. -/
theorem diamondPast_nil_strip_left
    {w : World P (Signature.EventType S)}
    {φ ψ : Formula S}
    (h : ⟪w⟫ ⊨[M]♢ᶠ↓[[]](φ ∧ᶠ ψ)) :
    ⟪w⟫ ⊨[M]♢ᶠ↓[[]]ψ := by
  classical
  have hDiamondNil :
      ⟪w⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ (φ ∧ᶠ ψ)) := by
    simpa [Formula.diamondPast] using h
  obtain ⟨q, hPast⟩ :=
    (Sat.diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ (φ ∧ᶠ ψ))).1 hDiamondNil
  obtain ⟨t, ht_mem, ht_place, hConj⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, w.time⟩)
      (φ := φ ∧ᶠ ψ)).1 hPast
  have hψ :=
    (Sat.and (M := M) (w := t)
      (φ := φ) (ψ := ψ)).1 hConj
  have hPastψ :
      ⟪⟨q, †, w.time⟩⟫ ⊨[M]↓ᶠ ψ :=
    (Sat.past (M := M)
      (w := ⟨q, †, w.time⟩)
      (φ := ψ)).2
      ⟨t, ht_mem, ht_place, hψ.2⟩
  have hDiamond' :
      ⟪w⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ ψ) :=
    (Sat.diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ ψ)).2
      ⟨q, hPastψ⟩
  simpa [Formula.diamondPast]
    using hDiamond'

/-- At end of time, a delivery for `(reporting, learner, value)` requires a
vote quorum witnessed at `reporting`. -/
theorem deliver_to_vote_box_end
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {reporting learner value : Signature.Value S}
    {p : P}
    (hDeliver :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting, learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  have hDeliverAx : AllWorldValid M (deliverBackwardAxiom voteSymb deliverSymb) := by
    apply hTheory
    simp [theory]
  obtain ⟨tDeliver, ht_mem, hSubset, hBox⟩ :=
    Deliver.box_witness (M := M)
      (voteSymb := voteSymb) (deliverSymb := deliverSymb)
      (hDeliverAx := hDeliverAx)
      (reporting := reporting) (learner := learner)
      (value := value) (p := p)
      (hDeliver := hDeliver)
  exact
    Deliver.lift_box_to_end (M := M)
      (voteSymb := voteSymb)
      (reporting := reporting) (learner := learner)
      (value := value) (t := tDeliver)
      (hSubset := hSubset) (hBox := hBox)
      (p := p)

end ThyHBB2
end Examples
end ModalDistribution
