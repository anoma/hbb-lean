import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# Shared HBB axiom schemes

Axiom formulas common to the broadcast theories `ThyHBB1`, `ThyHBB2`, and
`ThyHBB3`. The paper states these once and reuses them across Figures 7, 9,
and 11: the `Echo?`, `EchoNE`, and `Echo!` rules are identical in all three
theories, and the `Deliver?`/`Deliver!` rules are identical in `ThyHBB1` and
`ThyHBB2` (in `ThyHBB3` the deliver event is binary, so it has its own).
Each theory's `Axioms.lean` assembles its axiom set from these plus its own
vote rules. The `Lemmas` section holds the shared instantiation lemmas for
`Deliver?` and `Deliver!`.
-/

namespace ModalDistribution
namespace Examples
namespace HBB

open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History PreHistory World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

/-- Paper: Figures 7/9/11, rule (Echo?). Backward rule `Echo?`: every `echo(v)` stems from a past `propose(v)`. -/
@[simp] def echoBackwardAxiom
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value =>
    ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))

/-- Paper: Figures 7/9/11, axiom (EchoNE). Axiom `EchoNE`: sequential participants echo at most one value. -/
@[simp] def echoNonEquivAxiom
    (echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value => ∀ᶠ (fun altValue =>
    ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
      (↓ᶠ (ofEvent ⟨echoSymb, [altValue]⟩)) ⇒ᶠ
        (value ≃ᶠ altValue)))

/-- Paper: Figures 7/9/11, rule (Echo!). Forward rule `Echo!`: live knowledge of a proposal eventually triggers an
echo of some (possibly different) value. -/
@[simp] def echoForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
      ∃ᶠ (fun witness =>
        ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)))

/-- Paper: Figures 7/9, rule (Deliver?). Backward rule `Deliver?` (ternary deliver): deliveries require a
reporting-learner quorum of past votes. -/
@[simp] def deliverBackwardAxiom
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨deliverSymb, [reporting, learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))))

/-- Paper: Figures 7/9, rule (Deliver!). Forward rule `Deliver!` (ternary deliver): live knowledge of a vote quorum
eventually leads to delivery. -/
@[simp] def deliverForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩)) ⇒ᶠ
      ↕ᶠ(ofEvent ⟨deliverSymb, [reporting, learner, value]⟩))))

section Lemmas

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Instantiates the `Deliver?` axiom to extract the vote quorum that backs a
delivery observed at end of time. -/
theorem deliver_box_witness
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


/-- A delivery observed at the end of time yields a reporting-learner quorum of
votes at the end of time, by `Deliver?` and box lifting. -/
theorem deliver_to_vote_box_end
    (hDeliverAx : AllWorldValid M (deliverBackwardAxiom voteSymb deliverSymb))
    {reporting learner value : Signature.Value S}
    {p : P}
    (hDeliver :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting, learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
      □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  obtain ⟨tDeliver, ht_mem, hSubset, hBox⟩ :=
    deliver_box_witness (M := M)
      (hDeliverAx := hDeliverAx)
      (reporting := reporting) (learner := learner)
      (value := value) (p := p)
      (hDeliver := hDeliver)
  exact
    lift_boxPast_to_end (M := M)
      (t := tDeliver)
      (hSubset := hSubset) (hBox := hBox) p


/-- The instantiated `Deliver!` implication: live knowledge of a vote quorum
eventually yields a delivery. This is the form consumed by Lemma 6.4.3. -/
theorem deliverForward_imp
    (hAx : AllWorldValid M (deliverForwardAxiom liveSymb voteSymb deliverSymb))
    {reporting learner value : S.Value} :
    □W⊨[M]((predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩)) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩)) := by
  classical
  intro t ht
  have hLocal :
      ⟪t⟫ ⊨[M] deliverForwardAxiom liveSymb voteSymb deliverSymb :=
    hAx ht
  have hReporting :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun reporting' =>
        ∀ᶠ (fun learner' => ∀ᶠ (fun value' =>
          (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[reporting']] (ofEvent ⟨voteSymb, [learner', value']⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨deliverSymb, [reporting', learner', value']⟩))))
      (v := reporting)
      (by simpa [deliverForwardAxiom] using hLocal)
  have hLearner :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun learner' =>
        ∀ᶠ (fun value' =>
          (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner', value']⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨deliverSymb, [reporting, learner', value']⟩)))
      (v := learner) hReporting
  exact
    Sat.forall_elim (M := M) (w := t)
      (body := fun value' =>
        (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value']⟩)) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value']⟩))
      (v := value) hLearner

end Lemmas

end HBB
end Examples
end ModalDistribution
