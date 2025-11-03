import ModalDistribution.Examples.ThyLive
import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Logic.Semantics

/-!
# ThyHBB1 Liveness Helpers

Auxiliary lemmas supporting liveness arguments for `ThyHBB1`.  These facts
factor out the recurrent reasoning steps shared by the Liveness~1 and
Liveness~2 proofs, keeping the main theorems focused on the high-level flow.
-/

namespace ModalDistribution
namespace Examples

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

section

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {voteSymb deliverSymb : Signature.EventSymb S}
variable {reporting learner : Signature.Value S}
variable {value : Signature.Value S}

/-- Helper: instantiate the `Deliver!` forward rule at a concrete history
point.  This lifts a local vote quorum and liveness witness into an eventual
delivery fact at the same world. -/
lemma deliver_from_vote_box_local
    (hDeliverAx : AllWorldValid M
      (deliverForwardAxiom liveSymb voteSymb deliverSymb))
    {t : World P (Signature.EventType S)}
    (ht_mem : t ∈ M.history.val)
    (hLiveLocal : ⟪t⟫ ⊨[M]predicate0 liveSymb)
    (hVoteLocal :
      ⟪t⟫ ⊨[M]□ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ⟪t⟫ ⊨[M]↕ᶠ(ofEvent ⟨deliverSymb, [reporting, learner, value]⟩) := by
  classical
  have hForward :
      ⟪t⟫ ⊨[M]
        deliverForwardAxiom liveSymb voteSymb deliverSymb :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := deliverForwardAxiom liveSymb voteSymb deliverSymb)
      hDeliverAx ht_mem
  have hReporting :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun reporting' =>
        ∀ᶠ (fun learner' => ∀ᶠ (fun value' =>
          (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[reporting']] (ofEvent ⟨voteSymb, [learner', value']⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨deliverSymb, [reporting', learner', value']⟩))))
      (v := reporting) hForward
  have hLearner :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun learner' =>
        ∀ᶠ (fun value' =>
          (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner', value']⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨deliverSymb, [reporting, learner', value']⟩)))
      (v := learner) hReporting
  have hValue :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun value' =>
        (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value']⟩)) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value']⟩))
      (v := value) hLearner

  have hDeliverGuard :
      ⟪t⟫ ⊨[M](predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    (Sat.and (M := M) (w := t)
      (φ := predicate0 liveSymb)
      (ψ := □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))).2
    ⟨hLiveLocal, hVoteLocal⟩
  exact
    (Sat.imp (M := M) (w := t)
      (φ := predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))
      (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩))).1
      hValue hDeliverGuard

/-- From end-of-time knowledge of a vote quorum, deduce eventual
delivery.  This packages the `Deliver!` instantiation together with the
time-shifting arguments based on `ThyLive`. -/
lemma deliver_from_vote_box
    (hThyLive : M ⊨ᵀ ThyLive liveSymb)
    (hDeliverAx : AllWorldValid M
      (deliverForwardAxiom liveSymb voteSymb deliverSymb))
    {p : P}
    (hLiveTop : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb)
    (hVotesTop :
        ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]↕ᶠ(□ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value]⟩))) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]↕ᶠ(ofEvent ⟨deliverSymb, [reporting, learner, value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩

  -- Pull the sometime guard on the vote quorum back into the history.
  have hPastVotes :
      ⟪wTop⟫ ⊨[M]↓ᶠ (□ᶠ↓[[reporting]](ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    (Sat.atEnd (M := M)
      (w := wTop)
      (φ := ↓ᶠ (□ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩)))).1
      (by
        simpa [Formula.sometime]
          using hVotesTop)
  obtain ⟨t, ht_mem, ht_place, hVoteLocal⟩ :=
    (Sat.past (M := M)
      (w := wTop)
      (φ := □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hPastVotes

  -- Translate the liveness witness along the `ThyLive` equivalence.
  have hLiveEnd :
      ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb := by
    cases ht_place
    simpa [wTop, World.place, World.time] using hLiveTop
  have hLiveLocal :
      ⟪t⟫ ⊨[M] predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
      (liveSymb := liveSymb)
      (hTheory := hThyLive)
      (t := t) (ht := ht_mem)).mpr hLiveEnd

  -- Apply the local `Deliver!` helper and push the result back to end-of-time.
  have hDeliverLocal :=
    deliver_from_vote_box_local
      (M := M)
      (liveSymb := liveSymb)
      (voteSymb := voteSymb)
      (deliverSymb := deliverSymb)
      (reporting := reporting)
      (learner := learner)
      (value := value)
      (t := t)
      (hDeliverAx := hDeliverAx)
      (ht_mem := ht_mem)
      (hLiveLocal := hLiveLocal)
      (hVoteLocal := hVoteLocal)

  have hPastDeliverEnd :
      ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]↓ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩) :=
    (Sat.atEnd (M := M)
      (w := t)
      (φ := ↓ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩))).1
      (by
        simpa [Formula.sometime]
          using hDeliverLocal)
  have hPastDeliverTop :
      ⟪wTop⟫ ⊨[M]↓ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩) := by
    cases ht_place
    simpa [wTop, World.place, World.time] using hPastDeliverEnd
  exact
    (Sat.atEnd (M := M)
      (w := wTop)
      (φ := ↓ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩))).2
      hPastDeliverTop

end

end Examples
end ModalDistribution
