import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBSimp.Axioms
import ModalDistribution.Examples.HBBSimp.Lemmas
import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Core.Semifilter
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBSimp Happy Termination

This file records the Happy Termination statement for `HBBSimp`, mirroring
Happy Termination for HBBSimp. Under a live quorum for learner `l` and a
unique proposed value, any live participant that learns about the proposal will
eventually deliver it for `(l,l)`.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSimp

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

/-- Paper: Proposition 7.3.3 (Happy Termination). If learner `l` has a live quorum and
there is exactly one proposed value, then any live participant that learns about
the proposal will eventually deliver it for `(l,l)`. -/
theorem happy_termination
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M](♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
         predicate0 liveSymb ⇒ᶠ
         ↕ᶠ(ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hSeenPropose
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLiveHere
  have hThyLive : M ⊨ᵀ thyLive liveSymb :=
    theory_thyLive (M := M) hTheory
  -- Lemma 6.6.1, Proposition 5.2.8, (Echo?) with Lemma 4.2.2,
  -- Lemma 6.5.2(2) and Lemma 5.2.11: a live `l`-quorum knows of an
  -- `l`-quorum of echoes of `v`.
  have hEchoNestedGlobal :
      ⊨[M]□ᶠ↓[[l]]
        (predicate0 liveSymb ∧ᶠ □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
    HBB.unique_propose_live_nested_echo_quorum (M := M)
      (hLiveTheory := hThyLive)
      (hEcho := theory_echo_forward (M := M) hTheory)
      (hEchoBack := theory_echo_backward (M := M) hTheory)
      (hLiveQuorum := hLiveQuorum) (hUnique := hUnique)
      (hKnown := diamondPast_nil_valid_of_end (M := M)
        (by simpa [wTop] using hSeenPropose))
  -- Lemma 6.5.2(2) with (Vote!): the quorum votes.
  have hVotesGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩) :=
    HBB.boxPast_live_of_eventual_quorum
      (M := M) (liveSymb := liveSymb)
      (φ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
      (ψ := ofEvent ⟨voteSymb, [l, v]⟩)
      (l := l)
      (hLiveTheory := hThyLive)
      (hQuorum := hEchoNestedGlobal)
      (hImp := vote_forward_imp (M := M) (hTheory := hTheory))

  -- Lemma 6.5.3, applied to (Knowledge□↓) and (Deliver!), concludes
  -- eventual delivery.
  have hDeliverEventually :
      ⟪wTop⟫ ⊨[M]
        ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
    have hGlobal :=
      HBB.live_quorum_eventually_consequent (M := M)
        (hLiveTheory := hThyLive)
        (hQuorum := hVotesGlobal)
        (hImp := HBB.deliver_forward_imp (M := M)
          (theory_deliver_forward (M := M) hTheory))
    exact
      Sat.imp_elim (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l, l, v]⟩))
        (by simpa [wTop] using hGlobal p) hLiveHere
  simpa [wTop] using hDeliverEventually

/-- Paper: Proposition 7.3.3, first corollary. When the guarded proposal
diamond holds, every member of learner `l`'s quorum knows (in the past) that the
value was delivered. -/
theorem happy_termination_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M](♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
         □ᶠ↓[[l]] (ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLiveQuorum)
      (hMain :=
      happy_termination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (l := l) (v := v)
        (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum)
        (hUnique := hUnique))
/-- Paper: Proposition 7.3.3, second corollary. The guarded proposal diamond
ensures the delivery diamond for learner `l`. -/
theorem happy_termination_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M](♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLiveQuorum)
      (hMain :=
      happy_termination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (l := l) (v := v)
        (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum)
        (hUnique := hUnique))
end HBBSimp
end Examples
end ModalDistribution
