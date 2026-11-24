import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBSafe.Agreement
import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Examples.HBBSafe.Safety
import ModalDistribution.Examples.HBBSafe.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBSafe Cascade Termination

This file contains the Cascade Termination theorem for the HBBSafe broadcast protocol:

- **Cascade Termination** (`cascadeTermination`): If a value is delivered to one learner and certain
  liveness/intersection conditions hold, it will eventually be delivered to another learner.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSafe

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

section CascadeTermination

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 6.5.5 (Cascade Termination). Cascade Termination specialised to `HBBSafe`.
If a value is delivered to learner l₁' and:
- Learners l₁' and l₂' have intersecting quorums
- The safe condition holds for learner l
- All of learner l₂'s quorum members are live
Then if p is live, the value will eventually be delivered to learner l₂'. -/
theorem cascadeTermination
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         predicate0 liveSymb ⇒ᶠ
         ↕ᶠ(ofEvent ⟨deliverSymb, [l₂', l, v]⟩) := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLivep

  have hThyLiveTheory : M ⊨ᵀ ThyLive liveSymb :=
    theory_thyLive (M := M) hTheory

  -- (Deliver?) with Lemma 4.2.3(1): the delivery forces an end-of-time
  -- quorum of votes at the reporting learner.
  have hVoteBoxTop :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [l, v]⟩) := by
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := theory_deliverBackward (M := M) hTheory)
          (reporting := l₁') (learner := l)
          (value := v) (p := p)
          (hDeliver := hDeliver)
  have hVoteBoxGlobal :
      ⊨[M]□ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [l, v]⟩) := fun q => by
    simpa [wTop] using hVoteBoxTop

  -- Propositions 5.2.10 and 5.2.8: the live `l₂'`-quorum eventually knows of
  -- a vote of the intersecting `l₁'`-quorum.
  have hKnowsVoteGlobal :
      ⊨[M]□ᶠ↓[[l₂']]
        (predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩)) :=
    boxPast_live_knows_of_intersecting (M := M)
      (hLiveTheory := hThyLiveTheory)
      (hIntersect := hIntersect) (hLive := hLive)
      (hQuorum := hVoteBoxGlobal)

  -- (Vote?) with Lemma 4.2.3(1): knowing of the vote, the quorum knows of an
  -- `l`-quorum of echoes.
  have hStep4Global :
      ⊨[M]□ᶠ↓[[l₂']]
        (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
    boxPast_live_knowsVote_knowsEchoQuorum (M := M)
      (hVoteEcho := fun _ ht hVote =>
        (voteBackward_elim (M := M)
          (hAx := theory_voteBackward (M := M) hTheory)
          (hMem := ht) (hVote := hVote)).2)
      (hQuorum := hKnowsVoteGlobal)

  -- Lemma 6.5.2(2) with (Vote!): the safe learner's quorum eventually votes.
  -- Safety enters through `voteForward_imp`, i.e. Lemma 6.5.1.
  have hVotesGlobal :
      ⊨[M]□ᶠ↓[[l₂']]
        (predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [l, v]⟩) :=
    boxPast_live_of_eventual_quorum
      (M := M) (liveSymb := liveSymb)
      (φ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
      (ψ := ofEvent ⟨voteSymb, [l, v]⟩)
      (l := l₂')
      (hLiveTheory := hThyLiveTheory)
      (hQuorum := hStep4Global)
      (hImp := voteForward_imp (M := M)
        (hTheory := hTheory) (hSafe := hSafe))

  -- Lemma 6.5.3, applied to (Knowledge□↓) and (Deliver!): eventual vote
  -- knowledge becomes eventual delivery.
  have hDeliverEventually :
      ⊨[M](predicate0 liveSymb ⇒ᶠ
        ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', l, v]⟩)) :=
    live_quorum_eventually_consequent (M := M)
      (hLiveTheory := hThyLiveTheory)
      (hQuorum := hVotesGlobal)
      (hImp := HBB.deliverForward_imp (M := M)
        (theory_deliverForward (M := M) hTheory))
  exact
    Sat.imp_elim (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', l, v]⟩))
      (by simpa [wTop] using hDeliverEventually p) hLivep

/-- Paper: Proposition 6.5.5, first corollary. Corollary: a delivery for `(l₁', l)`
forces every `l₂'`-quorum member to know (in the past) that `(l₂', l)` was
delivered. -/
theorem cascadeTermination_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂']] (ofEvent ⟨deliverSymb, [l₂', l, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      cascadeTermination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hSafe := hSafe)
        (hLive := hLive))
/-- Paper: Proposition 6.5.5, second corollary. Corollary: a delivery for `(l₁', l)`
forces a delivery for `(l₂', l)` somewhere in the past of the history. -/
theorem cascadeTermination_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      cascadeTermination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hSafe := hSafe)
        (hLive := hLive))
end CascadeTermination
end HBBSafe
end Examples
end ModalDistribution
