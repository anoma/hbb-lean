import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBCorr.Axioms
import ModalDistribution.Examples.HBBCorr.Lemmas
import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBCorr Cascade Termination

Proposition 8.4.5 (Cascade Termination) for `HBBCorr`. When `l₁`
and `l₂` are always correlated and `l₂` has a live quorum, any delivery for
`l₁` eventually propagates to a live delivery for `l₂`.
-/

namespace ModalDistribution
namespace Examples
namespace HBBCorr

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
variable {correlationSymb : Signature.PredSymb S}

/-- Paper: Proposition 8.4.5 (Cascade Termination). If learners `l₁` and `l₂` are always
correlated and `l₂` has a live quorum, then any delivery for `l₁` eventually
forces a live delivery for `l₂`. -/
theorem cascade_termination
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hLiveQuorum : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) :
    ⊨[M]
      (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
        predicate0 liveSymb ⇒ᶠ
        ↕ᶠ (ofEvent ⟨deliverSymb, [l₂, v]⟩) := by
  have hThyLive := theory_thyLive hTheory
  intro p hDeliver hLive
  -- `(Deliver?)`: the delivery for `l₁` is backed by an `l₁`-quorum of votes.
  have hVotes₁ := deliver_to_vote_box_end hTheory hDeliver
  -- Lemma 8.4.4(2), Propositions 5.2.10 and 5.2.8: the live `l₂`-quorum
  -- eventually knows of a vote of the intersecting `l₁`-quorum.
  have hKnows := boxPast_live_knows_of_intersecting hThyLive
    (correlation_implies_quorum_intersection hTheory hCorrelation) hLiveQuorum
    (fun _ => hVotes₁)
  -- Lemma 6.5.2(2) with `(Vote'!)` as Lemma 8.4.3(3), using `⇕(l₁ ≐ l₂)`:
  -- the `l₂`-quorum votes `v`.
  have hVotes₂ := boxPast_live_of_eventual_quorum hThyLive _ (ofEvent ⟨voteSymb, [l₂, v]⟩) l₂
    hKnows fun ht hKnowsVote =>
      correlated_vote_eventually hTheory (live_quorum_seq _ M hThyLive hLiveQuorum) ht
        (sometime_mono (fun _ _ h => by
          simp only [Sat.and] at h ⊢
          exact ⟨⟨h.1, (Sat.everytime ..).2 fun _ hu _ =>
            correlation_of_mem hTheory hCorrelation hu⟩, h.2⟩) hKnowsVote)
  -- Lemma 6.5.3, applied to (Knowledge□↓) and (Deliver!), concludes
  -- eventual delivery.
  exact live_quorum_eventually_consequent hThyLive hVotes₂
    (deliver_forward_imp (theory_deliver_forward hTheory)) p hLive

/-- Paper: Proposition 8.4.5, first corollary. A delivery for `l₁`
forces every member of `l₂`'s quorum to know (in the past) that `l₂` delivered
the same value. -/
theorem cascade_termination_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hLiveQuorum : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂]] (ofEvent ⟨deliverSymb, [l₂, v]⟩) :=
  endValid_boxPast_of_imp_sometime M hLiveQuorum
    (cascade_termination hTheory hCorrelation hLiveQuorum)

/-- Paper: Proposition 8.4.5, second corollary. A delivery for `l₁`
produces a delivery for `l₂` somewhere in the past. -/
theorem cascade_termination_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S} {v : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    (hLiveQuorum : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂, v]⟩) :=
  endValid_diamondPast_of_imp_sometime M hLiveQuorum
    (cascade_termination hTheory hCorrelation hLiveQuorum)

end HBBCorr
end Examples
end ModalDistribution
