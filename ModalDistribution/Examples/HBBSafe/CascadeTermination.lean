import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Examples.HBBSafe.Safety
import ModalDistribution.Examples.HBBSafe.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBSafe Cascade Termination

This file contains the Cascade Termination theorem for the HBBSafe broadcast protocol:

- **Cascade Termination** (`cascade_termination`): If a value is delivered to one learner and
  certain liveness/intersection conditions hold, it will eventually be delivered to another
  learner.
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
theorem cascade_termination
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
  intro p hDeliver hLive_p
  have hThyLive := theory_thyLive hTheory
  -- (Deliver?), Lemma 4.2.3(1): an `l₁'`-quorum voted `(l, v)`.
  have hVotes₁ : ⊨[M] □ᶠ↓[[l₁']] ofEvent ⟨voteSymb, [l, v]⟩ := fun _ =>
    deliver_to_vote_box_end (theory_deliver_backward hTheory) hDeliver
  -- Propositions 5.2.10 and 5.2.8, `⊨ ♢_{l₁' l₂'} ⊤`, `⊨ □_{l₂'} live`: a live
  -- `l₂'`-quorum knows of a vote `(l, v)`.
  have hKnowsVote := boxPast_live_knows_of_intersecting hThyLive hIntersect hLive hVotes₁
  -- (Vote?), Lemma 4.2.3(1): that quorum knows of an `l`-quorum of `echo(v)`.
  have hKnowsEchoes := boxPast_live_knows_vote_knows_echo_quorum
    (fun _ ht hVote => (vote_backward_elim (theory_vote_backward hTheory) ht hVote).2) hKnowsVote
  -- Lemma 6.5.1, `⊨ safe(l)`, Lemma 6.5.2(2), (Vote!): the live `l₂'`-quorum votes `(l, v)`.
  have hVotes₂ := boxPast_live_of_eventual_quorum hThyLive _ _ l₂' hKnowsEchoes
    (vote_forward_imp hTheory hSafe)
  -- (Knowledge□↓), Lemma 6.5.3, (Deliver!): every live participant eventually delivers.
  exact live_quorum_eventually_consequent hThyLive hVotes₂
    (deliver_forward_imp (theory_deliver_forward hTheory)) p hLive_p

/-- Paper: Proposition 6.5.5, first corollary. Corollary: a delivery for `(l₁', l)`
forces every `l₂'`-quorum member to know (in the past) that `(l₂', l)` was
delivered. -/
theorem cascade_termination_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂']] (ofEvent ⟨deliverSymb, [l₂', l, v]⟩) :=
  endValid_boxPast_of_imp_sometime M hLive
    (cascade_termination hTheory hIntersect hSafe hLive)

/-- Paper: Proposition 6.5.5, second corollary. Corollary: a delivery for `(l₁', l)`
forces a delivery for `(l₂', l)` somewhere in the past of the history. -/
theorem cascade_termination_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l, v]⟩) :=
  endValid_diamondPast_of_imp_sometime M hLive
    (cascade_termination hTheory hIntersect hSafe hLive)

end CascadeTermination
end HBBSafe
end Examples
end ModalDistribution
