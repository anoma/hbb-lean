import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Examples.HBBSimp.Lemmas
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBSimp Cascade Termination

Proposition 7.3.2: if reporting learners `l₁'` and `l₂'` have intersecting
quorums and `l₂'` has a live quorum, then a delivery for `(l₁', ℓ)` leads every
live participant to deliver for `(l₂', ℓ)`.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSimp

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 7.3.2 (Cascade Termination). If reporting learners `l₁'` and `l₂'`
have intersecting quorums and learner `l₂'` is live, then any delivery for
`(l₁', ℓ)` propagates to `(l₂', ℓ)`. -/
theorem cascade_termination
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩)) ⇒ᶠ
         predicate0 liveSymb ⇒ᶠ
         ↕ᶠ(ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) := by
  intro p
  refine Sat.imp_intro _ _ fun hDeliver => ?_
  have hThyLive := theory_thyLive hTheory
  -- (Deliver?), Lemma 4.2.3(1): `⊨ □↓[l₁'] vote(ℓ, v)`.
  have hVotes : ⊨[M]□ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [ℓ, v]⟩) := fun q =>
    deliver_to_vote_box_end (theory_deliver_backward hTheory)
      (diamondPast_nil_valid_of_end hDeliver q)
  -- Propositions 5.2.10 and 5.2.8, `⊨ ♢[l₁' l₂'] ⊤`, `⊨ □[l₂'] live`:
  -- `⊨ □↓[l₂'] (live ∧ ♢↓ vote(ℓ, v))`.
  have hKnowVote := boxPast_live_knows_of_intersecting hThyLive hIntersect hLive hVotes
  -- (Vote?), Lemma 4.2.3(1): `⊨ □↓[l₂'] (live ∧ □↓[ℓ] echo(v))`.
  have hKnowEchoes := boxPast_live_knows_vote_knows_echo_quorum
    (fun _ ht => vote_backward_elim (theory_vote_backward hTheory) ht) hKnowVote
  -- Lemma 6.5.2(2), (Vote!): `⊨ □↓[l₂'] (live ∧ vote(ℓ, v))`.
  have hVotes' := boxPast_live_of_eventual_quorum hThyLive _ _ l₂' hKnowEchoes
    (vote_forward_imp hTheory)
  -- (Knowledge□↓), Lemma 6.5.3, (Deliver!): `⊨ live ⇒ ↕ deliver(l₂', ℓ, v)`.
  exact live_quorum_eventually_consequent hThyLive hVotes'
    (deliver_forward_imp (theory_deliver_forward hTheory)) p

/-- Paper: Proposition 7.3.2, first corollary. A delivery for `(l₁', ℓ)`
forces every member of `l₂'`'s quorum to know (in the past) that `(l₂', ℓ)` was
delivered. -/
theorem cascade_termination_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂']] (ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) :=
  endValid_boxPast_of_imp_sometime M hLive (cascade_termination hTheory hIntersect hLive)

/-- Paper: Proposition 7.3.2, second corollary. A delivery for `(l₁', ℓ)`
eventually yields a delivery for `(l₂', ℓ)`. -/
theorem cascade_termination_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' ℓ : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', ℓ, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', ℓ, v]⟩) :=
  endValid_diamondPast_of_imp_sometime M hLive (cascade_termination hTheory hIntersect hLive)

end HBBSimp
end Examples
end ModalDistribution
