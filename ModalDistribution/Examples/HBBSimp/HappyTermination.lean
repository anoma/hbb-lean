import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Examples.HBBSimp.Lemmas
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBSimp Happy Termination

Proposition 7.3.3: if learner `l` has a live quorum and exactly one value is
proposed, then once some live participant learns of the proposal, every live
participant eventually delivers it for `(l, l)`.
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
  intro p
  refine Sat.imp_intro _ _ fun hSeenPropose => ?_
  have hThyLive := theory_thyLive hTheory
  -- Proposition 5.2.8, Lemma 6.6.1, (Echo?) with Lemma 4.2.2, Lemma 6.5.2(2)
  -- and Lemma 5.2.11: `⊨ □↓[l] (live ∧ □↓[l] echo(v))`.
  have hEchoes : ⊨[M]□ᶠ↓[[l]] (predicate0 liveSymb ∧ᶠ □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
    unique_propose_live_nested_echo_quorum hThyLive (theory_echo_forward hTheory)
      (theory_echo_backward hTheory) hLiveQuorum hUnique
      (diamondPast_nil_valid_of_end hSeenPropose)
  -- Lemma 6.5.2(2), (Vote!): `⊨ □↓[l] (live ∧ vote(l, v))`.
  have hVotes := boxPast_live_of_eventual_quorum hThyLive _ _ l hEchoes
    (vote_forward_imp hTheory)
  -- (Knowledge□↓), Lemma 6.5.3, (Deliver!): `⊨ live ⇒ ↕ deliver(l, l, v)`.
  exact live_quorum_eventually_consequent hThyLive hVotes
    (deliver_forward_imp (theory_deliver_forward hTheory)) p

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
         □ᶠ↓[[l]] (ofEvent ⟨deliverSymb, [l, l, v]⟩) :=
  endValid_boxPast_of_imp_sometime M hLiveQuorum
    (happy_termination hTheory hLiveQuorum hUnique)

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
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l, l, v]⟩) :=
  endValid_diamondPast_of_imp_sometime M hLiveQuorum
    (happy_termination hTheory hLiveQuorum hUnique)

end HBBSimp
end Examples
end ModalDistribution
