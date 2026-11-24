import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Examples.HBBSafe.Safety
import ModalDistribution.Examples.HBBSafe.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBSafe Happy Termination

This file contains the Happy Termination theorem for the HBBSafe broadcast protocol:

- **Happy Termination** (`happy_termination`): Under uniqueness of proposals and a live quorum,
  if a live participant knows a proposal, it will eventually be delivered.
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

section HappyTermination

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 6.6.3 (Happy Termination). Happy Termination for HBBSafe.

Under uniqueness of proposals and a live quorum, if a live participant knows
a proposal for value v, then v will eventually be delivered. This establishes
that proposals from live participants will eventually propagate to delivery.

See also: `cascade_termination`, `happy_termination_boxPast`. -/
theorem happy_termination
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M](♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
         predicate0 liveSymb ⇒ᶠ
         ↕ᶠ(ofEvent ⟨deliverSymb, [l, l, v]⟩) := by
  intro p hKnown hLive_p
  have hThyLive := theory_thyLive hTheory
  -- Proposition 5.2.8, `⊨ □_l live`; Lemma 6.5.2(2) with Lemma 6.6.1; Lemma 5.2.11:
  -- a live `l`-quorum knows of an `l`-quorum of `echo(v)`.
  have hKnowsEchoes := unique_propose_live_nested_echo_quorum hThyLive
    (theory_echo_forward hTheory) (theory_echo_backward hTheory) hLiveQuorum hUnique
    (diamondPast_nil_valid_of_end hKnown)
  -- Lemma 6.6.2, `⊨ ∃!v.♢↓propose(v)`: `l` is everywhere and always safe.
  have hSafe : □W⊨[M] ⇕ᶠ ofPredicate ⟨safeSymb, [l]⟩ := fun {t} _ =>
    at_most_one_propose_safe hTheory l t.place (unique_propose_guard_at_history (hUnique _))
  -- Lemma 6.5.2(2), (Vote!): the live `l`-quorum votes `(l, v)`.
  have hVotes := boxPast_live_of_eventual_quorum hThyLive _ _ l hKnowsEchoes
    (vote_forward_imp_of_everytime hTheory hSafe)
  -- (Knowledge□↓), Lemma 6.5.3, (Deliver!): every live participant eventually delivers.
  exact live_quorum_eventually_consequent hThyLive hVotes
    (deliver_forward_imp (theory_deliver_forward hTheory)) p hLive_p

/-- Paper: Proposition 6.6.3, first corollary. Whenever a live learner
observes the guarded proposal diamond, every member of its quorum knows (in the
past) that the corresponding value was delivered. -/
theorem happy_termination_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
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

/-- Paper: Proposition 6.6.3, second corollary. Witnessing the guarded
proposal diamond guarantees the delivery diamond for learner `l`. -/
theorem happy_termination_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
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

end HappyTermination
end HBBSafe
end Examples
end ModalDistribution
