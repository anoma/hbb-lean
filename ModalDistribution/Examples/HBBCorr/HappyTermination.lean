import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBCorr.Axioms
import ModalDistribution.Examples.HBBCorr.Lemmas
import ModalDistribution.Examples.HBB.Termination
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.Semifilter
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBCorr Happy Termination

Proposition 8.5.1 (Happy Termination) for `HBBCorr`. Under a live quorum for
learner `l` and a unique proposed value, any live participant that learns about
the proposal will eventually deliver it for `l`.
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

/-- Paper: Proposition 8.5.1 (Happy Termination). If learner `l` has a live quorum and
there is exactly one proposed value, then any live participant that learns about
the proposal will eventually deliver it for `l`. -/
theorem happy_termination
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l : Signature.Value S} {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M]
      (♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        predicate0 liveSymb ⇒ᶠ
        ↕ᶠ (ofEvent ⟨deliverSymb, [l, v]⟩) := by
  have hThyLive := theory_thyLive hTheory
  intro p hKnown hLive
  -- Lemma 6.6.1, Proposition 5.2.8, (Echo?) with Lemma 4.2.2,
  -- Lemma 6.5.2(2) and Lemma 5.2.11: a live `l`-quorum knows of an
  -- `l`-quorum of echoes of `v`.
  have hEchoes := unique_propose_live_nested_echo_quorum hThyLive
    (theory_echo_forward hTheory) (theory_echo_backward hTheory) hLiveQuorum hUnique
    (diamondPast_nil_valid_of_end hKnown)
  -- Lemma 6.5.2(2) with Lemma 8.4.3(4): the quorum votes.
  have hVotes := boxPast_live_of_eventual_quorum hThyLive _ (ofEvent ⟨voteSymb, [l, v]⟩) l
    hEchoes (live_echo_eventually_vote hTheory (live_quorum_seq _ M hThyLive hLiveQuorum))
  -- Lemma 6.5.3, applied to (Knowledge□↓) and (Deliver!), concludes
  -- eventual delivery.
  exact live_quorum_eventually_consequent hThyLive hVotes
    (deliver_forward_imp (theory_deliver_forward hTheory)) p hLive

/-- Paper: Proposition 8.5.1, first corollary. When the guarded proposal
statement holds, every member of learner `l`'s quorum knows (in the past) that
`l` delivered the value. -/
theorem happy_termination_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l : Signature.Value S} {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M]
      (♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        □ᶠ↓[[l]] (ofEvent ⟨deliverSymb, [l, v]⟩) :=
  endValid_boxPast_of_imp_sometime M hLiveQuorum
    (happy_termination hTheory hLiveQuorum hUnique)

/-- Paper: Proposition 8.5.1, second corollary. The guarded proposal
statement guarantees the delivery diamond for learner `l`. -/
theorem happy_termination_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l : Signature.Value S} {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M]
      (♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l, v]⟩) :=
  endValid_diamondPast_of_imp_sometime M hLiveQuorum
    (happy_termination hTheory hLiveQuorum hUnique)

end HBBCorr
end Examples
end ModalDistribution
