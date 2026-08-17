import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB3.Axioms
import ModalDistribution.Examples.ThyHBB3.Lemmas
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.Semifilter
import ModalDistribution.Logic.Properties.Modalities

/-!
# ThyHBB3 Liveness 1

This file records the Liveness~1 statement for `ThyHBB3`, formalising
Liveness property 1 for ThyHBB3. Under a live quorum for learner `l` and a
unique proposed value, any live participant that learns about the proposal will
eventually deliver it for `l`.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB3

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

/-- Paper: Proposition 8.5.1 (Liveness 1). If learner `l` has a live quorum and
there is exactly one proposed value, then any live participant that learns about
the proposal will eventually deliver it for `l`. -/
theorem livenessOne
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
  classical
  have hLiveSequentialGlobal :
      ⊨[M]□ᶠ[[l]] Formula.seq :=
    live_quorum_seq (M := M)
      (hTheory := fun _ hAx => hTheory (Or.inl hAx))
      (hLiveQuorum := hLiveQuorum)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hThyLive : M ⊨ᵀ ThyLive liveSymb :=
    fun _ hAx => hTheory (Or.inl hAx)
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hProposeDiamond
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLiveHere
  have hProposeQuorumGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :=
    live_eventually_knows_event (M := M)
      (liveSymb := liveSymb)
      (l := l)
      (evt := ⟨proposeSymb, [v]⟩)
      (hTheory := hThyLive)
      (hLive := hLiveQuorum)
      (hEvent :=
        by
          intro q
          obtain ⟨q', hPast⟩ :=
            (Sat.diamond_nil (M := M)
              (w := wTop)
              (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)))).1
              (by simpa [Formula.diamondPast, wTop]
                using hProposeDiamond)
          have hDiamond :=
            (Sat.diamond_nil (M := M)
              (w := ⟨q, †, M.history.val⟩)
              (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)))).2
              ⟨q', by simpa [wTop] using hPast⟩
          simpa [Formula.diamondPast]
            using hDiamond)
  have hImpEcho :
      □W⊨[M]
        (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) ⇒ᶠ
        ↕ᶠ (ofEvent ⟨echoSymb, [v]⟩) :=
    ThyHBB1.uniquePropose_eventually_echo
      (M := M) (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (value := v)
      (hEcho := theory_echoForward (M := M) hTheory)
      (hEchoBack := theory_echoBackward (M := M) hTheory)
      (hUnique := hUnique)
  have hEchoQuorumGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨echoSymb, [v]⟩) :=
    ThyHBB1.boxPast_live_of_eventual_quorum
      (M := M)
      (liveSymb := liveSymb)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
      (ψ := ofEvent ⟨echoSymb, [v]⟩)
      (l := l)
      (hLiveTheory := hThyLive)
      (hQuorum := hProposeQuorumGlobal)
      (hImp := hImpEcho)
  -- Lemma 6.4.2(2) with (Vote!) as Lemma 8.4.3(4): the live echo quorum
  -- becomes a live vote quorum.
  have hLiveVoteTop :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩) := by
    have hGlobal :
        ⊨[M]□ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [l, v]⟩) :=
      ThyHBB1.boxPast_live_of_eventual_quorum (M := M)
        (hLiveTheory := hThyLive)
        (φ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
        (ψ := ofEvent ⟨voteSymb, [l, v]⟩)
        (l := l)
        (hQuorum := live_boxPast_nests (M := M)
          (liveSymb := liveSymb) (l := l)
          (φ := ofEvent ⟨echoSymb, [v]⟩)
          (hTheory := hThyLive)
          (hQuorum := hEchoQuorumGlobal))
        (hImp := live_echo_eventually_vote (M := M)
          (liveSymb := liveSymb) (proposeSymb := proposeSymb)
          (echoSymb := echoSymb) (voteSymb := voteSymb)
          (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
          (hTheory := hTheory) (l := l) (v := v)
          (hSeq := hLiveSequentialGlobal))
    simpa [wTop] using hGlobal p
  have hVoteEventuallyTop :
      ⟪wTop⟫ ⊨[M]
        ↕ᶠ
          (□ᶠ↓[[l]]
            (ofEvent ⟨voteSymb, [l, v]⟩)) := by
    classical
    -- Instantiate the knowledge axiom for `l`-quorum votes.
    have hKnowledgeMem :
        knowledgeBoxAxiom (S := S)
          liveSymb [l]
          (ofEvent ⟨voteSymb, [l, v]⟩) ∈ ThyLive liveSymb := by
      dsimp [ThyLive]
      refine Or.inr ?_
      refine Or.inr ?_
      refine Or.inr ?_
      exact ⟨[l], ofEvent ⟨voteSymb, [l, v]⟩, rfl⟩
    have hKnowledgeEvent :
        AllWorldValid M
          (knowledgeBoxAxiom (S := S)
            liveSymb [l]
            (ofEvent ⟨voteSymb, [l, v]⟩)) :=
      hThyLive hKnowledgeMem

    -- Evaluate the box hypothesis at the end of time.
    have hAtEnd :
        ⟪wTop⟫ ⊨[M]
          ⤒ᶠ (□ᶠ↓[[l]]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l, v]⟩)) :=
      (Sat.atEnd (M := M)
        (w := wTop)
        (φ := □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩))).2
        (by simpa [wTop, World.place, World.time] using hLiveVoteTop)

    have hImp :=
      Sat.imp_elim (M := M) (w := wTop)
        (φ := ⤒ᶠ (□ᶠ↓[[l]]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l, v]⟩)))
        (ψ := predicate0 liveSymb ⇒ᶠ
            ↕ᶠ (□ᶠ↓[[l]]
              (ofEvent ⟨voteSymb, [l, v]⟩)))
        (AllWorldValid.at_end (M := M)
          (φ := knowledgeBoxAxiom (S := S)
            liveSymb [l] (ofEvent ⟨voteSymb, [l, v]⟩))
          hKnowledgeEvent p)
        hAtEnd

    exact
      Sat.imp_elim (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (□ᶠ↓[[l]]
          (ofEvent ⟨voteSymb, [l, v]⟩)))
        hImp hLiveHere
  exact
    ThyHBB1.live_sometime_consequent_at (M := M)
      (hLiveTheory := hThyLive)
      (hImp := deliverForward_imp (M := M)
        (theory_deliverForward (M := M) hTheory))
      hLiveHere hVoteEventuallyTop

/-- Paper: Proposition 8.5.1, first corollary. When the guarded proposal
statement holds, every member of learner `l`'s quorum knows (in the past) that
`l` delivered the value. -/
theorem livenessOne_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l : Signature.Value S} {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M]
      (♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        □ᶠ↓[[l]] (ofEvent ⟨deliverSymb, [l, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLiveQuorum)
      (hMain :=
      livenessOne (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (l := l) (v := v) (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum) (hUnique := hUnique))
/-- Paper: Proposition 8.5.1, second corollary. The guarded proposal
statement guarantees the delivery diamond for learner `l`. -/
theorem livenessOne_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l : Signature.Value S} {v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) :
    ⊨[M]
      (♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLiveQuorum)
      (hMain :=
      livenessOne (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (l := l) (v := v) (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum) (hUnique := hUnique))
end ThyHBB3
end Examples
end ModalDistribution
