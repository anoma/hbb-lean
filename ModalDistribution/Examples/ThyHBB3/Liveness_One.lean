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
  have hLiveSeqAx :
      AllWorldValid M (liveSeqAxiom liveSymb) := by
    apply hTheory
    simp [theory]
  have hLiveSequentialGlobal :
      ⊨[M]□ᶠ[[l]] Formula.seq := by
    intro p
    set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
    have hLiveTop :
        ⟪wTop⟫ ⊨[M]□ᶠ[[l]] predicate0 liveSymb :=
      by simpa [wTop] using hLiveQuorum p
    obtain ⟨O, hO, hAllLive⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l)
        (φ := predicate0 liveSymb)).1 hLiveTop
    refine
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l)
        (φ := Formula.seq)).2 ?_
    refine ⟨O, hO, ?_⟩
    intro q hqO
    have hLive_q :
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb :=
      hAllLive q hqO
    have hSeqImp :
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
          liveSeqAxiom liveSymb :=
      hLiveSeqAx (by simp [World.time])
    have hImp :=
      (Sat.imp (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := predicate0 liveSymb)
        (ψ := Formula.seq)).1
        (by simpa [liveSeqAxiom] using hSeqImp)
    exact hImp hLive_q
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hThyLive : M ⊨ᵀ ThyLive liveSymb := by
    intro ax hAx
    exact hTheory (Or.inl hAx)
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hProposeDiamond
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLiveHere
  have hLiveQuorumTop :
      ⟪wTop⟫ ⊨[M] □ᶠ[[l]] predicate0 liveSymb := by
    simpa [wTop] using hLiveQuorum p
  have hLiveSequentialTop :
      ⟪wTop⟫ ⊨[M] □ᶠ[[l]] Formula.seq := by
    simpa [wTop] using hLiveSequentialGlobal p
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
      (hEcho := by
        apply hTheory
        simp [theory])
      (hEchoBack := by
        apply hTheory
        simp [theory])
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
  have hLiveEchoTop :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨echoSymb, [v]⟩) := by
    simpa [wTop] using hEchoQuorumGlobal p
  have hLiveNestedEchoTop :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    have hEchoQuorumTop :
        ⟪wTop⟫ ⊨[M]
          □ᶠ↓[[l]]
            (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨echoSymb, [v]⟩) :=
      by simpa [wTop] using hEchoQuorumGlobal p
    have hNestedGlobal :
        ⊨[M]
          □ᶠ↓[[l]]
            (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
      live_boxPast_nests (M := M)
        (liveSymb := liveSymb)
        (l := l)
        (φ := ofEvent ⟨echoSymb, [v]⟩)
        (hTheory := hThyLive)
        (hQuorum := hEchoQuorumGlobal)
    simpa [wTop] using hNestedGlobal p
  have hLiveVoteTop :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩) := by
    classical
    have hVoteImp :
        AllWorldValid M
          ((predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) :=
      live_echo_eventually_vote (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (hTheory := hTheory) (l := l) (v := v)
        (hSeq := hLiveSequentialGlobal)
    obtain ⟨O, hO, hAll⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)))).1
        hLiveNestedEchoTop
    refine
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [l, v]⟩))).2 ?_
    refine ⟨O, hO, ?_⟩
    intro q hqO
    have hPastNested :
        ⟪⟨q, †, wTop.time⟩⟫ ⊨[M]
          ↓ᶠ (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
      hAll q hqO
    obtain ⟨t, ht_mem, ht_place, hLiveEcho⟩ :=
      (Sat.past (M := M)
        (w := ⟨q, †, wTop.time⟩)
        (φ := predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).1
        hPastNested
    have ht_mem_history : t ∈ M.history.val :=
      by simpa [wTop, World.time] using ht_mem
    have hSplit :=
      (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).1
        hLiveEcho
    have hLiveLocal :
        ⟪t⟫ ⊨[M] predicate0 liveSymb := hSplit.1
    have hEchoLocal :
        ⟪t⟫ ⊨[M]
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩) := hSplit.2
    have hVoteImpLocal :=
      AllWorldValid.of_mem_history
        (M := M)
        (φ :=
          (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))
        hVoteImp ht_mem_history
    have hVoteGuard :
        ⟪t⟫ ⊨[M]
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
      (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).2
        ⟨hLiveLocal, hEchoLocal⟩
    have hVoteLocal :
        ⟪t⟫ ⊨[M]
          ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩) :=
      (Sat.imp (M := M) (w := t)
        (φ := predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
        (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).1
        hVoteImpLocal hVoteGuard
    obtain ⟨tVote, htVote_mem, htVote_place, hVoteEvent⟩ :=
      (Sat.sometime (M := M)
        (w := t)
        (φ := ofEvent ⟨voteSymb, [l, v]⟩)).1
        hVoteLocal
    have hLiveTopAtPlace :
        ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]
          predicate0 liveSymb :=
      (alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hThyLive)
        (t := t) (ht := ht_mem_history)).1
        hLiveLocal
    have hLiveTopVote :
        ⟪⟨tVote.place, †, M.history.val⟩⟫ ⊨[M]
          predicate0 liveSymb :=
      (Eq.subst
        (motive := fun p => Sat M p † M.history.val (predicate0 liveSymb))
        htVote_place.symm
        hLiveTopAtPlace)
    have hLiveVote :
        ⟪tVote⟫ ⊨[M] predicate0 liveSymb :=
      (alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hThyLive)
        (t := tVote)
        (ht := htVote_mem)).2 hLiveTopVote
    have ht_place_q : t.place = q := by
      simpa [World.place] using ht_place
    have htVote_place_q : tVote.place = q :=
      htVote_place.trans ht_place_q
    have hLiveVoteConj :
        ⟪tVote⟫ ⊨[M]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩) :=
      (Sat.and (M := M) (w := tVote)
        (φ := predicate0 liveSymb)
        (ψ := ofEvent ⟨voteSymb, [l, v]⟩)).2
        ⟨hLiveVote, hVoteEvent⟩
    exact
      (Sat.past (M := M)
        (w := ⟨q, †, wTop.time⟩)
        (φ := predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [l, v]⟩)).2
        ⟨tVote, htVote_mem, htVote_place_q, hLiveVoteConj⟩
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
