import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBCorr.Axioms
import ModalDistribution.Examples.HBBCorr.Lemmas
import ModalDistribution.Examples.HBBSafe.Safety
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.Semifilter
import ModalDistribution.Logic.Properties.Modalities

/-!
# HBBCorr Happy Termination

This file records the Happy Termination statement for `HBBCorr`, formalising
Happy Termination for HBBCorr. Under a live quorum for learner `l` and a
unique proposed value, any live participant that learns about the proposal will
eventually deliver it for `l`.
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
theorem happyTermination
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
  have hEventGlobal :
      ⊨[M]
        ♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) := by
    intro q
    obtain ⟨q', hPast⟩ :=
      (Sat.diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)))).1
        (by simpa [Formula.diamondPast, wTop] using hProposeDiamond)
    have hDiamond :=
      (Sat.diamond_nil (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)))).2
        ⟨q', by simpa [wTop] using hPast⟩
    simpa [Formula.diamondPast] using hDiamond
  -- Lemma 6.6.1 holds verbatim in HBBCorr: (Echo!), (Echo?) and `ThyLive`
  -- are as in HBBSafe (Remark 8.5.2).
  have hImpEcho :
      □W⊨[M]
        (↕ᶠ (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        ↕ᶠ (ofEvent ⟨echoSymb, [v]⟩) :=
    HBBSafe.uniquePropose_eventually_echo
      (M := M) (liveSymb := liveSymb)
      (proposeSymb := proposeSymb)
      (echoSymb := echoSymb)
      (value := v)
      (hEcho := theory_echoForward (M := M) hTheory)
      (hEchoBack := theory_echoBackward (M := M) hTheory)
      (hUnique := hUnique)
  -- Lemma 6.6.1: some live participant echoes `v`.
  have hLiveEchoGlobal :
      ⊨[M] ♢ᶠ↓[[]] (predicate0 liveSymb ∧ᶠ ofEvent ⟨echoSymb, [v]⟩) :=
    HBBSafe.diamondPast_live_of_eventual (M := M)
      (hLiveTheory := hThyLive)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
      (ψ := ofEvent ⟨echoSymb, [v]⟩)
      (hDiamond := hEventGlobal) (hImp := hImpEcho)
  -- Proposition 5.2.8: an `l`-quorum of live participants knows of that echo.
  have hKnowsEchoGlobal :
      ⊨[M] □ᶠ↓[[l]]
        (predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨echoSymb, [v]⟩)) := by
    have hKE :=
      live_eventually_knows (P := P) (M := M) (liveSymb := liveSymb)
        (l := l) (evt := ⟨echoSymb, [v]⟩)
        (hTheory := hThyLive) (hLive := hLiveQuorum)
        (hEvent := hLiveEchoGlobal)
    intro q
    simpa using hKE q
  -- (Echo?) and Lemma 4.2.2: that quorum knows of the proposal.
  have hProposeQuorumGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :=
    HBBSafe.boxPast_live_knowsEcho_knowsPropose (M := M)
      (hEchoBack := theory_echoBackward (M := M) hTheory)
      (hQuorum := hKnowsEchoGlobal)
  -- Lemma 6.5.2(2) and Lemma 6.6.1: that quorum echoes `v`.
  have hEchoQuorumGlobal :
      ⊨[M]
        □ᶠ↓[[l]]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨echoSymb, [v]⟩) :=
    HBBSafe.boxPast_live_of_eventual_quorum
      (M := M)
      (liveSymb := liveSymb)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
      (ψ := ofEvent ⟨echoSymb, [v]⟩)
      (l := l)
      (hLiveTheory := hThyLive)
      (hQuorum := hProposeQuorumGlobal)
      (hImp := hImpEcho)
  -- Lemma 5.2.11, then Lemma 6.5.2(2) with Lemma 8.4.3(4): the quorum votes.
  have hLiveVoteGlobal :
      ⊨[M]□ᶠ↓[[l]]
        (predicate0 liveSymb ∧ᶠ ofEvent ⟨voteSymb, [l, v]⟩) :=
    HBBSafe.boxPast_live_of_eventual_quorum (M := M)
      (hLiveTheory := hThyLive)
      (φ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
      (ψ := ofEvent ⟨voteSymb, [l, v]⟩)
      (l := l)
      (hQuorum := live_boxPast_nests (M := M)
        (liveSymb := liveSymb) (l := l)
        (evt := ⟨echoSymb, [v]⟩)
        (hTheory := hThyLive)
        (hQuorum := hEchoQuorumGlobal))
      (hImp := live_echo_eventually_vote (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (hTheory := hTheory) (l := l) (v := v)
        (hSeq := hLiveSequentialGlobal))
  -- (Knowledge□↓): every live participant eventually knows of the vote quorum.
  have hVoteEventuallyTop :
      ⟪wTop⟫ ⊨[M]
        ↕ᶠ
          (□ᶠ↓[[l]]
            (ofEvent ⟨voteSymb, [l, v]⟩)) :=
    Sat.imp_elim (M := M) (w := wTop)
      (φ := predicate0 liveSymb)
      (ψ := ↕ᶠ (□ᶠ↓[[l]] (ofEvent ⟨voteSymb, [l, v]⟩)))
      (by
        simpa [wTop] using
          live_eventually_knows_box (P := P) (M := M) (liveSymb := liveSymb)
            (l := l) (evt := ⟨voteSymb, [l, v]⟩)
            (hTheory := hThyLive) (hQuorum := hLiveVoteGlobal) p)
      hLiveHere
  exact
    HBBSafe.live_sometime_consequent_at (M := M)
      (hLiveTheory := hThyLive)
      (hImp := deliverForward_imp (M := M)
        (theory_deliverForward (M := M) hTheory))
      hLiveHere hVoteEventuallyTop

/-- Paper: Proposition 8.5.1, first corollary. When the guarded proposal
statement holds, every member of learner `l`'s quorum knows (in the past) that
`l` delivered the value. -/
theorem happyTermination_boxPast
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
      happyTermination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (l := l) (v := v) (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum) (hUnique := hUnique))
/-- Paper: Proposition 8.5.1, second corollary. The guarded proposal
statement guarantees the delivery diamond for learner `l`. -/
theorem happyTermination_diamondPast
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
      happyTermination (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
        (l := l) (v := v) (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum) (hUnique := hUnique))
end HBBCorr
end Examples
end ModalDistribution
