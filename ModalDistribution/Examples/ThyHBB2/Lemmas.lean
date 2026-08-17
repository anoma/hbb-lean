import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB2.Axioms
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History
import ModalDistribution.Core.Semifilter

/-!
# ThyHBB2 Helper Lemmas

This file bundles auxiliary lemmas for the ThyHBB2 development: translating
deliveries witnessed at end of time into vote quorums (`Deliver?`), tracing
votes back to echo quorums (`Vote?`), and turning live echo quorums into
votes (`Vote!`).
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB2

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

/-- Singleton past boxes yield a witness for the corresponding past diamond. -/
theorem boxPast_singleton_to_diamond_nil
    {w : World P (Signature.EventType S)}
    {learner : Signature.Value S}
    {φ : Formula S}
    (hBox : ⟪w⟫ ⊨[M]□ᶠ↓[[learner]]φ) :
    ⟪w⟫ ⊨[M]♢ᶠ↓[[]]φ := by
  classical
  have hBoxPlain :
      ⟪w⟫ ⊨[M]□ᶠ[[learner]](↓ᶠ φ) :=
    by simpa [Formula.boxPast] using hBox
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := w) (l := learner) (φ := ↓ᶠ φ)).1 hBoxPlain
  obtain ⟨q, hq⟩ :=
    (M.learner learner).quorum_nonempty hO
  have hPast :
      ⟪⟨q, †, w.time⟩⟫ ⊨[M] ↓ᶠ φ := hAll q hq
  have hDiamond :
      ⟪w⟫ ⊨[M]♢ᶠ[[]](↓ᶠ φ) :=
    (Sat.diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ φ)).2 ⟨q, hPast⟩
  simpa [Formula.diamondPast]
    using hDiamond

namespace Vote

/-- Instantiates `Vote?` to extract echo quorums supporting a vote. -/
theorem box_witness
    {p : P}
    {learner value : Signature.Value S}
    (hVoteAx : AllWorldValid M (voteBackwardAxiom echoSymb voteSymb))
    (hVote :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ∃ t : World P (Signature.EventType S),
      t ∈ M.history.val ∧
        t.time ⊆ M.history.val ∧
        ⟪t⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hDiamond_nil :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)) := by
    simpa [Formula.diamondPast, wTop] using hVote
  obtain ⟨qVote, hPastVote⟩ :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hDiamond_nil
  obtain ⟨tVote, ht_mem, ht_place, hVote_at⟩ :=
    (Sat.past (M := M)
      (w := ⟨qVote, †, wTop.time⟩)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hPastVote
  have ht_mem_history : tVote ∈ M.history.val := by
    simpa [wTop, World.time] using ht_mem
  have hBox_at_event :
      ⟪tVote⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
    voteBackward_elim (M := M)
      (hAx := hVoteAx)
      (hMem := ht_mem_history)
      (hVote := hVote_at)
  have hBefore_history : tVote.time ≺− M.history.val :=
    happensBefore_of_mem (P := P) (Event := Signature.EventType S)
      ht_mem_history
  have hSubset_history : tVote.time ⊆ M.history.val :=
    History.subset_of_happensBefore (H := M.history) hBefore_history
  exact ⟨tVote, ht_mem_history, hSubset_history, hBox_at_event⟩

/-- At end of time, a vote for `(learner, value)` requires an `learner`-quorum of
echoes backing it. -/
theorem to_echo_box_end
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {learner value : Signature.Value S}
    {p : P}
    (hVote :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  have hVoteAx : AllWorldValid M (voteBackwardAxiom echoSymb voteSymb) :=
    theory_voteBackward (M := M) hTheory
  obtain ⟨tVote, ht_mem, hSubset, hBox⟩ :=
    Vote.box_witness (M := M)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (hVoteAx := hVoteAx)
      (learner := learner) (value := value)
      (p := p) (hVote := hVote)
  exact
    lift_boxPast_to_end (M := M)
      (learner := learner)
      (φ := ofEvent ⟨echoSymb, [value]⟩)
      (t := tVote)
      (hSubset := hSubset) (hBox := hBox) p

end Vote

/-- Quorum intersections transport a vote witnessed at `l₁'` to some live
member of the `l₂'` quorum. -/
theorem live_vote_transfer
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' learner : Signature.Value S}
    {value : Signature.Value S}
    {p : P}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb)
    (hVote :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[l₁']](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hThyLiveTheory : M ⊨ᵀ ThyLive liveSymb := by
    intro ax hAx
    exact hTheory (Or.inl hAx)
  have hIntersectTop :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ := by
    simpa [wTop] using hIntersect p
  have hLiveQuorumTop :
      ⟪wTop⟫ ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb := by
    simpa [wTop] using hLive p
  have hVoteBoxPlain :
      ⟪wTop⟫ ⊨[M]□ᶠ[[l₁']](↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    by simpa [Formula.boxPast] using hVote
  obtain ⟨Ovote, hOvote, hAllVote⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := wTop) (l := l₁')
      (φ := ↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hVoteBoxPlain
  obtain ⟨Olive, hOlive, hAllLive⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := wTop) (l := l₂')
      (φ := predicate0 liveSymb)).1
      hLiveQuorumTop
  have hIntersectWitness :=
    (sat_diamond_pair_iff (M := M)
      (w := wTop) (l := l₁') (l' := l₂') (φ := ⊤ᶠ)).1
      (by simpa using hIntersectTop)
      Ovote hOvote Olive hOlive
  obtain ⟨q, hqIntersect, -⟩ := hIntersectWitness
  have hqOvote : q ∈ Ovote := hqIntersect.1
  have hqOlive : q ∈ Olive := hqIntersect.2
  have hPastVote :
      ⟪⟨q, †, wTop.time⟩⟫ ⊨[M]↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩) :=
    hAllVote q hqOvote
  obtain ⟨tVote, ht_mem, ht_place, hVoteEvent⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, wTop.time⟩)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hPastVote
  have ht_mem_history : tVote ∈ M.history.val := by
    simpa [wTop, World.time] using ht_mem
  have hLiveEnd' :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb := by
    simpa [wTop]
      using hAllLive q hqOlive
  have hLiveGlobal :
      ⟪⟨tVote.place, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb :=
    Eq.subst (motive :=
        fun x => ⟪⟨x, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb)
      ht_place.symm hLiveEnd'
  have hLiveLocal :
      ⟪tVote⟫ ⊨[M]predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
      (liveSymb := liveSymb)
      (hTheory := hThyLiveTheory)
      (t := tVote) (ht := ht_mem_history)).mpr hLiveGlobal
  have hConjLocal :
      ⟪tVote⟫ ⊨[M]predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [learner, value]⟩ :=
    (Sat.and (M := M) (w := tVote)
      (φ := predicate0 liveSymb)
      (ψ := ofEvent ⟨voteSymb, [learner, value]⟩)).2
      ⟨hLiveLocal, hVoteEvent⟩
  have hConjPast :
      ⟪⟨q, †, wTop.time⟩⟫ ⊨[M]↓ᶠ (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [learner, value]⟩) :=
    (Sat.past (M := M)
      (w := ⟨q, †, wTop.time⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩)).2
        ⟨tVote, by simpa [wTop, World.time] using ht_mem,
          ht_place,
          hConjLocal⟩
  have hDiamond :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩))).2
      ⟨q, hConjPast⟩
  simpa [Formula.diamondPast]
    using hDiamond

/-- Refine a `live ∧ vote` diamond (at end of time) by exposing the supporting
echo quorum via `Vote?`. -/
theorem vote_live_to_echo_diamond
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {learner value : Signature.Value S}
    {p : P}
    (hVote :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hVoteAx : AllWorldValid M (voteBackwardAxiom echoSymb voteSymb) :=
    theory_voteBackward (M := M) hTheory
  obtain ⟨qVote, hPastConj⟩ :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩))).1
      (by simpa [Formula.diamondPast, wTop] using hVote)
  obtain ⟨tVote, ht_mem, ht_place, hConjLocal⟩ :=
    (Sat.past (M := M)
      (w := ⟨qVote, †, wTop.time⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hPastConj
  have ht_mem_history : tVote ∈ M.history.val := by
    simpa [wTop, World.time] using ht_mem
  have hConjSplit :=
    (Sat.and (M := M) (w := tVote)
      (φ := predicate0 liveSymb)
      (ψ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hConjLocal
  have hLiveAt :
      ⟪tVote⟫ ⊨[M]predicate0 liveSymb := hConjSplit.1
  have hVoteAt :
      ⟪tVote⟫ ⊨[M] ofEvent ⟨voteSymb, [learner, value]⟩ := hConjSplit.2
  have hEchoBoxAt :
      ⟪tVote⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
    voteBackward_elim (M := M)
      (hAx := hVoteAx)
      (hMem := ht_mem_history)
      (hVote := hVoteAt)
  have hConjEcho :
      ⟪tVote⟫ ⊨[M]predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
    (Sat.and (M := M) (w := tVote)
      (φ := predicate0 liveSymb)
      (ψ := □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).2
      ⟨hLiveAt, hEchoBoxAt⟩
  have hPastEcho :
      ⟪⟨qVote, †, wTop.time⟩⟫ ⊨[M]↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) :=
    (Sat.past (M := M)
      (w := ⟨qVote, †, wTop.time⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).2
      ⟨tVote, by simpa [wTop, World.time] using ht_mem,
        by simpa [World.place] using ht_place,
        hConjEcho⟩
  have hDiamond' :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))) :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)))).2
      ⟨qVote, hPastEcho⟩
  simpa [Formula.diamondPast, wTop]
    using hDiamond'

theorem live_vote_box_from_echo
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₂' learner : Signature.Value S} {value : Signature.Value S} {p : P}
    (hEchoBox :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[l₂']](predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ↓[[l₂']](predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hVoteAx : AllWorldValid M (voteForwardAxiom liveSymb echoSymb voteSymb) :=
    theory_voteForward (M := M) hTheory
  have hThyLive : M ⊨ᵀ ThyLive liveSymb :=
    theory_thyLive (M := M) hTheory
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := wTop) (l := l₂')
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)))).1
      (by simpa [Formula.boxPast] using hEchoBox)
  refine
    (sat_box_singleton_exists (M := M)
      (w := wTop) (l := l₂')
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩))).2 ?_
  refine ⟨O, hO, ?_⟩
  intro q hqO
  have hPastLiveEcho :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) :=
    hAll q hqO
  obtain ⟨t, ht_mem, ht_place, hLiveEcho⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).1
      hPastLiveEcho
  have ht_mem_history : t ∈ M.history.val := by
    simpa [World.time] using ht_mem
  have hLiveEchoSplit :=
    (Sat.and (M := M) (w := t)
      (φ := predicate0 liveSymb)
      (ψ := □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩))).1
      hLiveEcho
  have hLiveLocal :
      ⟪t⟫ ⊨[M]predicate0 liveSymb := hLiveEchoSplit.1
  have hEchoLocal :
      ⟪t⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
    hLiveEchoSplit.2
  have ht_le : t.time ⪯ M.history.val :=
    PreHistory.happensBeforeEq_of_mem
      (P := P) (Event := Signature.EventType S)
      (hmem := by
        simpa [World.place, World.event, World.time] using ht_mem_history)
  have hVoteImp :=
    voteForward_elim (M := M)
      (hAx := hVoteAx)
      (hW := ht_le)
      (hLive := hLiveLocal)
      (hEchoBox := hEchoLocal)
  obtain ⟨t', ht'_mem, ht'_place, hVoteNow⟩ :=
    (Sat.sometime (M := M)
      (w := t)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hVoteImp
  have ht'_mem_history : t' ∈ M.history.val := ht'_mem
  have hLiveTop :
      ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
      (liveSymb := liveSymb)
      (hTheory := hThyLive)
      (t := t) (ht := ht_mem_history)).1
      hLiveLocal
  have ht'_place_q : t'.place = q :=
    ht'_place.trans ht_place
  have hLiveTop' :
      ⟪⟨t'.place, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb :=
    ht'_place ▸ hLiveTop
  have hLiveFuture :
      ⟪t'⟫ ⊨[M]predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
      (liveSymb := liveSymb)
      (hTheory := hThyLive)
      (t := t') (ht := ht'_mem_history)).2
      hLiveTop'
  exact
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := predicate0 liveSymb ∧ᶠ
        ofEvent ⟨voteSymb, [learner, value]⟩)).2
      ⟨t', ht'_mem_history, ht'_place_q,
        (Sat.and (M := M) (w := t')
          (φ := predicate0 liveSymb)
          (ψ := ofEvent ⟨voteSymb, [learner, value]⟩)).2
          ⟨hLiveFuture, hVoteNow⟩⟩

/-- Forget the left conjunct in an empty-guard past diamond. -/
theorem diamondPast_nil_strip_left
    {w : World P (Signature.EventType S)}
    {φ ψ : Formula S}
    (h : ⟪w⟫ ⊨[M]♢ᶠ↓[[]](φ ∧ᶠ ψ)) :
    ⟪w⟫ ⊨[M]♢ᶠ↓[[]]ψ := by
  classical
  have hDiamondNil :
      ⟪w⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ (φ ∧ᶠ ψ)) := by
    simpa [Formula.diamondPast] using h
  obtain ⟨q, hPast⟩ :=
    (Sat.diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ (φ ∧ᶠ ψ))).1 hDiamondNil
  obtain ⟨t, ht_mem, ht_place, hConj⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, w.time⟩)
      (φ := φ ∧ᶠ ψ)).1 hPast
  have hψ :=
    (Sat.and (M := M) (w := t)
      (φ := φ) (ψ := ψ)).1 hConj
  have hPastψ :
      ⟪⟨q, †, w.time⟩⟫ ⊨[M]↓ᶠ ψ :=
    (Sat.past (M := M)
      (w := ⟨q, †, w.time⟩)
      (φ := ψ)).2
      ⟨t, ht_mem, ht_place, hψ.2⟩
  have hDiamond' :
      ⟪w⟫ ⊨[M]♢ᶠ[[]]
          (↓ᶠ ψ) :=
    (Sat.diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ ψ)).2
      ⟨q, hPastψ⟩
  simpa [Formula.diamondPast]
    using hDiamond'

end ThyHBB2
end Examples
end ModalDistribution
