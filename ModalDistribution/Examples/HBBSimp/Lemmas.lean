import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBBSimp.Axioms
import ModalDistribution.Examples.HBBSafe.Uniqueness
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History
import ModalDistribution.Core.Semifilter

/-!
# HBBSimp Helper Lemmas

This file bundles auxiliary lemmas for the HBBSimp development: translating
deliveries witnessed at end of time into vote quorums (`Deliver?`), tracing
votes back to echo quorums (`Vote?`), and instantiating `Vote!` in the form
Lemma 6.5.2(2) consumes.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSimp

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

/-- The instantiated `Vote!` implication: a sometime-live quorum of past
echoes yields an eventual vote. This is the form consumed by Lemma 6.5.2(2). -/
theorem voteForward_imp
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l v : Signature.Value S} :
    □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
  classical
  intro t ht
  refine Sat.imp_intro (M := M) (w := t) ?_
  intro hLiveEcho
  exact
    voteForward_elim (M := M)
      (hAx := theory_voteForward (M := M) hTheory)
      (hW := ht)
      (hLiveEcho := hLiveEcho)

end HBBSimp
end Examples
end ModalDistribution
