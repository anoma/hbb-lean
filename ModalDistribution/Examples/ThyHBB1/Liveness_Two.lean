import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB1.Agreement
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Examples.ThyHBB1.LivenessHelpers
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties.Modalities

/-!
# ThyHBB1 Liveness Properties

This file contains the two liveness two theorem for the ThyHBB1 broadcast protocol:

- **Liveness 2** (`livenessTwo`): If a value is delivered to one learner and certain
  liveness/intersection conditions hold, it will eventually be delivered to another learner.
  Liveness property 2: deliveries propagate across intersecting learner quorums.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB1

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

section Liveness_Two

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 6.4.5 (Liveness 2). Liveness property 2 specialised to `ThyHBB1`.
If a value is delivered to learner l₁' and:
- Learners l₁' and l₂' have intersecting quorums
- The safe condition holds for learner l
- All of learner l₂'s quorum members are live
Then if p is live, the value will eventually be delivered to learner l₂'. -/
theorem livenessTwo
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
  classical
  have hSafe : ⊨[M]safeFormula proposeSymb l := fun q =>
    (safe_iff_safeFormula (M := M) (hTheory := hTheory)
      (w := ⟨q, †, M.history.val⟩)
      (PreHistory.happensBeforeEq_refl _) l).1 (hSafe q)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hSafeTop : ⟪wTop⟫ ⊨[M] safeFormula proposeSymb l := by
    simpa [wTop] using hSafe p
  have hIntersectTop : ⟪wTop⟫ ⊨[M] ♢ᶠ[[l₁', l₂']]⊤ᶠ := by
    simpa [wTop] using hIntersect p
  have hLiveQuorumTop : ⟪wTop⟫ ⊨[M] □ᶠ[[l₂']] predicate0 liveSymb := by
    simpa [wTop] using hLive p
  have hTimeSubsetTop : wTop.time ⊆trn M.history.val := by
    refine ⟨?_, ?_⟩
    · intro t ht
      simpa [wTop] using ht
    · simpa [wTop] using M.history.hered
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hDeliver
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hLivep

  have hThyLiveTheory : M ⊨ᵀ ThyLive liveSymb := by
    intro ax hAx
    exact hTheory (Or.inl hAx)

  -- Step 1: deliveries force quorum boxes of votes at the end of time.
  have hVoteBoxTop :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [l, v]⟩) := by
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := by apply hTheory; simp [theory])
          (reporting := l₁') (learner := l)
          (value := v) (p := p)
          (hDeliver := hDeliver)
  have hBoxSingleton :
      ⟪wTop⟫ ⊨[M]
        □ᶠ[[l₁']] (↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) :=
    by simpa [Formula.boxPast] using hVoteBoxTop

  have step1 :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[l₁']] (ofEvent ⟨voteSymb, [l, v]⟩) := by
    obtain ⟨O₀, hO₀, hAllO₀⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₁')
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).1
        hBoxSingleton
    have hDiamondWitness :
        ⟪wTop⟫ ⊨[M]
          ♢ᶠ[[l₁']]
            (↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
      refine
        (sat_diamond_singleton_iff (M := M)
          (w := wTop) (l := l₁')
          (φ := ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).2 ?_
      intro O hO
      have hIntersect :
          Semifilter.intersects O O₀ :=
        Semifilter.intersects_of_mem_quorums
          (L := M.learner l₁') hO hO₀
      obtain ⟨q, hqO, hqO₀⟩ :=
        (Semifilter.intersects_iff (P := P)
          (O := O) (O' := O₀)).1 hIntersect
      refine ⟨q, hqO, ?_⟩
      exact hAllO₀ q hqO₀
    simpa [Formula.diamondPast] using hDiamondWitness

  -- Step 2: intersecting quorums expose live voters.
  have step2 :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]]
          ((predicate0 liveSymb) ∧ᶠ
            (ofEvent ⟨voteSymb, [l, v]⟩)) := by
    classical
    obtain ⟨Ovote, hOvote, hAllVote⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₁')
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).1
        hBoxSingleton
    obtain ⟨Olive, hOlive, hAllLive⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l₂')
        (φ := predicate0 liveSymb)).1
        (by simpa [Formula.boxPast] using hLiveQuorumTop)
    have hIntersectWitness :=
      (sat_diamond_pair_iff (M := M)
        (w := wTop) (l := l₁') (l' := l₂')
        (φ := ⊤ᶠ)).1
        (by simpa using hIntersectTop)
        Ovote hOvote Olive hOlive
    obtain ⟨q, hqIntersect, -⟩ := hIntersectWitness
    have hqOvote : q ∈ Ovote := hqIntersect.1
    have hqOlive : q ∈ Olive := hqIntersect.2
    have hPastVote :
        ⟪⟨q, †, wTop.time⟩⟫ ⊨[M]
          ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩) :=
      hAllVote q hqOvote
    obtain ⟨tVote, ht_mem, ht_place, hVoteEvent⟩ :=
      (Sat.past (M := M)
        (w := ⟨q, †, wTop.time⟩)
        (φ := ofEvent ⟨voteSymb, [l, v]⟩)).1
        hPastVote
    have ht_mem_history : tVote ∈ M.history.val := by
      simpa [wTop, World.time] using ht_mem
    have ht_place_eq : tVote.place = q := by
      simpa [World.place] using ht_place
    have hLiveAtEnd :
        ⟪⟨q, †, wTop.time⟩⟫ ⊨[M] predicate0 liveSymb :=
      hAllLive q hqOlive
    have hGlobalAtPlace :
        ⟪⟨tVote.place, †, M.history.val⟩⟫ ⊨[M]
          predicate0 liveSymb := by
      have h := hAllLive q hqOlive
      cases ht_place_eq.symm with
      | refl => simpa [wTop, World.place, World.time] using h
    have hLivePast :
        ⟪tVote⟫ ⊨[M] predicate0 liveSymb :=
      (alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hThyLiveTheory)
        (t := tVote)
        (ht := ht_mem_history)).mpr hGlobalAtPlace
    have hConjPast :
        ⟪tVote⟫ ⊨[M]
          predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩ :=
      (Sat.and (M := M)
        (w := tVote)
        (φ := predicate0 liveSymb)
        (ψ := ofEvent ⟨voteSymb, [l, v]⟩)).2
        ⟨hLivePast, hVoteEvent⟩
    have hPastConj :
        ⟪⟨q, †, wTop.time⟩⟫ ⊨[M]
          ↓ᶠ (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩) :=
      Sat.past_intro_of_prefix (M := M)
        (w := ⟨q, †, wTop.time⟩)
        (t := tVote)
        (ht := ht_mem)
        (hp := ht_place)
        (hφ := hConjPast)
    have hPastWitness :
        ∃ r : P,
          ⟪⟨r, †, wTop.time⟩⟫ ⊨[M]
            ↓ᶠ (predicate0 liveSymb ∧ᶠ
              ofEvent ⟨voteSymb, [l, v]⟩) :=
      ⟨q, hPastConj⟩
    have hDiamondEmpty :=
      sat_diamondEmpty_of_local (M := M)
        (w := wTop)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩))
        hPastWitness
    simpa [Formula.diamondPast, Formula.diamondEmpty, id]
      using hDiamondEmpty

  -- Step 3: votes expose echoes guarded by safety in the past.
  have step3 :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ↓[[]]
          ((predicate0 liveSymb) ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    classical
    have hVoteAx : AllWorldValid M
        (voteBackwardAxiom safeSymb echoSymb voteSymb) := by
      apply hTheory
      simp [theory]
    obtain ⟨qVote, hPastConj⟩ :=
      (Sat.Sat_diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [l, v]⟩))).1
        (by
          simpa [Formula.diamondPast]
            using step2)
    obtain ⟨tVote, ht_mem, ht_place, hConjLocal⟩ :=
      (Sat.past (M := M)
        (w := ⟨qVote, †, wTop.time⟩)
        (φ := predicate0 liveSymb ∧ᶠ
          ofEvent ⟨voteSymb, [l, v]⟩)).1
        hPastConj
    have hConjSplit :=
      (Sat.and (M := M)
        (w := tVote)
        (φ := predicate0 liveSymb)
        (ψ := ofEvent ⟨voteSymb, [l, v]⟩)).1
        (by simpa using hConjLocal)
    have hLiveLocal :
        ⟪tVote⟫ ⊨[M] predicate0 liveSymb :=
      hConjSplit.1
    have hVoteEvent :
        ⟪tVote⟫ ⊨[M] ofEvent ⟨voteSymb, [l, v]⟩ :=
      hConjSplit.2
    have ht_mem_history : tVote ∈ M.history.val := by
      simpa [wTop, World.time] using ht_mem
    have hVoteImp :=
      Sat.forall_elim (M := M) (w := tVote)
        (body := fun learner =>
          ∀ᶠ fun value =>
            ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
              (ofPredicate ⟨safeSymb, [learner]⟩ ∧ᶠ
                □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)))
        (v := l)
        (h :=
          AllWorldValid.of_mem_history
            (M := M)
            (φ := voteBackwardAxiom safeSymb echoSymb voteSymb)
            hVoteAx ht_mem_history)
    have hVoteImp_value :=
      Sat.forall_elim (M := M) (w := tVote)
        (body := fun value =>
          ofEvent ⟨voteSymb, [l, value]⟩ ⇒ᶠ
            (ofPredicate ⟨safeSymb, [l]⟩ ∧ᶠ
              □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [value]⟩)))
        (v := v) hVoteImp
    have hSafeEcho :=
      (Sat.imp (M := M)
        (w := tVote)
        (φ := ofEvent ⟨voteSymb, [l, v]⟩)
        (ψ := ofPredicate ⟨safeSymb, [l]⟩ ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).1
        hVoteImp_value hVoteEvent
    have hSafeEchoSplit :=
      (Sat.and (M := M)
        (w := tVote)
        (φ := ofPredicate ⟨safeSymb, [l]⟩)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).1
        hSafeEcho
    have hEchoBox :
        ⟪tVote⟫ ⊨[M] □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩) :=
      hSafeEchoSplit.2
    have hConjTarget :
        ⟪tVote⟫ ⊨[M]
          predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩) :=
      (Sat.and (M := M)
        (w := tVote)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).2
        ⟨hLiveLocal, hEchoBox⟩
    have hPastConj' :
        ⟪⟨qVote, †, wTop.time⟩⟫ ⊨[M]
          ↓ᶠ (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
      Sat.past_intro_of_prefix (M := M)
        (w := ⟨qVote, †, wTop.time⟩)
        (t := tVote)
        (ht := ht_mem)
        (hp := ht_place)
        (hφ := hConjTarget)
    have hPastWitness :
        ∃ r : P,
          ⟪⟨r, †, wTop.time⟩⟫ ⊨[M]
            ↓ᶠ (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
      ⟨qVote, hPastConj'⟩
    have hDiamondEmpty :=
      sat_diamondEmpty_of_local (M := M)
        (w := wTop)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)))
        hPastWitness
    simpa [Formula.diamondPast, Formula.diamondEmpty, id]
      using hDiamondEmpty

  -- Step 4: live quorums eventually learn echo quorums.
  have hStep4Global :
      ⊨[M] □ᶠ↓[[l₂']]
        (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    classical
    obtain ⟨qEcho, hPastEcho⟩ :=
      (Sat.Sat_diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)))).1
        (by simpa [Formula.diamondPast] using step3)
    have hDiamondGlobal :
        ⊨[M] ♢ᶠ↓[[]]
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
      intro q
      refine (Sat.Sat_diamond_nil (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)))).2 ?_
      refine ⟨qEcho, ?_⟩
      simpa [wTop]
        using hPastEcho
    have hLiveGlobal :
        ⊨[M] □ᶠ[id [l₂']] predicate0 liveSymb := by
      intro q
      simpa using hLive q
    have hBoxGlobal :=
      live_eventually_knows_quorum
        (M := M) (liveSymb := liveSymb)
        (l := l₂') (l₁ := l)
        (evt := ⟨echoSymb, [v]⟩)
        (hTheory := hThyLiveTheory)
        (hLive := hLiveGlobal)
        (hQuorum := by simpa using hDiamondGlobal)
    intro q
    simpa using hBoxGlobal q

  have step4 :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂']]
          (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
    hStep4Global p

  let φVote : Formula S :=
    safeFormula proposeSymb l ∧ᶠ
      □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)

  -- Step 5: incorporate safety into the quorum knowledge.
  have hStep5Global :
      ⊨[M] □ᶠ↓[[l₂']]
        (predicate0 liveSymb ∧ᶠ φVote) := by
    classical
    intro q
    obtain ⟨O, hO, hAll⟩ :=
      (sat_box_singleton_exists (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (l := l₂')
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)))).1
        (by simpa [Formula.boxPast]
          using hStep4Global q)
    refine
      (sat_box_singleton_exists (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (l := l₂')
        (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ
          (safeFormula proposeSymb l ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))))).2 ?_
    refine ⟨O, hO, ?_⟩
    intro q' hq'O
    have hPastLiveEcho :
        ⟪⟨q', †, M.history.val⟩⟫ ⊨[M]
          ↓ᶠ (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
      hAll q' hq'O
    obtain ⟨t, ht_mem, ht_place, hLiveEcho⟩ :=
      (Sat.past (M := M)
        (w := ⟨q', †, M.history.val⟩)
        (φ := predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).1
        hPastLiveEcho
    have ht_mem_history : t ∈ M.history.val := by
      simpa [World.time] using ht_mem
    have hLiveEchoSplit :=
      (Sat.and (M := M)
        (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).1
        hLiveEcho
    have hLiveLocal :
        ⟪t⟫ ⊨[M] predicate0 liveSymb :=
      hLiveEchoSplit.1
    have hEchoBox :
        ⟪t⟫ ⊨[M] □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩) :=
      hLiveEchoSplit.2
    let wq : World P (Signature.EventType S) := ⟨q', †, M.history.val⟩
    have hSubsetTop' : wq.time ⊆trn M.history.val :=
      by simpa [wTop, wq, World.time]
        using hTimeSubsetTop
    have ht_le : t.time ⪯ M.history.val :=
      PreHistory.happensBeforeEq_of_mem
        (P := P) (Event := Signature.EventType S)
        (hmem := by
          simpa [wTop, World.place, World.event, World.time] using ht_mem)
    have hSubset_t : t.time ⊆trn M.history.val :=
      ModalDistribution.Logic.time_subset_trn_history
        (M := M) (t := t) ht_le
    have hSafeLocal :
        ⟪t⟫ ⊨[M] safeFormula proposeSymb l :=
      safe_axiom_body_monotone
        (M := M)
        (proposeSymb := proposeSymb)
        (w := wq)
        (w' := t)
        (l := l)
        (hSubset := by
          simpa [wTop, wq, World.time] using hSubset_t)
        (hPlace := by simpa [wTop, wq, World.place] using ht_place)
        (hBody := by
          simpa [wTop]
            using hSafe q')
    have hSafeConj :
        ⟪t⟫ ⊨[M]
          safeFormula proposeSymb l ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩) :=
      (Sat.and (M := M)
        (w := t)
        (φ := safeFormula proposeSymb l)
        (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).2
        ⟨hSafeLocal, hEchoBox⟩
    have hCombined :
        ⟪t⟫ ⊨[M]
          predicate0 liveSymb ∧ᶠ
            (safeFormula proposeSymb l ∧ᶠ
              □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) :=
      (Sat.and (M := M)
        (w := t)
        (φ := predicate0 liveSymb)
        (ψ := safeFormula proposeSymb l ∧ᶠ
          □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).2
        ⟨hLiveLocal, hSafeConj⟩
    exact
      Sat.past_intro_of_prefix (M := M)
        (w := ⟨q', †, M.history.val⟩)
        (t := t)
        (ht := ht_mem)
        (hp := ht_place)
        (hφ := hCombined)

  have step5 :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[l₂']]
          (predicate0 liveSymb ∧ᶠ φVote) :=
    hStep5Global p

  -- Step 6: convert guarded knowledge into eventual votes via `Vote!` and the knowledge axiom.
  have hVotesGlobal :
      ⊨[M]
        □ᶠ↓[[l₂']]
          (predicate0 liveSymb ∧ᶠ
            ofEvent ⟨voteSymb, [l, v]⟩) := by
    classical
    have hVoteForwardAx : AllWorldValid M
        (voteForwardAxiom liveSymb safeSymb echoSymb voteSymb) := by
      apply hTheory
      simp [theory]
    have hImpVotes : AllWorldValid M
        ((predicate0 liveSymb ∧ᶠ φVote) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
      intro t ht_mem
      have hLocal := hVoteForwardAx ht_mem
      have hLearner :=
        Sat.forall_elim (M := M) (w := t)
          (body := fun learner =>
            ∀ᶠ (fun value =>
              (⇕ᶠ (ofPredicate ⟨safeSymb, [learner]⟩)) ⇒ᶠ
                ((predicate0 liveSymb ∧ᶠ
                    □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
                  ↕ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩))))
          (v := l) hLocal
      have hValue :=
        Sat.forall_elim (M := M) (w := t)
          (body := fun value =>
            (⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩)) ⇒ᶠ
              ((predicate0 liveSymb ∧ᶠ
                  □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
                ↕ᶠ (ofEvent ⟨voteSymb, [l, value]⟩)))
          (v := v) hLearner
      let wt : World P (Signature.EventType S) := ⟨t.place, †, M.history.val⟩
      have hSafeTopWorld :
          ⟪wt⟫ ⊨[M] safeFormula proposeSymb l :=
        by simpa [wt, World.place, World.time]
          using hSafe t.place
      have hSubsetWt : wt.time ⊆trn M.history.val :=
        ⟨by intro s hs; simpa [wt, World.time] using hs, M.history.hered⟩
      have hSafeLocal :
          ⟪t⟫ ⊨[M] safeFormula proposeSymb l :=
        safeFormula_monotone_subset
          (M := M)
          (w := wt)
          (w' := t)
          (l := l)
          (hSubset := hSubsetWt)
          (hBefore := by
            simpa [World.time] using ht_mem)
          (hPlace := rfl)
          (hSafe := hSafeTopWorld)
      have hSafeAlways :
          ⟪t⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
        refine
          Sat.not_intro (M := M) (w := t)
            (φ := ↕ᶠ (¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))) ?_
        intro hSome
        obtain ⟨s, hs_mem, hs_place, hNotSafe⟩ :=
          (Sat.sometime (M := M) (w := t)
            (φ := ¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))).1 hSome
        have hAcc_s : s ≪⁻ wt :=
          ⟨by
              simpa [wt, World.time]
                using hs_mem,
            by
              simpa [wt, World.place]
                using hs_place⟩
        have hSafe_s :
            ⟪s⟫ ⊨[M] safeFormula proposeSymb l :=
          safeFormula_monotone_subset
            (M := M)
            (w := wt)
            (w' := s)
            (l := l)
            (hSubset := hSubsetWt)
            (hBefore :=
              by
                simpa [World.time] using
                  PreHistory.happensBeforeEq_of_accessible
                    (P := P) (Event := Signature.EventType S)
                    hAcc_s.1)
            (hPlace := by simpa [World.place] using hAcc_s.2)
            (hSafe := hSafeTopWorld)
        have hs_le : s.time ⪯ M.history.val :=
          PreHistory.happensBeforeEq_of_mem
            (P := P) (Event := Signature.EventType S)
            (hmem := by
              simpa [World.place, World.event, World.time] using hs_mem)
        have hSafePred_s :
            ⟪s⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩ :=
          (safe_iff_safeFormula (M := M) (hTheory := hTheory)
            (w := s) hs_le l).2 hSafe_s
        exact
          (Sat.not_elim (M := M) (w := s)
            (φ := ofPredicate ⟨safeSymb, [l]⟩))
            hNotSafe hSafePred_s
      have hGuard :=
        (Sat.imp (M := M) (w := t)
          (φ := ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩))
          (ψ := (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).1
          (by simpa using hValue)
          hSafeAlways
      refine
        (Sat.imp (M := M) (w := t)
          (φ := predicate0 liveSymb ∧ᶠ φVote)
          (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).2 ?_
      intro hConj
      have hConjSplit :=
        (Sat.and (M := M) (w := t)
          (φ := predicate0 liveSymb)
          (ψ := φVote)).1 hConj
      have hLive := hConjSplit.1
      have hPhi := hConjSplit.2
      have hPhiSplit :=
        (Sat.and (M := M) (w := t)
          (φ := safeFormula proposeSymb l)
          (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).1 hPhi
      have hSafe := hPhiSplit.1
      have hBox := hPhiSplit.2
      have hLiveAndBox :
          ⟪t⟫ ⊨[M]
            predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩) :=
        (Sat.and (M := M) (w := t)
          (φ := predicate0 liveSymb)
          (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).2
          ⟨hLive, hBox⟩
      exact
        (Sat.imp (M := M) (w := t)
          (φ := predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
          (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).1
          hGuard hLiveAndBox
    exact
      boxPast_live_of_eventual_quorum
        (M := M) (liveSymb := liveSymb)
        (φ := φVote)
        (ψ := ofEvent ⟨voteSymb, [l, v]⟩)
        (l := l₂')
        (hLiveTheory := hThyLiveTheory)
        (hQuorum := hStep5Global)
        (hImp := hImpVotes)

  -- Step 7: live participants eventually know the quorum of votes.
  have step6 :
      ⟪wTop⟫ ⊨[M]
        predicate0 liveSymb ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l₂']] (ofEvent ⟨voteSymb, [l, v]⟩)) := by
    classical
    have hKnowledge :=
      _root_.ModalDistribution.Examples.live_eventually_knows_box
        (M := M) (liveSymb := liveSymb)
        (l := l₂') (φ := ofEvent ⟨voteSymb, [l, v]⟩)
        (hTheory := hThyLiveTheory)
        (hQuorum := hVotesGlobal)
    simpa [wTop]
      using hKnowledge p

  have step7 :
      (⟪wTop⟫ ⊨[M] predicate0 liveSymb) →
        (⟪wTop⟫ ⊨[M]
          ↕ᶠ (□ᶠ↓[[l₂']]
            (ofEvent ⟨voteSymb, [l, v]⟩))) := by
    intro hLiveTop
    exact
      (Sat.imp (M := M) (w := wTop)
        (φ := predicate0 liveSymb)
        (ψ := ↕ᶠ (□ᶠ↓[[l₂']]
          (ofEvent ⟨voteSymb, [l, v]⟩)))).1
        step6 hLiveTop

  -- Step 8: live eventually delivers via forward axiom.
  have step8 :
      (⟪wTop⟫ ⊨[M] predicate0 liveSymb) →
        (⟪wTop⟫ ⊨[M]
          ↕ᶠ (ofEvent ⟨deliverSymb, [l₂', l, v]⟩)) := by
    intro hLiveTop
    have hVotesTop := step7 hLiveTop
    have hDeliverAx : AllWorldValid M
        (deliverForwardAxiom liveSymb voteSymb deliverSymb) := by
      apply hTheory
      simp [theory]
    exact
      deliver_from_vote_box
        (M := M)
        (liveSymb := liveSymb)
        (voteSymb := voteSymb)
        (deliverSymb := deliverSymb)
        (reporting := l₂') (learner := l) (value := v)
        (hThyLive := hThyLiveTheory)
        (hDeliverAx := hDeliverAx)
        (hLiveTop := hLiveTop)
        (hVotesTop := hVotesTop)

  exact step8 hLivep

/-- Paper: Proposition 6.4.5, first corollary. Corollary: a delivery for `(l₁', l)`
forces every `l₂'`-quorum member to know (in the past) that `(l₂', l)` was
delivered. -/
theorem livenessTwo_boxPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         □ᶠ↓[[l₂']] (ofEvent ⟨deliverSymb, [l₂', l, v]⟩) := by
  classical
  exact
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      livenessTwo (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hSafe := hSafe)
        (hLive := hLive))
/-- Paper: Proposition 6.4.5, second corollary. Corollary: a delivery for `(l₁', l)`
forces a delivery for `(l₂', l)` somewhere in the past of the history. -/
theorem livenessTwo_diamondPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁' l₂' l : Signature.Value S}
    {v : Signature.Value S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁', l₂']]⊤ᶠ)
    (hSafe : ⊨[M]ofPredicate ⟨safeSymb, [l]⟩)
    (hLive : ⊨[M]□ᶠ[[l₂']]predicate0 liveSymb) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l, v]⟩)) ⇒ᶠ
         ♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l, v]⟩) := by
  classical
  exact
    endValid_diamondPast_of_imp_sometime (M := M)
      (hGuard := hLive)
      (hMain :=
      livenessTwo (M := M)
        (liveSymb := liveSymb) (proposeSymb := proposeSymb)
        (echoSymb := echoSymb) (voteSymb := voteSymb)
        (deliverSymb := deliverSymb) (v := v)
        (hTheory := hTheory)
        (hIntersect := hIntersect)
        (hSafe := hSafe)
        (hLive := hLive))
end Liveness_Two
end ThyHBB1
end Examples
end ModalDistribution
