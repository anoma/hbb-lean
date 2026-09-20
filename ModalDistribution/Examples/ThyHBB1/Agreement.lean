import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History

/-!
# ThyHBB1 Agreement Property

This file contains the main agreement theorem for the ThyHBB1 broadcast protocol.

## Main Result

- **`agreement`**
  The agreement property states that if two different values are delivered at different learners,
  then sequentiality must be violated. More precisely, if:
  - Two deliver events occur for values v₁ and v₂ at learners l₁ and l₂
  - Sequentiality holds between reporting learners reporting₁ and reporting₂
  Then v₁ = v₂.

This is the fundamental correctness property of the broadcast protocol: under sequentiality
assumptions, all processes that deliver a value must deliver the same value.

## Proof Structure

The proof proceeds by contradiction, assuming v₁ ≠ v₂ and deriving a contradiction:

1. **Step 1**: Apply the Deliver? axiom to obtain vote quorums for both values
2. **Step 2**: Use sequentiality to show one vote must happen before the other
3. **Step 3**: Extract witnesses from the diamond-past operator
4. **Step 4**: Apply Vote? and Echo? axioms to get echo quorums with safe predicate
5. **Step 5**: Use the safe predicate definition to derive sequentiality between learners
6. **Step 6**: Apply sequentiality again with EchoNE to force v₁ = v₂ (contradiction)

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
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}
variable {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Proposition 6.3.1 (Agreement). Agreement property for ThyHBB1.

Under sequentiality assumptions, if two different values are delivered at different
learners, they must be equal. This is the fundamental correctness property of the
broadcast protocol: all processes that deliver a value must deliver the same value.

The proof proceeds by contradiction, deriving a contradiction from the assumption
that two different values v₁ ≠ v₂ are delivered under sequentiality.

The paper-facing modal form is `agreement_modal`. -/
theorem agreement
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ reporting₁ reporting₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ∀ Q ∈ (M.learner reporting₁).quorums,
      ∀ R ∈ (M.learner reporting₂).quorums,
        ∃ p ∈ Q ∩ R, isSequential (Event := S.EventType) p M.history.val)
    (hDeliver₁ : Occurs M (ofEvent ⟨deliverSymb, [reporting₁, l₁, v₁]⟩))
    (hDeliver₂ : Occurs M (ofEvent ⟨deliverSymb, [reporting₂, l₂, v₂]⟩)) :
    v₁ = v₂ := by
  classical
  let p : P := Classical.choice inferInstance
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hSeq : ⊨[M]♢ᶠ[[reporting₁, reporting₂]]Formula.seq := by
    intro q
    exact (sat_diamond_pair_iff M _ reporting₁ reporting₂ Formula.seq).2 hSeq
  have hDeliver₁ := (occurs_iff_end_diamondPast).1 hDeliver₁ p
  have hDeliver₂ := (occurs_iff_end_diamondPast).1 hDeliver₂ p
  have hSeqTop : ⟪wTop⟫ ⊨[M] ♢ᶠ[[reporting₁, reporting₂]]Formula.seq := hSeq p
  by_cases hNe : v₁ = v₂
  · simpa [Sat] using hNe

  have hVoteBox₁ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[reporting₁]] (ofEvent ⟨voteSymb, [l₁, v₁]⟩) := by
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := by apply hTheory; simp [theory])
          (reporting := reporting₁) (learner := l₁)
          (value := v₁) (p := p)
          (hDeliver := hDeliver₁)
  have hVoteBox₂ :
      ⟪wTop⟫ ⊨[M]
        □ᶠ↓[[reporting₂]] (ofEvent ⟨voteSymb, [l₂, v₂]⟩) := by
    simpa [wTop]
      using
        HBB.deliver_to_vote_box_end (M := M)
          (hDeliverAx := by apply hTheory; simp [theory])
          (reporting := reporting₂) (learner := l₂)
          (value := v₂) (p := p)
          (hDeliver := hDeliver₂)

  have step2 :
      ⟪wTop⟫ ⊨[M]
        (♢ᶠ↓[[]] ((ofEvent ⟨voteSymb, [l₁, v₁]⟩) ∧ᶠ
                    ↓ᶠ (ofEvent ⟨voteSymb, [l₂, v₂]⟩))) ∨ᶠ
        (♢ᶠ↓[[]] ((ofEvent ⟨voteSymb, [l₂, v₂]⟩) ∧ᶠ
                    ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v₁]⟩))) := by
    have hDistinct :
        (⟨voteSymb, [l₁, v₁]⟩ : Signature.Event S) ≠
          ⟨voteSymb, [l₂, v₂]⟩ := by
      intro h
      injection h with _ hArgs
      cases hArgs
      exact hNe rfl
    exact
      seq_two_quorums_eventually
        (M := M) (w := wTop)
        (l := reporting₁) (l' := reporting₂)
        (evt := ⟨voteSymb, [l₁, v₁]⟩)
        (evt' := ⟨voteSymb, [l₂, v₂]⟩)
        (hSeq := hSeqTop)
        (hEvt := hVoteBox₁)
        (hEvt' := hVoteBox₂)
        (hDistinct := hDistinct)

  have hVoteAx : AllWorldValid M
      (voteBackwardAxiom safeSymb echoSymb voteSymb) :=
    theory_voteBackward (M := M) hTheory

  have hEchoBack :
      □W⊨[M]echoBackwardAxiom proposeSymb echoSymb :=
    theory_echoBackward (M := M) hTheory

  have hEchoNE : AllWorldValid M (echoNonEquivAxiom echoSymb) :=
    theory_echoNonEquiv (M := M) hTheory

  have derive_contradiction :
      ∀ {la lb : Signature.Value S} {va vb : Signature.Value S},
        va ≠ vb →
        (⟪wTop⟫ ⊨[M] ♢ᶠ↓[[]]
            ((ofEvent ⟨voteSymb, [la, va]⟩) ∧ᶠ
              ↓ᶠ (ofEvent ⟨voteSymb, [lb, vb]⟩))) →
        va = vb := by
    intro la lb va vb hDistinct hDiamond
    have hDiamondBase :
        ⟪wTop⟫ ⊨[M]
          ♢ᶠ[[]]
            (↓ᶠ ((ofEvent ⟨voteSymb, [la, va]⟩) ∧ᶠ
              ↓ᶠ (ofEvent ⟨voteSymb, [lb, vb]⟩))) := by
      simpa [Formula.diamondPast] using hDiamond
    obtain ⟨qVote, hPastVotes⟩ :=
      (Sat.diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ ((ofEvent ⟨voteSymb, [la, va]⟩) ∧ᶠ
          ↓ᶠ (ofEvent ⟨voteSymb, [lb, vb]⟩)))).1 hDiamondBase
    obtain ⟨wNow, hNow_mem, hNow_place, hVotes⟩ :=
      (Sat.past (M := M)
        (w := ⟨qVote, †, wTop.time⟩)
        (φ := (ofEvent ⟨voteSymb, [la, va]⟩) ∧ᶠ
          ↓ᶠ (ofEvent ⟨voteSymb, [lb, vb]⟩))).1 hPastVotes
    have hNow_mem_history : wNow ∈ M.history.val := by
      simpa [wTop] using hNow_mem
    have hBefore_now : wNow.time ≺− M.history.val :=
      happensBefore_of_mem (P := P)
        (Event := Signature.EventType S) hNow_mem_history
    let Hpred : History P (Signature.EventType S) :=
      History.predecessorHistory (H := M.history)
        (h' := wNow.time) hBefore_now
    have hSubset_trn_now :
        wNow.time ⊆trn M.history.val := by
      have hSubset :=
        History.happensBefore_implies_transitiveSubset
          Hpred M.history
          (by simpa [Hpred, History.predecessorHistory]
            using hBefore_now)
      simpa [Hpred, History.predecessorHistory] using hSubset
    have hSubset_plain_now :
        wNow.time ⊆ M.history.val :=
      History.transitiveSubset_subset
        (P := P) (Event := Signature.EventType S) hSubset_trn_now

    have hVotes_split :=
      (Sat.and (M := M) (w := wNow)
        (φ := ofEvent ⟨voteSymb, [la, va]⟩)
        (ψ := ↓ᶠ (ofEvent ⟨voteSymb, [lb, vb]⟩))).1
        (by simpa using hVotes)
    have hVote_now :
        ⟪wNow⟫ ⊨[M] ofEvent ⟨voteSymb, [la, va]⟩ := hVotes_split.1
    have hPast_vote_other :
        ⟪wNow⟫ ⊨[M] ↓ᶠ (ofEvent ⟨voteSymb, [lb, vb]⟩) :=
      hVotes_split.2

    have hSafeEcho_now_split :=
      voteBackward_elim (M := M)
        (hAx := hVoteAx)
        (hMem := hNow_mem_history)
        (hVote := hVote_now)
    have hNow_le : wNow.time ⪯ M.history.val :=
      PreHistory.happensBeforeEq_of_mem
        (P := P) (Event := Signature.EventType S)
        (hmem := by
          simpa [World.place, World.event, World.time] using hNow_mem_history)
    have hSafe_la :=
      (safe_iff_safeFormula (M := M) (hTheory := hTheory)
        (w := wNow) hNow_le la).1 hSafeEcho_now_split.1
    have hEcho_la_box := hSafeEcho_now_split.2

    obtain ⟨wPast, hPast_mem, hPast_place, hVotePast⟩ :=
      (Sat.past (M := M)
        (w := wNow)
        (φ := ofEvent ⟨voteSymb, [lb, vb]⟩)).1
        hPast_vote_other
    have hPast_mem_history : wPast ∈ M.history.val :=
      hSubset_plain_now _ hPast_mem
    have hEcho_lb_local :=
      (voteBackward_elim (M := M)
        (hAx := hVoteAx)
        (hMem := hPast_mem_history)
        (hVote := hVotePast)).2

    have hPastBox_lb :
        ⟪wNow⟫ ⊨[M]
          ↓ᶠ (□ᶠ↓[[lb]] (ofEvent ⟨echoSymb, [vb]⟩)) :=
      Sat.past_intro_of_prefix (M := M)
        (w := wNow) (t := wPast)
        (ht := hPast_mem) (hp := hPast_place)
        (hφ := hEcho_lb_local)
    have hEcho_lb_box :
        ⟪wNow⟫ ⊨[M]
          □ᶠ↓[[lb]] (ofEvent ⟨echoSymb, [vb]⟩) :=
      pastBoxCollapsesToPresentBox (M := M) (w := wNow)
        (l := lb) (φ := ofEvent ⟨echoSymb, [vb]⟩)
        (hMem := hNow_mem_history) hPastBox_lb

    have step5 :
        ⟪wNow⟫ ⊨[M] ♢ᶠ[[la, lb]] Formula.seq := by
      let uniqueCond : Formula S :=
        ∃≤ᶠ1 v ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)
      let seqGuard : Formula S :=
        ∀ᶠ fun l' => ♢ᶠ[[la, l']] Formula.seq
      have hSafe_disj :
          ⟪wNow⟫ ⊨[M]
            uniqueCond ∨ᶠ seqGuard := by
        simpa [safeFormula, uniqueCond, seqGuard, Formula.or]
          using hSafe_la
      cases sat_or_cases (M := M) (w := wNow)
          (φ := uniqueCond) (ψ := seqGuard) hSafe_disj with
      | inr hSeqGuard =>
          simpa using Sat.forall_elim (M := M) (w := wNow)
            (body := fun l' => ♢ᶠ[[la, l']] Formula.seq)
            (v := lb) hSeqGuard
      | inl hUniqueCond =>
          have hDiamond_va :=
            boxEcho_to_propose_diamond (M := M)
              (w := wNow)
              (hSubset := hSubset_trn_now)
              (hEchoBack := hEchoBack)
              (learner := la) (value := va) hEcho_la_box
          have hDiamond_vb :=
            boxEcho_to_propose_diamond (M := M)
              (w := wNow)
              (hSubset := hSubset_trn_now)
              (hEchoBack := hEchoBack)
              (learner := lb) (value := vb) hEcho_lb_box
          exact False.elim
            (hDistinct
              (uniquePropose_equal_values (M := M)
                (w := wNow)
                (value := va) (altValue := vb)
                hUniqueCond hDiamond_va hDiamond_vb))

    have hEq_disj :
        ⟪wNow⟫ ⊨[M]
          (♢ᶠ↓[[]]
              ((ofEvent ⟨echoSymb, [va]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [vb]⟩))) ∨ᶠ
          (♢ᶠ↓[[]]
              ((ofEvent ⟨echoSymb, [vb]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [va]⟩))) :=
      seq_two_quorums_eventually
        (M := M) (w := wNow)
        (l := la) (l' := lb)
        (evt := ⟨echoSymb, [va]⟩)
        (evt' := ⟨echoSymb, [vb]⟩)
        (hSeq := step5) (hEvt := hEcho_la_box)
        (hEvt' := hEcho_lb_box)
        (hDistinct := by
          intro h
          have hArgs := congrArg Signature.Event.args h
          cases hArgs
          exact hDistinct rfl)
    cases sat_or_cases (M := M) (w := wNow)
        (φ := ♢ᶠ↓[[]]
          ((ofEvent ⟨echoSymb, [va]⟩) ∧ᶠ
            ↓ᶠ (ofEvent ⟨echoSymb, [vb]⟩)))
        (ψ := ♢ᶠ↓[[]]
          ((ofEvent ⟨echoSymb, [vb]⟩) ∧ᶠ
            ↓ᶠ (ofEvent ⟨echoSymb, [va]⟩))) hEq_disj with
    | inl hLeft =>
        exact
          echoNonEquiv_diamond (M := M)
            (echoSymb := echoSymb)
            (hEchoNE := hEchoNE) (hSubset := hSubset_trn_now)
            (valNow := va) (valPast := vb) hLeft
    | inr hRight =>
        exact
          (echoNonEquiv_diamond (M := M)
            (echoSymb := echoSymb)
            (hEchoNE := hEchoNE) (hSubset := hSubset_trn_now)
            (valNow := vb) (valPast := va) hRight).symm

  cases sat_or_cases (M := M) (w := wTop)
      (φ := ♢ᶠ↓[[]]
        ((ofEvent ⟨voteSymb, [l₁, v₁]⟩) ∧ᶠ
          ↓ᶠ (ofEvent ⟨voteSymb, [l₂, v₂]⟩)))
      (ψ := ♢ᶠ↓[[]]
        ((ofEvent ⟨voteSymb, [l₂, v₂]⟩) ∧ᶠ
          ↓ᶠ (ofEvent ⟨voteSymb, [l₁, v₁]⟩))) step2 with
  | inl hLeft =>
      have hEqFinal :=
        derive_contradiction
          (la := l₁) (lb := l₂)
          (va := v₁) (vb := v₂)
          hNe hLeft
      simpa [Sat] using hEqFinal
  | inr hRight =>
      have hEqFinal :=
        derive_contradiction
          (la := l₂) (lb := l₁)
          (va := v₂) (vb := v₁)
          (fun h => hNe h.symm) hRight
      simpa [Sat] using hEqFinal.symm

/-- Paper-facing modal form of agreement. -/
theorem agreement_modal
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ reporting₁ reporting₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]♢ᶠ[[reporting₁, reporting₂]]Formula.seq) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, l₁, v₁]⟩)) ⇒ᶠ
         (♢ᶠ↓[[]] (ofEvent ⟨deliverSymb, [reporting₂, l₂, v₂]⟩)) ⇒ᶠ
         (v₁ ≃ᶠ v₂) := by
  intro p hDeliver₁ hDeliver₂
  apply agreement hTheory
  · exact (sat_diamond_pair_iff M _ reporting₁ reporting₂ Formula.seq).1 (hSeq p)
  · exact observedAt_final_iff.mp (observedAt_iff.mpr hDeliver₁)
  · exact observedAt_final_iff.mp (observedAt_iff.mpr hDeliver₂)


end ThyHBB1
end Examples
end ModalDistribution
