import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBB.Uniqueness
import ModalDistribution.Examples.HBBSafe.Axioms
import ModalDistribution.Examples.HBBSafe.Safety
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History

/-!
# HBBSafe Agreement Property

This file contains the main agreement theorem for the HBBSafe broadcast protocol.

## Main Result

- **`agreement`**
  The agreement property states that if two different values are delivered at different learners,
  then sequentiality must be violated. More precisely, if:
  - Two deliver events occur for values v₁ and v₂ at learners l₁ and l₂
  - Sequentiality holds between reporting processes l₁' and l₂'
  Then v₁ = v₂.

This is the fundamental correctness property of the broadcast protocol: under sequentiality
assumptions, all processes that deliver a value must deliver the same value.

## Proof Structure

The paper assumes `v₁ ≠ v₂` and derives a contradiction:

1. (Deliver?), Lemma 4.2.3(1): an `l₁'`-quorum voted `(l₁, v₁)` and an `l₂'`-quorum
   voted `(l₂, v₂)`.
2. Proposition 5.1.5(3), `v₁ ≠ v₂`, `⊨ ♢_{l₁' l₂'} seq`: some participant cast one of the
   votes after the other. The two cases are symmetric (step (∗) of the paper).
3. That participant, at some event-tuple `w`, votes `(la, va)` having voted `(lb, vb)`.
4. (Vote?), Lemma 4.2.3(2): at `w`, `la` is safe and there are an `la`-quorum of
   `echo(va)` and an `lb`-quorum of `echo(vb)`.
5. (Safe), `va ≠ vb`: the first disjunct of (Safe) fails, because by (Echo?) both `va`
   and `vb` were proposed (step (∗∗)); so `♢_{la lb} seq`.
6. Proposition 5.1.5(3), (EchoNE): one echo precedes the other at a sequential
   participant, so `va = vb`, a contradiction.

Steps 3–6 are `eq_of_vote_after_vote`.
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
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}
variable {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Steps 3–6 of Proposition 6.4.1: if some participant votes `(la, va)` after having
voted `(lb, vb)`, then `va = vb`. -/
theorem eq_of_vote_after_vote
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {p : P} {la lb va vb : S.Value}
    (hVotes : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] ♢ᶠ↓[[]]
      (ofEvent ⟨voteSymb, [la, va]⟩ ∧ᶠ ↓ᶠ ofEvent ⟨voteSymb, [lb, vb]⟩)) :
    va = vb := by
  refine Classical.byContradiction fun hNe => ?_
  -- Step 3: an event-tuple `w` of the history votes `(la, va)` after voting `(lb, vb)`.
  obtain ⟨_, hPast⟩ := (Sat.diamond_nil ..).1 hVotes
  obtain ⟨w, hw, -, hVotesW⟩ := (Sat.past ..).1 hPast
  obtain ⟨hVoteA, hPastVoteB⟩ := (Sat.and ..).1 hVotesW
  have hSub : w.time ⊆trn M.history.val := time_subset_trn_history M (M.time_le_of_mem hw)
  -- Step 4, (Vote?) at `w`: `la` is safe and an `la`-quorum echoed `va`.
  obtain ⟨hSafe, hEchoA⟩ := vote_backward_elim (theory_vote_backward hTheory) hw hVoteA
  -- Step 4, (Vote?) at the earlier vote and Lemma 4.2.3(2): an `lb`-quorum echoed `vb`.
  obtain ⟨u, hu, huPlace, hVoteB⟩ := (Sat.past ..).1 hPastVoteB
  have hEchoB : ⟪w⟫ ⊨[M] □ᶠ↓[[lb]] ofEvent ⟨echoSymb, [vb]⟩ :=
    past_box_collapses_to_present_box M w lb _ hw <| Sat.past_intro_of_prefix hu huPlace
      (vote_backward_elim (theory_vote_backward hTheory) (hSub.1 _ hu) hVoteB).2
  -- Step 5, (Safe): by (Echo?) both `va` and `vb` were proposed, so the first disjunct
  -- would force `va = vb`; hence `la` and `lb` have sequential quorum intersections.
  have hSeq : ⟪w⟫ ⊨[M] ♢ᶠ[[la, lb]] Formula.seq := by
    rcases (Sat.or ..).1 ((safe_iff_safeFormula hTheory w (M.time_le_of_mem hw) la).1 hSafe)
      with hUnique | hSeqAll
    · have hEchoBack : □W⊨[M] echoBackwardAxiom proposeSymb echoSymb :=
        theory_echo_backward hTheory
      exact absurd (unique_propose_equal_values va vb hUnique
        (box_echo_to_propose_diamond hSub hEchoBack hEchoA)
        (box_echo_to_propose_diamond hSub hEchoBack hEchoB)) hNe
    · exact hSeqAll lb
  -- Step 6, Proposition 5.1.5(3) and (EchoNE): one echo precedes the other at a
  -- sequential participant, so `va = vb`.
  have hEchoNE : □W⊨[M] echoNonEquivAxiom echoSymb := theory_echo_non_equiv hTheory
  rcases (Sat.or ..).1 (seq_two_quorums_eventually hSeq hEchoA hEchoB (by simpa using hNe))
    with h | h
  · exact hNe (echo_non_equiv_diamond hEchoNE hSub h)
  · exact hNe (echo_non_equiv_diamond hEchoNE hSub h).symm

/-- Paper: Proposition 6.4.1 (Agreement). Agreement property for HBBSafe.

Under sequentiality assumptions, if two different values are delivered at different
learners, they must be equal. This is the fundamental correctness property of the
broadcast protocol: all processes that deliver a value must deliver the same value.

The proof proceeds by contradiction, deriving a contradiction from the assumption
that two different values v₁ ≠ v₂ are delivered under sequentiality.

See also: `agreement_of_deliveries`, agreement properties for HBBSimp and HBBCorr. -/
theorem agreement
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ l₁' l₂' : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]♢ᶠ[[l₁', l₂']]Formula.seq) :
    ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩)) ⇒ᶠ
         (♢ᶠ↓[[]] (ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) ⇒ᶠ
         (v₁ ≃ᶠ v₂) := by
  intro p hDeliver₁ hDeliver₂
  show v₁ = v₂
  refine Classical.byContradiction fun hNe => ?_
  -- Step 1, (Deliver?) and Lemma 4.2.3(1): quorums of votes for both deliveries.
  have hDeliverAx : □W⊨[M] deliverBackwardAxiom voteSymb deliverSymb :=
    theory_deliver_backward hTheory
  have hVotes₁ := deliver_to_vote_box_end hDeliverAx hDeliver₁
  have hVotes₂ := deliver_to_vote_box_end hDeliverAx hDeliver₂
  -- Step 2, Proposition 5.1.5(3), `v₁ ≠ v₂`, `⊨ ♢_{l₁' l₂'} seq`: one vote came after the
  -- other. The cases are symmetric; steps 3–6 are `eq_of_vote_after_vote`.
  rcases (Sat.or ..).1 (seq_two_quorums_eventually (hSeq p) hVotes₁ hVotes₂ (by simp [hNe]))
    with h | h
  · exact hNe (eq_of_vote_after_vote hTheory h)
  · exact hNe (eq_of_vote_after_vote hTheory h).symm

/-- Paper: Proposition 6.4.1, hypothesis form. Agreement from deliveries helper for HBBSafe
(Corollary of agreement property).

Whenever both deliveries for (l₁', l₁) and (l₂', l₂) occur at the end of time,
the delivered values must coincide. This factors out the core reasoning used in
the main agreement theorem.

See also: `agreement`. -/
theorem agreement_of_deliveries
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l₁ l₂ l₁' l₂' : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]♢ᶠ[[l₁', l₂']]Formula.seq)
    (hDeliver₁ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₁', l₁, v₁]⟩))
    (hDeliver₂ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [l₂', l₂, v₂]⟩)) :
    ⊨[M] v₁ ≃ᶠ v₂ :=
  fun p => agreement hTheory hSeq p (hDeliver₁ p) (hDeliver₂ p)

end HBBSafe
end Examples
end ModalDistribution
