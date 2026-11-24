import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# HBBSafe Axioms

This file defines the axiom system of the theory `HBBSafe` (Figure 8 of the
paper), organized into:

- **Backward rules** (`Echo?`, `Vote?`, `Deliver?`): causal requirements for events
- **Other rules**: `thyLive`, non-equivocation (`EchoNE`), and the `Safe` axiom
  defining the `safe` predicate
- **Forward rules** (`Echo!`, `Vote!`, `Deliver!`): liveness guarantees

The rules shared verbatim with `HBBSimp`/`HBBCorr` come from `Examples.HBB`.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSafe

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section BackwardAxioms

/-- Paper: Figure 8, right-hand side of axiom (Safe). The right-hand side of axiom `Safe`: either at
most one value has been proposed, or the learner has sequential quorum intersections with every
learner. -/
@[simp] def safeFormula
    (proposeSymb : Signature.EventSymb S)
    (learner : S.Value) : Formula S :=
  ((∃≤ᶠ1 v ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) ∨ᶠ
      ∀ᶠ (fun l' => ♢ᶠ[[learner, l']] Formula.seq))

/-- Paper: Figure 8, axiom (Safe). Axiom `Safe`: the `safe` predicate is characterised by
`safeFormula`. -/
@[simp] def safeAxiom
    (safeSymb : Signature.PredSymb S)
    (proposeSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner =>
    ofPredicate ⟨safeSymb, [learner]⟩ ⇔ᶠ safeFormula proposeSymb learner)

/-- Paper: Figure 8, rule (Vote?). Backward rule `Vote?`: voting requires safety and prior
echoes. -/
@[simp] def voteBackwardAxiom
    (safeSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
      (ofPredicate ⟨safeSymb, [learner]⟩ ∧ᶠ
        □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩))))

end BackwardAxioms

section ForwardAxioms

/-- Paper: Figure 8, rule (Vote!). Forward rule `Vote!`: persistent safety and echoes lead to a
vote. -/
@[simp] def voteForwardAxiom
    (liveSymb safeSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (⇕ᶠ (ofPredicate ⟨safeSymb, [learner]⟩)) ⇒ᶠ
      ((↕ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩))) ⇒ᶠ
        ↕ᶠ(ofEvent ⟨voteSymb, [learner, value]⟩))))

end ForwardAxioms

section Theory

variable
    (liveSymb safeSymb : Signature.PredSymb S)
    (proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S)

/-- Paper: Definition 6.2.2 (theory HBBSafe). The collection of axioms forming the theory
`HBBSafe`. -/
@[simp] def theory : Theory S :=
  { ax |
      ax ∈ thyLive liveSymb ∨
      ax = echoBackwardAxiom proposeSymb echoSymb ∨
      ax = voteBackwardAxiom safeSymb echoSymb voteSymb ∨
      ax = deliverBackwardAxiom voteSymb deliverSymb ∨
      ax = echoNonEquivAxiom echoSymb ∨
      ax = safeAxiom safeSymb proposeSymb ∨
      ax = echoForwardAxiom liveSymb proposeSymb echoSymb ∨
      ax = voteForwardAxiom liveSymb safeSymb echoSymb voteSymb ∨
      ax = deliverForwardAxiom liveSymb voteSymb deliverSymb }

end Theory

section Projections

/-! Each axiom of `HBBSafe` is valid in every model of the theory. -/

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- A model of `HBBSafe` is a model of `thyLive`. -/
theorem theory_thyLive
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) : M ⊨ᵀ thyLive liveSymb :=
  fun _ hAx => hTheory (Or.inl hAx)

theorem theory_echo_backward
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] echoBackwardAxiom proposeSymb echoSymb :=
  hTheory (by simp [theory])

theorem theory_vote_backward
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] voteBackwardAxiom safeSymb echoSymb voteSymb :=
  hTheory (by simp [theory])

theorem theory_deliver_backward
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] deliverBackwardAxiom voteSymb deliverSymb :=
  hTheory (by simp [theory])

theorem theory_echo_non_equiv
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] echoNonEquivAxiom echoSymb :=
  hTheory (by simp [theory])

theorem theory_safe
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] safeAxiom safeSymb proposeSymb :=
  hTheory (by simp [theory])

theorem theory_echo_forward
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] echoForwardAxiom liveSymb proposeSymb echoSymb :=
  hTheory (by simp [theory])

theorem theory_vote_forward
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] voteForwardAxiom liveSymb safeSymb echoSymb voteSymb :=
  hTheory (by simp [theory])

theorem theory_deliver_forward
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] deliverForwardAxiom liveSymb voteSymb deliverSymb :=
  hTheory (by simp [theory])

end Projections

section Instantiations

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- In any model of `HBBSafe`, the `safe` predicate coincides with
`safeFormula` at every world, by axiom `Safe`. -/
theorem safe_iff_safeFormula
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (w : World P (Signature.EventType S))
    (hW : w.time ⪯ M.history.val) (l : S.Value) :
    (⟪w⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) ↔
      (⟪w⟫ ⊨[M] safeFormula proposeSymb l) :=
  ⟨Sat.iff_mp M w (theory_safe hTheory hW l), Sat.iff_mpr M w (theory_safe hTheory hW l)⟩

/-- Instantiate `Vote?` at an event-tuple of the model: a vote yields safety of the
learner and a quorum of past echoes. -/
theorem vote_backward_elim
    (hAx : □W⊨[M] voteBackwardAxiom safeSymb echoSymb voteSymb)
    {w : World P (Signature.EventType S)}
    (hMem : w ∈ M.history.val)
    {learner value : S.Value}
    (hVote : ⟪w⟫ ⊨[M] ofEvent ⟨voteSymb, [learner, value]⟩) :
    (⟪w⟫ ⊨[M] ofPredicate ⟨safeSymb, [learner]⟩) ∧
      (⟪w⟫ ⊨[M] □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) :=
  (Sat.and ..).1 (hAx (M.time_le_of_mem hMem) learner value hVote)

end Instantiations

end HBBSafe
end Examples
end ModalDistribution
