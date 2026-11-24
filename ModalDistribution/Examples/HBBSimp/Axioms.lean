import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# HBBSimp Axioms

This file records the axiom system of the theory `HBBSimp` (Figure 10 of the
paper): backward rules `Echo?`/`Vote?`/`Deliver?`, non-equivocation `EchoNE`,
and forward rules `Echo!`/`Vote!`/`Deliver!`, over `thyLive`.

Compared to `HBBSafe`, the theory has no `safe` predicate: `Vote?` and `Vote!`
are unguarded. The rules shared verbatim with the other theories come from
`Examples.HBB`.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSimp

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section BackwardAxioms

/-- Paper: Figure 10, rule (Vote?). Backward rule `Vote?`: votes require an `l`-quorum of echoes. -/
@[simp] def voteBackwardAxiom
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)))

end BackwardAxioms

section ForwardAxioms

/-- Paper: Figure 10, rule (Vote!). Forward rule `Vote!`: a live quorum of echoes eventually leads
to a vote. -/
@[simp] def voteForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (↕ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩))) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)))

end ForwardAxioms

section Theory

variable
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S)

/-- Paper: Definition 7.1.1 (theory HBBSimp). The theory `HBBSimp`: the axioms
of `thyLive` together with the rules of Figure 10. -/
@[simp] def theory : Logic.Theory S :=
  { ax |
      ax ∈ thyLive liveSymb ∨
      ax = echoBackwardAxiom proposeSymb echoSymb ∨
      ax = voteBackwardAxiom echoSymb voteSymb ∨
      ax = deliverBackwardAxiom voteSymb deliverSymb ∨
      ax = echoNonEquivAxiom echoSymb ∨
      ax = echoForwardAxiom liveSymb proposeSymb echoSymb ∨
      ax = voteForwardAxiom liveSymb echoSymb voteSymb ∨
      ax = deliverForwardAxiom liveSymb voteSymb deliverSymb }

end Theory

section Projections

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- A model of `HBBSimp` is a model of `thyLive`. -/
theorem theory_thyLive
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    M ⊨ᵀ thyLive liveSymb :=
  fun _ hAx => hTheory (Or.inl hAx)

/-- A model of `HBBSimp` validates `(Echo?)`. -/
theorem theory_echo_backward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] echoBackwardAxiom proposeSymb echoSymb :=
  hTheory (by simp [theory])

/-- A model of `HBBSimp` validates `(Vote?)`. -/
theorem theory_vote_backward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] voteBackwardAxiom echoSymb voteSymb :=
  hTheory (by simp [theory])

/-- A model of `HBBSimp` validates `(Deliver?)`. -/
theorem theory_deliver_backward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] deliverBackwardAxiom voteSymb deliverSymb :=
  hTheory (by simp [theory])

/-- A model of `HBBSimp` validates `(EchoNE)`. -/
theorem theory_echo_non_equiv
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] echoNonEquivAxiom echoSymb :=
  hTheory (by simp [theory])

/-- A model of `HBBSimp` validates `(Echo!)`. -/
theorem theory_echo_forward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] echoForwardAxiom liveSymb proposeSymb echoSymb :=
  hTheory (by simp [theory])

/-- A model of `HBBSimp` validates `(Vote!)`. -/
theorem theory_vote_forward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] voteForwardAxiom liveSymb echoSymb voteSymb :=
  hTheory (by simp [theory])

/-- A model of `HBBSimp` validates `(Deliver!)`. -/
theorem theory_deliver_forward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    □W⊨[M] deliverForwardAxiom liveSymb voteSymb deliverSymb :=
  hTheory (by simp [theory])

end Projections

section Instantiations

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Instantiate `Vote?` at a world of the model: a vote yields a quorum of
past echoes. -/
theorem vote_backward_elim
    (hAx : □W⊨[M] voteBackwardAxiom echoSymb voteSymb)
    {w : World P (Signature.EventType S)}
    (hMem : w ∈ M.history.val)
    {learner value : S.Value}
    (hVote : ⟪w⟫ ⊨[M] ofEvent ⟨voteSymb, [learner, value]⟩) :
    ⟪w⟫ ⊨[M] □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩) :=
  Sat.imp_elim _ _ (Sat.forall_elim _ _ _ value
    (Sat.forall_elim _ _ _ learner (AllWorldValid.of_mem_history M hAx hMem))) hVote

/-- Instantiate `Vote!` at a world of the model: a sometime-live quorum of past
echoes yields an eventual vote. -/
theorem vote_forward_elim
    (hAx : □W⊨[M] voteForwardAxiom liveSymb echoSymb voteSymb)
    {w : World P (Signature.EventType S)}
    (hW : w.time ⪯ M.history.val)
    {learner value : S.Value}
    (hLiveEcho : ⟪w⟫ ⊨[M] (↕ᶠ (predicate0 liveSymb ∧ᶠ
      □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)))) :
    ⟪w⟫ ⊨[M] ↕ᶠ(ofEvent ⟨voteSymb, [learner, value]⟩) :=
  Sat.imp_elim _ _ (Sat.forall_elim _ _ _ value
    (Sat.forall_elim _ _ _ learner (hAx hW))) hLiveEcho

end Instantiations

end HBBSimp

end Examples
end ModalDistribution
