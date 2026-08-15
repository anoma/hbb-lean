import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# ThyHBB3 Axioms

This file records the axiom schemes for the `ThyHBB3` broadcast protocol. The
Theory ThyHBB3 axioms:

* Backward rules `Echo?`, `Vote?`, and `Deliver?`
* Non-equivocation axioms `EchoNE` and `VoteNE`
* Correlation axioms `3twined`, `$\mnta\tf{seq}$`, `$\mnta\utn$`,
  `$\mnta$symm`, and `$\mnta$tran`
* Forward rules `Echo!`, `Vote!`, `Vote'!`, and `Deliver!`

All declarations are definitions of modal formulas; proofs are supplied when the
corresponding lemmas are formalised later.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB3

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section BackwardRules

/-- Backward rule `Vote?`: votes are justified either by an echo quorum or by a
correlated chain of prior votes. Backward rule axiom. -/
@[simp] def voteBackwardAxiom
    (echoSymb voteSymb : Signature.EventSymb S)
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun value =>
    ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
      ((□ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ∨ᶠ
        ∃ᶠ fun correlated =>
          ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩))

/-- Backward rule `Deliver?`: deliveries require an `l`-quorum of votes.
Backward rule axiom. -/
@[simp] def deliverBackwardAxiom
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun value =>
    ofEvent ⟨deliverSymb, [learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[learner]] (ofEvent ⟨voteSymb, [learner, value]⟩)

end BackwardRules

section NonEquivocation

/-- Axiom `VoteNE`: correlated vote chains determine a unique value.
Backward rule axiom. -/
@[simp] def voteNonEquivAxiom
    (voteSymb : Signature.EventSymb S)
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun value =>
    ∀ᶠ fun correlated => ∀ᶠ fun altValue =>
      ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
        (↓ᶠ (ofEvent ⟨voteSymb, [correlated, altValue]⟩)) ⇒ᶠ
          (ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
            (value ≃ᶠ altValue))

end NonEquivocation

section Correlation

/-- Axiom `3twined`: three correlated learners always intersect.
Backward rule axiom. -/
@[simp] def threeTwinedAxiom : Formula S :=
  ∀ᶠ fun learner₁ => ∀ᶠ fun learner₂ => ∀ᶠ fun learner₃ =>
    ♢ᶠ[[learner₁, learner₂, learner₃]] ⊤ᶠ

/-- Axiom `$\mnta\tf{seq}$`: correlated learners have sequential intersections.
Backward rule axiom. -/
@[simp] def mntaSeqAxiom
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun correlated =>
    ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
      ♢ᶠ[[learner, correlated]] Formula.seq

/-- Axiom `$\mnta\utn$`: correlation is historically persistent.
Backward rule axiom. -/
@[simp] def mntaEventuallyAxiom
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun correlated =>
    ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
      ⇓ᶠ (ofPredicate ⟨correlationSymb, [learner, correlated]⟩)

/-- Axiom `$\mnta$symm`: correlation is symmetric.
Backward rule axiom. -/
@[simp] def mntaSymmAxiom
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun correlated =>
    ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
      ofPredicate ⟨correlationSymb, [correlated, learner]⟩

/-- Axiom `$\mnta$tran`: correlation is transitive.
Backward rule axiom. -/
@[simp] def mntaTransAxiom
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun middle => ∀ᶠ fun correlated =>
    ofPredicate ⟨correlationSymb, [learner, middle]⟩ ⇒ᶠ
      ofPredicate ⟨correlationSymb, [middle, correlated]⟩ ⇒ᶠ
        ofPredicate ⟨correlationSymb, [learner, correlated]⟩

end Correlation

section ForwardRules

/-- Forward rule `Vote!`: live learners eventually vote after echo quorums.
Backward rule axiom. -/
@[simp] def voteForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun value =>
    (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
      ∃ᶠ fun witnessed =>
        ↕ᶠ (ofEvent ⟨voteSymb, [learner, witnessed]⟩)

/-- Forward rule `Vote'!`: correlated live knowledge propagates votes.
Backward rule axiom. -/
@[simp] def voteForwardCorrelatedAxiom
    (liveSymb : Signature.PredSymb S)
    (voteSymb : Signature.EventSymb S)
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun correlated => ∀ᶠ fun value =>
    (predicate0 liveSymb ∧ᶠ
        (⇕ᶠ (ofPredicate ⟨correlationSymb, [learner, correlated]⟩)) ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩)) ⇒ᶠ
      ∃ᶠ fun witnessed =>
        ↕ᶠ (ofEvent ⟨voteSymb, [learner, witnessed]⟩)

/-- Forward rule `Deliver!`: live vote quorums eventually lead to deliveries.
Backward rule axiom. -/
@[simp] def deliverForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun value =>
    (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]] (ofEvent ⟨voteSymb, [learner, value]⟩)) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨deliverSymb, [learner, value]⟩)

end ForwardRules

section Theory

variable
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S)
    (correlationSymb : Signature.PredSymb S)

/-- Theory ThyHBB3 .
It extends `ThyLive` with the `ThyHBB3`-specific axioms in Backward rule axiom. -/
@[simp] def theory : Logic.Theory S :=
  { ax |
      ax ∈ ThyLive liveSymb ∨
      ax = echoBackwardAxiom proposeSymb echoSymb ∨
      ax = voteBackwardAxiom echoSymb voteSymb correlationSymb ∨
      ax = deliverBackwardAxiom voteSymb deliverSymb ∨
      ax = echoNonEquivAxiom echoSymb ∨
      ax = voteNonEquivAxiom voteSymb correlationSymb ∨
      ax = threeTwinedAxiom (S := S) ∨
      ax = mntaSeqAxiom correlationSymb ∨
      ax = mntaEventuallyAxiom correlationSymb ∨
      ax = mntaSymmAxiom correlationSymb ∨
      ax = mntaTransAxiom correlationSymb ∨
      ax = echoForwardAxiom liveSymb proposeSymb echoSymb ∨
      ax = voteForwardAxiom liveSymb echoSymb voteSymb ∨
      ax = voteForwardCorrelatedAxiom liveSymb voteSymb correlationSymb ∨
      ax = deliverForwardAxiom liveSymb voteSymb deliverSymb }

end Theory

end ThyHBB3

end Examples
end ModalDistribution
