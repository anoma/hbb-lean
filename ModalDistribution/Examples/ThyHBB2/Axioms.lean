import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# ThyHBB2 Axioms

This file records the axiom schemes for the `ThyHBB2` broadcast protocol theory.
Theory ThyHBB2 axioms:

- **Backward rules**: `Echo?`, `Vote?`, and `Deliver?`
- **Non-equivocation**: `EchoNE`
- **Forward rules**: `Echo!`, `Vote!`, and `Deliver!`
- **Theory assembly**: `ThyHBB2` extends `ThyLive` with these axioms

Compared to `ThyHBB1`, the theory drops the `safe` predicate from `Vote?` and
 `Vote!`, reflecting the simplified protocol assumptions.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB2

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section BackwardAxioms

/-- Backward rule `Echo?`: every `Echo(v)` stems from a past `Propose(v)`.
Backward rule axiom. -/
@[simp] def echoBackwardAxiom
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value =>
    ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))

/-- Backward rule `Vote?`: votes require an `l`-quorum of echoes.
Backward rule axiom. -/
@[simp] def voteBackwardAxiom
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)))

/-- Backward rule `Deliver?`: deliveries require an `l'`-quorum of votes.
Backward rule axiom. -/
@[simp] def deliverBackwardAxiom
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨deliverSymb, [reporting, learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))))

end BackwardAxioms

section NonEquivocation

/-- Axiom `EchoNE`: sequential participants echo at most one value.
Backward rule axiom. -/
@[simp] def echoNonEquivAxiom
    (echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value => ∀ᶠ (fun altValue =>
    ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
      (↓ᶠ (ofEvent ⟨echoSymb, [altValue]⟩)) ⇒ᶠ
        (value ≃ᶠ altValue)))

end NonEquivocation

section ForwardAxioms

/-- Forward rule `Echo!`: live knowledge of a proposal eventually triggers an echo.
Backward rule axiom. -/
@[simp] def echoForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
      ∃ᶠ (fun witness => ↕ᶠ (ofEvent ⟨echoSymb, [witness]⟩)))

/-- Forward rule `Vote!`: a live quorum of echoes eventually leads to a vote.
Backward rule axiom. -/
@[simp] def voteForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)))

/-- Forward rule `Deliver!`: live knowledge of votes leads to delivery.
Backward rule axiom. -/
@[simp] def deliverForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩)) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩))))

end ForwardAxioms

section Theory

variable
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S)

/-- Theory ThyHBB2 .
It extends `ThyLive` with the `ThyHBB2`-specific axioms shown in Backward rule axiom. -/
@[simp] def theory : Logic.Theory S :=
  { ax |
      ax ∈ ThyLive liveSymb ∨
      ax = echoBackwardAxiom proposeSymb echoSymb ∨
      ax = voteBackwardAxiom echoSymb voteSymb ∨
      ax = deliverBackwardAxiom voteSymb deliverSymb ∨
      ax = echoNonEquivAxiom echoSymb ∨
      ax = echoForwardAxiom liveSymb proposeSymb echoSymb ∨
      ax = voteForwardAxiom liveSymb echoSymb voteSymb ∨
      ax = deliverForwardAxiom liveSymb voteSymb deliverSymb }

end Theory

end ThyHBB2

end Examples
end ModalDistribution
