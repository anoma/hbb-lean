import ModalDistribution.Logic.Semantics

/-!
# Shared HBB axiom schemes

Axiom formulas common to the broadcast theories `ThyHBB1`, `ThyHBB2`, and
`ThyHBB3`. The paper states these once and reuses them across Figures 7, 9,
and 11: the `Echo?`, `EchoNE`, and `Echo!` rules are identical in all three
theories, and the `Deliver?`/`Deliver!` rules are identical in `ThyHBB1` and
`ThyHBB2` (in `ThyHBB3` the deliver event is binary, so it has its own).
Each theory's `Axioms.lean` assembles its axiom set from these plus its own
vote rules.
-/

namespace ModalDistribution
namespace Examples
namespace HBB

open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

/-- Backward rule `Echo?`: every `echo(v)` stems from a past `propose(v)`. -/
@[simp] def echoBackwardAxiom
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value =>
    ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))

/-- Axiom `EchoNE`: sequential participants echo at most one value. -/
@[simp] def echoNonEquivAxiom
    (echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value => ∀ᶠ (fun altValue =>
    ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
      (↓ᶠ (ofEvent ⟨echoSymb, [altValue]⟩)) ⇒ᶠ
        (value ≃ᶠ altValue)))

/-- Forward rule `Echo!`: live knowledge of a proposal eventually triggers an
echo of some (possibly different) value. -/
@[simp] def echoForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
      ∃ᶠ (fun witness =>
        ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)))

/-- Backward rule `Deliver?` (ternary deliver): deliveries require a
reporting-learner quorum of past votes. -/
@[simp] def deliverBackwardAxiom
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨deliverSymb, [reporting, learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))))

/-- Forward rule `Deliver!` (ternary deliver): live knowledge of a vote quorum
eventually leads to delivery. -/
@[simp] def deliverForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩)) ⇒ᶠ
      ↕ᶠ(ofEvent ⟨deliverSymb, [reporting, learner, value]⟩))))

end HBB
end Examples
end ModalDistribution
