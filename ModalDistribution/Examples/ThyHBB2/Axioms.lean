import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# ThyHBB2 Axioms

This file records the axiom system of the theory `ThyHBB2` (Figure 9 of the
paper): backward rules `Echo?`/`Vote?`/`Deliver?`, non-equivocation `EchoNE`,
and forward rules `Echo!`/`Vote!`/`Deliver!`, over `ThyLive`.

Compared to `ThyHBB1`, the theory has no `safe` predicate: `Vote?` and `Vote!`
are unguarded. The rules shared verbatim with the other theories come from
`Examples.HBB`.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB2

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section BackwardAxioms

/-- Backward rule `Vote?`: votes require an `l`-quorum of echoes. -/
@[simp] def voteBackwardAxiom
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)))

end BackwardAxioms

section NonEquivocation

end NonEquivocation

section ForwardAxioms

/-- Forward rule `Vote!`: a live quorum of echoes eventually leads to a vote. -/
@[simp] def voteForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)))

end ForwardAxioms

section Theory

variable
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S)

/-- Theory ThyHBB2 .
It extends `ThyLive` with the `ThyHBB2`-specific axioms shown in -/
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
