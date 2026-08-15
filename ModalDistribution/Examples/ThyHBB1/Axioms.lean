import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# ThyHBB1 Axioms

This file defines the axiom schemes for the ThyHBB1 broadcast protocol theory.
The axioms are organized into:

- **Backward rules** (Echo?, Vote?, Deliver?): Causal requirements for events
- **Safety formula**: Definition of the safe predicate
- **Non-equivalence axiom** (EchoNE): Sequential participants echo at most one value
- **Forward rules** (Echo!, Vote!, Deliver!): Liveness guarantees
- **Theory assembly**: ThyHBB1 as a collection of axioms

These mirror Figure (HBB1) from the paper and extend ThyLive with protocol-specific axioms.
-/

namespace ModalDistribution
namespace Examples

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section BackwardAxioms

/-- Backward rule `Echo?`: every `Echo(v)` stems from a past `Propose(v)`. -/
@[simp] def echoBackwardAxiom
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun v =>
    ofEvent ⟨echoSymb, [v]⟩ ⇒ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))

/-- The right-hand side of axiom `Safe`: either at most one value has been
proposed, or the learner has sequential quorum intersections with every
learner. -/
@[simp] def safeFormula
    (proposeSymb : Signature.EventSymb S)
    (learner : S.Value) : Formula S :=
  ((∃≤ᶠ1 v ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) ∨ᶠ
      ∀ᶠ (fun l' => ♢ᶠ[[learner, l']] Formula.seq))

/-- Axiom `Safe`: the `safe` predicate is characterised by `safeFormula`. -/
@[simp] def safeAxiom
    (safeSymb : Signature.PredSymb S)
    (proposeSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner =>
    ofPredicate ⟨safeSymb, [learner]⟩ ⇔ᶠ safeFormula proposeSymb learner)

/-- Backward rule `Vote?`: voting requires safety and prior echoes. -/
@[simp] def voteBackwardAxiom
    (safeSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
      (ofPredicate ⟨safeSymb, [learner]⟩ ∧ᶠ
        □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩))))

/-- Backward rule `Deliver?`: deliveries require past votes. -/
@[simp] def deliverBackwardAxiom
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨deliverSymb, [reporting, learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))))

end BackwardAxioms

section NonEquivalenceAxiom

/-- Axiom `EchoNE`: sequential participants echo at most one value. -/
@[simp] def echoNonEquivAxiom
    (echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value => ∀ᶠ (fun altValue =>
    ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
      (↓ᶠ (ofEvent ⟨echoSymb, [altValue]⟩)) ⇒ᶠ
        (value ≃ᶠ altValue)))

end NonEquivalenceAxiom

section ForwardAxioms

/-- Forward rule `Echo!`: live knowledge of a proposal eventually triggers an echo. -/
@[simp] def echoForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
      ∃ᶠ (fun witness =>
        ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)))

/-- Forward rule `Vote!`: persistent safety and echoes lead to a vote. -/
@[simp] def voteForwardAxiom
    (liveSymb safeSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (⇕ᶠ (ofPredicate ⟨safeSymb, [learner]⟩)) ⇒ᶠ
      ((predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
        ↕ᶠ(ofEvent ⟨voteSymb, [learner, value]⟩))))

/-- Forward rule `Deliver!`: live knowledge of votes leads to delivery. -/
@[simp] def deliverForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩)) ⇒ᶠ
      ↕ᶠ(ofEvent ⟨deliverSymb, [reporting, learner, value]⟩))))

end ForwardAxioms

section Theory

variable
    (liveSymb safeSymb : Signature.PredSymb S)
    (proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S)

/-- The collection of axioms forming the theory `ThyHBB1`. -/
@[simp] def ThyHBB1 : Theory S :=
  { ax |
      ax ∈ ThyLive liveSymb ∨
      ax = echoBackwardAxiom proposeSymb echoSymb ∨
      ax = voteBackwardAxiom safeSymb echoSymb voteSymb ∨
      ax = deliverBackwardAxiom voteSymb deliverSymb ∨
      ax = echoNonEquivAxiom echoSymb ∨
      ax = safeAxiom safeSymb proposeSymb ∨
      ax = echoForwardAxiom liveSymb proposeSymb echoSymb ∨
      ax = voteForwardAxiom liveSymb safeSymb echoSymb voteSymb ∨
      ax = deliverForwardAxiom liveSymb voteSymb deliverSymb }

end Theory

section SafePredicate

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- In any model of `ThyHBB1`, the `safe` predicate coincides with
`safeFormula` at every world, by axiom `Safe`. -/
theorem safe_iff_safeFormula
    (hTheory : M ⊨ᵀ
      ThyHBB1 liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (w : World P (Signature.EventType S))
    (hW : w.time ⪯ M.history.val) (l : S.Value) :
    (⟪w⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) ↔
      (⟪w⟫ ⊨[M] safeFormula proposeSymb l) := by
  classical
  have hAx : AllWorldValid M (safeAxiom safeSymb proposeSymb) := by
    apply hTheory
    simp [ThyHBB1]
  have hInst := Sat.forall_elim (M := M) (w := w)
    (body := fun learner =>
      ofPredicate ⟨safeSymb, [learner]⟩ ⇔ᶠ safeFormula proposeSymb learner)
    (v := l) (hAx hW)
  exact ⟨Sat.iff_mp (M := M) (w := w) hInst,
    Sat.iff_mpr (M := M) (w := w) hInst⟩

end SafePredicate

end Examples
end ModalDistribution
