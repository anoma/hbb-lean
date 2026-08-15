import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# ThyHBB1 Axioms

This file defines the axiom system of the theory `ThyHBB1` (Figure 7 of the
paper), organized into:

- **Backward rules** (`Echo?`, `Vote?`, `Deliver?`): causal requirements for events
- **Other rules**: `ThyLive`, non-equivocation (`EchoNE`), and the `Safe` axiom
  defining the `safe` predicate
- **Forward rules** (`Echo!`, `Vote!`, `Deliver!`): liveness guarantees

The rules shared verbatim with `ThyHBB2`/`ThyHBB3` come from `Examples.HBB`.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB1

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section BackwardAxioms

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

end BackwardAxioms

section NonEquivalenceAxiom

end NonEquivalenceAxiom

section ForwardAxioms

/-- Forward rule `Vote!`: persistent safety and echoes lead to a vote. -/
@[simp] def voteForwardAxiom
    (liveSymb safeSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (⇕ᶠ (ofPredicate ⟨safeSymb, [learner]⟩)) ⇒ᶠ
      ((predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
        ↕ᶠ(ofEvent ⟨voteSymb, [learner, value]⟩))))

end ForwardAxioms

section Theory

variable
    (liveSymb safeSymb : Signature.PredSymb S)
    (proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S)

/-- The collection of axioms forming the theory `ThyHBB1`. -/
@[simp] def theory : Theory S :=
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
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (w : World P (Signature.EventType S))
    (hW : w.time ⪯ M.history.val) (l : S.Value) :
    (⟪w⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) ↔
      (⟪w⟫ ⊨[M] safeFormula proposeSymb l) := by
  classical
  have hAx : AllWorldValid M (safeAxiom safeSymb proposeSymb) := by
    apply hTheory
    simp [theory]
  have hInst := Sat.forall_elim (M := M) (w := w)
    (body := fun learner =>
      ofPredicate ⟨safeSymb, [learner]⟩ ⇔ᶠ safeFormula proposeSymb learner)
    (v := l) (hAx hW)
  exact ⟨Sat.iff_mp (M := M) (w := w) hInst,
    Sat.iff_mpr (M := M) (w := w) hInst⟩

end SafePredicate

end ThyHBB1
end Examples
end ModalDistribution
