import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# Shared HBB axiom schemes

Axiom formulas common to the broadcast theories `HBBSafe`, `HBBSimp`, and
`HBBCorr`. The paper states these once and reuses them across Figures 8, 10,
and 11: the `Echo?`, `EchoNE`, and `Echo!` rules are identical in all three
theories, and the `Deliver?`/`Deliver!` rules are identical in `HBBSafe` and
`HBBSimp` (in `HBBCorr` the deliver event is binary, so it has its own).
Each theory's `Axioms.lean` assembles its axiom set from these plus its own
vote rules. The `Lemmas` section holds the shared instantiation lemmas for
`Deliver?` and `Deliver!`.

The theory-independent results built on these axioms live in the `HBB`
submodules:

- **`HBB.Liveness`**: Lemmas 6.5.2 and 6.5.3, which need only `thyLive`
- **`HBB.Uniqueness`**: Lemma 6.6.1 and the echo lemmas built on `Echo?`,
  `EchoNE`, and `Echo!`
- **`HBB.Termination`**: the steps shared by the Happy and Cascade
  Termination proofs of the three theories
-/

namespace ModalDistribution
namespace Examples
namespace HBB

open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History PreHistory World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

/-- Paper: Figures 8/10/12, rule (Echo?). Backward rule `Echo?`: every `echo(v)` stems from a past
`propose(v)`. -/
@[simp] def echoBackwardAxiom
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value =>
    ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))

/-- Paper: Figures 8/10/12, axiom (EchoNE). Axiom `EchoNE`: sequential participants echo at most one
value. -/
@[simp] def echoNonEquivAxiom
    (echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value => ∀ᶠ (fun altValue =>
    ofEvent ⟨echoSymb, [value]⟩ ⇒ᶠ
      (↓ᶠ (ofEvent ⟨echoSymb, [altValue]⟩)) ⇒ᶠ
        (value ≃ᶠ altValue)))

/-- Paper: Figures 8/10/12, rule (Echo!). Forward rule `Echo!`: live knowledge of a proposal
eventually triggers an echo of some (possibly different) value. -/
@[simp] def echoForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun value =>
    (↕ᶠ (predicate0 liveSymb ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))) ⇒ᶠ
      ∃ᶠ (fun witness =>
        ↕ᶠ(ofEvent ⟨echoSymb, [witness]⟩)))

/-- Paper: Figures 8/10, rule (Deliver?). Backward rule `Deliver?` (ternary deliver): deliveries
require a reporting-learner quorum of past votes. -/
@[simp] def deliverBackwardAxiom
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    ofEvent ⟨deliverSymb, [reporting, learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))))

/-- Paper: Figures 8/10, rule (Deliver!). Forward rule `Deliver!` (ternary deliver): live knowledge
of a vote quorum eventually leads to delivery. -/
@[simp] def deliverForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ (fun reporting => ∀ᶠ (fun learner => ∀ᶠ (fun value =>
    (↕ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))) ⇒ᶠ
      ↕ᶠ(ofEvent ⟨deliverSymb, [reporting, learner, value]⟩))))

section Lemmas

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- A delivery observed at the end of time yields a reporting-learner quorum of
votes at the end of time, by `Deliver?` and box lifting. -/
theorem deliver_to_vote_box_end
    (hDeliverAx : AllWorldValid M (deliverBackwardAxiom voteSymb deliverSymb))
    {reporting learner value : Signature.Value S}
    {p : P}
    (hDeliver :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting, learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
      □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩) := by
  -- Some participant delivered at an event-tuple `t`.
  obtain ⟨q, hq⟩ := (Sat.diamond_nil M _ _).1 hDeliver
  obtain ⟨t, ht, -, htDeliver⟩ := (Sat.past M _ _).1 hq
  -- (Deliver?) at `t` gives a quorum of votes before `t`; it persists to the end of time.
  exact lift_boxPast_to_end M (History.subset_of_happensBefore (happensBefore_of_mem ht))
    (AllWorldValid.of_mem_history M hDeliverAx ht reporting learner value htDeliver) p

/-- The instantiated `Deliver!` implication: live knowledge of a vote quorum
eventually yields a delivery. This is the form consumed by Lemma 6.5.3. -/
theorem deliver_forward_imp
    (hAx : AllWorldValid M (deliverForwardAxiom liveSymb voteSymb deliverSymb))
    {reporting learner value : S.Value} :
    □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[reporting]] (ofEvent ⟨voteSymb, [learner, value]⟩))) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨deliverSymb, [reporting, learner, value]⟩)) := fun ht =>
  hAx ht reporting learner value

end Lemmas

end HBB
end Examples
end ModalDistribution
