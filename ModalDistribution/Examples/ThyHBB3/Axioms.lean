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
* Correlation axioms `3twined`, `(≐seq)`, `(≐⇓)`, `(≐symm)`, and `(≐tran)`
* Forward rules `Echo!`, `Vote!`, `Vote'!`, and `Deliver!`

These are Figure 11 of the paper; the shared `Echo?`/`EchoNE`/`Echo!` rules
come from `Examples.HBB`.
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

/-- Paper: Figure 11, rule (Vote?). Backward rule `Vote?`: votes are justified either by an echo quorum or by a
correlated chain of prior votes. -/
@[simp] def voteBackwardAxiom
    (echoSymb voteSymb : Signature.EventSymb S)
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun value =>
    ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
      ((□ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ∨ᶠ
        ∃ᶠ fun correlated =>
          ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩))

/-- Paper: Figure 11, rule (Deliver?). Backward rule `Deliver?`: deliveries require an `l`-quorum of votes. -/
@[simp] def deliverBackwardAxiom
    (voteSymb deliverSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun value =>
    ofEvent ⟨deliverSymb, [learner, value]⟩ ⇒ᶠ
      □ᶠ↓[[learner]] (ofEvent ⟨voteSymb, [learner, value]⟩)

end BackwardRules

section NonEquivocation

/-- Paper: Figure 11, axiom (VoteNE). Axiom `VoteNE`: correlated vote chains determine a unique value. -/
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

/-- Paper: Figure 11, axiom (3twined). Axiom `3twined`: any three quorums (of any three learners) intersect. -/
@[simp] def threeTwinedAxiom : Formula S :=
  ∀ᶠ fun learner₁ => ∀ᶠ fun learner₂ => ∀ᶠ fun learner₃ =>
    ♢ᶠ[[learner₁, learner₂, learner₃]] ⊤ᶠ

/-- Paper: Figure 11, axiom (≐seq). Axiom `$\mnta\tf{seq}$`: correlated learners have sequential intersections. -/
@[simp] def correlationSeqAxiom
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun correlated =>
    ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
      ♢ᶠ[[learner, correlated]] Formula.seq

/-- Paper: Figure 11, axiom (≐⇓). Axiom `$\mnta\utn$`: correlation is historically persistent. -/
@[simp] def correlationMonotoneAxiom
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun correlated =>
    ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
      ⇓ᶠ (ofPredicate ⟨correlationSymb, [learner, correlated]⟩)

/-- Paper: Figure 11, axiom (≐symm). Axiom `$\mnta$symm`: correlation is symmetric. -/
@[simp] def correlationSymmAxiom
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun correlated =>
    ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
      ofPredicate ⟨correlationSymb, [correlated, learner]⟩

/-- Paper: Figure 11, axiom (≐tran). Axiom `$\mnta$tran`: correlation is transitive. -/
@[simp] def correlationTransAxiom
    (correlationSymb : Signature.PredSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun middle => ∀ᶠ fun correlated =>
    ofPredicate ⟨correlationSymb, [learner, middle]⟩ ⇒ᶠ
      ofPredicate ⟨correlationSymb, [middle, correlated]⟩ ⇒ᶠ
        ofPredicate ⟨correlationSymb, [learner, correlated]⟩

end Correlation

section ForwardRules

/-- Paper: Figure 11, rule (Vote!). Forward rule `Vote!`: live learners eventually vote after echo quorums. -/
@[simp] def voteForwardAxiom
    (liveSymb : Signature.PredSymb S)
    (echoSymb voteSymb : Signature.EventSymb S) : Formula S :=
  ∀ᶠ fun learner => ∀ᶠ fun value =>
    (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
      ∃ᶠ fun witnessed =>
        ↕ᶠ (ofEvent ⟨voteSymb, [learner, witnessed]⟩)

/-- Paper: Figure 11, rule (Vote'!). Forward rule `Vote'!`: correlated live knowledge propagates votes. -/
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

/-- Paper: Figure 11, rule (Deliver!). Forward rule `Deliver!`: live vote quorums eventually lead to deliveries. -/
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

/-- Paper: Definition 8.2.1 (theory ThyHBB3). Theory ThyHBB3 .
It extends `ThyLive` with the `ThyHBB3`-specific axioms in -/
@[simp] def theory : Logic.Theory S :=
  { ax |
      ax ∈ ThyLive liveSymb ∨
      ax = echoBackwardAxiom proposeSymb echoSymb ∨
      ax = voteBackwardAxiom echoSymb voteSymb correlationSymb ∨
      ax = deliverBackwardAxiom voteSymb deliverSymb ∨
      ax = echoNonEquivAxiom echoSymb ∨
      ax = voteNonEquivAxiom voteSymb correlationSymb ∨
      ax = threeTwinedAxiom (S := S) ∨
      ax = correlationSeqAxiom correlationSymb ∨
      ax = correlationMonotoneAxiom correlationSymb ∨
      ax = correlationSymmAxiom correlationSymb ∨
      ax = correlationTransAxiom correlationSymb ∨
      ax = echoForwardAxiom liveSymb proposeSymb echoSymb ∨
      ax = voteForwardAxiom liveSymb echoSymb voteSymb ∨
      ax = voteForwardCorrelatedAxiom liveSymb voteSymb correlationSymb ∨
      ax = deliverForwardAxiom liveSymb voteSymb deliverSymb }

end Theory


section Projections

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {correlationSymb : Signature.PredSymb S}

/-- A model of `ThyHBB3` is a model of `ThyLive`. -/
theorem theory_thyLive
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    M ⊨ᵀ ThyLive liveSymb :=
  fun _ hAx => hTheory (Or.inl hAx)

theorem theory_echoBackward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] echoBackwardAxiom proposeSymb echoSymb :=
  hTheory (by simp [theory])

theorem theory_voteBackward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] voteBackwardAxiom echoSymb voteSymb correlationSymb :=
  hTheory (by simp [theory])

theorem theory_deliverBackward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] deliverBackwardAxiom voteSymb deliverSymb :=
  hTheory (by simp [theory])

theorem theory_echoNonEquiv
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] echoNonEquivAxiom echoSymb :=
  hTheory (by simp [theory])

theorem theory_voteNonEquiv
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] voteNonEquivAxiom voteSymb correlationSymb :=
  hTheory (by simp [theory])

theorem theory_threeTwined
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] (threeTwinedAxiom : Formula S) :=
  hTheory (by simp [theory])

theorem theory_correlationSeq
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] correlationSeqAxiom correlationSymb :=
  hTheory (by simp [theory])

theorem theory_correlationMonotone
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] correlationMonotoneAxiom correlationSymb :=
  hTheory (by simp [theory])

theorem theory_correlationSymm
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] correlationSymmAxiom correlationSymb :=
  hTheory (by simp [theory])

theorem theory_correlationTrans
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] correlationTransAxiom correlationSymb :=
  hTheory (by simp [theory])

theorem theory_echoForward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] echoForwardAxiom liveSymb proposeSymb echoSymb :=
  hTheory (by simp [theory])

theorem theory_voteForward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] voteForwardAxiom liveSymb echoSymb voteSymb :=
  hTheory (by simp [theory])

theorem theory_voteForwardCorrelated
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] voteForwardCorrelatedAxiom liveSymb voteSymb correlationSymb :=
  hTheory (by simp [theory])

theorem theory_deliverForward
    (hTheory : M ⊨ᵀ theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb) :
    □W⊨[M] deliverForwardAxiom liveSymb voteSymb deliverSymb :=
  hTheory (by simp [theory])

end Projections

section Instantiations

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {correlationSymb : Signature.PredSymb S}
variable {w : World P (Signature.EventType S)}

/-- Instantiate `(Vote?)` at a world: a vote is justified by an echo quorum
or by a correlated prior vote. -/
theorem voteBackward_elim
    (hAx : □W⊨[M] voteBackwardAxiom echoSymb voteSymb correlationSymb)
    (hW : w.time ⪯ M.history.val)
    {learner value : S.Value}
    (hVote : ⟪w⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) :
    ⟪w⟫ ⊨[M]
      ((□ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ∨ᶠ
        ∃ᶠ fun correlated =>
          ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩)) := by
  classical
  have hLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner' =>
        ∀ᶠ fun value' =>
          ofEvent ⟨voteSymb, [learner', value']⟩ ⇒ᶠ
            ((□ᶠ↓[[learner']] (ofEvent ⟨echoSymb, [value']⟩)) ∨ᶠ
              ∃ᶠ fun correlated =>
                ofPredicate ⟨correlationSymb, [correlated, learner']⟩ ∧ᶠ
                  ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value']⟩)))
      (v := learner)
      (by simpa [voteBackwardAxiom] using hAx hW)
  have hValue :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value' =>
        ofEvent ⟨voteSymb, [learner, value']⟩ ⇒ᶠ
          ((□ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value']⟩)) ∨ᶠ
            ∃ᶠ fun correlated =>
              ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value']⟩)))
      (v := value) hLearner
  exact
    (Sat.imp (M := M) (w := w)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)
      (ψ := (□ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)) ∨ᶠ
        ∃ᶠ fun correlated =>
          ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩))).1
      hValue hVote

/-- Instantiate `(Deliver?)` at a world: a delivery forces a vote quorum. -/
theorem deliverBackward_elim
    (hAx : □W⊨[M] deliverBackwardAxiom voteSymb deliverSymb)
    (hW : w.time ⪯ M.history.val)
    {learner value : S.Value}
    (hDeliver : ⟪w⟫ ⊨[M]ofEvent ⟨deliverSymb, [learner, value]⟩) :
    ⟪w⟫ ⊨[M]□ᶠ↓[[learner]] (ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  have hLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner' =>
        ∀ᶠ fun value' =>
          ofEvent ⟨deliverSymb, [learner', value']⟩ ⇒ᶠ
            □ᶠ↓[[learner']] (ofEvent ⟨voteSymb, [learner', value']⟩))
      (v := learner)
      (by simpa [deliverBackwardAxiom] using hAx hW)
  have hValue :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value' =>
        ofEvent ⟨deliverSymb, [learner, value']⟩ ⇒ᶠ
          □ᶠ↓[[learner]] (ofEvent ⟨voteSymb, [learner, value']⟩))
      (v := value) hLearner
  exact
    (Sat.imp (M := M) (w := w)
      (φ := ofEvent ⟨deliverSymb, [learner, value]⟩)
      (ψ := □ᶠ↓[[learner]] (ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hValue hDeliver

/-- Instantiate `(VoteNE)` at a world: correlated votes agree on the value. -/
theorem voteNonEquiv_elim
    (hAx : □W⊨[M] voteNonEquivAxiom voteSymb correlationSymb)
    (hW : w.time ⪯ M.history.val)
    {learner value correlated altValue : S.Value}
    (hVote : ⟪w⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩)
    (hPastVote : ⟪w⟫ ⊨[M]↓ᶠ (ofEvent ⟨voteSymb, [correlated, altValue]⟩))
    (hCorr : ⟪w⟫ ⊨[M]ofPredicate ⟨correlationSymb, [learner, correlated]⟩) :
    ⟪w⟫ ⊨[M](value ≃ᶠ altValue) := by
  classical
  have hLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner' =>
        ∀ᶠ fun value' => ∀ᶠ fun correlated' => ∀ᶠ fun altValue' =>
          ofEvent ⟨voteSymb, [learner', value']⟩ ⇒ᶠ
            (↓ᶠ (ofEvent ⟨voteSymb, [correlated', altValue']⟩)) ⇒ᶠ
              (ofPredicate ⟨correlationSymb, [learner', correlated']⟩ ⇒ᶠ
                (value' ≃ᶠ altValue')))
      (v := learner)
      (by simpa [voteNonEquivAxiom] using hAx hW)
  have hValue :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value' =>
        ∀ᶠ fun correlated' => ∀ᶠ fun altValue' =>
          ofEvent ⟨voteSymb, [learner, value']⟩ ⇒ᶠ
            (↓ᶠ (ofEvent ⟨voteSymb, [correlated', altValue']⟩)) ⇒ᶠ
              (ofPredicate ⟨correlationSymb, [learner, correlated']⟩ ⇒ᶠ
                (value' ≃ᶠ altValue')))
      (v := value) hLearner
  have hCorrelated :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun correlated' =>
        ∀ᶠ fun altValue' =>
          ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
            (↓ᶠ (ofEvent ⟨voteSymb, [correlated', altValue']⟩)) ⇒ᶠ
              (ofPredicate ⟨correlationSymb, [learner, correlated']⟩ ⇒ᶠ
                (value ≃ᶠ altValue')))
      (v := correlated) hValue
  have hAlt :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun altValue' =>
        ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
          (↓ᶠ (ofEvent ⟨voteSymb, [correlated, altValue']⟩)) ⇒ᶠ
            (ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
              (value ≃ᶠ altValue')))
      (v := altValue) hCorrelated
  exact
    Sat.imp_elim (M := M) (w := w)
      (φ := ofPredicate ⟨correlationSymb, [learner, correlated]⟩)
      (ψ := value ≃ᶠ altValue)
      (Sat.imp_elim (M := M) (w := w)
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [correlated, altValue]⟩))
        (ψ := ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
          (value ≃ᶠ altValue))
        (Sat.imp_elim (M := M) (w := w)
          (φ := ofEvent ⟨voteSymb, [learner, value]⟩)
          (ψ := (↓ᶠ (ofEvent ⟨voteSymb, [correlated, altValue]⟩)) ⇒ᶠ
            (ofPredicate ⟨correlationSymb, [learner, correlated]⟩ ⇒ᶠ
              (value ≃ᶠ altValue)))
          hAlt hVote)
        hPastVote)
      hCorr

/-- Instantiate `(3twined)` at a world: any three quorums intersect. -/
theorem threeTwined_elim
    (hAx : □W⊨[M] (threeTwinedAxiom : Formula S))
    (hW : w.time ⪯ M.history.val)
    {l₁ l₂ l₃ : S.Value} :
    ⟪w⟫ ⊨[M]♢ᶠ[[l₁, l₂, l₃]] ⊤ᶠ := by
  classical
  have hFirst :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner₁ =>
        ∀ᶠ fun learner₂ => ∀ᶠ fun learner₃ =>
          ♢ᶠ[[learner₁, learner₂, learner₃]] ⊤ᶠ)
      (v := l₁)
      (by simpa [threeTwinedAxiom] using hAx hW)
  have hSecond :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner₂ =>
        ∀ᶠ fun learner₃ => ♢ᶠ[[l₁, learner₂, learner₃]] ⊤ᶠ)
      (v := l₂) hFirst
  exact
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner₃ => ♢ᶠ[[l₁, l₂, learner₃]] ⊤ᶠ)
      (v := l₃) hSecond

/-- Instantiate `(≐seq)` at a world: correlated learners have a sequential
quorum intersection. -/
theorem correlationSeq_elim
    (hAx : □W⊨[M] correlationSeqAxiom correlationSymb)
    (hW : w.time ⪯ M.history.val)
    {learner correlated : S.Value}
    (hCorr : ⟪w⟫ ⊨[M]ofPredicate ⟨correlationSymb, [learner, correlated]⟩) :
    ⟪w⟫ ⊨[M]♢ᶠ[[learner, correlated]] Formula.seq := by
  classical
  have hLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner' =>
        ∀ᶠ fun correlated' =>
          ofPredicate ⟨correlationSymb, [learner', correlated']⟩ ⇒ᶠ
            ♢ᶠ[[learner', correlated']] Formula.seq)
      (v := learner)
      (by simpa [correlationSeqAxiom] using hAx hW)
  have hCorrelated :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun correlated' =>
        ofPredicate ⟨correlationSymb, [learner, correlated']⟩ ⇒ᶠ
          ♢ᶠ[[learner, correlated']] Formula.seq)
      (v := correlated) hLearner
  exact
    (Sat.imp (M := M) (w := w)
      (φ := ofPredicate ⟨correlationSymb, [learner, correlated]⟩)
      (ψ := ♢ᶠ[[learner, correlated]] Formula.seq)).1
      hCorrelated hCorr

/-- Instantiate `(≐⇓)` at a world: correlation persists through the past. -/
theorem correlationMonotone_elim
    (hAx : □W⊨[M] correlationMonotoneAxiom correlationSymb)
    (hW : w.time ⪯ M.history.val)
    {learner correlated : S.Value}
    (hCorr : ⟪w⟫ ⊨[M]ofPredicate ⟨correlationSymb, [learner, correlated]⟩) :
    ⟪w⟫ ⊨[M]⇓ᶠ (ofPredicate ⟨correlationSymb, [learner, correlated]⟩) := by
  classical
  have hLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner' =>
        ∀ᶠ fun correlated' =>
          ofPredicate ⟨correlationSymb, [learner', correlated']⟩ ⇒ᶠ
            ⇓ᶠ (ofPredicate ⟨correlationSymb, [learner', correlated']⟩))
      (v := learner)
      (by simpa [correlationMonotoneAxiom] using hAx hW)
  have hCorrelated :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun correlated' =>
        ofPredicate ⟨correlationSymb, [learner, correlated']⟩ ⇒ᶠ
          ⇓ᶠ (ofPredicate ⟨correlationSymb, [learner, correlated']⟩))
      (v := correlated) hLearner
  exact
    (Sat.imp (M := M) (w := w)
      (φ := ofPredicate ⟨correlationSymb, [learner, correlated]⟩)
      (ψ := ⇓ᶠ (ofPredicate ⟨correlationSymb, [learner, correlated]⟩))).1
      hCorrelated hCorr

/-- Instantiate `(≐symm)` at a world: correlation is symmetric. -/
theorem correlationSymm_elim
    (hAx : □W⊨[M] correlationSymmAxiom correlationSymb)
    (hW : w.time ⪯ M.history.val)
    {learner correlated : S.Value}
    (hCorr : ⟪w⟫ ⊨[M]ofPredicate ⟨correlationSymb, [learner, correlated]⟩) :
    ⟪w⟫ ⊨[M]ofPredicate ⟨correlationSymb, [correlated, learner]⟩ := by
  classical
  have hLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner' =>
        ∀ᶠ fun correlated' =>
          ofPredicate ⟨correlationSymb, [learner', correlated']⟩ ⇒ᶠ
            ofPredicate ⟨correlationSymb, [correlated', learner']⟩)
      (v := learner)
      (by simpa [correlationSymmAxiom] using hAx hW)
  have hCorrelated :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun correlated' =>
        ofPredicate ⟨correlationSymb, [learner, correlated']⟩ ⇒ᶠ
          ofPredicate ⟨correlationSymb, [correlated', learner]⟩)
      (v := correlated) hLearner
  exact
    (Sat.imp (M := M) (w := w)
      (φ := ofPredicate ⟨correlationSymb, [learner, correlated]⟩)
      (ψ := ofPredicate ⟨correlationSymb, [correlated, learner]⟩)).1
      hCorrelated hCorr

/-- The instantiated `Deliver!` implication: live knowledge of a vote quorum
eventually yields a delivery. This is the form consumed by Lemma 6.4.3. -/
theorem deliverForward_imp
    (hAx : □W⊨[M] deliverForwardAxiom liveSymb voteSymb deliverSymb)
    {learner value : S.Value} :
    □W⊨[M]((predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[learner]] (ofEvent ⟨voteSymb, [learner, value]⟩)) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨deliverSymb, [learner, value]⟩)) := by
  classical
  intro t ht
  have hLocal :
      ⟪t⟫ ⊨[M] deliverForwardAxiom liveSymb voteSymb deliverSymb :=
    hAx ht
  have hLearner :=
    Sat.forall_elim (M := M) (w := t)
      (body := fun learner' =>
        ∀ᶠ fun value' =>
          (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[learner']] (ofEvent ⟨voteSymb, [learner', value']⟩)) ⇒ᶠ
            ↕ᶠ (ofEvent ⟨deliverSymb, [learner', value']⟩))
      (v := learner)
      (by simpa [deliverForwardAxiom] using hLocal)
  exact
    Sat.forall_elim (M := M) (w := t)
      (body := fun value' =>
        (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[learner]] (ofEvent ⟨voteSymb, [learner, value']⟩)) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨deliverSymb, [learner, value']⟩))
      (v := value) hLearner

end Instantiations

end ThyHBB3

end Examples
end ModalDistribution
