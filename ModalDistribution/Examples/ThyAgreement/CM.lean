import ModalDistribution.Examples.ThyAgreement.Axioms

namespace ModalDistribution.Examples.ThyAgreement
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- Causal monotonicity gives vote monotonicity. -/
theorem ProtocolCM.voteMonotone (h : ProtocolCM M σ) : VoteMonotonicity M σ := by
  intro w hw g c v n hg _ _ a ha
  exact h.causalMonotone hw ha hg

/-- CM ⇒ VM. -/
def ProtocolCM.toVM (h : ProtocolCM M σ) : ProtocolVM M σ :=
  { h.toBaseProtocol with voteMonotone := h.voteMonotone }

/-! ## Correctness properties

In `ThyAgreement` these are axioms of `BaseProtocol`; the theorems below restate
them in the forms HBB4's `CM`/`VM` modules export, so that clients (and the
paper-facing modal versions) read the same for both theories. -/

/-- End-of-time agreement when every final participant correlates the learners. -/
theorem agreement (h : BaseProtocol M σ) {a b v u : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hv : Occurs M (σ.deliver a v)) (hu : Occurs M (σ.deliver b u)) : v = u :=
  h.agreement hab hv hu

/-- Liveness 1. -/
theorem livenessOne (h : BaseProtocol M σ) {l v : S.Value}
    (hLiveQuorum : ∃ Q ∈ (M.learner l).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hUnique : UniqueOccurrence M σ.propose)
    (hObserved : ∃ e ∈ M.history.val,
      (⟪e⟫ ⊨[M] σ.live) ∧ ObservedAt M e (σ.propose v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver l v) :=
  h.livenessOne hLiveQuorum hUnique hObserved p hLive

/-- Liveness 2. -/
theorem livenessTwo (h : BaseProtocol M σ) {a b v : S.Value}
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver b v) :=
  h.livenessTwo hCorrelation hLiveQuorum hDelivered p hLive

/-- Agreement in the paper's modal notation. -/
theorem agreement_modal (h : BaseProtocol M σ) {a b v u : S.Value}
    (hab : ⊨[M] □ᶠ[] (σ.correlation a b)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ
      (♢ᶠ↓[[]] (σ.deliver b u)) ⇒ᶠ (v ≃ᶠ u) :=
  occurrence_agreement_iff.mp (agreement h (correlated_final_iff_end.mpr hab))

/-- Liveness 1 in the paper's modal notation. -/
theorem livenessOne_modal (h : BaseProtocol M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  apply occurrence_liveness_iff.mp
  rintro ⟨e, he, hboth⟩ p hlive
  obtain ⟨hl, hp⟩ := (Sat.and ..).mp hboth
  exact livenessOne h (quorum_final_iff_end.mpr hLiveQuorum)
    ((uniqueOccurrence_iff_end σ.propose).mpr hUnique)
    ⟨e, he, hl, observedAt_iff.mpr hp⟩ p hlive

/-- Liveness 2 in the paper's modal notation. -/
theorem livenessTwo_modal (h : BaseProtocol M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b))
    (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) :=
  occurrence_liveness_iff.mp (livenessTwo h
    (correlated_final_iff_end.mpr hCorrelation) (quorum_final_iff_end.mpr hLiveQuorum))

end ModalDistribution.Examples.ThyAgreement

/-! The `CM` and `VM` namespaces re-export the properties for the two coherence
theories, matching HBB4's module layout. -/

namespace ModalDistribution.Examples.ThyAgreement.CM
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory
variable {S : Signature} {P : Type} [Nonempty P] {M : Model S P} {σ : ProtocolSignature S}

theorem agreement (h : ProtocolCM M σ) {a b v u : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hv : Occurs M (σ.deliver a v)) (hu : Occurs M (σ.deliver b u)) : v = u :=
  ThyAgreement.agreement h.toBaseProtocol hab hv hu
theorem livenessOne (h : ProtocolCM M σ) {l v : S.Value}
    (hLiveQuorum : ∃ Q ∈ (M.learner l).quorums, ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hUnique : UniqueOccurrence M σ.propose)
    (hObserved : ∃ e ∈ M.history.val, (⟪e⟫ ⊨[M] σ.live) ∧ ObservedAt M e (σ.propose v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) : OccursAt M p (σ.deliver l v) :=
  ThyAgreement.livenessOne h.toBaseProtocol hLiveQuorum hUnique hObserved p hLive
theorem livenessTwo (h : ProtocolCM M σ) {a b v : S.Value}
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums, ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) : OccursAt M p (σ.deliver b v) :=
  ThyAgreement.livenessTwo h.toBaseProtocol hCorrelation hLiveQuorum hDelivered p hLive
theorem agreement_modal (h : ProtocolCM M σ) {a b v u : S.Value}
    (hab : ⊨[M] □ᶠ[] (σ.correlation a b)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ (♢ᶠ↓[[]] (σ.deliver b u)) ⇒ᶠ (v ≃ᶠ u) :=
  ThyAgreement.agreement_modal h.toBaseProtocol hab
theorem livenessOne_modal (h : ProtocolCM M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live) (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) :=
  ThyAgreement.livenessOne_modal h.toBaseProtocol hLiveQuorum hUnique
theorem livenessTwo_modal (h : ProtocolCM M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b)) (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) :=
  ThyAgreement.livenessTwo_modal h.toBaseProtocol hCorrelation hLiveQuorum

end ModalDistribution.Examples.ThyAgreement.CM
