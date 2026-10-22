import ModalDistribution.Examples.ThyAgreement.CM

namespace ModalDistribution.Examples.ThyAgreement.VM
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory
variable {S : Signature} {P : Type} [Nonempty P] {M : Model S P} {σ : ProtocolSignature S}

theorem agreement (h : ProtocolVM M σ) {a b v u : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hv : Occurs M (σ.deliver a v)) (hu : Occurs M (σ.deliver b u)) : v = u :=
  ThyAgreement.agreement h.toBaseProtocol hab hv hu
theorem livenessOne (h : ProtocolVM M σ) {l v : S.Value}
    (hLiveQuorum : ∃ Q ∈ (M.learner l).quorums, ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hUnique : UniqueOccurrence M σ.propose)
    (hObserved : ∃ e ∈ M.history.val, (⟪e⟫ ⊨[M] σ.live) ∧ ObservedAt M e (σ.propose v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) : OccursAt M p (σ.deliver l v) :=
  ThyAgreement.livenessOne h.toBaseProtocol hLiveQuorum hUnique hObserved p hLive
theorem livenessTwo (h : ProtocolVM M σ) {a b v : S.Value}
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums, ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) : OccursAt M p (σ.deliver b v) :=
  ThyAgreement.livenessTwo h.toBaseProtocol hCorrelation hLiveQuorum hDelivered p hLive
theorem agreement_modal (h : ProtocolVM M σ) {a b v u : S.Value}
    (hab : ⊨[M] □ᶠ[] (σ.correlation a b)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ (♢ᶠ↓[[]] (σ.deliver b u)) ⇒ᶠ (v ≃ᶠ u) :=
  ThyAgreement.agreement_modal h.toBaseProtocol hab
theorem livenessOne_modal (h : ProtocolVM M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live) (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) :=
  ThyAgreement.livenessOne_modal h.toBaseProtocol hLiveQuorum hUnique
theorem livenessTwo_modal (h : ProtocolVM M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b)) (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) :=
  ThyAgreement.livenessTwo_modal h.toBaseProtocol hCorrelation hLiveQuorum

end ModalDistribution.Examples.ThyAgreement.VM
