import ModalDistribution.Examples.ThyHBB4.WeakSafety
import ModalDistribution.Examples.ThyHBB4.LivenessTwo

/-! Correctness endpoints for the two weaker coherence theories.
The liveness argument is shared; each theory supplies proved delivery legality. -/
namespace ModalDistribution.Examples.ThyHBB4
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

namespace CW
/-- Liveness 1 under comparison-witness coherence. -/
theorem livenessOne (h : ProtocolCW M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  exact ThyHBB4.livenessOne h.toBaseProtocol hLiveQuorum hUnique

/-- Liveness 2 under comparison-witness coherence. -/
theorem livenessTwo (h : ProtocolCW M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b))
    (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) := by
  exact livenessTwo_of_delivery_legal h.toBaseProtocol (delivery_legal h) hCorrelation hLiveQuorum
end CW

namespace SW
/-- Liveness 1 under positive-round switch coherence. -/
theorem livenessOne (h : ProtocolSW M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  exact ThyHBB4.livenessOne h.toBaseProtocol hLiveQuorum hUnique

/-- Switch coherence supplies the comparison witnesses required for agreement. -/
theorem agreement (h : ProtocolSW M σ) {a b v u : S.Value}
    (hab : ∀ p : P, Corr M σ ⟨p, †, M.history.val⟩ a b) :
    ∀ p : P, (⟪(p, †, M.history.val)⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver a v)) →
      (⟪(p, †, M.history.val)⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver b u)) → v = u := by
  exact CW.agreement h.toCW hab

/-- Liveness 2 under positive-round switch coherence. -/
theorem livenessTwo (h : ProtocolSW M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b))
    (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) := by
  exact CW.livenessTwo h.toCW hCorrelation hLiveQuorum
end SW

end ModalDistribution.Examples.ThyHBB4
