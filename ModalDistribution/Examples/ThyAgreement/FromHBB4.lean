import ModalDistribution.Examples.ThyHBB4.CM
import ModalDistribution.Examples.ThyHBB4.VM
import ModalDistribution.Examples.ThyAgreement.Axioms

/-!
# HBB4 implies ThyAgreement

Every model of HBB4-with-CM (resp. HBB4-with-VM) is a model of ThyAgreement-with-CM
(resp. -VM). Two things are transported:

* the vocabulary reading: HBB4's decision rank is the realized depth
  `maxDepth M l`, whereas `ThyAgreement` carries a static budget `depthBound` with
  the axiom `depthBound_dominates`; `σ.toAgreement M` sets
  `depthBound l := maxDepth M l`, for which dominance is reflexivity;
* the correctness properties: `ThyAgreement` *assumes* agreement, Liveness 1 and
  Liveness 2, which HBB4 *proves* (`ThyHBB4.CM.agreement`, …), from its event
  rules together with causal or vote monotonicity. This is why the implication
  is stated for `ProtocolCM` and `ProtocolVM` and not for `BaseProtocol` alone:
  HBB4's base rules without a coherence condition do not yield agreement.

The remaining fields of `ThyAgreement.BaseProtocol` (`thyLive`, the correlation
axioms) are HBB4's own.
-/

namespace ModalDistribution.Examples.ThyAgreement
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]

/-- An HBB4 reading of the vocabulary, read as a `ThyAgreement` one for the model
`M`: the depth budget is the realized depth of `M`. -/
noncomputable def _root_.ModalDistribution.Examples.ThyHBB4.ProtocolSignature.toAgreement
    (σ : ThyHBB4.ProtocolSignature S) (M : Model S P) : ProtocolSignature S where
  liveSymb := σ.liveSymb
  correlationSymb := σ.correlationSymb
  proposeSymb := σ.proposeSymb
  echoSymb := σ.echoSymb
  voteSymb := σ.voteSymb
  deliverSymb := σ.deliverSymb
  depthBound := fun l => ThyHBB4.maxDepth M (Correlated M σ.correlationSymb) l

/-- **HBB4 (CM) ⇒ ThyAgreement (CM).** -/
theorem _root_.ModalDistribution.Examples.ThyHBB4.ProtocolCM.toAgreement
    {M : Model S P} {σ : ThyHBB4.ProtocolSignature S}
    (h : ThyHBB4.ProtocolCM M σ) : ProtocolCM M (σ.toAgreement M) where
  thyLive := h.thyLive
  depthBound_dominates := fun _ => Nat.le_refl _
  correlationSeq := h.correlationSeq
  correlationSymm := h.correlationSymm
  correlationTrans := h.correlationTrans
  correlationPast := h.correlationPast
  agreement := fun hab hv hu => ThyHBB4.CM.agreement h hab hv hu
  livenessOne := fun hQ hU hO p hp => ThyHBB4.CM.livenessOne h hQ hU hO p hp
  livenessTwo := fun hC hQ hD p hp => ThyHBB4.CM.livenessTwo h hC hQ hD p hp
  causalMonotone := h.causalMonotone

/-- **HBB4 (VM) ⇒ ThyAgreement (VM).** -/
theorem _root_.ModalDistribution.Examples.ThyHBB4.ProtocolVM.toAgreement
    {M : Model S P} {σ : ThyHBB4.ProtocolSignature S}
    (h : ThyHBB4.ProtocolVM M σ) : ProtocolVM M (σ.toAgreement M) where
  thyLive := h.thyLive
  depthBound_dominates := fun _ => Nat.le_refl _
  correlationSeq := h.correlationSeq
  correlationSymm := h.correlationSymm
  correlationTrans := h.correlationTrans
  correlationPast := h.correlationPast
  agreement := fun hab hv hu => ThyHBB4.VM.agreement h hab hv hu
  livenessOne := fun hQ hU hO p hp => ThyHBB4.VM.livenessOne h hQ hU hO p hp
  livenessTwo := fun hC hQ hD p hp => ThyHBB4.VM.livenessTwo h hC hQ hD p hp
  voteMonotone := h.voteMonotone

end ModalDistribution.Examples.ThyAgreement
