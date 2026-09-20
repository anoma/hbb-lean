import ModalDistribution.Examples.ThyHBB4.Safety

/-! Implications between the coherence conditions: CM ⇒ SW ⇒ CW.
All three conditions and theory declarations are in `Axioms.lean`. -/

namespace ModalDistribution.Examples.ThyHBB4

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped PreHistory Formula

variable {S : Signature} {P : Type} [Nonempty P]

variable {M : Model S P} {σ : ProtocolSignature S}

theorem ProtocolCM.switchCoherence (h : ProtocolCM M σ) : SwitchCoherence M σ := by
  intro w hw f g b s u c t v n _ hgw _ _ _ _ _ _ a ha
  exact h.causalMonotone hw ha hgw

/-- Quorum intersection at the observing world supplies same-signer children;
SW applied to the later child supplies precisely the CW row inclusion. -/
theorem SwitchCoherence.comparisonWitness (h : BaseProtocol M σ)
    (hsw : SwitchCoherence M σ) : ComparisonWitness M σ := by
  intro w hw E F b s u c t v k hE hF hk huv hbc hEv hFv
  cases k with
  | zero => omega
  | succ n =>
    obtain ⟨Q, hQ, hq⟩ := quorum_exists_iff.mp
      (h.voteSuccBackward (predecessor_possible hw hE) hEv)
    obtain ⟨T, hT, ht⟩ := quorum_exists_iff.mp
      (h.voteSuccBackward (predecessor_possible hw hF) hFv)
    obtain ⟨p, hp, hseq⟩ :=
      (sat_diamond_pair_iff (M := M) (w := w) (l := b) (l' := c)
        (φ := Formula.seq)).mp (h.correlationSeq hw hbc) Q hQ T hT
    obtain ⟨f, hf, hfp, hfv⟩ := hq p hp.1
    obtain ⟨g, hg, hgp, hgv⟩ := ht p hp.2
    have hfw := accessible_trans hw hf hE
    have hgw := accessible_trans hw hg hF
    refine ⟨f, g, hf, hg, hfv, hgv, ?_⟩
    rcases hseq f g hfw hgw hfp hgp with hfg | hgf | heq
    · refine Or.inl ⟨hfg, ?_⟩
      intro a hba
      exact hsw hw hfg hgw (hfp.trans hgp.symm) (by omega) huv hbc hfv hgv a
        (h.correlationTrans hw (h.correlationSymm hw hbc) hba)
    · exact Or.inr ⟨hgf, hsw hw hgf hfw (hgp.trans hfp.symm) (by omega)
        (Ne.symm huv) (h.correlationSymm hw hbc) hgv hfv⟩
    · subst g
      exact False.elim (huv (vote_value_eq hfv hgv))

def ProtocolCM.toSW (h : ProtocolCM M σ) : ProtocolSW M σ :=
  { h.toBaseProtocol with switchCoherence := h.switchCoherence }

def ProtocolSW.toCW (h : ProtocolSW M σ) : ProtocolCW M σ :=
  { h.toBaseProtocol with comparisonWitness := SwitchCoherence.comparisonWitness h.toBaseProtocol h.switchCoherence }

end ModalDistribution.Examples.ThyHBB4
