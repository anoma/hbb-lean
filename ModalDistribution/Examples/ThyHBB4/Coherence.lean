import ModalDistribution.Examples.ThyHBB4.Safety

/-! The positive-round switch and comparison-witness conditions of Definitions
2.1 and 2.2. Witnesses preserve each parent's target, source and value and belong
 to that parent's causal past. -/

namespace ModalDistribution.Examples.ThyHBB4

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped PreHistory Formula

variable {S : Signature} {P : Type} [Nonempty P]

/-- Only the later event of a positive-round, same-signer switch is constrained. -/
def SwitchCoherence (M : Model S P) (σ : ProtocolSignature S) : Prop :=
  ∀ {w}, w.time ⪯ M.history.val → ∀ {f g : World P S.EventType}
    {b s u c t v : S.Value} {n : Nat},
    f ≪ g → g ≪ w → f.place = g.place → 1 ≤ n → u ≠ v →
    Corr M σ w b c →
    (⟪f⟫ ⊨[M] σ.vote b s u n) → (⟪g⟫ ⊨[M] σ.vote c t v n) →
    ∀ a, Corr M σ w c a → Corr M σ g c a

/-- The two predecessor votes need only be strictly comparable; their signers
need not coincide. Each predecessor lies in its own parent's past. -/
def ComparisonWitness (M : Model S P) (σ : ProtocolSignature S) : Prop :=
  ∀ {w}, w.time ⪯ M.history.val → ∀ {E F : World P S.EventType}
    {b s u c t v : S.Value} {k : Nat},
    E ≪ w → F ≪ w → 2 ≤ k → u ≠ v → Corr M σ w b c →
    (⟪E⟫ ⊨[M] σ.vote b s u k) → (⟪F⟫ ⊨[M] σ.vote c t v k) →
    ∃ f g, f ≪ E ∧ g ≪ F ∧
      (⟪f⟫ ⊨[M] σ.vote b s u (k - 1)) ∧
      (⟪g⟫ ⊨[M] σ.vote c t v (k - 1)) ∧
      ((f ≪ g ∧ ∀ a, Corr M σ w b a → Corr M σ g c a) ∨
       (g ≪ f ∧ ∀ a, Corr M σ w b a → Corr M σ f b a))

structure ProtocolSW (M : Model S P) (σ : ProtocolSignature S)
    : Prop extends BaseProtocol M σ where
  switchCoherence : SwitchCoherence M σ

structure ProtocolCW (M : Model S P) (σ : ProtocolSignature S)
    : Prop extends BaseProtocol M σ where
  comparisonWitness : ComparisonWitness M σ

variable {M : Model S P} {σ : ProtocolSignature S}

theorem Protocol.switchCoherence (h : Protocol M σ) : SwitchCoherence M σ := by
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

def Protocol.toSW (h : Protocol M σ) : ProtocolSW M σ :=
  { h.toBaseProtocol with switchCoherence := h.switchCoherence }

def ProtocolSW.toCW (h : ProtocolSW M σ) : ProtocolCW M σ :=
  { h.toBaseProtocol with comparisonWitness := SwitchCoherence.comparisonWitness h.toBaseProtocol h.switchCoherence }

end ModalDistribution.Examples.ThyHBB4
