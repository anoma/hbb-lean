import ModalDistribution.Examples.ThyHBB4.Axioms

namespace ModalDistribution.Examples.ThyHBB4

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}
variable {w : World P S.EventType} {l s v : S.Value} {n : Nat}

theorem someVote_iff :
    (⟪w⟫ ⊨[M] σ.someVote l v n) ↔ ∃ s, (⟪w⟫ ⊨[M] σ.vote l s v n) := by
  exact Sat.exists_iff (M := M) w (fun s => σ.vote l s v n)

/-- Forgetting a fixed source is valid; the converse is not assumed. -/
theorem fixedCertificate_to_certificate
    (h : ⟪w⟫ ⊨[M] σ.fixedCertificate l s v n) :
    ⟪w⟫ ⊨[M] σ.certificate l v n := by
  obtain ⟨Q, hQ, hall⟩ :=
    (sat_box_singleton_exists M w l (↓ᶠ (σ.vote l s v n))).1 h
  apply (sat_box_singleton_exists M w l (↓ᶠ (σ.someVote l v n))).2
  refine ⟨Q, hQ, ?_⟩
  intro p hp
  obtain ⟨u, hu, hplace, hvote⟩ := hall p hp
  exact ⟨u, hu, hplace, someVote_iff.mpr ⟨s, hvote⟩⟩

/-- A constant correlation row has depth exactly one, in any finite model. -/
theorem maxDepth_eq_one_of_constant
    {R : World P S.EventType → S.Value → S.Value → Prop} {a : S.Value}
    (hconstant : ∀ w u, correlationRow R a w = correlationRow R a u) :
    maxDepth M R a = 1 := by
  have hpos := maxDepth_pos M R a
  have hle : maxDepth M R a ≤ 1 := by
    by_cases hn : maxDepth M R a ≤ 1
    · exact hn
    apply False.elim
    have htwo : 1 < maxDepth M R a := by omega
    obtain ⟨ws, _, _, hrows⟩ := maxDepth_attained M R a
    exact hrows ⟨0, by omega⟩ ⟨1, htwo⟩ (by show 0 < 1; omega)
      (hconstant _ _)
  omega

end ModalDistribution.Examples.ThyHBB4
