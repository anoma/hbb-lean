import ModalDistribution.Core.History

open scoped PreHistory

namespace ModalDistribution

variable {P Event : Type*}

/-- Definition 2.3.11: Elementwise transitivity – elements of elements are also
    elements. -/
def isElementwiseTransitive (H : PreHistory P Event) : Prop :=
  ∀ ⦃H' H'' : History P Event⦄,
    H''.val ≺− H'.val →
    H'.val ≺− H →
    H''.val ≺− H

/-- Lemma 2.3.12(1): Transitivity implies elementwise transitivity. -/
lemma History.isTransitive.elementwise {H : PreHistory P Event}
    (htrans : isTransitive (P := P) (Event := Event) H) :
    isElementwiseTransitive (P := P) (Event := Event) H := by
  intro H' H'' hH'' hH'
  rcases hH'' with ⟨p, e, mem⟩
  have hsubset : H'.val ⊆ H := htrans H'.val hH'
  exact ⟨p, e, hsubset _ mem⟩

/-- Lemma 2.3.12(2): Elementwise transitivity does not imply transitivity. -/
lemma History.elementwise_not_transitive :
  ∃ (P Event : Type) (H : PreHistory P Event),
    isElementwiseTransitive H ∧ ¬ isTransitive H := by
  classical
  let H₀ : PreHistory Bool Unit :=
    PreHistory.mk [((false : Bool), MaybeEvent.none, PreHistory.empty)]
  let H : PreHistory Bool Unit :=
    PreHistory.mk
      [ ((false : Bool), MaybeEvent.none, H₀)
      , ((true : Bool), MaybeEvent.none, PreHistory.empty) ]
  refine ⟨Bool, Unit, H, ?_, ?_⟩
  · intro H' H'' hH'' hH'
    classical
    rcases hH' with ⟨p, e, mem⟩
    have mem_cases :
        (p = (false : Bool) ∧ e = MaybeEvent.none ∧ H'.val = H₀) ∨
        (p = (true : Bool) ∧ e = MaybeEvent.none ∧ H'.val = PreHistory.empty) := by
      simpa [H, PreHistory.mem_mk, List.mem_cons] using mem
    rcases mem_cases with ⟨hp, he, hval⟩ | ⟨hp, he, hval⟩
    · subst hp; subst he
      rcases hH'' with ⟨p', e', mem'⟩
      have mem₀ : p' = (false : Bool) ∧ e' = MaybeEvent.none ∧ H''.val = PreHistory.empty := by
        have := mem'
        simp [H₀, PreHistory.mem_mk, hval, Prod.ext_iff] at this
        exact this
      rcases mem₀ with ⟨hp', he', hval'⟩
      subst hp'
      subst he'
      refine ⟨(true : Bool), MaybeEvent.none, ?_⟩
      simp [H, hval', PreHistory.mem_mk]
    · subst hp; subst he
      rcases hH'' with ⟨p', e', mem'⟩
      have mem_empty : (p', e', H''.val) ∈ PreHistory.empty := by
        simp [hval] at mem'
      have : False := by
        simp [PreHistory.empty, PreHistory.mem_mk] at mem_empty
      cases this
  · intro htrans
    have h_before : H₀ ≺− H := by
      refine ⟨(false : Bool), MaybeEvent.none, ?_⟩
      simp [H, PreHistory.mem_mk]
    have hsubset := htrans H₀ h_before
    have : (false, MaybeEvent.none, PreHistory.empty) ∈ H₀ := by
      simp [H₀, PreHistory.mem_mk]
    have : (false, MaybeEvent.none, PreHistory.empty) ∈ H := hsubset _ this
    simp [H, H₀, PreHistory.mem_mk, List.mem_cons] at this
    cases this

/-- Lemma 2.3.12(3): Histories are elementwise-transitive. -/
lemma History.elementwise (H : History P Event) :
    isElementwiseTransitive (P := P) (Event := Event) H.val :=
  (History.isTransitive.elementwise (P := P) (Event := Event)
    (History.transitive H))

end ModalDistribution
