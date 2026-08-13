import ModalDistribution.Core.History

open scoped PreHistory

namespace ModalDistribution
namespace Examples
namespace HistoryStructures

/-- The raw prehistory for minimal history -/
def minimalHistory_val : PreHistory Unit Unit :=
  PreHistory.mk [((), MaybeEvent.none, PreHistory.empty)]

/-- `minimalHistory_val` is transitive. -/
theorem minimalHistory_transitive :
    isTransitive minimalHistory_val := by
  intro h' hbefore
  rcases hbefore with ⟨p, e, hmem⟩
  have h_eq : (p, e, h') = ((), MaybeEvent.none, PreHistory.empty) := by
    simpa [minimalHistory_val, PreHistory.mem_mk]
      using hmem
  cases h_eq
  simp

/-- `minimalHistory_val` is hereditarily transitive. -/
theorem minimalHistory_hered :
    isHereditarilyTransitive minimalHistory_val := by
  classical
  refine
    (isHereditarilyTransitive_unfold
      (P := Unit) (Event := Unit) minimalHistory_val).mpr ?_
  constructor
  · exact minimalHistory_transitive
  · intro h' hbefore
    rcases hbefore with ⟨p, e, hmem⟩
    have h_eq : (p, e, h') = ((), MaybeEvent.none, PreHistory.empty) := by
      simpa [minimalHistory_val, PreHistory.mem_mk]
        using hmem
    cases h_eq
    exact History.hereditarilyTransitive (History.emptyHistory Unit Unit)

/-- A minimal history structure with one participant. -/
def minimalHistory : History Unit Unit :=
  { val := minimalHistory_val
    hered := minimalHistory_hered }

/-- A history that extends `minimalHistory` by adding an extra event-tuple. -/
def extendedHistory_val : PreHistory Unit Unit :=
  PreHistory.mk
    [ ((), MaybeEvent.some (), PreHistory.empty)
    , ((), MaybeEvent.none, PreHistory.empty) ]

/-- `extendedHistory_val` is transitive. -/
theorem extendedHistory_transitive :
    isTransitive extendedHistory_val := by
  intro h' hbefore
  rcases hbefore with ⟨p, e, hmem⟩
  have h_cases :
      (p, e, h') = ((), MaybeEvent.some (), PreHistory.empty) ∨
      (p, e, h') = ((), MaybeEvent.none, PreHistory.empty) := by
    simpa [extendedHistory_val, PreHistory.mem_mk]
      using hmem
  cases h_cases with
  | inl h_eq =>
      cases h_eq
      simp
  | inr h_eq =>
      cases h_eq
      simp

/-- `extendedHistory_val` is hereditarily transitive. -/
theorem extendedHistory_hered :
    isHereditarilyTransitive extendedHistory_val := by
  classical
  refine
    (isHereditarilyTransitive_unfold
      (P := Unit) (Event := Unit) extendedHistory_val).mpr ?_
  constructor
  · exact extendedHistory_transitive
  · intro h' hbefore
    rcases hbefore with ⟨p, e, hmem⟩
    have h_cases :
        (p, e, h') = ((), MaybeEvent.some (), PreHistory.empty) ∨
        (p, e, h') = ((), MaybeEvent.none, PreHistory.empty) := by
      simpa [extendedHistory_val, PreHistory.mem_mk]
        using hmem
    cases h_cases with
    | inl h_eq =>
        cases h_eq
        simpa using History.hereditarilyTransitive (History.emptyHistory Unit Unit)
    | inr h_eq =>
        cases h_eq
        simpa using History.hereditarilyTransitive (History.emptyHistory Unit Unit)

/-- The extended example history. -/
def extendedHistory : History Unit Unit :=
  { val := extendedHistory_val
    hered := extendedHistory_hered }

/-- Transitive subsets need not arise from happens-before predecessors. -/
theorem transitiveSubset_not_implies_happensBeforeEq :
  ∃ (H' H : History Unit Unit),
    H'.val ⊆trn H.val ∧ ¬ H'.val ⪯ H.val := by
  classical
  refine ⟨minimalHistory, extendedHistory, ?_, ?_⟩
  · constructor
    · intro t ht
      have ht' : t = ((), MaybeEvent.none, PreHistory.empty) := by
        simpa [minimalHistory, minimalHistory_val, PreHistory.mem_mk] using ht
      subst ht'
      simp [extendedHistory, extendedHistory_val, PreHistory.mem_mk]
    · exact minimalHistory_hered
  · intro h_le
    have := (PreHistory.happensBeforeEq_iff
      (h1 := minimalHistory_val)
      (h2 := extendedHistory_val)).mp h_le
    cases this with
    | inl hbefore =>
        rcases hbefore with ⟨p, e, hmem⟩
        have h_cases :
            (p = () ∧ e = MaybeEvent.some () ∧ minimalHistory_val = PreHistory.empty) ∨
            (p = () ∧ e = MaybeEvent.none ∧ minimalHistory_val = PreHistory.empty) := by
          simpa [extendedHistory_val, PreHistory.mem_mk, Prod.ext_iff] using hmem
        rcases h_cases with ⟨hp, he, hh⟩ | ⟨hp, he, hh⟩
        · subst hp; subst he
          have h_nonempty :
              ((), MaybeEvent.none, PreHistory.empty) ∈ minimalHistory_val := by
            simp [minimalHistory_val, PreHistory.mem_mk]
          have : False := by
            simp [hh] at h_nonempty
          cases this
        · subst hp; subst he
          have h_nonempty :
              ((), MaybeEvent.none, PreHistory.empty) ∈ minimalHistory_val := by
            simp [minimalHistory_val, PreHistory.mem_mk]
          have : False := by
            simp [hh] at h_nonempty
          cases this
    | inr h_eq =>
        have h_in : ((), MaybeEvent.some (), PreHistory.empty)
            ∈ extendedHistory_val := by
          simp [extendedHistory_val, PreHistory.mem_mk]
        have h_in' : ((), MaybeEvent.some (), PreHistory.empty)
            ∈ minimalHistory_val := by
          simpa [h_eq] using h_in
        have : False := by
          simp [minimalHistory_val, PreHistory.mem_mk] at h_in'
        cases this

end HistoryStructures
end Examples
end ModalDistribution
