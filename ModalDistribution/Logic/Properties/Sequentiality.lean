import ModalDistribution.Logic.Semantics
import ModalDistribution.Core.History
import ModalDistribution.Logic.Properties.Modalities

/-!
# Sequentiality lemmas

The results of paper Section 5.1 about the sequentiality predicate `seq`: its
characterisation by linearity of the in-place past (Lemma 5.1.2), its
monotonicity (Lemma 5.1.3, Proposition 5.1.4), and the ordering of events seen
by two quorums (Proposition 5.1.5).
-/

namespace ModalDistribution
namespace Logic

open Set
open History
open PreHistory
open World
open scoped Formula History PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {w w' : World P (Signature.EventType S)}

/-- Paper: Lemma 5.1.2. `w ⊨ seq` exactly when the event-tuples in-place
accessible from `w` are linearly ordered by accessibility. -/
theorem seq_iff_linear_accessible
    : (⟪w⟫ ⊨[M]Formula.seq) ↔
      (∀ {w₁ w₂ : World P (Signature.EventType S)},
        w₁ ≪⁻ w → w₂ ≪⁻ w →
          (w₁ ≪ w₂ ∨ w₂ ≪ w₁ ∨ w₁ = w₂)) :=
  -- Unpack sequentiality (Definition 3.4.9(1)) and `≪⁻` (Definition 3.4.2(4)).
  (Sat.seq M w).trans
    ⟨fun hSeq {_ _} ⟨h₁, hp₁⟩ ⟨h₂, hp₂⟩ => hSeq _ _ h₁ h₂ hp₁ hp₂,
      fun h _ _ h₁ h₂ hp₁ hp₂ => h ⟨h₁, hp₁⟩ ⟨h₂, hp₂⟩⟩

/-- Paper: Lemma 5.1.3. If `w' ≪⁻ w` then everything in-place accessible from
`w'` is in-place accessible from `w`. -/
theorem accessible_subset_of_accessible
    (hW : w.time ⪯ M.history.val)
    (hAcc : w' ≪⁻ w) :
    {t : World P (Signature.EventType S) | t ≪⁻ w'} ⊆
      {t : World P (Signature.EventType S) | t ≪⁻ w} := fun _ ht =>
  -- Transitivity of `≪` (Proposition 3.4.5) and of equality of places.
  ⟨accessible_trans (H := M.history) (hW := hW) (h₂ := ht.1) (h₁ := hAcc.1),
    ht.2.trans hAcc.2⟩

/-- Paper: Proposition 5.1.4(1). If `w' ≪⁻ w` then `w ⊨ seq` implies
`w' ⊨ seq`. -/
theorem seq_monotone_of_subset
    (hW : w.time ⪯ M.history.val)
    (hAcc : w' ≪⁻ w)
    (hSeq : ⟪w⟫ ⊨[M]Formula.seq) :
    ⟪w'⟫ ⊨[M]Formula.seq :=
  -- By Lemma 5.1.2 both sides are linearity statements, and Lemma 5.1.3 nests
  -- the sets that must be linear.
  seq_iff_linear_accessible.2 fun h₁ h₂ =>
    seq_iff_linear_accessible.1 hSeq
      (accessible_subset_of_accessible hW hAcc h₁)
      (accessible_subset_of_accessible hW hAcc h₂)

/-- Paper: Proposition 5.1.4(2). `w ⊨ seq ⇒ ⇓seq`, a restatement of part (1). -/
theorem seq_monotone_all_itp
    (hW : w.time ⪯ M.history.val)
    (hSeq : ⟪w⟫ ⊨[M]Formula.seq) :
    ⟪w⟫ ⊨[M]⇓ᶠ Formula.seq :=
  (Sat.allPast ..).2 fun _ ht hp => seq_monotone_of_subset hW ⟨ht, hp⟩ hSeq

/-- Paper: Proposition 5.1.5(1). If `l` and `l'` quorums intersect at
participants satisfying `ψ`, and an `l`-quorum satisfies `φ` and an
`l'`-quorum satisfies `φ'`, then some participant satisfies all three. -/
theorem two_quorums_exists
    {ls : Signature.Value S}
    {ls' : Signature.Value S}
    {ψ φ φ' : Formula S}
    (hψ : ⟪w⟫ ⊨[M]♢ᶠ[[ls, ls']]ψ)
    (hφ : ⟪w⟫ ⊨[M]□ᶠ[[ls]]φ)
    (hφ' : ⟪w⟫ ⊨[M]□ᶠ[[ls']]φ') :
    ⟪w⟫ ⊨[M] ♢ᶠ[] ((ψ ∧ᶠ φ) ∧ᶠ φ') := by
  obtain ⟨O, hO, hφO⟩ := (sat_box_singleton_exists ..).1 hφ
  obtain ⟨O', hO', hφO'⟩ := (sat_box_singleton_exists ..).1 hφ'
  obtain ⟨q, ⟨hqO, hqO'⟩, hψq⟩ := (sat_diamond_pair_iff ..).1 hψ O hO O' hO'
  exact (Sat.diamondEmpty ..).2
    ⟨q, Sat.and_intro M _ (Sat.and_intro M _ hψq (hφO q hqO)) (hφO' q hqO')⟩

/-- Paper: Proposition 5.1.5(2). At a sequential world, two distinct past
events at the current place occur one after the other. -/
theorem seq_two_quorums_events
    {w : World P (Signature.EventType S)}
    {evt evt' : Signature.EventType S}
    (hSeq : ⟪w⟫ ⊨[M]Formula.seq)
    (hEvt_local : ⟪w⟫ ⊨[M]↓ᶠ (Formula.ofEvent evt))
    (hEvt'_local : ⟪w⟫ ⊨[M]↓ᶠ (Formula.ofEvent evt'))
    (hDistinct : evt ≠ evt') :
    ⟪w⟫ ⊨[M]
      ((↓ᶠ ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt'))) ∨ᶠ
        (↓ᶠ ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))) := by
  obtain ⟨t₁, ht₁, hp₁, hE₁⟩ := (Sat.past ..).1 hEvt_local
  obtain ⟨t₂, ht₂, hp₂, hE₂⟩ := (Sat.past ..).1 hEvt'_local
  -- Sequentiality orders the two event-tuples at the current place.
  rcases (Sat.seq M w).1 hSeq t₁ t₂ ht₁ ht₂ hp₁ hp₂ with h₁₂ | h₂₁ | rfl
  · -- `E` happened before `E'`.
    refine (Sat.or ..).2 (.inr (Sat.past_intro_of_prefix ht₂ hp₂ ?_))
    exact Sat.and_intro M _ hE₂ (Sat.past_intro_of_prefix h₁₂ (hp₁.trans hp₂.symm) hE₁)
  · -- `E'` happened before `E`.
    refine (Sat.or ..).2 (.inl (Sat.past_intro_of_prefix ht₁ hp₁ ?_))
    exact Sat.and_intro M _ hE₁ (Sat.past_intro_of_prefix h₂₁ (hp₂.trans hp₁.symm) hE₂)
  · -- One event-tuple cannot carry two distinct events.
    exact absurd (MaybeEvent.some.inj (hE₁.1.symm.trans hE₂.1)) hDistinct

/-- Paper: Proposition 5.1.5(3). If `l` and `l'` have sequential quorum
intersections, an `l`-quorum saw `E` and an `l'`-quorum saw `E'`, then some
participant saw them in one order or the other. -/
theorem seq_two_quorums_eventually
    {w : World P (Signature.EventType S)}
    {l l' : Signature.Value S}
    {evt evt' : Signature.EventType S}
    (hSeq : ⟪w⟫ ⊨[M]♢ᶠ[[l, l']]Formula.seq)
    (hEvt : ⟪w⟫ ⊨[M]□ᶠ↓[[l]](Formula.ofEvent evt))
    (hEvt' : ⟪w⟫ ⊨[M]□ᶠ↓[[l']](Formula.ofEvent evt'))
    (hDistinct : evt ≠ evt') :
    ⟪w⟫ ⊨[M]
      ((♢ᶠ↓[[]] ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt'))) ∨ᶠ
        (♢ᶠ↓[[]] ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))) := by
  -- Part (1) gives a participant `q` that is sequential and saw both events ...
  obtain ⟨q, hq⟩ := (Sat.diamondEmpty ..).1 (two_quorums_exists hSeq hEvt hEvt')
  simp only [Sat.and] at hq
  obtain ⟨⟨hSeq_q, hE_q⟩, hE'_q⟩ := hq
  -- ... part (2) orders the events at `q`, and a past witness at `q` is a
  -- past witness at any place.
  have toDiamond : ∀ {X : Formula S},
      (⟪⟨q, †, w.time⟩⟫ ⊨[M] ↓ᶠ X) → ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] X := fun h =>
    let ⟨t, ht, _, hX⟩ := (Sat.past ..).1 h
    Sat.diamondPast_nil.2 ⟨t, ht, hX⟩
  exact (Sat.or ..).2
    ((sat_or_cases (seq_two_quorums_events hSeq_q hE_q hE'_q hDistinct)).imp toDiamond toDiamond)

end Logic
end ModalDistribution
