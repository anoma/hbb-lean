import ModalDistribution.Logic.Semantics
import ModalDistribution.Core.History
import ModalDistribution.Logic.Properties.Modalities

/-!
# Sequentiality lemmas

This module packages the lemmas and propositions whose primary focus is the
sequentiality modality `Formula.seq`: the Section 5.1 characterisation and
monotonicity results, and the quorum-intersection witnesses of
Proposition 5.1.5.
-/

namespace ModalDistribution
namespace Logic

open Set
open History
open PreHistory
open World
open scoped Formula History PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type}
variable {w w' : World P (Signature.EventType S)}

variable [Nonempty P]
variable {M : Model S P}

/-- Paper: Lemma 5.1.2. Sequentiality coincides with linear ordering of the in-place slice. -/
theorem seq_iff_linear_accessible
    : (⟪w⟫ ⊨[M]Formula.seq) ↔
      (∀ {w₁ w₂ : World P (Signature.EventType S)},
        w₁ ≪⁻ w → w₂ ≪⁻ w →
          (w₁ ≪ w₂ ∨ w₂ ≪ w₁ ∨ w₁ = w₂)) := by
  classical
  constructor
  · intro hSeq
    have hSeq' : isSequential (P := P) (Event := Signature.EventType S)
        w.place w.time :=
      (Sat.seq (M := M) (w := w)).1 hSeq
    intro w₁ w₂ hw₁ hw₂
    have hw₁_mem : w₁ ∈ w.time := by
      simpa [World.accessible] using hw₁.1
    have hw₂_mem : w₂ ∈ w.time := by
      simpa [World.accessible] using hw₂.1
    have hw₁_place : World.place w₁ = w.place := hw₁.2
    have hw₂_place : World.place w₂ = w.place := hw₂.2
    exact hSeq' w₁ w₂ hw₁_mem hw₂_mem hw₁_place hw₂_place
  · intro h
    have hSeq :
        isSequential (P := P) (Event := Signature.EventType S)
          w.place w.time := by
      intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
      have ht₁_access : t₁ ≪⁻ w :=
        ⟨by simpa [World.accessible] using ht₁, hp₁⟩
      have ht₂_access : t₂ ≪⁻ w :=
        ⟨by simpa [World.accessible] using ht₂, hp₂⟩
      exact h (w₁ := t₁) (w₂ := t₂) ht₁_access ht₂_access
    exact (Sat.seq (M := M) (w := w)).2 hSeq

/-- Paper: Lemma 5.1.3. Accessible predecessors preserve in-place accessibility slices. -/
theorem accessible_subset_of_accessible
    (hW : w.time ⪯ M.history.val)
    (hAcc : w' ≪⁻ w) :
    {t : World P (Signature.EventType S) | t ≪⁻ w'} ⊆
      {t : World P (Signature.EventType S) | t ≪⁻ w} := fun _ ht =>
  ⟨accessible_trans (H := M.history) (hW := hW) (h₂ := ht.1) (h₁ := hAcc.1),
    ht.2.trans hAcc.2⟩

/-- Paper: Proposition 5.1.4(1). Sequentiality persists along same-place accessibility. -/
theorem seq_monotone_of_subset
    (hW : w.time ⪯ M.history.val)
    (hAcc : w' ≪⁻ w)
    (hSeq : ⟪w⟫ ⊨[M]Formula.seq) :
    ⟪w'⟫ ⊨[M]Formula.seq := by
  classical
  -- Lemma 5.1.2 reduces sequentiality to linearity of the in-place cone,
  -- and Lemma 5.1.3 nests the cones.
  refine (seq_iff_linear_accessible (M := M) (w := w')).2 ?_
  intro w₁ w₂ h₁ h₂
  exact
    (seq_iff_linear_accessible (M := M) (w := w)).1 hSeq
      (accessible_subset_of_accessible (M := M) (hW := hW) (hAcc := hAcc) h₁)
      (accessible_subset_of_accessible (M := M) (hW := hW) (hAcc := hAcc) h₂)

/-- Paper: Proposition 5.1.4(2). Sequentiality implies `⇓ᶠ`-sequentiality.
This restates part 1 under `⇓`. -/
theorem seq_monotone_allItp
    (hW : w.time ⪯ M.history.val)
    (hSeq : ⟪w⟫ ⊨[M]Formula.seq) :
    ⟪w⟫ ⊨[M]⇓ᶠ Formula.seq := by
  classical
  refine (Sat.allPast (M := M) (w := w) (φ := Formula.seq)).2 ?_
  intro t ht hp
  exact
    seq_monotone_of_subset (M := M) (hW := hW)
      (hAcc := ⟨by simpa [World.accessible] using ht, hp⟩)
      (hSeq := hSeq)

/-- Paper: Proposition 5.1.5(1). Quorum intersections furnish a joint witness. -/
theorem two_quorums_exists
    {ls : Signature.Value S}
    {ls' : Signature.Value S}
    {ψ φ φ' : Formula S}
    (hψ : ⟪w⟫ ⊨[M]♢ᶠ[[ls, ls']]ψ)
    (hφ : ⟪w⟫ ⊨[M]□ᶠ[[ls]]φ)
    (hφ' : ⟪w⟫ ⊨[M]□ᶠ[[ls']]φ') :
    ⟪w⟫ ⊨[M] ♢ᶠ[] ((ψ ∧ᶠ φ) ∧ᶠ φ') := by
  classical
  obtain ⟨O, hO, hO_all⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := w) (l := ls) (φ := φ)).1 hφ
  obtain ⟨O', hO', hO'_all⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := w) (l := ls') (φ := φ')).1 hφ'
  obtain ⟨q, hqMem, hqψ⟩ :=
    (sat_diamond_pair_iff (M := M)
      (w := w) (l := ls) (l' := ls') (φ := ψ)).1 hψ
      O hO O' hO'
  have hqφ : ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ :=
    hO_all q (Set.mem_of_mem_inter_left hqMem)
  have hqφ' : ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ' :=
    hO'_all q (Set.mem_of_mem_inter_right hqMem)
  have hψφ : ⟪⟨q, †, w.time⟩⟫ ⊨[M] (ψ ∧ᶠ φ) := by
    have :=
      (Sat.and (M := M) (w := ⟨q, †, w.time⟩)
        (φ := ψ) (ψ := φ))
    exact this.2 ⟨hqψ, hqφ⟩
  have hConj :
      ⟪⟨q, †, w.time⟩⟫ ⊨[M]
        ((ψ ∧ᶠ φ) ∧ᶠ φ') := by
    have :=
      (Sat.and (M := M) (w := ⟨q, †, w.time⟩)
        (φ := (ψ ∧ᶠ φ)) (ψ := φ'))
    exact this.2 ⟨hψφ, hqφ'⟩
  have hWitness : ∃ r, ⟪⟨r, †, w.time⟩⟫ ⊨[M]
      ((ψ ∧ᶠ φ) ∧ᶠ φ') := ⟨q, hConj⟩
  exact
    sat_diamondEmpty_of_local (M := M)
      (w := w) (φ := ((ψ ∧ᶠ φ) ∧ᶠ φ')) hWitness

variable {H H' : History P (Signature.EventType S)}
variable {p : P}
variable {w w₁ w₂ : World P (Signature.EventType S)}
variable {w' : World P (Signature.EventType S)}
variable {t t' t₁ t₂ : World P (Signature.EventType S)}
variable {h' : PreHistory P (Signature.EventType S)}
variable {l l' : Signature.Value S}
variable {evt evt' : Signature.EventType S}
variable {φ ψ φ' : Formula S}

/-- Sequentiality depends only on the place and timeline of the current world. -/
theorem seq_localView_of_seq
    (hSeq : ⟪w⟫ ⊨[M]Formula.seq)
    (hPlace : w'.place = w.place)
    (hTime : w'.time = w.time) :
    ⟪w'⟫ ⊨[M]Formula.seq := by
  classical
  rcases w with ⟨p, e, τ⟩
  rcases w' with ⟨p', e', τ'⟩
  dsimp [World.place, World.time] at hPlace hTime
  subst hPlace
  subst hTime
  simpa [World.place, World.time, Sat] using hSeq

/-- Satisfaction of the empty past diamond depends only on the underlying timeline,
not the distinguished participant. -/
theorem sat_diamondPast_empty_participant_iff
    {w₁ w₂ : World P (Signature.EventType S)}
    (hTime : w₁.time = w₂.time) (φ : Formula S) :
    (⟪w₁⟫ ⊨[M] ♢ᶠ↓[[]] φ) ↔ (⟪w₂⟫ ⊨[M] ♢ᶠ↓[[]] φ) := by
  classical
  rcases w₁ with ⟨p₁, evt₁, H₁⟩
  rcases w₂ with ⟨p₂, evt₂, H₂⟩
  have hTime' : H₁ = H₂ := by simpa [World.time] using hTime
  constructor
  · intro h
    obtain ⟨p, hp⟩ :=
      (Sat.diamond_nil (M := M)
        (w := ⟨p₁, evt₁, H₁⟩)
        (φ := ↓ᶠ φ)).1
        (by simpa [Formula.diamondPast])
    have hp₁ : ⟪⟨p, †, H₂⟩⟫ ⊨[M] ↓ᶠ φ := by
      simpa [World.time, hTime'] using hp
    exact
      (Sat.diamond_nil (M := M)
        (w := ⟨p₂, evt₂, H₂⟩)
        (φ := ↓ᶠ φ)).2 ⟨p, hp₁⟩
  · intro h
    obtain ⟨p, hp⟩ :=
      (Sat.diamond_nil (M := M)
        (w := ⟨p₂, evt₂, H₂⟩)
        (φ := ↓ᶠ φ)).1
        (by simpa [Formula.diamondPast, hTime'])
    have hp₂ : ⟪⟨p, †, H₁⟩⟫ ⊨[M] ↓ᶠ φ := by
      simpa [World.time, hTime'] using hp
    exact
      (Sat.diamond_nil (M := M)
        (w := ⟨p₁, evt₁, H₁⟩)
        (φ := ↓ᶠ φ)).2 ⟨p, hp₂⟩

/-- Paper: Proposition 5.1.5(2). Specialized to local witnesses: sequential world with two distinct local events
implies temporal ordering. -/
theorem seq_two_quorums_events
    {w : World P (Signature.EventType S)}
    {evt evt' : Signature.EventType S}
    (hSeq : ⟪w⟫ ⊨[M]Formula.seq)
    (hEvt_local : ⟪w⟫ ⊨[M]↓ᶠ (Formula.ofEvent evt))
    (hEvt'_local : ⟪w⟫ ⊨[M]↓ᶠ (Formula.ofEvent evt'))
    (hDistinct : evt ≠ evt') :
    ⟪w⟫ ⊨[M]
      ((♢ᶠ↓[[]] ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt'))) ∨ᶠ
        (♢ᶠ↓[[]] ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))) := by
  classical
  have hSeqTime :
      isSequential (P := P) (Event := Signature.EventType S)
        w.place w.time :=
    (Sat.seq (M := M) (w := w)).1 hSeq
  obtain ⟨t₁, ht₁_mem, ht₁_place, ht₁_event⟩ :=
    (Sat.past (M := M) (w := w) (φ := Formula.ofEvent evt)).1 hEvt_local
  obtain ⟨t₂, ht₂_mem, ht₂_place, ht₂_event⟩ :=
    (Sat.past (M := M) (w := w) (φ := Formula.ofEvent evt')).1 hEvt'_local
  have hp₁ : t₁.place = w.place := ht₁_place
  have hp₂ : t₂.place = w.place := ht₂_place
  have hOrder :=
    hSeqTime t₁ t₂ ht₁_mem ht₂_mem hp₁ hp₂
  obtain ⟨hEvt₁_eq, hEvt₁_mem⟩ :=
    (Sat.ofEvent (M := M) (w := t₁) (E := evt)).1 ht₁_event
  obtain ⟨hEvt₂_eq, hEvt₂_mem⟩ :=
    (Sat.ofEvent (M := M) (w := t₂) (E := evt')).1 ht₂_event
  have hEvt₁_place : t₁.event = MaybeEvent.some evt := hEvt₁_eq
  have hEvt₂_place : t₂.event = MaybeEvent.some evt' := hEvt₂_eq
  have hp_eq : t₁.place = t₂.place := by
    calc
      t₁.place = w.place := hp₁
      _ = t₂.place := hp₂.symm
  cases hOrder with
  | inl hIn =>
      have ht₁_in_t₂ : t₁ ∈ t₂.time := by
        simpa [World.accessible] using hIn
      have hDown_evt :
          ⟪t₂⟫ ⊨[M] ↓ᶠ (Formula.ofEvent evt) :=
        Sat.past_intro_of_prefix (M := M)
          (w := t₂) (t := t₁)
          (ht := ht₁_in_t₂)
          (hp := hp_eq)
          (hφ := ht₁_event)
      have hConj :
          ⟪t₂⟫ ⊨[M]
            ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)) :=
        (Sat.and (M := M) (w := t₂)
          (φ := Formula.ofEvent evt') (ψ := ↓ᶠ (Formula.ofEvent evt))).2
          ⟨ht₂_event, hDown_evt⟩
      have hPastWitness :
          ⟪⟨w.place, †, w.time⟩⟫ ⊨[M]
            ↓ᶠ ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)) :=
        (Sat.past (M := M)
          (w := ⟨w.place, †, w.time⟩)
          (φ := (Formula.ofEvent evt' ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))).2
          ⟨t₂, by simpa using ht₂_mem,
            by simpa [hp₂], hConj⟩
      have hDiamond' :
          ⟪w⟫ ⊨[M]
            ♢ᶠ↓[[]]
              ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)) :=
        (Sat.diamond_nil (M := M)
          (w := w)
          (φ := ↓ᶠ ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))).2
          ⟨w.place, hPastWitness⟩
      exact
        sat_or_of_right (M := M) (w := w)
          (φ := ♢ᶠ↓[[]]
                    ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')))
          (ψ := ♢ᶠ↓[[]]
                    ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))
          hDiamond'
  | inr hInOrEq =>
      cases hInOrEq with
      | inl hIn =>
          have ht₂_in_t₁ : t₂ ∈ t₁.time := by
            simpa [World.accessible] using hIn
          have hDown_evt' :
              ⟪t₁⟫ ⊨[M] ↓ᶠ (Formula.ofEvent evt') :=
            Sat.past_intro_of_prefix (M := M)
              (w := t₁) (t := t₂)
              (ht := ht₂_in_t₁)
              (hp := hp_eq.symm)
              (hφ := ht₂_event)
          have hConj :
              ⟪t₁⟫ ⊨[M]
                ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')) :=
            (Sat.and (M := M) (w := t₁)
              (φ := Formula.ofEvent evt) (ψ := ↓ᶠ (Formula.ofEvent evt'))).2
              ⟨ht₁_event, hDown_evt'⟩
          have hPastWitness :
              ⟪⟨w.place, †, w.time⟩⟫ ⊨[M]
                ↓ᶠ ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')) :=
            (Sat.past (M := M)
              (w := ⟨w.place, †, w.time⟩)
              (φ := (Formula.ofEvent evt ∧ᶠ ↓ᶠ (Formula.ofEvent evt')))).2
              ⟨t₁, by simpa using ht₁_mem,
                by simpa [hp₁], hConj⟩
          have hDiamond' :
              ⟪w⟫ ⊨[M]
                ♢ᶠ↓[[]]
                  ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')) :=
            (Sat.diamond_nil (M := M)
              (w := w)
              (φ := ↓ᶠ ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')))).2
              ⟨w.place, hPastWitness⟩
          exact
            sat_or_of_left (M := M) (w := w)
              (φ := ♢ᶠ↓[[]]
                        ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')))
              (ψ := ♢ᶠ↓[[]]
                        ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))
              hDiamond'
      | inr hEq =>
          cases hEq
          have hMaybe : MaybeEvent.some evt = MaybeEvent.some evt' :=
            (Eq.trans hEvt₂_place.symm hEvt₁_place).symm
          have hEqual : evt = evt' := MaybeEvent.some.inj hMaybe
          exact (hDistinct hEqual).elim

/-- Paper: Proposition 5.1.5(3). Sequential eventual ordering: distinct events from two quorums are temporally ordered. -/
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
  classical
  have hWitness :=
    two_quorums_exists (M := M)
      (w := w)
      (ls := l) (ls' := l')
      (ψ := Formula.seq)
      (φ := ↓ᶠ (Formula.ofEvent evt))
      (φ' := ↓ᶠ (Formula.ofEvent evt'))
      hSeq hEvt hEvt'
  obtain ⟨q, hLocal⟩ :=
    (Sat.diamond_nil (M := M)
      (w := w)
      (φ :=
        ((Formula.seq ∧ᶠ ↓ᶠ (Formula.ofEvent evt)) ∧ᶠ
          ↓ᶠ (Formula.ofEvent evt')))).1
      (by simpa [Formula.diamondEmpty] using hWitness)
  simp only [Sat.and] at hLocal
  obtain ⟨⟨hSeq_local, hEvt_local⟩, hEvt'_local⟩ := hLocal
  set w_q : World P (Signature.EventType S) :=
    ⟨q, w.event, w.time⟩
  have hSeq_q : ⟪w_q⟫ ⊨[M] Formula.seq :=
    seq_localView_of_seq
      (w := ⟨q, †, w.time⟩)
      (w' := w_q)
      (M := M)
      (hSeq := hSeq_local)
      (hPlace := rfl)
      (hTime := rfl)
  have hEvt_q : ⟪w_q⟫ ⊨[M] ↓ᶠ (Formula.ofEvent evt) := by
    obtain ⟨t, ht_mem, ht_place, ht_evt⟩ :=
      (Sat.past (M := M)
        (w := ⟨q, †, w.time⟩)
        (φ := Formula.ofEvent evt)).1 hEvt_local
    exact
      (Sat.past (M := M)
        (w := w_q)
        (φ := Formula.ofEvent evt)).2
        ⟨t, by simpa [World.time] using ht_mem,
          by simpa [World.place] using ht_place, ht_evt⟩
  have hEvt'_q : ⟪w_q⟫ ⊨[M] ↓ᶠ (Formula.ofEvent evt') := by
    obtain ⟨t, ht_mem, ht_place, ht_evt⟩ :=
      (Sat.past (M := M)
        (w := ⟨q, †, w.time⟩)
        (φ := Formula.ofEvent evt')).1 hEvt'_local
    exact
      (Sat.past (M := M)
        (w := w_q)
        (φ := Formula.ofEvent evt')).2
        ⟨t, by simpa [World.time] using ht_mem,
          by simpa [World.place] using ht_place, ht_evt⟩
  have hDisj_q :=
    seq_two_quorums_events (M := M) (w := w_q)
      (hSeq := hSeq_q)
      (hEvt_local := hEvt_q)
      (hEvt'_local := hEvt'_q)
      (hDistinct := hDistinct)
  set φ₁ :=
      ♢ᶠ↓[[]]
        ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt'))
    with hφ₁
  set φ₂ :=
      ♢ᶠ↓[[]]
        ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt))
    with hφ₂
  have hCases :=
    sat_or_cases (M := M) (w := w_q)
      (φ := φ₁) (ψ := φ₂) hDisj_q
  cases hCases with
  | inl hφ₁_q =>
      have hφ₁_w : ⟪w⟫ ⊨[M] φ₁ := by
        have :=
          (sat_diamondPast_empty_participant_iff
            (M := M)
            (w₁ := w_q)
            (w₂ := w)
            (hTime := rfl)
            (φ :=
              (Formula.ofEvent evt ∧ᶠ ↓ᶠ (Formula.ofEvent evt')))).1 hφ₁_q
        simpa [hφ₁]
      exact sat_or_of_left (M := M) (w := w)
        (φ := φ₁) (ψ := φ₂) hφ₁_w
  | inr hφ₂_q =>
      have hφ₂_w : ⟪w⟫ ⊨[M] φ₂ := by
        have :=
          (sat_diamondPast_empty_participant_iff
            (M := M)
            (w₁ := w_q)
            (w₂ := w)
            (hTime := rfl)
            (φ :=
              (Formula.ofEvent evt' ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))).1 hφ₂_q
        simpa [hφ₂]
      exact sat_or_of_right (M := M) (w := w)
        (φ := φ₁) (ψ := φ₂) hφ₂_w

end Logic
end ModalDistribution
