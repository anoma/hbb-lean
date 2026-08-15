import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB1.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History

/-!
# ThyHBB1 Safety and Liveness Helper Lemmas

This file contains intermediate lemmas supporting the safety and liveness properties of the
ThyHBB1 broadcast protocol. These lemmas are extracted from the main ThyHBB1 file to improve
modularity and maintainability.

The lemmas are organized into several categories:

- **Monotonicity lemmas**: Properties about how formulas behave under history restriction
  - `uniquePropose_monotone`: Uniqueness of proposals is preserved in smaller histories
  - `safe_seq_guard_monotone`: Sequential guard monotonicity
  - `safe_axiom_body_monotone`: Safety axiom body monotonicity
  - `safeFormula_monotone_subset`: Safety persists when restricting to smaller histories
  - `safeFormula_allPast`: Safety implies it always held in the past

- **Quorum and liveness lemmas**: Lifting properties through quorums
  - `boxPast_of_eventual_quorum`: Quorum knowledge with global implication lifts to future quorum
  - `boxPast_live_of_eventual_quorum`: Previous result under ThyLive assumption
  - `live_eventually_consequent`: Composing eventual consequences at end of time

- **Modality equivalences**:
  - `box_sometime_iff_boxPast`: Equivalence between box-sometime and boxPast modalities

These lemmas serve as building blocks for the main agreement and liveness theorems.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB1

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section Results

variable {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {w w' : World P (Signature.EventType S)}

/-/ Deliveries force vote quorums at end of time (`Deliver?`). -/

variable {w w' : World P (Signature.EventType S)}

/-- Monotonicity of the at-most-one proposal condition. -/
theorem uniquePropose_monotone
    (hSubset : w'.time ⊆trn w.time)
    (hUnique :
      ⟪w⟫ ⊨[M]∃≤ᶠ1 v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    ⟪w'⟫ ⊨[M]
      ∃≤ᶠ1 v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) := by
  classical
  dsimp [Formula.existsAtMostOne] at hUnique ⊢
  have hSubset_subset : w'.time ⊆ w.time :=
    History.transitiveSubset_subset
      (P := P) (Event := Signature.EventType S) hSubset
  refine Sat.forall_intro (M := M) (w := w')
      (body := fun value =>
        ∀ᶠ fun altValue =>
          (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [altValue]⟩)) ⇒ᶠ
            (value ≃ᶠ altValue)) ?_
  intro v
  have hUnique_v :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value =>
        ∀ᶠ fun altValue =>
          (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [value]⟩)) ⇒ᶠ
          (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [altValue]⟩)) ⇒ᶠ
            (value ≃ᶠ altValue))
      (v := v) hUnique
  refine Sat.forall_intro (M := M) (w := w')
      (body := fun altValue =>
        (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v]⟩)) ⇒ᶠ
        (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [altValue]⟩)) ⇒ᶠ
          (v ≃ᶠ altValue)) ?_
  intro v'
  have hUnique_vv :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun altValue =>
        (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v]⟩)) ⇒ᶠ
        (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [altValue]⟩)) ⇒ᶠ
          (v ≃ᶠ altValue))
      (v := v') hUnique_v
  refine Sat.imp_intro (M := M) (w := w')
      (φ := ♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v]⟩))
      (ψ := (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v']⟩)) ⇒ᶠ
        (v ≃ᶠ v')) ?_
  intro hDiamondValue
  have hDiamondValueW :
      ⟪w⟫ ⊨[M]
        ♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v]⟩) := by
    have :=
      sat_diamondPast_nil_event_subset (M := M)
        (w := w) (w' := w') (symb := proposeSymb) (args := [v])
        hSubset
        (by simpa [Formula.ofEvent] using hDiamondValue)
    simpa [Formula.ofEvent] using this
  refine Sat.imp_intro (M := M) (w := w')
      (φ := ♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v']⟩))
      (ψ := v ≃ᶠ v') ?_
  intro hDiamondAlt
  have hDiamondAltW :
      ⟪w⟫ ⊨[M]
        ♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v']⟩) := by
    have :=
      sat_diamondPast_nil_event_subset (M := M)
        (w := w) (w' := w') (symb := proposeSymb) (args := [v'])
        hSubset
        (by simpa [Formula.ofEvent] using hDiamondAlt)
    simpa [Formula.ofEvent] using this
  have hEq :=
    Sat.imp_elim (M := M) (w := w)
      (φ := ♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v]⟩))
      (ψ := (♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v']⟩)) ⇒ᶠ
        (v ≃ᶠ v'))
      hUnique_vv hDiamondValueW
  have hEq' :=
    Sat.imp_elim (M := M) (w := w)
      (φ := ♢ᶠ↓[[]] (Formula.ofEvent ⟨proposeSymb, [v']⟩))
      (ψ := v ≃ᶠ v')
      hEq hDiamondAltW
  have hEq'' : v = v' :=
    (Sat.eq (M := M) (w := w) (v₁ := v) (v₂ := v')).1 hEq'
  exact
    (Sat.eq (M := M) (w := w') (v₁ := v) (v₂ := v')).2 hEq''

/-- Monotonicity of the sequential quorum guard in the `Safe` axiom. -/
theorem safe_seq_guard_monotone
    (l : Signature.Value S)
    (hSubset : w'.time ⊆trn w.time)
    (hPlace : w'.place = w.place)
    (hSeqGuard : ⟪w⟫ ⊨[M]∀ᶠ (fun l' => ♢ᶠ[[l, l']]Formula.seq)) :
    ⟪w'⟫ ⊨[M]∀ᶠ (fun l' => ♢ᶠ[[l, l']] Formula.seq) := by
  classical
  have hSubset_subset : w'.time ⊆ w.time :=
    History.transitiveSubset_subset
      (P := P) (Event := Signature.EventType S) hSubset
  have hPlace' : w.place = w'.place := hPlace.symm
  refine Sat.forall_intro (M := M) (w := w')
      (body := fun l' => ♢ᶠ[[l, l']] Formula.seq) ?_
  intro v
  have hGuard_v :
      ⟪w⟫ ⊨[M] ♢ᶠ[[l, v]] Formula.seq :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun l' => ♢ᶠ[[l, l']] Formula.seq)
      (v := v) hSeqGuard
  have hGuard_data :=
    (sat_diamond_pair_iff (M := M)
      (w := w) (l := l) (l' := v) (φ := Formula.seq)).1 hGuard_v
  refine (sat_diamond_pair_iff (M := M)
      (w := w') (l := l) (l' := v) (φ := Formula.seq)).2 ?_
  intro O hO O' hO'
  obtain ⟨q, hqInter, hSeq_local⟩ := hGuard_data O hO O' hO'
  have hSeq_global :
      isSequential (P := P) (Event := Signature.EventType S) q w.time :=
    (Sat.seq (M := M) (w := ⟨q, †, w.time⟩)).1 hSeq_local
  have hSeq_restrict :
      isSequential (P := P) (Event := Signature.EventType S) q w'.time := by
    intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
    exact hSeq_global t₁ t₂ (hSubset_subset _ ht₁) (hSubset_subset _ ht₂) hp₁ hp₂
  have hSeq_local' :
      ⟪⟨q, †, w'.time⟩⟫ ⊨[M] Formula.seq :=
    (Sat.seq (M := M) (w := ⟨q, †, w'.time⟩)).2 hSeq_restrict
  have _ := hPlace'
  exact ⟨q, hqInter, hSeq_local'⟩

/-- Monotonicity of the `Safe` axiom body with respect to transitive subsets. -/
theorem safe_axiom_body_monotone
    (l : Signature.Value S)
    (hSubset : w'.time ⊆trn w.time)
    (hPlace : w'.place = w.place)
    (hBody : ⟪w⟫ ⊨[M]safeFormula proposeSymb l) :
    ⟪w'⟫ ⊨[M]safeFormula proposeSymb l := by
  classical
  have hPlace' := hPlace
  let uniqueCond : Formula S :=
    ∃≤ᶠ1 v ↦
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)
  let seqGuard : Formula S :=
    ∀ᶠ (fun l' => ♢ᶠ[[l, l']] Formula.seq)
  have hImp :
      ⟪w⟫ ⊨[M]
        ((¬ᶠ uniqueCond) ⇒ᶠ seqGuard) := by
    simpa [uniqueCond, seqGuard, Formula.or]
      using hBody
  refine
    (Sat.imp_intro (M := M) (w := w')
      (φ := ¬ᶠ uniqueCond) (ψ := seqGuard)) ?_
  intro hNotUnique'
  have hNotUnique :
      ⟪w⟫ ⊨[M] ¬ᶠ uniqueCond := by
    refine Sat.not_intro (M := M) (w := w)
      (φ := uniqueCond) ?_
    intro hUnique
    have hUnique' :
        ⟪w'⟫ ⊨[M] uniqueCond :=
      uniquePropose_monotone (M := M)
        (w := w) (w' := w') hSubset hUnique
    exact
      Sat.not_elim (M := M) (w := w') (φ := uniqueCond)
        hNotUnique' hUnique'
  have hSeqGuard :
      ⟪w⟫ ⊨[M] seqGuard :=
    Sat.imp_elim (M := M) (w := w)
      (φ := ¬ᶠ uniqueCond) (ψ := seqGuard)
      hImp hNotUnique
  have hSeqGuard' :
      ⟪w'⟫ ⊨[M] seqGuard :=
    safe_seq_guard_monotone (M := M)
      (w := w) (w' := w') (l := l)
      (hSubset := hSubset) (hPlace := hPlace')
      (hSeqGuard := hSeqGuard)
  exact hSeqGuard'

/-- Safety persists along same-place accessibility. -/
theorem safeFormula_monotone_subset
    (l : Signature.Value S)
    (hSubset : w.time ⊆trn M.history.val)
    (hBefore : w'.time ⪯ w.time)
    (hPlace : w'.place = w.place)
    (hSafe : ⟪w⟫ ⊨[M]safeFormula proposeSymb l) :
    ⟪w'⟫ ⊨[M]safeFormula proposeSymb l := by
  classical
  -- hereditary transitivity for the larger history ensures all predecessors stay inside it
  have hHer_w : isHereditarilyTransitive (P := P) (Event := Signature.EventType S) w.time :=
    hSubset.2
  have hTrans_w :
      ∀ ⦃h⦄, h ≺− w.time → h ⊆ w.time :=
    (isHereditarilyTransitive.trans (P := P) (Event := Signature.EventType S)
      hHer_w)
  have hSubset' :
      w'.time ⊆ w.time :=
    PreHistory.subset_of_happensBeforeEq
      (P := P) (Event := Signature.EventType S)
      (htrans := hTrans_w) hBefore
  have hHer_w' :
      isHereditarilyTransitive (P := P) (Event := Signature.EventType S) w'.time :=
    by
      rcases
          (PreHistory.happensBeforeEq_iff
            (P := P) (Event := Signature.EventType S)
            w'.time w.time).1 hBefore with
        hBefore' | hEq
      · exact
          isHereditarilyTransitive.desc
            (P := P) (Event := Signature.EventType S)
            hHer_w hBefore'
      · exact Eq.subst hEq.symm hHer_w
  have hSubset_trn : w'.time ⊆trn w.time :=
    ⟨hSubset', hHer_w'⟩
  exact
    safe_axiom_body_monotone (M := M)
      (w := w) (w' := w') (l := l)
      (hSubset := hSubset_trn) (hPlace := hPlace)
      (hBody := hSafe)

/-- Safety implies it always held in the past. -/
theorem safeFormula_allPast
    (l : Signature.Value S)
    (hwMem : w ∈ M.history.val)
    (hSafe : ⟪w⟫ ⊨[M]safeFormula proposeSymb l) :
    ⟪w⟫ ⊨[M]⇓ᶠ (safeFormula proposeSymb l) := by
  classical
  refine Sat.not_intro (M := M) (w := w)
      (φ := ↓ᶠ (¬ᶠ safeFormula proposeSymb l)) ?_
  intro hPast
  obtain ⟨t, ht_mem, ht_place, hNotSafe⟩ :=
    (Sat.past (M := M) (w := w)
      (φ := ¬ᶠ safeFormula proposeSymb l)).1 hPast
  have hAcc : t ≪⁻ w := ⟨ht_mem, ht_place⟩
  have hSubsetTime : w.time ⊆trn M.history.val := by
    have hBefore_w : w.time ≺− M.history.val :=
      happensBefore_of_mem (P := P)
        (Event := Signature.EventType S)
        (H := M.history.val) (e := w) hwMem
    let Hw : History P (Signature.EventType S) :=
      History.predecessorHistory (H := M.history) hBefore_w
    have hIncl :=
      History.happensBefore_implies_transitiveSubset Hw M.history hBefore_w
    simpa [Hw, History.predecessorHistory]
      using hIncl
  have hSafe_t :
      ⟪t⟫ ⊨[M] safeFormula proposeSymb l :=
    safeFormula_monotone_subset (M := M)
      (w := w) (w' := t) (l := l)
      (hSubset := hSubsetTime)
      (hBefore :=
        PreHistory.happensBeforeEq_of_accessible
          (P := P) (Event := Signature.EventType S) hAcc.1)
      (hPlace := hAcc.2)
      (hSafe := hSafe)
  exact
    Sat.not_elim (M := M) (w := t)
      (φ := safeFormula proposeSymb l) hNotSafe hSafe_t

/-- Paper: Lemma 6.4.2(1). Quorum knowledge of `φ` and a
global implication to `ψ` lift `φ` to a future quorum of `ψ`. -/
theorem boxPast_of_eventual_quorum
    (φ ψ : Formula S)
    (l : Signature.Value S)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]φ)
    (hImp : □W⊨[M](φ ⇒ᶠ ↕ᶠψ)) :
    ⊨[M]□ᶠ↓[[l]] ψ := by
  classical
  refine fun p => ?_
  let wₚ : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hBox_p :
      ⟪wₚ⟫ ⊨[M]
        □ᶠ[[l]] (Formula.past φ) := by
    simpa [Formula.boxPast, wₚ]
      using hQuorum p
  obtain ⟨O, hO, hAllφ⟩ :=
    (sat_box_singleton_exists (M := M)
        (w := wₚ) (l := l)
        (φ := Formula.past φ)).1 hBox_p
  have hImp_event : AllWorldValid M (φ ⇒ᶠ ↕ᶠ ψ) := hImp
  refine
    (sat_box_singleton_exists (M := M)
        (w := wₚ) (l := l)
        (φ := Formula.past ψ)).2 ?_
  refine ⟨O, hO, ?_⟩
  intro q hqO
  have hPastφ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] Formula.past φ := by
    simpa [wₚ]
      using hAllφ q hqO
  obtain ⟨tPast, ht_mem, ht_place, hφ_t⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := φ)).1 hPastφ
  rcases tPast with ⟨q', evtPast, HPast⟩
  have ht_mem_history :
      (q', evtPast, HPast) ∈ M.history.val := by
    simpa [World.time]
      using ht_mem
  have hImp_local :=
    AllWorldValid.of_mem_history
      (M := M) (φ := φ ⇒ᶠ ↕ᶠ ψ)
      hImp_event ht_mem_history
  have hSometime :
      ⟪⟨q', evtPast, HPast⟩⟫ ⊨[M] ↕ᶠ ψ :=
    (Sat.imp (M := M)
      (w := ⟨q', evtPast, HPast⟩)
      (φ := φ) (ψ := ↕ᶠ ψ)).1 hImp_local hφ_t
  have hPastψ_end :
      ⟪⟨q', †, M.history.val⟩⟫ ⊨[M] Formula.past ψ :=
    (Sat.atEnd (M := M)
      (w := ⟨q', evtPast, HPast⟩)
      (φ := Formula.past ψ)).1
      (by
        simpa [Formula.sometime] using hSometime)
  have hPastψ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] Formula.past ψ := by
    cases ht_place
    simpa using hPastψ_end
  simpa using hPastψ

/-- Paper: Lemma 6.4.2(2). The previous result under the
`ThyLive` assumption. -/
theorem boxPast_live_of_eventual_quorum
    (hLiveTheory : M ⊨ᵀ ThyLive liveSymb)
    (φ ψ : Formula S)
    (l : Signature.Value S)
    (hQuorum : ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ φ))
    (hImp : □W⊨[M]((predicate0 liveSymb ∧ᶠ φ) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ ψ) := by
  classical
  refine fun p => ?_
  let wₚ : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hBox_p :
      ⟪wₚ⟫ ⊨[M]
        □ᶠ[[l]]
          (Formula.past (predicate0 liveSymb ∧ᶠ φ)) := by
    simpa [Formula.boxPast, wₚ]
      using hQuorum p
  obtain ⟨O, hO, hAllLiveφ⟩ :=
    (sat_box_singleton_exists (M := M)
        (w := wₚ) (l := l)
        (φ := Formula.past (predicate0 liveSymb ∧ᶠ φ))).1 hBox_p
  have hImp_event :
      AllWorldValid M ((predicate0 liveSymb ∧ᶠ φ) ⇒ᶠ ↕ᶠ ψ) := hImp
  refine
    (sat_box_singleton_exists (M := M)
        (w := wₚ) (l := l)
        (φ := Formula.past (predicate0 liveSymb ∧ᶠ ψ))).2 ?_
  refine ⟨O, hO, ?_⟩
  intro q hqO
  have hPastLiveφ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        Formula.past (predicate0 liveSymb ∧ᶠ φ) := by
    simpa [wₚ]
      using hAllLiveφ q hqO
  obtain ⟨tφ, htφ_mem, htφ_place, hLiveφ_tφ⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := predicate0 liveSymb ∧ᶠ φ)).1 hPastLiveφ
  rcases tφ with ⟨qφ, evtφ, Hφ⟩
  have htφ_place' : qφ = q := htφ_place
  have hLiveφ_split :=
    (Sat.and (M := M) (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := predicate0 liveSymb) (ψ := φ)).1 hLiveφ_tφ
  have hLive_tφ :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M] predicate0 liveSymb := hLiveφ_split.1
  have hφ_tφ :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M] φ := hLiveφ_split.2
  have htφ_mem_history :
      (qφ, evtφ, Hφ) ∈ M.history.val := by
    simpa [World.time]
      using htφ_mem
  have hImp_local :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := (predicate0 liveSymb ∧ᶠ φ) ⇒ᶠ ↕ᶠ ψ)
      hImp_event htφ_mem_history
  have hSometime :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M] ↕ᶠ ψ :=
    (Sat.imp (M := M)
      (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := predicate0 liveSymb ∧ᶠ φ) (ψ := ↕ᶠ ψ)).1
      hImp_local hLiveφ_tφ
  have hPastψ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] Formula.past ψ := by
    have hPastψ_end :
        ⟪⟨qφ, †, M.history.val⟩⟫ ⊨[M] Formula.past ψ :=
      (Sat.atEnd (M := M)
        (w := ⟨qφ, evtφ, Hφ⟩)
        (φ := Formula.past ψ)).1
        (by
          simpa [Formula.sometime] using hSometime)
    cases htφ_place'
    simpa using hPastψ_end
  obtain ⟨tψ, htψ_mem, htψ_place, hψ_tψ⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := ψ)).1 hPastψ
  rcases tψ with ⟨qψ, evtψ, Hψ⟩
  have htψ_place' : qψ = q := htψ_place
  have hEquiv :=
      alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hLiveTheory)
        (t := ⟨qφ, evtφ, Hφ⟩)
        (ht := by simpa using htφ_mem)
  have hLive_global' :
      ⟪⟨qφ, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb :=
    (hEquiv).1 hLive_tφ
  have htφ_place_copy := htφ_place'
  have hLive_global :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb := by
    cases htφ_place_copy
    simpa using hLive_global'
  have hLive_global_qψ :
      ⟪⟨qψ, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb := by
    have htψ_place_copy := htψ_place'
    cases htψ_place_copy
    simpa using hLive_global
  have hLive_tψ :
      ⟪⟨qψ, evtψ, Hψ⟩⟫ ⊨[M] predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hLiveTheory)
        (t := ⟨qψ, evtψ, Hψ⟩)
        (ht := by simpa [World.time] using htψ_mem)).mpr hLive_global_qψ
  have hConj_tψ :
      ⟪⟨qψ, evtψ, Hψ⟩⟫ ⊨[M]
        (predicate0 liveSymb ∧ᶠ ψ) :=
    (Sat.and (M := M) (w := ⟨qψ, evtψ, Hψ⟩)
      (φ := predicate0 liveSymb) (ψ := ψ)).2
      ⟨hLive_tψ, hψ_tψ⟩
  have hPastLiveψ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        Formula.past (predicate0 liveSymb ∧ᶠ ψ) :=
    (Sat.past_intro_of_prefix (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (t := ⟨qψ, evtψ, Hψ⟩)
      (φ := predicate0 liveSymb ∧ᶠ ψ)
      (ht := by simpa [World.time] using htψ_mem)
      (hp := by simpa [World.place] using htψ_place)
      (hφ := hConj_tψ))
  simpa [wₚ]
    using hPastLiveψ

/-- Paper: Lemma 6.4.3. Composing eventual consequences at the end of
time. -/
theorem live_eventually_consequent
    (hLiveTheory : M ⊨ᵀ ThyLive liveSymb)
    (φ ψ : Formula S)
    (hLive : ⊨[M](predicate0 liveSymb ⇒ᶠ ↕ᶠφ))
    (hImp : □W⊨[M]((predicate0 liveSymb ∧ᶠ φ) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M](predicate0 liveSymb ⇒ᶠ ↕ᶠψ) := by
  classical
  refine fun p => ?_
  let wₚ : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hLiveImp := hLive p
  have hImp_event : AllWorldValid M ((predicate0 liveSymb ∧ᶠ φ) ⇒ᶠ ↕ᶠ ψ) := hImp
  refine
    (Sat.imp (M := M)
      (w := wₚ)
      (φ := predicate0 liveSymb) (ψ := ↕ᶠ ψ)).2 ?_
  intro hLive_p
  have hSometimeφ :
      ⟪wₚ⟫ ⊨[M] ↕ᶠ φ :=
    (Sat.imp (M := M)
      (w := wₚ)
      (φ := predicate0 liveSymb) (ψ := ↕ᶠ φ)).1
      hLiveImp hLive_p
  have hPastφ :
      ⟪wₚ⟫ ⊨[M] Formula.past φ :=
    (Sat.atEnd (M := M)
      (w := wₚ)
      (φ := Formula.past φ)).1
      (by
        simpa [Formula.sometime] using hSometimeφ)
  obtain ⟨tφ, htφ_mem, htφ_place, hφ_tφ⟩ :=
    (Sat.past (M := M)
      (w := wₚ)
      (φ := φ)).1 hPastφ
  rcases tφ with ⟨qφ, evtφ, Hφ⟩
  have htφ_place' : qφ = p := htφ_place
  have htφ_place_copy1 := htφ_place'
  have htφ_place_copy2 := htφ_place'
  have hLive_local :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M] predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hLiveTheory)
      (t := ⟨qφ, evtφ, Hφ⟩)
        (ht := by simpa [World.time] using htφ_mem)).mpr
      (by
        cases htφ_place_copy1
        simpa using hLive_p)
  have htφ_mem_history :
      (qφ, evtφ, Hφ) ∈ M.history.val := by
    simpa [World.time]
      using htφ_mem
  have hImp_local :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := (predicate0 liveSymb ∧ᶠ φ) ⇒ᶠ ↕ᶠ ψ)
      hImp_event htφ_mem_history
  have hConj :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M]
        (predicate0 liveSymb ∧ᶠ φ) :=
    (Sat.and (M := M) (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := predicate0 liveSymb) (ψ := φ)).2
      ⟨hLive_local, hφ_tφ⟩
  have hSometimeψ_tφ :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M] ↕ᶠ ψ :=
    (Sat.imp (M := M)
      (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := predicate0 liveSymb ∧ᶠ φ) (ψ := ↕ᶠ ψ)).1
      hImp_local hConj
  have hPastψ_raw :
      ⟪⟨qφ, †, M.history.val⟩⟫ ⊨[M] Formula.past ψ :=
    (Sat.atEnd (M := M)
      (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := Formula.past ψ)).1
      (by
        simpa [Formula.sometime] using hSometimeψ_tφ)
  have htφ_place_copy3 := htφ_place_copy2
  have hPastψ :
      ⟪wₚ⟫ ⊨[M] Formula.past ψ := by
    cases htφ_place_copy3
    simpa using hPastψ_raw
  exact
    (Sat.atEnd (M := M)
      (w := wₚ)
      (φ := Formula.past ψ)).2 hPastψ

/-- Paper: Lemma 6.4.4. `\atd{l}` of `\sometime φ` coincides
with `\atddot{l} φ`. -/
theorem box_sometime_iff_boxPast
    (φ : Formula S)
    (l : Signature.Value S) :
    (⊨[M]□ᶠ[[l]] ↕ᶠφ) ↔
      (⊨[M]□ᶠ↓[[l]] φ) := by
  classical
  constructor
  · intro hBox
    refine fun p => ?_
    let wₚ : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
    have hBox_p :
        ⟪wₚ⟫ ⊨[M]
          □ᶠ[[l]] ↕ᶠ φ := hBox p
    obtain ⟨O, hO, hAll⟩ :=
      (sat_box_singleton_exists (M := M)
          (w := wₚ) (l := l)
          (φ := ↕ᶠ φ)).1 hBox_p
    refine
      (sat_box_singleton_exists (M := M)
          (w := wₚ) (l := l)
          (φ := Formula.past φ)).2 ?_
    refine ⟨O, hO, ?_⟩
    intro q hqO
    have hSome_local := hAll q hqO
    have hSome :
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] ↕ᶠ φ :=
      hSome_local
    have hPast :
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] Formula.past φ :=
      (Sat.atEnd (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := Formula.past φ)).1
        (by
          simpa [Formula.sometime]
            using hSome)
    exact hPast
  · intro hBox
    refine fun p => ?_
    let wₚ : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
    have hBox_p :
        ⟪wₚ⟫ ⊨[M]
          □ᶠ[[l]] (Formula.past φ) :=
      hBox p
    obtain ⟨O, hO, hAll⟩ :=
      (sat_box_singleton_exists (M := M)
          (w := wₚ) (l := l)
          (φ := Formula.past φ)).1 hBox_p
    refine
      (sat_box_singleton_exists (M := M)
          (w := wₚ) (l := l)
          (φ := ↕ᶠ φ)).2 ?_
    refine ⟨O, hO, ?_⟩
    intro q hqO
    have hPast_local := hAll q hqO
    have hPast :
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] Formula.past φ :=
      hPast_local
    have hSome :
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] ↕ᶠ φ :=
      (Sat.atEnd (M := M)
        (w := ⟨q, †, M.history.val⟩)
        (φ := Formula.past φ)).2 hPast
    exact hSome

/-- Paper: Lemma 6.4.1(1). Safety of a learner is monotone along in-place accessibility: if `safe(l)`
holds at a world of the model, it holds at every same-place predecessor. -/
theorem safe_monotone
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (l : Signature.Value S)
    {w w' : World P (Signature.EventType S)}
    (hW : w.time ⪯ M.history.val)
    (hAcc : w' ≪⁻ w)
    (hSafe : ⟪w⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) :
    ⟪w'⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩ := by
  classical
  have hW' : w'.time ⪯ M.history.val := by
    rcases (PreHistory.happensBeforeEq_iff
        (P := P) (Event := Signature.EventType S) w.time M.history.val).1 hW with hlt | heq
    · exact (PreHistory.happensBeforeEq_iff
        (P := P) (Event := Signature.EventType S) _ _).2
        (Or.inl (accessible_happensBefore_history (H := M.history)
          (hW := hW) (hAcc := hAcc.1)))
    · exact (PreHistory.happensBeforeEq_iff
        (P := P) (Event := Signature.EventType S) _ _).2
        (Or.inl (by
          rw [← heq]
          exact PreHistory.happensBefore_of_accessible
            (P := P) (Event := Signature.EventType S) hAcc.1))
  have hSafeF :=
    (safe_iff_safeFormula (M := M) (hTheory := hTheory) (w := w) hW l).1 hSafe
  have hSafeF' :=
    safeFormula_monotone_subset (M := M) l
      (hSubset := time_subset_trn_history (M := M) (t := w) hW)
      (hBefore := PreHistory.happensBeforeEq_of_accessible
        (P := P) (Event := Signature.EventType S) hAcc.1)
      (hPlace := hAcc.2)
      hSafeF
  exact (safe_iff_safeFormula (M := M) (hTheory := hTheory) (w := w') hW' l).2 hSafeF'

/-- Paper: Lemma 6.4.1(2). Safety of a learner at an event-tuple of the model implies it held at every
past event at the same place. -/
theorem safe_allPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (l : Signature.Value S)
    {w : World P (Signature.EventType S)}
    (hwMem : w ∈ M.history.val)
    (hSafe : ⟪w⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) :
    ⟪w⟫ ⊨[M]⇓ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
  classical
  have hW : w.time ⪯ M.history.val :=
    PreHistory.happensBeforeEq_of_mem
      (P := P) (Event := Signature.EventType S)
      (hmem := by
        simpa [World.place, World.event, World.time] using hwMem)
  refine Sat.not_intro (M := M) (w := w)
    (φ := ↓ᶠ (¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))) ?_
  intro hPast
  obtain ⟨t, ht_mem, ht_place, hNot⟩ :=
    (Sat.past (M := M) (w := w)
      (φ := ¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))).1 hPast
  have hAcc : t ≪⁻ w :=
    ⟨by simpa [World.accessible] using ht_mem, ht_place⟩
  have hSafe_t :=
    safe_monotone (M := M) (hTheory := hTheory) (l := l)
      (hW := hW) (hAcc := hAcc) hSafe
  exact
    Sat.not_elim (M := M) (w := t)
      (φ := ofPredicate ⟨safeSymb, [l]⟩) hNot hSafe_t


/-- The instantiated `Vote!` implication used by the liveness proofs: when a
learner is safe at the end of time, any live participant holding an echo
quorum eventually votes. Safety persists to every relevant past world by
`safe_monotone`. -/
theorem voteForward_imp
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l v : Signature.Value S}
    (hSafe : ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) :
    □W⊨[M]((predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
  classical
  intro t ht
  refine Sat.imp_intro (M := M) (w := t) ?_
  intro hConj
  have hSplit :=
    (Sat.and (M := M) (w := t)
      (φ := predicate0 liveSymb)
      (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).1 hConj
  have hSafeAlways :
      ⟪t⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
    refine (Sat.everytime (M := M) (w := t)
      (φ := ofPredicate ⟨safeSymb, [l]⟩)).2 ?_
    intro s hs _
    exact
      safe_monotone (M := M) (hTheory := hTheory) (l := l)
        (w := ⟨s.place, †, M.history.val⟩)
        (hW := PreHistory.happensBeforeEq_refl _)
        (hAcc := ⟨by simpa [World.accessible] using hs, rfl⟩)
        (by simpa using hSafe s.place)
  exact
    voteForward_elim (M := M)
      (hAx := theory_voteForward (M := M) hTheory)
      (hW := ht)
      (hSafeAlways := hSafeAlways)
      (hLive := hSplit.1)
      (hEchoBox := hSplit.2)

end Results


end ThyHBB1
end Examples
end ModalDistribution
