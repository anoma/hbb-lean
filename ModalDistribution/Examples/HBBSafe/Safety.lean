import ModalDistribution.Examples.HBB.Uniqueness
import ModalDistribution.Examples.HBBSafe.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History

/-!
# HBBSafe safety lemmas

Lemmas about the `safe` predicate of `HBBSafe` and the `Vote!` rule it guards:

- **Monotonicity of the `Safe` formula**: `safe_seq_guard_monotone`,
  `safe_axiom_body_monotone`, `safeFormula_monotone_subset`, and
  `safeFormula_allPast`: the `Safe` formula persists when restricting to smaller
  histories

- **Safety of a learner** (Lemma 6.5.1):
  - `safe_monotone`: `safe` persists along in-place accessibility
  - `safe_allPast`: `safe` implies it always held in the past

- **Uniqueness implies safety** (Lemma 6.6.2): `atMostOnePropose_safeFormula`
  and `atMostOnePropose_safe`

- **`Vote!` instantiations**: `voteForward_imp_of_everytime` and `voteForward_imp`
  package the axiom together with its safety guard for the liveness proofs

The theory-independent lemmas these build on live in `HBB.Liveness` and
`HBB.Uniqueness`.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSafe

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

/-- Paper: Lemma 6.5.1(1). Safety of a learner is monotone along in-place accessibility: if
`safe(l)` holds at a world of the model, it holds at every same-place predecessor. -/
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

/-- Paper: Lemma 6.5.1(2). Safety of a learner at an event-tuple of the model implies it held at
every past event at the same place. -/
theorem safe_allPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (l : Signature.Value S)
    {w : World P (Signature.EventType S)}
    (hW : w.time ⪯ M.history.val)
    (hSafe : ⟪w⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) :
    ⟪w⟫ ⊨[M]⇓ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
  classical
  refine (Sat.allPast (M := M) (w := w)
    (φ := ofPredicate ⟨safeSymb, [l]⟩)).2 ?_
  intro t ht_mem ht_place
  exact
    safe_monotone (M := M) (hTheory := hTheory) (l := l)
      (hW := hW)
      (hAcc := ⟨by simpa [World.accessible] using ht_mem, ht_place⟩)
      hSafe

/-- at most one proposal implies every learner is safe. -/
theorem atMostOnePropose_safeFormula
    (l : Signature.Value S) :
    ⊨[M](∃≤ᶠ1 v ↦
        (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        safeFormula proposeSymb l := by
  classical
  let uniqueCond : Formula S :=
    ∃≤ᶠ1 v ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)
  let seqGuard : Formula S :=
    ∀ᶠ (fun l' => ♢ᶠ[[l, l']] Formula.seq)
  intro p
  refine (Sat.imp (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := uniqueCond)
      (ψ := safeFormula proposeSymb l)).2 ?_
  intro hUniqueCond
  have hOr :=
    (Sat.or (M := M) (w := ⟨p, †, M.history.val⟩)
      (φ := uniqueCond) (ψ := seqGuard)).2
      (Or.inl hUniqueCond)
  simpa [uniqueCond, seqGuard, safeFormula]
    using hOr

/-- Paper: Lemma 6.6.2. If at most one value is proposed, then every learner is everywhere and
always safe. -/
theorem atMostOnePropose_safe
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (l : Signature.Value S) :
    ⊨[M](∃≤ᶠ1 v ↦
        (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hUnique
  refine Sat.not_intro (M := M) (w := wTop)
    (φ := ↕ᶠ (¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))) ?_
  intro hSome
  obtain ⟨s, hs_mem, hs_place, hNot⟩ :=
    (Sat.sometime (M := M) (w := wTop)
      (φ := ¬ᶠ (ofPredicate ⟨safeSymb, [l]⟩))).1 hSome
  have hs_mem' : s ∈ M.history.val := by
    simpa [wTop, World.time] using hs_mem
  have hs_le : s.time ⪯ M.history.val :=
    PreHistory.happensBeforeEq_of_mem
      (P := P) (Event := Signature.EventType S)
      (hmem := by
        simpa [World.place, World.event, World.time] using hs_mem')
  have hUnique_s :
      ⟪s⟫ ⊨[M]∃≤ᶠ1 v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) :=
    uniquePropose_monotone (M := M)
      (w := wTop) (w' := s)
      (hSubset := by
        simpa [wTop, World.time] using
          time_subset_trn_history (M := M) (t := s) hs_le)
      (hUnique := by simpa [wTop] using hUnique)
  have hSafeF_s : ⟪s⟫ ⊨[M] safeFormula proposeSymb l := by
    have hOr :=
      (Sat.or (M := M) (w := s)
        (φ := ∃≤ᶠ1 v ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
        (ψ := ∀ᶠ (fun l' => ♢ᶠ[[l, l']] Formula.seq))).2
        (Or.inl hUnique_s)
    simpa [safeFormula] using hOr
  have hSafe_s : ⟪s⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩ :=
    (safe_iff_safeFormula (M := M) (hTheory := hTheory)
      (w := s) hs_le l).2 hSafeF_s
  exact
    Sat.not_elim (M := M) (w := s)
      (φ := ofPredicate ⟨safeSymb, [l]⟩) hNot hSafe_s

/-- The instantiated `Vote!` implication, taking the everywhere-always safety
guard in the form axiom `Vote!` demands it. -/
theorem voteForward_imp_of_everytime
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l v : Signature.Value S}
    (hSafeAlways : □W⊨[M] ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩)) :
    □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
  classical
  intro t ht
  refine Sat.imp_intro (M := M) (w := t) ?_
  intro hLiveEcho
  exact
    voteForward_elim (M := M)
      (hAx := theory_voteForward (M := M) hTheory)
      (hW := ht)
      (hSafeAlways := hSafeAlways ht)
      (hLiveEcho := hLiveEcho)

/-- The instantiated `Vote!` implication used by the liveness proofs: when a
learner is safe at the end of time, any live participant holding an echo
quorum eventually votes. Safety persists to every relevant past world by
`safe_monotone` (Lemma 6.5.1). -/
theorem voteForward_imp
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l v : Signature.Value S}
    (hSafe : ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) :
    □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
  classical
  refine voteForward_imp_of_everytime (M := M)
    (hTheory := hTheory) ?_
  intro t _
  -- Lemma 6.5.1(2) at the end-of-time world of `t.place` gives safety at
  -- every event of that place, which is exactly `⇕safe` at `t`.
  have hAllPast :
      ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]
        ⇓ᶠ (ofPredicate ⟨safeSymb, [l]⟩) :=
    safe_allPast (M := M) (hTheory := hTheory) (l := l)
      (hW := PreHistory.happensBeforeEq_refl _)
      (hSafe := by simpa using hSafe t.place)
  refine (Sat.everytime (M := M) (w := t)
    (φ := ofPredicate ⟨safeSymb, [l]⟩)).2 ?_
  intro s hs hplace
  exact
    (Sat.allPast (M := M)
      (w := ⟨t.place, †, M.history.val⟩)
      (φ := ofPredicate ⟨safeSymb, [l]⟩)).1
      hAllPast s (by simpa [World.time] using hs)
      (by simpa [World.place] using hplace)

end Results

end HBBSafe
end Examples
end ModalDistribution
