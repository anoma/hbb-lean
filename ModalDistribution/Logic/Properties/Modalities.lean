import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties.Quorums
import ModalDistribution.Logic.Properties.Satisfaction
import ModalDistribution.Core.Semifilter
import ModalDistribution.Core.History

/-!
# The modalities (paper Section 4)

The quorum intersection properties of Subsection 4.1 (Lemma 4.1.1 and
Notation 4.1.2, with their supporting lemmas) and the modal properties of
Subsection 4.2 (Lemmas 4.2.1-4.2.3), over the satisfaction machinery from
`Logic.Properties.Satisfaction`. The file ends with the generic derivation
lemmas for the boxed and diamond corollaries of the liveness theorems.
-/

namespace ModalDistribution
namespace Logic

open Set
open History
open scoped Semifilter Formula History PreHistory Model

set_option autoImplicit false

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

section DiamondSection


/-! ## Quorum intersection properties (paper Subsection 4.1) -/

/-- Paper: Lemma 4.1.1(1). N-way quorum intersection witness).

Characterizes the global diamond modality `♢ᶠ[ls] φ` in terms of quorum witnesses:
a formula holds under the diamond modality if and only if there exists a witness
participant present in all quorums from every learner family.

This is fundamental to establishing agreement properties in broadcast protocols,
as it provides the connection between modal satisfaction and quorum intersection.

See also: `nWayQuorumIntersectionNonempty`, `quorumWitnessImpliesNonempty`. -/
theorem nWayQuorumIntersectionWitness
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] (♢ᶠ[ls] φ)) ↔ hasQuorumWitness (M := M) ls φ := by
  classical
  constructor
  · intro h
    have hSat :=
      h (Classical.choice (show Nonempty P from inferInstance))
    have hCheck :=
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := ls) (φ := φ) _).1 hSat
    have hWitnessAcc :=
      (diamondCheck_iff_quorumWitnessAcc (M := M)
        (ls := ls)
        (Q := fun q => ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]φ)
        (acc := Set.univ)).1 hCheck
    exact
      (quorumWitnessAcc_univ (M := M)
        (ls := ls) (φ := φ)).1 hWitnessAcc
  · intro hWitness
    have hWitnessAcc :=
      (quorumWitnessAcc_univ (M := M)
        (ls := ls) (φ := φ)).2 hWitness
    have hCheck :=
      (diamondCheck_iff_quorumWitnessAcc (M := M)
        (ls := ls)
        (Q := fun q => ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]φ)
        (acc := Set.univ)).2 hWitnessAcc
    intro p
    exact
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := ls) (φ := φ)
        (w := ⟨p, †, M.history.val⟩)).2 hCheck

/-- Paper: Lemma 4.1.1(2). N-way quorum intersection nonemptiness).

Specializes the witness characterization to the trivial formula `⊤`: the global diamond
`♢ᶠ[ls] ⊤ᶠ` holds if and only if all quorum families have nonempty intersection.

This provides a simpler sufficient condition for quorum intersection when we don't
need to track satisfaction of a specific formula.

See also: `nWayQuorumIntersectionWitness`, `quorumWitnessImpliesNonempty`. -/
theorem nWayQuorumIntersectionNonempty
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] (♢ᶠ[ls] ⊤ᶠ)) ↔ hasQuorumNonempty (M := M) ls := by
  classical
  refine
    (nWayQuorumIntersectionWitness (M := M) (ls := ls) (φ := ⊤ᶠ)).trans ?_
  constructor
  · intro hWitness F
    rcases hWitness F with ⟨p, hpAll, _⟩
    exact ⟨p, hpAll⟩
  · intro hNonempty F
    rcases hNonempty F with ⟨p, hpAll⟩
    refine ⟨p, hpAll, ?_⟩
    simpa [Formula.top]
      using (Sat.top (M := M)
        (w := ⟨p, †, M.history.val⟩))

/-- Paper: Lemma 4.1.1(3). Quorum witness implies nonemptiness).

If a formula has a quorum witness (satisfies `♢ᶠ[ls] φ`), then the quorum families
have nonempty intersection (satisfies `♢ᶠ[ls] ⊤ᶠ`). This weakening is useful when
we only need to establish that quorums intersect, not that they intersect at worlds
satisfying a specific formula.

See also: `nWayQuorumIntersectionWitness`, `nWayQuorumIntersectionNonempty`. -/
theorem quorumWitnessImpliesNonempty
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] (♢ᶠ[ls] φ)) →
      (⊨[M] (♢ᶠ[ls] ⊤ᶠ)) := by
  intro h
  have hWitness :=
    (nWayQuorumIntersectionWitness (M := M) (ls := ls) (φ := φ)).1 h
  have hNonempty : hasQuorumNonempty (M := M) ls := by
    intro F
    obtain ⟨p, hpAll, _⟩ := hWitness F
    exact ⟨p, hpAll⟩
  exact
    (nWayQuorumIntersectionNonempty (M := M) (ls := ls)).2 hNonempty

/-- Paper: Notation 4.1.2 (nonempty quorum intersections). Nonempty quorum intersections. -/
@[simp] def hasNonemptyIntersections
    (M : Model S P) (ls : List S.Value) : Prop :=
  ⊨[M] (♢ᶠ[ls] ⊤ᶠ)

/-- Paper: Notation 4.1.2 (sequential quorum intersections). Sequential quorum intersections. -/
@[simp] def hasSequentialIntersections
    (M : Model S P) (ls : List S.Value) : Prop :=
  ⊨[M] (♢ᶠ[ls] Formula.seq)

/-- Paper: Notation 4.1.2 (live quorum intersections). Live quorum intersections. -/
@[simp] def hasLiveIntersections
    (M : Model S P) (liveSymb : Signature.PredSymb S)
    (ls : List S.Value) : Prop :=
  ⊨[M] (♢ᶠ[ls] (Formula.predicate0 liveSymb))

/-- Present-time box implies past-guarded box.

Quorum witnesses correspond to present-time diamonds: having a quorum witness
is equivalent to the global diamond modality holding.

See also: `pastBoxAtTopWorld`, `nWayQuorumIntersectionWitness`. -/
theorem presentBoxImpliesPastBox
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    hasQuorumWitness (M := M) ls φ ↔
      (⊨[M] ♢ᶠ[ls] φ) :=
  by
    classical
    simpa using
      (nWayQuorumIntersectionWitness (M := M)
        (ls := ls) (φ := φ)).symm

/-- Past-guarded box at top world.

Nonempty quorum intersections correspond to eventually-past diamonds: having
a quorum witness for ⊤ is equivalent to the eventually-past diamond holding.
This specializes the present-time correspondence to past-guarded modalities.

See also: `presentBoxImpliesPastBox`, `pastBoxTopImpliesPredecessor`. -/
theorem pastBoxAtTopWorld
    (M : Model S P)
    (ls : List S.Value) :
    hasQuorumWitness (M := M) ls ⊤ᶠ ↔
      (⊨[M] ♢ᶠ⇓[ls] ⊤ᶠ) :=
  by
    classical
    have hPresent :=
      presentBoxImpliesPastBox (M := M)
        (ls := ls) (φ := ⊤ᶠ)
    refine hPresent.trans ?_
    unfold EndValid
    apply forall_congr'
    intro p
    exact
      (Sat.diamond_congr (M := M)
        (w := ⟨p, †, M.history.val⟩)
        (ts := ls)
        (φ := ⊤ᶠ) (ψ := ⇓ᶠ ⊤ᶠ)
        (h := fun q =>
          (localSat_allPast_top_eq (M := M)
            (w := ⟨q, †, M.history.val⟩)).symm))

/-- Past box at top implies predecessor.

Under the activity assumption (□ᶠ[] (↓ᶠ ⊤ᶠ)), quorum witnesses for ⊤ correspond
to past-guarded diamonds ♢ᶠ↓[ls] ⊤ᶠ. The activity assumption ensures that all
participants have a non-empty history, allowing past operators to be meaningful.

See also: `pastBoxAtTopWorld`, `pastBoxSeqImpliesPredecessor`. -/
theorem pastBoxTopImpliesPredecessor
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (hasQuorumWitness (M := M) ls ⊤ᶠ ↔
        (⊨[M] ♢ᶠ↓[ls] ⊤ᶠ)) := by
  classical
  intro hActive
  have hPresentPast :=
    presentBoxImpliesPastBox (M := M) (ls := ls) (φ := ↓ᶠ ⊤ᶠ)
  have hActiveLocal :=
    (EndValid.boxEmpty_guard (M := M)
      (φ := ↓ᶠ ⊤ᶠ)) hActive
  constructor
  · intro hWitness
    have hWitnessPast :=
      hasQuorumWitness.of_imp (M := M) (ls := ls)
        (φ := ⊤ᶠ) (ψ := ↓ᶠ ⊤ᶠ)
        (h := fun p _ => hActiveLocal p) hWitness
    exact
      (by
        simpa [Formula.diamondPast]
          using (hPresentPast).1 hWitnessPast)
  · intro hDiamondPast
    have hWitnessPast :=
      (hPresentPast).2
        (by simpa [Formula.diamondPast]
          using hDiamondPast)
    exact
      hasQuorumWitness.of_imp (M := M) (ls := ls)
        (φ := ↓ᶠ ⊤ᶠ) (ψ := ⊤ᶠ)
        (h := fun p _ =>
          (Sat.top (M := M)
            (w := ⟨p, †, M.history.val⟩)))
        hWitnessPast

/-- Past box for sequentiality implies predecessor.

Under the activity assumption, sequential witnesses persist: having a sequential
quorum witness implies the past-guarded sequential diamond holds. Note that the
reverse implication fails in our semantics: a participant can satisfy `↓ Formula.seq`
via an earlier sequential prefix even when the current history contains incomparable
events.

See also: `pastBoxTopImpliesPredecessor`, `presentBoxImpliesPastBox`. -/
theorem pastBoxSeqImpliesPredecessor
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (hasQuorumWitness (M := M) ls Formula.seq →
        (⊨[M] ♢ᶠ↓[ls] Formula.seq)) := by
  classical
  intro hActive hWitness
  have hWitnessPast :=
    hasQuorumWitness.seq_to_past (M := M) (ls := ls)
      hActive hWitness
  exact
    (presentBoxImpliesPastBox (M := M) (ls := ls)
      (φ := ↓ᶠ Formula.seq)).1 hWitnessPast

/-! ## Modal properties (paper Subsection 4.2) -/

/-- Paper: Lemma 4.2.1(1). Singleton box implies diamond).

A singleton quorum box □ᶠ↓[[l]]φ guarantees that every quorum from learner l
satisfies the past-guarded formula, which implies the empty diamond ♢ᶠ↓[[]] φ
(someone satisfies the formula). This is the local version of the implication.

See also: `globalSingletonBoxImpliesDiamond`, `quorumBoxImpliesEmptyDiamond`. -/
theorem singletonBoxImpliesDiamond
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S)
    (hBox : ⟪w⟫ ⊨[M]□ᶠ↓[[l]]φ) :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] φ) := by
  classical
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := w) (l := l)
      (φ := ↓ᶠ φ)).1 hBox
  obtain ⟨q, hq⟩ :=
    Semifilter.quorum_nonempty (L := M.learner l) hO
  refine
    sat_diamondEmpty_of_local (M := M)
      (w := w) (φ := ↓ᶠ φ)
      ⟨q, hAll q hq⟩

/-- Paper: Lemma 4.2.1(2). Global singleton box implies diamond).

The global version: if □ᶠ[[l]] φ holds globally, then ♢ᶠ[] φ holds globally.
This lifts the local singleton box implication to the global level.

See also: `singletonBoxImpliesDiamond`, `diamondPast_idem`. -/
theorem globalSingletonBoxImpliesDiamond
    (M : Model S P)
    (l : Signature.Value S) (φ : Formula S) :
    (⊨[M] □ᶠ[[l]] φ) → (⊨[M] ♢ᶠ[] φ) := by
  classical
  intro hBox p
  have hLocal := hBox p
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (l := l) (φ := φ)).1 hLocal
  obtain ⟨q, hq⟩ :=
    Semifilter.quorum_nonempty (L := M.learner l) hO
  exact
    sat_diamondEmpty_of_local (M := M)
      (w := ⟨p, †, M.history.val⟩) (φ := φ)
      ⟨q, hAll q hq⟩

/-- Paper: Lemma 4.2.1(2). Quorum box implies empty diamond).

A singleton quorum box □ᶠ[[l]] φ at any world implies the empty diamond ♢ᶠ[] φ
at that world. This is a strengthening that works for arbitrary histories, not
just the global top history.

See also: `singletonBoxImpliesDiamond`, `diamondPast_idem`. -/
theorem quorumBoxImpliesEmptyDiamond
    (M : Model S P)
    (H : History P (Signature.EventType S)) (p : P)
    (l : Signature.Value S) (φ : Formula S) :
    (⟪⟨p, †, H.val⟩⟫ ⊨[M] □ᶠ[[l]] φ) →
      (⟪⟨p, †, H.val⟩⟫ ⊨[M] ♢ᶠ[] φ) := by
  classical
  intro hBox
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := ⟨p, †, H.val⟩)
      (l := l) (φ := φ)).1 hBox
  obtain ⟨q, hq⟩ :=
    Semifilter.quorum_nonempty (L := M.learner l) hO
  exact
    sat_diamondEmpty_of_local (M := M)
      (w := ⟨p, †, H.val⟩) (φ := φ)
      ⟨q, hAll q hq⟩

/-- Transport a past-box witness from a predecessor world to the current world. -/
private theorem sat_boxPast_of_predecessor
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S)
    (hMem : w ∈ M.history.val)
    {t : World P (Signature.EventType S)}
    (ht_mem : t ∈ w.time)
    (hBox_t : ⟪t⟫ ⊨[M]□ᶠ↓[[l]]φ) :
    (⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) := by
  classical
  have hBefore :
      w.time ≺− M.history.val :=
    History.happensBefore_of_mem (P := P)
      (Event := Signature.EventType S)
      (H := M.history.val) (e := w) hMem
  let wHist :=
    History.predecessorHistory (H := M.history) hBefore
  have hAcc : t ≪ w := by
    simpa [World.accessible, World.time] using ht_mem
  have hBeforeTime :
      PreHistory.happensBefore (World.time t) (World.time w) :=
    PreHistory.happensBefore_of_accessible (P := P)
      (Event := Signature.EventType S) hAcc
  have hSubset_t :
      World.time t ⊆ w.time := by
    have hSubset' :
        World.time t ⊆ wHist.val :=
      History.subset_of_happensBefore (H := wHist)
        (h_before := by
          simpa [wHist, World.time] using hBeforeTime)
    simpa [wHist] using hSubset'
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := t) (l := l) (φ := ↓ᶠ φ)).1 hBox_t
  refine
    (sat_box_singleton_exists (M := M)
      (w := w) (l := l) (φ := ↓ᶠ φ)).2 ?_
  refine ⟨O, hO, ?_⟩
  intro q hq
  have hPast := hAll q hq
  have hPast' :=
    sat_past_of_subset (M := M)
      (q := q) (H := World.time t) (H' := w.time)
      (φ := φ) (hSubset := hSubset_t) hPast
  simpa [World.place, World.event, World.time] using hPast'

/-- Paper: Lemma 4.2.2 (the S4 axiom). Quorum box global implies empty diamond.

Past diamonds are idempotent: ♢ᶠ↓[[]] (↓ᶠ φ) is equivalent to ♢ᶠ↓[[]] φ.
This shows that nested past operators collapse, simplifying reasoning about
temporal formulas in distributed protocols.

See also: `pastBoxCollapsesToPresentBox`, `pastDiamondBoxCollapsesToPresentBox`. -/
theorem diamondPast_idem
    (M : Model S P)
    (w : World P (Signature.EventType S)) (φ : Formula S)
    (hMem : w ∈ M.history.val) :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (♢ᶠ↓[[]] φ)) →
      (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] φ) := by
  classical
  intro hDiamond
  -- Membership witnesses a transitive predecessor history for `w`
  have hBefore :
      w.time ≺− M.history.val :=
    History.happensBefore_of_mem (P := P)
      (Event := Signature.EventType S) (H := M.history.val)
      (e := w) hMem
  let wPred :=
    History.predecessorHistory (H := M.history) hBefore
  have hTrans :
      isTransitive (P := P) (Event := Signature.EventType S) w.time := by
    have := History.transitive (P := P)
      (Event := Signature.EventType S) wPred
    simpa [wPred] using this
  -- Unfold the outer empty diamond to expose the past witness
  obtain ⟨p, hPast⟩ :=
    (Sat.Sat_diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ (♢ᶠ↓[[]] φ))).1
      (by simpa [Formula.diamondPast] using hDiamond)
  -- The past witness provides a predecessor tuple in `w.time`
  obtain ⟨t, ht_mem, ht_place, hDiamond_t⟩ :=
    (Sat.past (M := M)
      (w := ⟨p, †, w.time⟩)
      (φ := ♢ᶠ↓[[]] φ)).1 hPast
  -- Unfold the inner diamond at the predecessor world
  obtain ⟨q, hPastφ⟩ :=
    (Sat.Sat_diamond_nil (M := M)
      (w := t)
      (φ := ↓ᶠ φ)).1
      (by simpa [Formula.diamondPast] using hDiamond_t)
  -- Extract the final past witness
  obtain ⟨t', ht'_mem, ht'_place, hφ⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, t.time⟩) (φ := φ)).1 hPastφ
  -- Show that the predecessor history embeds back into `w.time`
  have ht_subset :
      World.time t ⊆ w.time := by
    have hAcc : t ≪ ⟨p, †, w.time⟩ := by
      simpa [World.time] using ht_mem
    have :=
      PreHistory.accessible_subset (P := P)
        (Event := Signature.EventType S)
        (t' := t) (t := ⟨p, †, w.time⟩)
        hAcc
        (by
          have := hTrans
          simpa [World.time, isTransitive] using this)
    simpa [World.time] using this
  -- Transport the innermost witness back to the ambient world
  have hPastFinal :
      (⟪⟨q, †, w.time⟩⟫ ⊨[M] ↓ᶠ φ) :=
    (Sat.past (M := M)
      (w := ⟨q, †, w.time⟩)
      (φ := φ)).2
      ⟨t', ht_subset t' ht'_mem,
        by simpa [World.place] using ht'_place, hφ⟩
  -- Repackage the witness for the outermost empty diamond
  have hDiamondFinal :
      (⟪w⟫ ⊨[M] ♢ᶠ[[]] (↓ᶠ φ)) :=
    (Sat.Sat_diamond_nil (M := M)
      (w := w) (φ := ↓ᶠ φ)).2 ⟨q, hPastFinal⟩
  simpa [Formula.diamondPast] using hDiamondFinal

/-- Paper: Lemma 4.2.3(1). Past box collapses to present box).

A past-guarded box ↓ᶠ (□ᶠ↓[[l]] φ) collapses to a present box □ᶠ↓[[l]] φ.
This idempotency property shows that nested temporal operators can be simplified,
making proofs about temporal formulas more tractable.

See also: `pastDiamondBoxCollapsesToPresentBox`, `diamondPast_idem`. -/
theorem pastBoxCollapsesToPresentBox
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S)
    (hMem : w ∈ M.history.val) :
    (⟪w⟫ ⊨[M] ↓ᶠ (□ᶠ↓[[l]] φ)) →
      (⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) := by
  classical
  intro hPastBox
  -- Extract the predecessor world witnessing the past box
  obtain ⟨t, ht_mem, ht_place, hBox_t⟩ :=
    (Sat.past (M := M)
      (w := w) (φ := □ᶠ↓[[l]] φ)).1 hPastBox
  -- Transport the singleton past box from the predecessor to the current world
  have hBox :=
    sat_boxPast_of_predecessor (M := M)
      (w := w) (l := l) (φ := φ) hMem
      (t := t) ht_mem
      (by
        simpa [World.place, World.event, World.time, Formula.boxPast]
          using hBox_t)
  simpa [Formula.boxPast] using hBox

/-- Paper: Lemma 4.2.3(2). Past diamond-box collapses to present box).

A past-guarded diamond containing a box ♢ᶠ↓[[]] (□ᶠ↓[[l]] φ) collapses to a
present box □ᶠ↓[[l]] φ. This strengthens the previous collapsing lemma by showing
that even with an intervening diamond, the box structure is preserved.

See also: `pastBoxCollapsesToPresentBox`, `singletonBoxImpliesDiamond`. -/
theorem pastDiamondBoxCollapsesToPresentBox
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S)
    (hMem : w ∈ M.history.val) :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (□ᶠ↓[[l]] φ)) →
      (⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) := by
  classical
  intro hDiamond
  obtain ⟨q, hPastBox⟩ :=
    (Sat.Sat_diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ (□ᶠ↓[[l]] φ))).1 hDiamond
  obtain ⟨t, ht_mem, ht_place, hBox_t⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, w.time⟩)
      (φ := □ᶠ↓[[l]] φ)).1 hPastBox
  have hBox :=
    sat_boxPast_of_predecessor (M := M)
      (w := w) (l := l) (φ := φ) hMem
      (t := t) ht_mem
      (by
        simpa [World.place, World.event, World.time, Formula.boxPast]
          using hBox_t)
  exact hBox

/-! ## Corollary derivation for the liveness theorems -/

/-- From an end-of-time implication `(♢↓[]ψ) ⇒ G ⇒ ↕D` and a guard quorum
`□[l]G`, conclude the past-box corollary `(♢↓[]ψ) ⇒ □↓[l]D`. This packages
the derivation of the boxed corollaries of the liveness theorems. -/
theorem endValid_boxPast_of_imp_sometime
    (M : Model S P)
    {l : Signature.Value S} {ψ G D : Formula S}
    (hGuard : ⊨[M]□ᶠ[[l]]G)
    (hMain : ⊨[M](♢ᶠ↓[[]]ψ) ⇒ᶠ (G ⇒ᶠ ↕ᶠ D)) :
    ⊨[M](♢ᶠ↓[[]]ψ) ⇒ᶠ □ᶠ↓[[l]]D := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hGuardTop : ⟪wTop⟫ ⊨[M] □ᶠ[[l]] G := by simpa [wTop] using hGuard p
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hAnte
  obtain ⟨rProp, hPastAnte⟩ :=
    (Sat.diamond_nil (M := M) (w := wTop)
        (φ := Formula.past ψ)).1
      (by simpa [Formula.diamondPast] using hAnte)
  obtain ⟨O, hO, hAllG⟩ :=
    (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l) (φ := G)).1 hGuardTop
  refine
    (sat_box_singleton_exists (M := M)
        (w := wTop) (l := l) (φ := ↓ᶠ D)).2
      ⟨O, hO, ?_⟩
  intro q hqO
  set wq : World P (Signature.EventType S) := ⟨q, †, M.history.val⟩
  have hAnte_q : ⟪wq⟫ ⊨[M] ♢ᶠ↓[[]] ψ := by
    have hPastWitness :
        ⟪⟨rProp, †, wq.time⟩⟫ ⊨[M] Formula.past ψ := by
      simpa [wq, wTop, World.time] using hPastAnte
    have hDiamond :=
      (Sat.diamond_nil (M := M) (w := wq)
          (φ := Formula.past ψ)).2 ⟨rProp, hPastWitness⟩
    simpa [Formula.diamondPast] using hDiamond
  have hImp_q :
      ⟪wq⟫ ⊨[M] (♢ᶠ↓[[]] ψ) ⇒ᶠ (G ⇒ᶠ ↕ᶠ D) := by
    simpa [wq] using hMain q
  have hNext :=
    Sat.imp_elim (M := M) (w := wq)
      (φ := ♢ᶠ↓[[]] ψ) (ψ := G ⇒ᶠ ↕ᶠ D)
      hImp_q hAnte_q
  have hG_q : ⟪wq⟫ ⊨[M] G := by
    simpa [wq, wTop, World.time] using hAllG q hqO
  have hEventual :=
    Sat.imp_elim (M := M) (w := wq)
      (φ := G) (ψ := ↕ᶠ D) hNext hG_q
  have hPast :=
    (Sat.atEnd (M := M) (w := wq)
      (φ := Formula.past D)).1
      (by simpa [Formula.sometime] using hEventual)
  simpa using hPast

/-- The diamond corollary of `endValid_boxPast_of_imp_sometime`:
`(♢↓[]ψ) ⇒ ♢↓[]D`. -/
theorem endValid_diamondPast_of_imp_sometime
    (M : Model S P)
    {l : Signature.Value S} {ψ G D : Formula S}
    (hGuard : ⊨[M]□ᶠ[[l]]G)
    (hMain : ⊨[M](♢ᶠ↓[[]]ψ) ⇒ᶠ (G ⇒ᶠ ↕ᶠ D)) :
    ⊨[M](♢ᶠ↓[[]]ψ) ⇒ᶠ ♢ᶠ↓[[]]D := by
  classical
  have hBox :=
    endValid_boxPast_of_imp_sometime (M := M)
      (hGuard := hGuard) (hMain := hMain)
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hAnte
  have hBoxPast :=
    Sat.imp_elim (M := M) (w := wTop)
      (φ := ♢ᶠ↓[[]] ψ)
      (ψ := □ᶠ↓[[l]] D)
      (by simpa [wTop] using hBox p)
      hAnte
  have hDiamond :=
    singletonBoxImpliesDiamond (M := M) (w := wTop)
      (l := l) (φ := D) hBoxPast
  simpa [wTop] using hDiamond

end DiamondSection

end Logic
end ModalDistribution
