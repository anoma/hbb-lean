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
  have hAcc : t ≪ w := by
    simpa [World.accessible, World.time] using ht_mem
  -- Transitivity of accessibility (Proposition 3.4.5).
  have hSubset_t :
      World.time t ⊆ w.time := fun x hx =>
    accessible_trans (H := M.history)
      (hW := M.time_le_of_mem hMem) (h₂ := hx) (h₁ := hAcc)
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
  -- Unfold the two nested diamonds down to the innermost witness `t'`.
  obtain ⟨p, hPast⟩ :=
    (Sat.diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ (♢ᶠ↓[[]] φ))).1
      (by simpa [Formula.diamondPast] using hDiamond)
  obtain ⟨t, ht_mem, ht_place, hDiamond_t⟩ :=
    (Sat.past (M := M)
      (w := ⟨p, †, w.time⟩)
      (φ := ♢ᶠ↓[[]] φ)).1 hPast
  obtain ⟨q, hPastφ⟩ :=
    (Sat.diamond_nil (M := M)
      (w := t)
      (φ := ↓ᶠ φ)).1
      (by simpa [Formula.diamondPast] using hDiamond_t)
  obtain ⟨t', ht'_mem, ht'_place, hφ⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, t.time⟩) (φ := φ)).1 hPastφ
  -- Transitivity of accessibility (Proposition 3.4.5) puts `t'` in `w.time`.
  have hAcc' : t' ≪ w :=
    accessible_trans (H := M.history)
      (hW := M.time_le_of_mem hMem)
      (h₂ := by simpa [World.accessible, World.time] using ht'_mem)
      (h₁ := by simpa [World.accessible, World.time] using ht_mem)
  -- Repackage the witness for the outer empty diamond.
  have hPastFinal :
      (⟪⟨q, †, w.time⟩⟫ ⊨[M] ↓ᶠ φ) :=
    (Sat.past (M := M)
      (w := ⟨q, †, w.time⟩)
      (φ := φ)).2
      ⟨t', by simpa [World.accessible, World.time] using hAcc',
        by simpa [World.place] using ht'_place, hφ⟩
  simpa [Formula.diamondPast] using
    (Sat.diamond_nil (M := M)
      (w := w) (φ := ↓ᶠ φ)).2 ⟨q, hPastFinal⟩

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
    (Sat.diamond_nil (M := M)
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

/-- Paper: Lemma 6.4.4. `\atd{l}` of `\sometime φ` coincides
with `\atddot{l} φ`. -/
theorem box_sometime_iff_boxPast
    (M : Model S P)
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
  refine Sat.imp_intro (M := M) (w := wTop) ?_
  intro hAnte
  -- The omniscient antecedent transports to every participant.
  obtain ⟨rProp, hPastAnte⟩ :=
    (Sat.diamond_nil (M := M) (w := wTop)
        (φ := Formula.past ψ)).1
      (by simpa [Formula.diamondPast] using hAnte)
  have hAnteGlobal : ⊨[M]♢ᶠ↓[[]]ψ := by
    intro q
    have hDiamond :=
      (Sat.diamond_nil (M := M) (w := ⟨q, †, M.history.val⟩)
          (φ := Formula.past ψ)).2
        ⟨rProp, by simpa [wTop, World.time] using hPastAnte⟩
    simpa [Formula.diamondPast] using hDiamond
  -- Every member of the guard quorum eventually sees `D`.
  have hBoxSometime : ⊨[M]□ᶠ[[l]](↕ᶠ D) := by
    intro q
    obtain ⟨O, hO, hAllG⟩ :=
      (sat_box_singleton_exists (M := M)
          (w := ⟨q, †, M.history.val⟩) (l := l) (φ := G)).1 (hGuard q)
    refine
      (sat_box_singleton_exists (M := M)
          (w := ⟨q, †, M.history.val⟩) (l := l) (φ := ↕ᶠ D)).2
        ⟨O, hO, ?_⟩
    intro r hrO
    exact
      Sat.imp_elim (M := M) (w := ⟨r, †, M.history.val⟩)
        (φ := G) (ψ := ↕ᶠ D)
        (Sat.imp_elim (M := M) (w := ⟨r, †, M.history.val⟩)
          (φ := ♢ᶠ↓[[]]ψ) (ψ := G ⇒ᶠ ↕ᶠ D)
          (hMain r) (hAnteGlobal r))
        (hAllG r hrO)
  -- Lemma 6.4.4 turns the eventualities into a past box.
  simpa [wTop] using
    (box_sometime_iff_boxPast (M := M) (φ := D) (l := l)).1
      hBoxSometime p

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
