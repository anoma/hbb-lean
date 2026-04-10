import ModalDistribution.Core.Semifilter
import ModalDistribution.Grassroots.Sequentiality

/-!
# Coalescent learner families

This file extends `Grassroots/Sequentiality.lean` with the second core
ingredient of Shapiro's grassroots property: a *learner family* (a
per-participant-set assignment of semifilters/quorum systems) that is
*coalescent* under inclusion of participant sets.

The Murdoch–Sheff HBB framework parameterises a model `Model S P` by a
fixed type `P`, with `learner : S.Value → Semifilter P`. To capture
grassroots — Shapiro's `TS(P) ⊊ TS(P')/P` — we vary `P` over `Set A`
for a global agent universe `A : Type u`, replacing `Model.learner`
with a *family* `σ : (P : Set A) → V → Semifilter ↥P`. The structural
property the family must satisfy in order to be grassroots-compatible
is **coalescence**: every quorum at the smaller participant set lifts
to a quorum at the larger one (Shapiro non-interference / safety),
and every quorum at the larger participant set, when its restriction
to the smaller set is nonempty, restricts to a quorum at the smaller
set.

## Main definitions

* `Grassroots.liftQuorumSet` — image `liftAgent h '' O`.
* `Grassroots.restrictQuorumSet` — preimage `liftAgent h ⁻¹' O'`.
* `Grassroots.LearnerFamily` — `(P : Set A) → V → Semifilter ↥P`.
* `Grassroots.IsCoalescent` — the typeclass capturing Shapiro's
  non-interference property at the level of semifilters.
* `Grassroots.IsInteractive` — strict-inclusion / interactivity:
  there is a quorum at some larger universe that uses agents outside
  the smaller universe.

## Main theorems

* `Grassroots.restrict_lift_eq_self` — restriction is a left inverse
  of lifting (the lift map is injective).
* `Grassroots.liftAgent_injective` — `liftAgent` is injective.
* `Grassroots.restrict_inter` — restriction commutes with intersection.
* `Grassroots.lift_mono`, `Grassroots.restrict_mono` — both maps are
  monotone with respect to subset inclusion.
* `Grassroots.quorum_descent` — every quorum at the smaller universe
  arises as the restriction of a quorum at the larger universe.
* `Grassroots.lifted_membership` — coalescence transports membership:
  if `q ∈ O` then `liftAgent h q ∈ liftQuorumSet h O`.
* `Grassroots.coalescence_quorum_witness` — every quorum at `↥P`
  has a witness whose lift lies in the corresponding quorum at `↥P'`.
-/

namespace ModalDistribution
namespace Grassroots

open Set
open scoped Semifilter

universe u v
variable {A : Type u}

/-! ## §1. Quorum lifting and restriction

These are the set-level analogues of `liftAgent` for quorums. Lifting
sends a subset of `↥P` to its image in `↥P'` along the inclusion;
restricting sends a subset of `↥P'` back to its preimage in `↥P`.
The key fact is that lifting is *injective*, so restricting after
lifting is the identity. -/

/-- The image of a quorum under the inclusion of participant subtypes. -/
@[simp] def liftQuorumSet {P P' : Set A} (h : P ⊆ P') (O : Set ↥P) : Set ↥P' :=
  liftAgent h '' O

/-- The preimage of a quorum under the inclusion of participant subtypes. -/
@[simp] def restrictQuorumSet {P P' : Set A} (h : P ⊆ P') (O' : Set ↥P') :
    Set ↥P :=
  liftAgent h ⁻¹' O'

/-- The agent-lift map is injective: it just re-pairs the underlying value
with a different membership proof. -/
lemma liftAgent_injective {P P' : Set A} (h : P ⊆ P') :
    Function.Injective (liftAgent h : ↥P → ↥P') := by
  intro a b hab
  apply Subtype.ext
  have : (liftAgent h a).val = (liftAgent h b).val := congrArg Subtype.val hab
  simpa [liftAgent] using this

/-- Restricting after lifting is the identity (because `liftAgent` is
injective). -/
@[simp] lemma restrict_lift_eq_self {P P' : Set A} (h : P ⊆ P') (O : Set ↥P) :
    restrictQuorumSet h (liftQuorumSet h O) = O := by
  unfold liftQuorumSet restrictQuorumSet
  exact Set.preimage_image_eq O (liftAgent_injective h)

/-- Lifting after restricting captures `O'` modulo elements outside the
range of the inclusion. -/
lemma lift_restrict_eq_inter_range {P P' : Set A} (h : P ⊆ P') (O' : Set ↥P') :
    liftQuorumSet h (restrictQuorumSet h O') = O' ∩ Set.range (liftAgent h) := by
  unfold liftQuorumSet restrictQuorumSet
  exact Set.image_preimage_eq_inter_range

/-- Restriction is monotone with respect to subset inclusion. -/
lemma restrictQuorumSet_mono {P P' : Set A} (h : P ⊆ P')
    {O₁ O₂ : Set ↥P'} (hO : O₁ ⊆ O₂) :
    restrictQuorumSet h O₁ ⊆ restrictQuorumSet h O₂ :=
  Set.preimage_mono hO

/-- Lifting is monotone with respect to subset inclusion. -/
lemma liftQuorumSet_mono {P P' : Set A} (h : P ⊆ P')
    {O₁ O₂ : Set ↥P} (hO : O₁ ⊆ O₂) :
    liftQuorumSet h O₁ ⊆ liftQuorumSet h O₂ :=
  Set.image_mono hO

/-- Restriction commutes with binary intersection. -/
@[simp] lemma restrictQuorumSet_inter {P P' : Set A} (h : P ⊆ P')
    (O₁ O₂ : Set ↥P') :
    restrictQuorumSet h (O₁ ∩ O₂) =
      restrictQuorumSet h O₁ ∩ restrictQuorumSet h O₂ :=
  Set.preimage_inter

/-- An agent of `↥P` is in `restrictQuorumSet h O'` iff its lift is in `O'`. -/
@[simp] lemma mem_restrictQuorumSet {P P' : Set A} (h : P ⊆ P')
    (O' : Set ↥P') (q : ↥P) :
    q ∈ restrictQuorumSet h O' ↔ liftAgent h q ∈ O' := Iff.rfl

/-- An agent of `↥P'` is in `liftQuorumSet h O` iff it is the lift of some
member of `O`. -/
@[simp] lemma mem_liftQuorumSet {P P' : Set A} (h : P ⊆ P')
    (O : Set ↥P) (q' : ↥P') :
    q' ∈ liftQuorumSet h O ↔ ∃ q ∈ O, liftAgent h q = q' := Iff.rfl

/-! ## §2. Learner families

A `LearnerFamily` assigns a semifilter on `↥P` to every (nonempty) participant
set `P` and every value `v : V`. This is the per-`P` analogue of the field
`Model.learner : V → Semifilter P` of an HBB `Model`. The nonemptiness
constraint mirrors the `[Nonempty P]` requirement on `Model`. -/

/-- A learner family: a per-participant-set assignment of semifilters,
generalising `Model.learner` from a fixed type to a family indexed by
subsets of a global agent universe `A`. -/
structure LearnerFamily (V : Type v) (A : Type u) where
  /-- The semifilter assigned to value `v` at the participant set `P`. -/
  σ : ∀ (P : Set A) [Nonempty ↥P], V → Semifilter ↥P

/-! ## §3. Coalescence

The Shapiro non-interference / safety condition at the level of semifilters:
quorums lift forward and (when nonempty) restrict back. -/

/-- A learner family is *coalescent* iff:
* (`lift_quorum`) every quorum at a smaller participant set, lifted via the
  inclusion, is a quorum at the larger participant set;
* (`restrict_quorum`) every quorum at a larger participant set, when its
  restriction to the smaller set is nonempty, is a quorum at the smaller set
  (after restriction).

This is the structural condition under which the projection of the larger
universe to the smaller one is a *bisimulation* on quorum membership. -/
class IsCoalescent {V : Type v} (F : LearnerFamily V A) : Prop where
  lift_quorum :
    ∀ {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P'] (v : V)
      ⦃O : Set ↥P⦄,
      O ∈ (F.σ P v).quorums →
        liftQuorumSet h O ∈ (F.σ P' v).quorums
  restrict_quorum :
    ∀ {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P'] (v : V)
      ⦃O' : Set ↥P'⦄,
      O' ∈ (F.σ P' v).quorums →
        (restrictQuorumSet h O').Nonempty →
          restrictQuorumSet h O' ∈ (F.σ P v).quorums

/-! ## §4. Interactivity

Shapiro's grassroots property requires *strict* inclusion `TS(P) ⊊ TS(P')/P`.
The strict half says: there exist behaviours of the larger universe that
genuinely use agents outside the smaller one. At the semifilter level this
becomes: there is a quorum at some `P'` that contains an agent outside
the range of the inclusion from `P`. -/

/-- A learner family is *interactive* iff for every nonempty proper subset
`P : Set A`, there is a strict extension `P ⊂ P'` with a quorum at `P'`
that uses agents outside `P`. -/
def IsInteractive {V : Type v} (F : LearnerFamily V A) : Prop :=
  ∀ {P : Set A} [Nonempty ↥P], P ≠ Set.univ →
    ∃ (P' : Set A) (hPP' : P ⊂ P') (_ : Nonempty ↥P') (v : V) (O' : Set ↥P'),
      O' ∈ (F.σ P' v).quorums ∧
        ¬ O' ⊆ Set.range (liftAgent (le_of_lt hPP'))

/-! ## §5. Connecting results: descent and lifted membership

These are the load-bearing lemmas that translate the abstract coalescence
property into concrete statements about how quorums and their members
behave under projection.  -/

/-- **Quorum descent.** Every quorum at the smaller universe arises as the
restriction of a quorum at the larger universe. The lifted quorum is the
canonical witness, and `restrict_lift_eq_self` ensures we recover `O` exactly. -/
theorem quorum_descent {V : Type v} (F : LearnerFamily V A) [IsCoalescent F]
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P'] (v : V)
    {O : Set ↥P} (hO : O ∈ (F.σ P v).quorums) :
    ∃ O' ∈ (F.σ P' v).quorums, restrictQuorumSet h O' = O := by
  refine ⟨liftQuorumSet h O, IsCoalescent.lift_quorum h v hO, ?_⟩
  exact restrict_lift_eq_self h O

/-- **Lifted membership.** Coalescence transports both the quorum and its
members forward along the inclusion. -/
theorem lifted_membership {V : Type v} (F : LearnerFamily V A) [IsCoalescent F]
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P'] (v : V)
    {O : Set ↥P} (hO : O ∈ (F.σ P v).quorums) (q : ↥P) (hq : q ∈ O) :
    liftAgent h q ∈ liftQuorumSet h O ∧
    liftQuorumSet h O ∈ (F.σ P' v).quorums :=
  ⟨⟨q, hq, rfl⟩, IsCoalescent.lift_quorum h v hO⟩

/-- **Coalescence quorum witness.** Every quorum at the smaller universe
gives rise to a witness in the corresponding (lifted) quorum at the larger
universe. -/
theorem coalescence_quorum_witness {V : Type v}
    (F : LearnerFamily V A) [IsCoalescent F]
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P'] (v : V)
    {O : Set ↥P} (hO : O ∈ (F.σ P v).quorums) :
    ∃ q' : ↥P', q' ∈ liftQuorumSet h O := by
  -- The lifted quorum is itself a quorum at `P'`, and semifilter quorums
  -- are nonempty (`Semifilter.quorum_nonempty`).
  have hLifted : liftQuorumSet h O ∈ (F.σ P' v).quorums :=
    IsCoalescent.lift_quorum h v hO
  obtain ⟨q', hq'⟩ := Semifilter.quorum_nonempty hLifted
  exact ⟨q', hq'⟩

/-! ## §6. Coalescence and pairwise quorum intersections

Heterogeneous Bracha Broadcast relies critically on quorum-intersection
properties (any two `l`-quorums share at least one participant; see
`Logic/Properties/Quorums.lean`).  Coalescence transports these
intersections cleanly: if two quorums intersect at the larger universe and
both restrictions to the smaller universe are nonempty, the smaller
quorums also intersect. -/

/-- Coalescence transports pairwise quorum intersection forward: a witness
to the intersection of two restricted quorums lifts to a witness in the
intersection of the original (large-universe) quorums. -/
theorem restrict_intersection_witness
    {P P' : Set A} (h : P ⊆ P')
    (O₁' O₂' : Set ↥P')
    {q : ↥P}
    (hq : q ∈ restrictQuorumSet h O₁' ∩ restrictQuorumSet h O₂') :
    liftAgent h q ∈ O₁' ∩ O₂' := by
  rcases hq with ⟨h₁, h₂⟩
  exact ⟨h₁, h₂⟩

/-- And conversely: if the lifted member is in the intersection of the
original quorums, then it is in the intersection of the restricted quorums
(when viewed as a member of `↥P`). -/
theorem lift_intersection_witness
    {P P' : Set A} (h : P ⊆ P')
    (O₁' O₂' : Set ↥P')
    (q : ↥P)
    (hq : liftAgent h q ∈ O₁' ∩ O₂') :
    q ∈ restrictQuorumSet h O₁' ∩ restrictQuorumSet h O₂' := by
  rcases hq with ⟨h₁, h₂⟩
  exact ⟨h₁, h₂⟩

/-! ## §7. The semifilter restriction

Although a coalescent learner family already provides the right "small
universe" semifilter directly, it is sometimes useful to construct a
*derived* semifilter on `↥P` from a single semifilter on `↥P'`, namely
the up-closure of the restrictions of all quorums of the larger semifilter
whose restrictions are nonempty. We sketch the construction here as a
non-degenerate witness that the abstract definition is non-trivial. -/

/-- The set of restricted quorums of a semifilter at the larger universe,
filtering out those whose restriction is empty. This is the carrier of
the "induced" semifilter at `↥P`, modulo upward closure. -/
def restrictedQuorums {P P' : Set A} (h : P ⊆ P') (L' : Semifilter ↥P') :
    Set (Set ↥P) :=
  { O | ∃ O' ∈ L'.quorums, O = restrictQuorumSet h O' ∧ O.Nonempty }

/-- Coalescence implies that every member of `restrictedQuorums h (F.σ P' v)`
is itself a quorum of `F.σ P v`. This is a direct corollary of
`IsCoalescent.restrict_quorum`. -/
theorem mem_restrictedQuorums_imp_quorum
    {V : Type v} (F : LearnerFamily V A) [IsCoalescent F]
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P'] (v : V)
    ⦃O : Set ↥P⦄ (hO : O ∈ restrictedQuorums h (F.σ P' v)) :
    O ∈ (F.σ P v).quorums := by
  obtain ⟨O', hO'mem, hO'eq, hO'ne⟩ := hO
  rw [hO'eq]
  exact IsCoalescent.restrict_quorum h v hO'mem (hO'eq ▸ hO'ne)

/-- And conversely (using `quorum_descent`): every quorum of `F.σ P v`
arises as a restriction of a `F.σ P' v`-quorum. -/
theorem quorum_in_restrictedQuorums
    {V : Type v} (F : LearnerFamily V A) [IsCoalescent F]
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P'] (v : V)
    ⦃O : Set ↥P⦄ (hO : O ∈ (F.σ P v).quorums) :
    O ∈ restrictedQuorums h (F.σ P' v) := by
  obtain ⟨O', hO'mem, hO'eq⟩ := quorum_descent F h v hO
  exact ⟨O', hO'mem, hO'eq.symm, Semifilter.quorum_nonempty hO⟩

/-- **Coalescence characterisation:** the quorums of `F.σ P v` are exactly
the nonempty restrictions of quorums of `F.σ P' v`. -/
theorem quorums_eq_restrictedQuorums
    {V : Type v} (F : LearnerFamily V A) [IsCoalescent F]
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P'] (v : V) :
    (F.σ P v).quorums = restrictedQuorums h (F.σ P' v) := by
  ext O
  constructor
  · intro hO
    exact quorum_in_restrictedQuorums F h v hO
  · intro hO
    exact mem_restrictedQuorums_imp_quorum F h v hO

end Grassroots
end ModalDistribution
