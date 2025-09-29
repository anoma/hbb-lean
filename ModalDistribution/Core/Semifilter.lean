import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic
import ModalDistribution.Core.History

open Set

/-!
# Semifilter Structures

This file introduces semifilters as the set-theoretic foundation for quorums, following
Notation 3.2.1 and Definition 3.2.2 of the HBB paper. Semifilters capture nonempty,
up-closed families of pairwise intersecting quorums on a set of participants.

## Main definitions

* `Semifilter.intersects` (`≬`): quorum-intersection predicate from Notation 3.2.1.
* `Semifilter`: structure of nonempty up-closed pairwise-intersecting families of quorums.

## References

* Notation 3.2.1 in "Logical Analysis of Heterogeneous Broadcasts".
* Definition 3.2.2 in "Logical Analysis of Heterogeneous Broadcasts".
-/

namespace Semifilter

variable {P : Type*}

/-- Notation 3.2.1: `O ≬ O'` when two quorums intersect (their intersection is nonempty). -/
@[simp] def intersects (O O' : Set P) : Prop := (O ∩ O').Nonempty

end Semifilter

scoped[Semifilter] infix:50 " ≬ " => Semifilter.intersects

open scoped Semifilter

/-- Definition 3.2.2: A semifilter is a nonempty up-closed family of pairwise
intersecting quorums over a participant set `P`. -/
structure Semifilter (P : Type*) where
  /-- Carrier set of quorums. -/
  quorums : Set (Set P)
  /-- Definition 3.2.2(1): the family of quorums is nonempty. -/
  nonempty : quorums.Nonempty
  /-- Definition 3.2.2(2): the family is up-closed under supersets inside `P`. -/
  upwardClosed : ∀ ⦃O O' : Set P⦄, O ∈ quorums → O ⊆ O' → O' ∈ quorums
  /-- Definition 3.2.2(3): quorums pairwise intersect. -/
  pairwiseInter : ∀ ⦃O O' : Set P⦄, O ∈ quorums → O' ∈ quorums → O ≬ O'

namespace Semifilter

variable {P : Type*}

/-/ Intersections are symmetric. -/
lemma intersects_comm {O O' : Set P} :
    (O ≬ O') ↔ (O' ≬ O) := by
  classical
  simp [Semifilter.intersects, inter_comm]

/-- A quorum intersects itself exactly when it is nonempty. -/
lemma intersects_self_iff_nonempty {O : Set P} :
    (O ≬ O) ↔ O.Nonempty := by
  classical
  simp [Semifilter.intersects, inter_self]

/-- Intersections distribute over a shared witness. -/
lemma intersects_of_mem {p : P} {O O' : Set P}
    (hpO : p ∈ O) (hpO' : p ∈ O') :
    O ≬ O' := by
  classical
  refine ⟨p, ?_⟩
  exact ⟨hpO, hpO'⟩

/-- Intersections are witnessed precisely by shared members. -/
lemma intersects_iff {O O' : Set P} :
    (O ≬ O') ↔ ∃ p, p ∈ O ∧ p ∈ O' := by
  classical
  constructor
  · intro hint
    rcases hint with ⟨p, hp⟩
    exact ⟨p, hp.1, hp.2⟩
  · rintro ⟨p, hpO, hpO'⟩
    exact intersects_of_mem (P := P) hpO hpO'

/-- Intersecting quorums are themselves nonempty on the left. -/
lemma intersects_nonempty_left {O O' : Set P} :
    O ≬ O' → O.Nonempty :=
  by
    intro hint
    rcases hint with ⟨p, hp⟩
    exact ⟨p, hp.1⟩

/-- Intersecting quorums are themselves nonempty on the right. -/
lemma intersects_nonempty_right {O O' : Set P} :
    O ≬ O' → O'.Nonempty :=
  by
    intro hint
    rcases hint with ⟨p, hp⟩
    exact ⟨p, hp.2⟩

/-- Intersections are monotone in their arguments. -/
lemma intersects_mono {O O' O₁ O₂ : Set P}
    (h₁ : O ⊆ O₁) (h₂ : O' ⊆ O₂) (hint : O ≬ O') :
    O₁ ≬ O₂ := by
  classical
  rcases hint with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  exact ⟨h₁ hp.1, h₂ hp.2⟩

/-- Definition 3.2.2(2): Supersets of quorums remain quorums. -/
lemma upwards_of_subset {L : Semifilter P} {O O' : Set P}
    (hO : O ∈ L.quorums) (h_subset : O ⊆ O') :
    O' ∈ L.quorums := by
  exact L.upwardClosed hO h_subset

/-- Definition 3.2.2(3): Quorums intersect pairwise. -/
lemma intersects_mem {L : Semifilter P} {O O' : Set P}
    (hO : O ∈ L.quorums) (hO' : O' ∈ L.quorums) :
    O ≬ O' := by
  exact L.pairwiseInter hO hO'

/-- Definition 3.2.2(1): Every quorum in a semifilter is nonempty. -/
lemma quorum_nonempty {L : Semifilter P} {O : Set P}
    (hO : O ∈ L.quorums) :
    O.Nonempty := by
  have := L.pairwiseInter hO hO
  simpa [intersects_self_iff_nonempty] using this

/-- Any two quorums in a semifilter intersect. -/
lemma intersects_of_mem_quorums {L : Semifilter P} {O₁ O₂ : Set P}
    (h₁ : O₁ ∈ L.quorums) (h₂ : O₂ ∈ L.quorums) :
    O₁ ≬ O₂ :=
  L.pairwiseInter h₁ h₂

/-- Definition 3.2.2(1): A semifilter contains at least one quorum. -/
lemma exists_quorum (L : Semifilter P) :
    ∃ O : Set P, O ∈ L.quorums := by
  exact L.nonempty

/-- If a property cannot be witnessed on every quorum, some quorum forces its negation. -/
lemma exists_quorum_forall_not {L : Semifilter P} {R : P → Prop}
    (h : ¬ ∀ O ∈ L.quorums, ∃ q ∈ O, R q) :
    ∃ O ∈ L.quorums, ∀ q ∈ O, ¬ R q := by
  classical
  have : ∃ O ∈ L.quorums, ¬ (∃ q ∈ O, R q) := by
    simpa using not_forall.mp h
  rcases this with ⟨O, hO, hNone⟩
  refine ⟨O, hO, ?_⟩
  intro q hq
  have : ¬ (R q) := by
    have hno := not_exists.mp hNone q
    exact (not_and.mp hno) hq
  simpa using this

/-- Intersections grow monotonically with supersets on the left. -/
lemma intersects_mono_left {O O' O'' : Set P}
    (h_subset : O ⊆ O') (hint : O ≬ O'') :
    O' ≬ O'' := by
  classical
  have hmono :=
    intersects_mono (P := P) (O := O) (O' := O'') (O₁ := O') (O₂ := O'')
      h_subset subset_rfl hint
  simpa using hmono

/-- Intersections grow monotonically with supersets on the right. -/
lemma intersects_mono_right {O O' O'' : Set P}
    (h_subset : O' ⊆ O'') (hint : O ≬ O') :
    O ≬ O'' := by
  classical
  have hmono :=
    intersects_mono (P := P) (O := O) (O' := O') (O₁ := O) (O₂ := O'')
      subset_rfl h_subset hint
  simpa using hmono

/-- The empty set fails to intersect any quorum. -/
@[simp] lemma intersects_empty_left {O : Set P} :
    (∅ : Set P) ≬ O ↔ False := by
  classical
  simp [Semifilter.intersects]

/-- Any quorum fails to intersect the empty set. -/
@[simp] lemma intersects_empty_right {O : Set P} :
    O ≬ (∅ : Set P) ↔ False := by
  classical
  simp [Semifilter.intersects]

/-- Extensionality: semifilters coincide when they have the same quorums. -/
@[ext] lemma ext {L₁ L₂ : Semifilter P}
    (h : ∀ O : Set P, O ∈ L₁.quorums ↔ O ∈ L₂.quorums) :
    L₁ = L₂ := by
  classical
  cases L₁ with
  | mk Q₁ n₁ u₁ p₁ =>
    cases L₂ with
    | mk Q₂ n₂ u₂ p₂ =>
      have hQ : Q₁ = Q₂ := by
        ext O
        exact (h O)
      subst hQ
      have : n₁ = n₂ := Subsingleton.elim _ _
      subst this
      have : u₁ = u₂ := Subsingleton.elim _ _
      subst this
      have : p₁ = p₂ := Subsingleton.elim _ _
      subst this
      rfl

/-! ### N-way intersection notation (Lemma 4.1.1) -/

variable {ι : Type*}

/-- A family of sets indexed by `s` belongs to a semifilter when every member does. -/
def familyQuorums (L : Semifilter P) (s : Finset ι) (F : ι → Set P) : Prop :=
  ∀ i ∈ s, F i ∈ L.quorums

/-- Every empty index family vacuously belongs to a semifilter. -/
lemma familyQuorums_empty (L : Semifilter P) (F : ι → Set P) :
    familyQuorums L (∅ : Finset ι) F := by
  intro i hi
  cases hi

/-- Membership for finite families reduces to the head and tail quorums. -/
lemma familyQuorums_insert [DecidableEq ι]
    (L : Semifilter P) {s : Finset ι} {i : ι} {F : ι → Set P} :
    familyQuorums L (insert i s) F ↔
      F i ∈ L.quorums ∧ familyQuorums L s F := by
  classical
  constructor
  · intro h
    refine ⟨h i (by simp), ?_⟩
    intro j hj
    exact h j (by simp [Finset.mem_insert, hj])
  · rintro ⟨hi, hs⟩ j hj
    rcases Finset.mem_insert.mp hj with hji | hjmem
    · subst hji
      exact hi
    · exact hs j hjmem

/-- Finite intersection of an indexed family used in quorum statements. -/
def familyInter (s : Finset ι) (F : ι → Set P) : Set P :=
  ⋂ i ∈ s, F i

/-- Families of quorums restrict along subset indices. -/
lemma familyQuorums_mono_subset
    (L : Semifilter P) {s t : Finset ι} {F : ι → Set P}
    (hs : s ⊆ t) :
    familyQuorums L t F → familyQuorums L s F :=
  by
    intro hF i hi
    exact hF i (hs hi)

/-- Nonemptiness of the family intersection. Matches “n-way quorum intersection is
nonempty” in Lemma 4.1.1(2). -/
def familyInterNonempty (s : Finset ι) (F : ι → Set P) : Prop :=
  (familyInter (P := P) s F).Nonempty

/-- Witnessed property over the intersection. Captures Lemma 4.1.1(1) in set form. -/
def familyInterWitness (s : Finset ι) (F : ι → Set P) (R : P → Prop) : Prop :=
  ∃ p, p ∈ familyInter (P := P) s F ∧ R p

/-- All quorum choices indexed by `s` yield nonempty intersections. -/
def allFamilyInterNonempty (L : Semifilter P) (s : Finset ι) : Prop :=
  ∀ F, familyQuorums (P := P) L s F → familyInterNonempty (P := P) s F

/-- All quorum choices indexed by `s` carry a witness for `R`. -/
def allFamilyInterWitness (L : Semifilter P) (s : Finset ι) (R : P → Prop) : Prop :=
  ∀ F, familyQuorums (P := P) L s F → familyInterWitness (P := P) s F R

/-- Sequential quorum intersections: every indexed family of quorums meets at a
participant sequential in the ambient history. (Paper Lemma 4.1.1 specialized to
`seq`.) -/
def sequentialFamilyIntersections
    {P Event : Type*} (H : History P Event)
    (L : Semifilter P) (s : Finset ι) : Prop :=
  allFamilyInterWitness (P := P) (ι := ι) L s
    (fun p => isSequential (P := P) (Event := Event) p H.val)

/-- Nonempty quorum intersections specialized to finite index sets. -/
def nonemptyFamilyIntersections (L : Semifilter P) (s : Finset ι) : Prop :=
  allFamilyInterNonempty (P := P) (ι := ι) L s

/-- Lemma 4.1.1(1): set-theoretic form. -/
lemma familyInterWitness_iff
    (L : Semifilter P) (s : Finset ι) (R : P → Prop) :
    allFamilyInterWitness (P := P) (ι := ι) L s R ↔
      ∀ F, familyQuorums (P := P) (ι := ι) L s F →
        ∃ p, p ∈ familyInter (P := P) s F ∧ R p := by
  classical
  rfl

/-- The intersection over an empty index set is the full participant set. -/
@[simp] lemma familyInter_empty (F : ι → Set P) :
    familyInter (P := P) (∅ : Finset ι) F = Set.univ := by
  classical
  ext p
  simp [familyInter]

/-- Intersections over singletons collapse to their unique quorum. -/
@[simp] lemma familyInter_singleton (i : ι) (F : ι → Set P) :
    familyInter (P := P) ({i} : Finset ι) F = F i := by
  classical
  ext p
  simp [familyInter]

/-- Elements of a family intersection reside in each quorum indexed by the set. -/
lemma familyInter_subset {s : Finset ι} {F : ι → Set P} {p : P} :
    p ∈ familyInter (P := P) s F → ∀ i ∈ s, p ∈ F i := by
  classical
  intro hp i hi
  have := hp
  simp [familyInter] at this
  exact this i hi

/-- Pointwise enlargement of the indexed family enlarges the intersection. -/
lemma familyInter_subset_of_pointwise
    {s : Finset ι} {F G : ι → Set P}
    (hFG : ∀ i ∈ s, F i ⊆ G i) :
    familyInter (P := P) s F ⊆ familyInter (P := P) s G := by
  classical
  intro p hp
  have hmem : ∀ i ∈ s, p ∈ F i :=
    familyInter_subset (P := P) (s := s) (F := F) hp
  have hmem' : ∀ i ∈ s, p ∈ G i := by
    intro i hi
    exact hFG i hi (hmem i hi)
  simpa [familyInter] using hmem'

/-- Lemma 4.1.1(2): nonempty intersections are equivalent to the nonempty predicate. -/
lemma familyInterNonempty_iff
    (L : Semifilter P) (s : Finset ι) :
    nonemptyFamilyIntersections (P := P) (ι := ι) L s ↔
      ∀ F, familyQuorums (P := P) (ι := ι) L s F →
        (familyInter (P := P) s F).Nonempty := by
  classical
  rfl

/-- Lemma 4.1.1(3): witnessed intersections imply nonempty intersections. -/
lemma familyInterWitness_imp_nonempty
    (L : Semifilter P) (s : Finset ι) (R : P → Prop) :
    allFamilyInterWitness (P := P) (ι := ι) L s R →
      nonemptyFamilyIntersections (P := P) (ι := ι) L s := by
  classical
  intro h
  refine (familyInterNonempty_iff (P := P) (ι := ι) L s).2 ?_
  intro F hF
  obtain ⟨p, hp, _⟩ := (familyInterWitness_iff (P := P) (ι := ι) L s R).mp h F hF
  exact ⟨p, hp⟩

/-- Adding quorums to the index set preserves the witness property. -/
lemma familyInterWitness_mono_index
    {L : Semifilter P} {s t : Finset ι} (hst : s ⊆ t) (R : P → Prop) :
    allFamilyInterWitness (P := P) (ι := ι) L t R →
      allFamilyInterWitness (P := P) (ι := ι) L s R := by
  classical
  intro h
  obtain ⟨base, hbase⟩ := L.nonempty
  refine (familyInterWitness_iff (P := P) (ι := ι) L s R).2 ?_
  intro F hF
  classical
  let G : ι → Set P := fun i => if hi : i ∈ s then F i else base
  have hG : familyQuorums (P := P) (ι := ι) L t G := by
    intro i hi
    by_cases his : i ∈ s
    · have : F i ∈ L.quorums := hF i his
      simpa [G, his] using this
    · simp [G, his, hbase]
  obtain ⟨p, hpInt, hRp⟩ :=
    (familyInterWitness_iff (P := P) (ι := ι) L t R).mp h G hG
  have hp_all : ∀ i ∈ t, p ∈ G i := by
    simpa [familyInter] using hpInt
  have hpF : ∀ i ∈ s, p ∈ F i := by
    intro i hi
    have : p ∈ G i := hp_all i (hst hi)
    simpa [G, hi] using this
  have hp_s : p ∈ familyInter (P := P) s F := by
    simpa [familyInter] using hpF
  exact ⟨p, hp_s, hRp⟩

/-- Strengthening the property preserves witnesses. -/
lemma familyInterWitness_mono_property
    {L : Semifilter P} {s : Finset ι} {R R' : P → Prop}
    (hRR' : ∀ p, R p → R' p) :
    allFamilyInterWitness (P := P) (ι := ι) L s R →
      allFamilyInterWitness (P := P) (ι := ι) L s R' := by
  classical
  intro h
  refine (familyInterWitness_iff (P := P) (ι := ι) L s R').2 ?_
  intro F hF
  obtain ⟨p, hp, hRp⟩ := (familyInterWitness_iff (P := P) (ι := ι) L s R).mp h F hF
  exact ⟨p, hp, hRR' p hRp⟩

/-- Two-way intersections: special case of Lemma 4.1.1 for pairs. -/
lemma twoWayIntersections
    (L : Semifilter P) (R : P → Prop)
    (O₁ O₂ : Set P)
    (h₁ : O₁ ∈ L.quorums) (h₂ : O₂ ∈ L.quorums)
    (hw : allFamilyInterWitness (P := P) (ι := Bool) L (Finset.univ : Finset Bool) R) :
    (O₁ ∩ O₂).Nonempty := by
  classical
  let F : Bool → Set P := fun b => cond b O₂ O₁
  have hF : familyQuorums (P := P) (ι := Bool) L (Finset.univ : Finset Bool) F := by
    intro b _
    cases b <;> simp [F, h₁, h₂]
  obtain ⟨p, hp, _⟩ :=
    (familyInterWitness_iff (P := P) (ι := Bool) L (Finset.univ : Finset Bool) R).mp hw F hF
  have hp_all : ∀ b ∈ (Finset.univ : Finset Bool), p ∈ F b := by
    simpa [familyInter] using hp
  have hp₁ : p ∈ O₁ := by
    simpa [F] using hp_all false (by simp)
  have hp₂ : p ∈ O₂ := by
    simpa [F] using hp_all true (by simp)
  refine ⟨p, ?_⟩
  exact ⟨hp₁, hp₂⟩

/-- Nonempty two-way intersections: specialising to `True`. -/
lemma twoWayIntersections_nonempty
    (L : Semifilter P)
    (O₁ O₂ : Set P)
    (h₁ : O₁ ∈ L.quorums) (h₂ : O₂ ∈ L.quorums)
    (hw : nonemptyFamilyIntersections (P := P) (ι := Bool) L (Finset.univ : Finset Bool)) :
    (O₁ ∩ O₂).Nonempty := by
  classical
  let F : Bool → Set P := fun b => cond b O₂ O₁
  have hF : familyQuorums (P := P) (ι := Bool) L (Finset.univ : Finset Bool) F := by
    intro b _
    cases b <;> simp [F, h₁, h₂]
  obtain ⟨p, hp⟩ :=
    (familyInterNonempty_iff (P := P) (ι := Bool) L (Finset.univ : Finset Bool)).mp hw F hF
  have hp_all : ∀ b ∈ (Finset.univ : Finset Bool), p ∈ F b := by
    simpa [familyInter] using hp
  have hp₁ : p ∈ O₁ := by
    simpa [F] using hp_all false (by simp)
  have hp₂ : p ∈ O₂ := by
    simpa [F] using hp_all true (by simp)
  refine ⟨p, ?_⟩
  exact ⟨hp₁, hp₂⟩

/-- Three-way intersections: set-level version for size-three index sets. -/
lemma threeWayIntersections
    (L : Semifilter P) (R : P → Prop)
    (O₁ O₂ O₃ : Set P)
    (h₁ : O₁ ∈ L.quorums) (h₂ : O₂ ∈ L.quorums) (h₃ : O₃ ∈ L.quorums)
    (hw : allFamilyInterWitness (P := P) (ι := Fin 3) L (Finset.univ : Finset (Fin 3)) R) :
    (O₁ ∩ O₂ ∩ O₃).Nonempty := by
  classical
  haveI := Classical.decEq (Fin 3)
  let F : Fin 3 → Set P := fun i =>
    Fin.cases O₁ (fun j => Fin.cases O₂ (fun _ => O₃) j) i
  have hF : familyQuorums (P := P) (ι := Fin 3) L (Finset.univ : Finset (Fin 3)) F := by
    intro i _
    rcases Fin.eq_zero_or_eq_succ i with hzero | ⟨j, hj⟩
    · subst hzero
      simpa [F] using h₁
    · subst hj
      rcases Fin.eq_zero_or_eq_succ j with hjzero | ⟨k, hk⟩
      · subst hjzero
        simpa [F] using h₂
      · subst hk
        cases k using Fin.cases with
        | zero => simpa [F] using h₃
        | succ k' => exact False.elim (Fin.elim0 k')
  obtain ⟨p, hp, _⟩ :=
    (familyInterWitness_iff (P := P) (ι := Fin 3) L (Finset.univ : Finset (Fin 3)) R).mp hw F hF
  have hp_all : ∀ i : Fin 3, p ∈ F i := by
    simpa [familyInter] using hp
  have hp₁ : p ∈ O₁ := by simpa [F] using hp_all 0
  have hp₂ : p ∈ O₂ := by simpa [F] using hp_all 1
  have hp₃ : p ∈ O₃ := by simpa [F] using hp_all 2
  refine ⟨p, ?_⟩
  exact ⟨⟨hp₁, hp₂⟩, hp₃⟩

/-- Nonempty three-way intersections. -/
lemma threeWayIntersections_nonempty
    (L : Semifilter P)
    (O₁ O₂ O₃ : Set P)
    (h₁ : O₁ ∈ L.quorums) (h₂ : O₂ ∈ L.quorums) (h₃ : O₃ ∈ L.quorums)
    (hw : nonemptyFamilyIntersections (P := P) (ι := Fin 3) L (Finset.univ : Finset (Fin 3))) :
    (O₁ ∩ O₂ ∩ O₃).Nonempty := by
  classical
  haveI := Classical.decEq (Fin 3)
  let F : Fin 3 → Set P := fun i =>
    Fin.cases O₁ (fun j => Fin.cases O₂ (fun _ => O₃) j) i
  have hF : familyQuorums (P := P) (ι := Fin 3) L (Finset.univ : Finset (Fin 3)) F := by
    intro i _
    rcases Fin.eq_zero_or_eq_succ i with hzero | ⟨j, hj⟩
    · subst hzero
      simpa [F] using h₁
    · subst hj
      rcases Fin.eq_zero_or_eq_succ j with hjzero | ⟨k, hk⟩
      · subst hjzero
        simpa [F] using h₂
      · subst hk
        cases k using Fin.cases with
        | zero => simpa [F] using h₃
        | succ k' => exact False.elim (Fin.elim0 k')
  obtain ⟨p, hp⟩ :=
    (familyInterNonempty_iff (P := P) (ι := Fin 3) L (Finset.univ : Finset (Fin 3))).mp hw F hF
  have hp_all : ∀ i : Fin 3, p ∈ F i := by
    simpa [familyInter] using hp
  have hp₁ : p ∈ O₁ := by simpa [F] using hp_all 0
  have hp₂ : p ∈ O₂ := by simpa [F] using hp_all 1
  have hp₃ : p ∈ O₃ := by simpa [F] using hp_all 2
  refine ⟨p, ?_⟩
  exact ⟨⟨hp₁, hp₂⟩, hp₃⟩

/-- Witness extraction convenience: pick a family, get a witness from the intersection. -/
lemma familyInterWitness_exists {L : Semifilter P} {s : Finset ι} {R : P → Prop}
    (hw : allFamilyInterWitness (P := P) (ι := ι) L s R)
    (F : ι → Set P) (hF : familyQuorums (P := P) (ι := ι) L s F) :
    ∃ p, p ∈ familyInter (P := P) s F ∧ R p := by
  classical
  exact (familyInterWitness_iff (P := P) (ι := ι) L s R).mp hw F hF

/-- Family inclusion preserves the quorum property. -/
lemma familyQuorums_mono
    {L : Semifilter P} {s : Finset ι} {F G : ι → Set P}
    (hFG : ∀ i ∈ s, F i ⊆ G i)
    (hF : familyQuorums (P := P) (ι := ι) L s F) :
    familyQuorums (P := P) (ι := ι) L s G := by
  intro i hi
  exact L.upwardClosed (hF i hi) (hFG i hi)

/-- Sequential two-way intersections specialised to histories. -/
lemma twoWaySequential
    {P Event : Type*} (H : History P Event)
    (L : Semifilter P)
    (O₁ O₂ : Set P)
    (h₁ : O₁ ∈ L.quorums) (h₂ : O₂ ∈ L.quorums)
    (hw : sequentialFamilyIntersections (P := P) (Event := Event) H L (Finset.univ : Finset Bool)) :
    ∃ p, p ∈ O₁ ∩ O₂ ∧ isSequential (P := P) (Event := Event) p H.val := by
  classical
  let F : Bool → Set P := fun b => cond b O₂ O₁
  have hF : familyQuorums (P := P) (ι := Bool) L (Finset.univ : Finset Bool) F := by
    intro b _
    cases b <;> simp [F, h₁, h₂]
  obtain ⟨p, hp, hseq⟩ :=
    (familyInterWitness_iff (P := P) (ι := Bool) L (Finset.univ : Finset Bool)
      (fun q => isSequential (P := P) (Event := Event) q H.val)).mp hw F hF
  have hp_all : ∀ b ∈ (Finset.univ : Finset Bool), p ∈ F b := by
    simpa [familyInter] using hp
  have hp₁ : p ∈ O₁ := by
    simpa [F] using hp_all false (by simp)
  have hp₂ : p ∈ O₂ := by
    simpa [F] using hp_all true (by simp)
  refine ⟨p, ⟨hp₁, hp₂⟩, hseq⟩

/-- Sequential three-way intersections specialised to histories. -/
lemma threeWaySequential
    {P Event : Type*} (H : History P Event)
    (L : Semifilter P)
    (O₁ O₂ O₃ : Set P)
    (h₁ : O₁ ∈ L.quorums) (h₂ : O₂ ∈ L.quorums) (h₃ : O₃ ∈ L.quorums)
    (hw : sequentialFamilyIntersections (P := P) (Event := Event) H L
      (Finset.univ : Finset (Fin 3))) :
    ∃ p, p ∈ O₁ ∩ O₂ ∩ O₃ ∧ isSequential (P := P) (Event := Event) p H.val := by
  classical
  haveI := Classical.decEq (Fin 3)
  let F : Fin 3 → Set P := fun i =>
    Fin.cases O₁ (fun j => Fin.cases O₂ (fun _ => O₃) j) i
  have hF : familyQuorums (P := P) (ι := Fin 3) L (Finset.univ : Finset (Fin 3)) F := by
    intro i _
    rcases Fin.eq_zero_or_eq_succ i with hzero | ⟨j, hj⟩
    · subst hzero
      simpa [F] using h₁
    · subst hj
      rcases Fin.eq_zero_or_eq_succ j with hjzero | ⟨k, hk⟩
      · subst hjzero
        simpa [F] using h₂
      · subst hk
        cases k using Fin.cases with
        | zero => simpa [F] using h₃
        | succ k' => exact False.elim (Fin.elim0 k')
  obtain ⟨p, hp, hseq⟩ :=
    (familyInterWitness_iff (P := P) (ι := Fin 3) L (Finset.univ : Finset (Fin 3))
      (fun q => isSequential (P := P) (Event := Event) q H.val)).mp hw F hF
  have hp_all : ∀ i : Fin 3, p ∈ F i := by
    simpa [familyInter] using hp
  have hp₁ : p ∈ O₁ := by simpa [F] using hp_all 0
  have hp₂ : p ∈ O₂ := by simpa [F] using hp_all 1
  have hp₃ : p ∈ O₃ := by simpa [F] using hp_all 2
  refine ⟨p, ⟨⟨hp₁, hp₂⟩, hp₃⟩, hseq⟩

/-- Singleton index collections reduce to the underlying set. -/
lemma familySingle_inter
    (L : Semifilter P) (R : P → Prop) (O : Set P)
    (hO : O ∈ L.quorums)
    (hw : allFamilyInterWitness (P := P) (ι := Unit) L (Finset.univ : Finset Unit) R) :
    ∃ p, p ∈ O ∧ R p := by
  classical
  let F : Unit → Set P := fun _ => O
  have hF : familyQuorums (P := P) (ι := Unit) L (Finset.univ : Finset Unit) F := by
    intro _ _
    simpa [F] using hO
  obtain ⟨p, hp, hRp⟩ :=
    (familyInterWitness_iff (P := P) (ι := Unit) L (Finset.univ : Finset Unit) R).mp hw F hF
  refine ⟨p, ?_, hRp⟩
  simpa [F, familyInter] using hp

/-- Nonemptiness for singleton index collections. -/
lemma familySingle_nonempty
    (L : Semifilter P) (O : Set P)
    (hO : O ∈ L.quorums)
    (hw : nonemptyFamilyIntersections (P := P) (ι := Unit) L (Finset.univ : Finset Unit)) :
    O.Nonempty := by
  classical
  let F : Unit → Set P := fun _ => O
  have hF : familyQuorums (P := P) (ι := Unit) L (Finset.univ : Finset Unit) F := by
    intro _ _
    simpa [F] using hO
  obtain ⟨p, hp⟩ :=
    (familyInterNonempty_iff (P := P) (ι := Unit) L (Finset.univ : Finset Unit)).mp hw F hF
  exact ⟨p, by simpa [F, familyInter] using hp⟩

end Semifilter
