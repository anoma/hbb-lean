import ModalDistribution.Grassroots.Coalescent

/-!
# Leader-rooted learner families

This file develops a concrete `IsCoalescent`-style example: the
*leader-rooted* learner family. Pick a fixed `leader : A`; every quorum
at every (leader-containing) participant set must include the leader.

## Why a parallel hierarchy

The unrestricted `IsCoalescent` typeclass from `Coalescent.lean`
quantifies over **all** pairs `P ⊆ P' : Set A` of participant subsets.
A leader-rooted family is only naturally defined on participant sets
*containing the leader*, so coalescence can only hold *conditionally*
on leader-presence in both endpoints.

To express this as a real typeclass instance (rather than as standalone
conditional theorems), we introduce a parallel hierarchy:

* `LeaderRootedFamily V A` — like `LearnerFamily V A`, but each `σ`-call
  takes an extra hypothesis `leader ∈ P` (in addition to `[Nonempty ↥P]`).
* `IsLeaderCoalescent F` — like `IsCoalescent`, but the `lift_quorum`
  and `restrict_quorum` quantifiers also carry hypotheses
  `F.leader ∈ P` and `F.leader ∈ P'`.

The canonical leader-rooted family `LeaderRooted.family leader V` is
then a true `instance` of `IsLeaderCoalescent`, with **no `sorry`**.

## Main definitions

* `Grassroots.LeaderRooted.quorumsContaining` — set of subsets of `↥P`
  that contain the leader.
* `Grassroots.LeaderRooted.semifilter` — the leader-rooted semifilter at
  a participant set containing the leader.
* `Grassroots.LeaderRootedFamily` — the structure of leader-rooted
  learner families.
* `Grassroots.IsLeaderCoalescent` — coalescence for leader-rooted
  families.
* `Grassroots.LeaderRooted.family` — the canonical leader-rooted family.

## Main theorems

* `Grassroots.LeaderRooted.semifilter_quorums_iff` — characterisation
  of quorum membership for the leader-rooted semifilter.
* `Grassroots.LeaderRooted.family_quorums_iff` — characterisation at
  the family level.
* `Grassroots.LeaderRooted.instCoalescent` — the canonical family is
  `IsLeaderCoalescent`. This is the main positive result.
-/

namespace ModalDistribution
namespace Grassroots

open Set
open scoped Semifilter

universe u v
variable {A : Type u}

/-! ## §1. The leader-rooted semifilter

A subset of `↥P` is a *leader-rooted quorum* iff it contains the
designated leader (whose membership in `P` is supplied as a hypothesis).
The collection of leader-rooted quorums forms a semifilter:

* nonempty: `Set.univ` always contains the leader;
* upward-closed: any superset of a leader-containing set still contains
  the leader;
* pairwise intersecting: any two leader-containing sets share the leader. -/

namespace LeaderRooted

/-- The set of subsets of `↥P` that contain the leader. -/
@[simp] def quorumsContaining (leader : A) {P : Set A} (hLeader : leader ∈ P) :
    Set (Set ↥P) :=
  { S | (⟨leader, hLeader⟩ : ↥P) ∈ S }

/-- The leader-rooted semifilter on `↥P`, defined when `leader ∈ P`. -/
def semifilter (leader : A) {P : Set A} (hLeader : leader ∈ P) :
    Semifilter ↥P where
  quorums := quorumsContaining leader hLeader
  nonempty := ⟨Set.univ, by simp [quorumsContaining]⟩
  upwardClosed := by
    intro O O' hO hsub
    exact hsub hO
  pairwiseInter := by
    intro O O' hO hO'
    exact ⟨⟨leader, hLeader⟩, hO, hO'⟩

/-- Membership in the leader-rooted semifilter is just leader-membership. -/
@[simp] lemma semifilter_quorums_iff
    (leader : A) {P : Set A} (hLeader : leader ∈ P) (S : Set ↥P) :
    S ∈ (semifilter leader hLeader).quorums ↔
      (⟨leader, hLeader⟩ : ↥P) ∈ S := by
  rfl

end LeaderRooted

/-! ## §2. Leader-rooted learner families

The structure mirrors `LearnerFamily V A` from `Coalescent.lean`, but the
`σ` field takes an additional explicit hypothesis `leader ∈ P`. This
captures the fact that the leader-rooted construction is only meaningful
when the leader is in scope. -/

/-- A *leader-rooted learner family*: a learner family with a designated
leader, defined only on participant sets that contain the leader. -/
structure LeaderRootedFamily (V : Type v) (A : Type u) where
  /-- The designated leader. -/
  leader : A
  /-- The semifilter assigned to value `v` at participant set `P`,
  given the witness `leader ∈ P`. -/
  σ : ∀ (P : Set A) (_hLeader : leader ∈ P) [Nonempty ↥P],
        V → Semifilter ↥P

/-! ## §3. Coalescence for leader-rooted families

The non-interference / safety condition for leader-rooted families:
quorums lift forward and restrict back, *under the additional assumption
that both participant sets contain the leader*. -/

/-- A leader-rooted learner family is *leader-coalescent* iff its semifilter
behaves coherently under inclusion of participant sets, both of which
contain the leader. -/
class IsLeaderCoalescent {V : Type v} (F : LeaderRootedFamily V A) : Prop where
  /-- Lift quorums forward when both sets contain the leader. -/
  lift_quorum :
    ∀ {P P' : Set A} (h : P ⊆ P')
      (hP : F.leader ∈ P) (hP' : F.leader ∈ P')
      [Nonempty ↥P] [Nonempty ↥P'] (v : V) ⦃O : Set ↥P⦄,
      O ∈ (F.σ P hP v).quorums →
        liftQuorumSet h O ∈ (F.σ P' hP' v).quorums
  /-- Restrict quorums backward when both sets contain the leader, provided
  the restriction is nonempty. -/
  restrict_quorum :
    ∀ {P P' : Set A} (h : P ⊆ P')
      (hP : F.leader ∈ P) (hP' : F.leader ∈ P')
      [Nonempty ↥P] [Nonempty ↥P'] (v : V) ⦃O' : Set ↥P'⦄,
      O' ∈ (F.σ P' hP' v).quorums →
        (restrictQuorumSet h O').Nonempty →
          restrictQuorumSet h O' ∈ (F.σ P hP v).quorums

/-! ## §4. The canonical leader-rooted family -/

namespace LeaderRooted

/-- The canonical leader-rooted family: maps every leader-containing
participant set to the corresponding `LeaderRooted.semifilter`. -/
def family (leader : A) (V : Type v) : LeaderRootedFamily V A where
  leader := leader
  σ := fun _ hLeader _ _ => semifilter leader hLeader

/-- Leader of the canonical family. -/
@[simp] lemma family_leader (leader : A) (V : Type v) :
    (family (A := A) leader V).leader = leader := rfl

/-- Quorum membership in the canonical family is just leader-membership. -/
@[simp] lemma family_quorums_iff
    (leader : A) (V : Type v) (P : Set A) (hLeader : leader ∈ P)
    [Nonempty ↥P] (v : V) (S : Set ↥P) :
    S ∈ ((family leader V).σ P hLeader v).quorums ↔
      (⟨leader, hLeader⟩ : ↥P) ∈ S := by
  unfold family
  exact semifilter_quorums_iff leader hLeader S

end LeaderRooted

/-! ## §5. The canonical leader-rooted family is leader-coalescent

This is the main positive result of this file: a real `instance`
witnessing that the leader-rooted construction satisfies the
`IsLeaderCoalescent` typeclass. The proof unfolds the semifilter
definition and uses proof irrelevance to identify
`liftAgent h ⟨leader, hP⟩` with `⟨leader, hP'⟩`.  -/

namespace LeaderRooted

/-- **The canonical leader-rooted family is leader-coalescent.** -/
instance instCoalescent (leader : A) (V : Type v) :
    IsLeaderCoalescent (family (A := A) leader V) where
  lift_quorum := by
    intro P P' h hP hP' _ _ v O hO
    -- After unfolding the family and the semifilter, hO is the
    -- statement `(⟨leader, hP⟩ : ↥P) ∈ O`.
    -- We need to show `(⟨leader, hP'⟩ : ↥P') ∈ liftQuorumSet h O`.
    rw [family_quorums_iff] at hO
    rw [family_quorums_iff]
    -- Goal: ⟨leader, hP'⟩ ∈ liftQuorumSet h O
    --     = ⟨leader, hP'⟩ ∈ liftAgent h '' O
    refine ⟨⟨leader, hP⟩, hO, ?_⟩
    -- liftAgent h ⟨leader, hP⟩ = ⟨leader, hP'⟩ by Subtype extensionality.
    apply Subtype.ext
    rfl
  restrict_quorum := by
    intro P P' h hP hP' _ _ v O' hO' _
    -- hO' : O' ∈ (family ...).σ P' hP' v).quorums = (⟨leader, hP'⟩ : ↥P') ∈ O'
    rw [family_quorums_iff] at hO'
    rw [family_quorums_iff]
    -- Goal: ⟨leader, hP⟩ ∈ restrictQuorumSet h O'
    --     = liftAgent h ⟨leader, hP⟩ ∈ O'
    change liftAgent h ⟨leader, hP⟩ ∈ O'
    -- liftAgent h ⟨leader, hP⟩ = ⟨leader, hP'⟩ by Subtype extensionality.
    have hEq : (liftAgent h ⟨leader, hP⟩ : ↥P') = ⟨leader, hP'⟩ := by
      apply Subtype.ext
      rfl
    rw [hEq]
    exact hO'

/-- The canonical leader-rooted family is *interactive* whenever there is
some other agent that *could* enlarge the participant set: any extension
that adds a fresh agent gives a quorum (the pair `{leader, fresh}`) that
uses agents outside `P`. -/
theorem family_interactive
    (leader : A) (V : Type v) [Inhabited V]
    {P : Set A} (hP : leader ∈ P) [Nonempty ↥P]
    {q : A} (hqP : q ∉ P) :
    ∃ (P' : Set A) (h : P ⊆ P') (hP' : leader ∈ P') (_ : Nonempty ↥P')
      (v : V) (O' : Set ↥P'),
      O' ∈ ((family (A := A) leader V).σ P' hP' v).quorums ∧
        ¬ O' ⊆ Set.range (liftAgent h) := by
  -- Take P' = P ∪ {q}.
  have hPsub : P ⊆ P ∪ {q} := Set.subset_union_left
  have hLeaderP' : leader ∈ P ∪ {q} := Or.inl hP
  have hqP' : q ∈ P ∪ {q} := Or.inr rfl
  haveI : Nonempty ↥(P ∪ {q}) := ⟨⟨leader, hLeaderP'⟩⟩
  refine ⟨P ∪ {q}, hPsub, hLeaderP', inferInstance, default,
          {⟨leader, hLeaderP'⟩, ⟨q, hqP'⟩}, ?_, ?_⟩
  · -- The set {⟨leader, _⟩, ⟨q, _⟩} contains the leader, hence is a quorum.
    rw [family_quorums_iff]
    exact Or.inl rfl
  · -- The fresh element ⟨q, _⟩ is not in the range of liftAgent.
    intro hsub
    have hMem : (⟨q, hqP'⟩ : ↥(P ∪ {q})) ∈
        ({⟨leader, hLeaderP'⟩, ⟨q, hqP'⟩} : Set _) := by
      right; rfl
    obtain ⟨a, ha⟩ := hsub hMem
    -- a : ↥P, ha : liftAgent _ a = ⟨q, _⟩
    have hav : (a : A) = q := by
      have := congrArg Subtype.val ha
      simpa using this
    -- a : ↥P means a.property : (a : A) ∈ P, so q ∈ P, contradicting hqP.
    exact hqP (hav ▸ a.property)

end LeaderRooted

end Grassroots
end ModalDistribution
