import ModalDistribution.Logic.Semantics
import ModalDistribution.Core.Semifilter
import ModalDistribution.Core.History

/-!
# Quorum families

A `QuorumFamily` chooses one quorum per learner in a list. The `♢` clause of
`Sat` quantifies over exactly these choices; `head`, `tail` and `cons` take
them apart and build them up one learner at a time.
-/

namespace ModalDistribution
namespace Logic

open Set
open scoped Semifilter Formula History PreHistory Model

set_option autoImplicit false

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

/-- A choice of one quorum for each learner in `learners`: the tuples
`(O₁, …, Oₙ) ∈ ς(l₁) × ⋯ × ς(lₙ)` over which the `♢` clause quantifies. -/
structure QuorumFamily (M : Model S P)
    (learners : List S.Value) where
  /-- The quorum chosen for the `i`-th learner. -/
  choose : Fin learners.length → Set P
  /-- Each chosen quorum is a quorum of its learner. -/
  valid : ∀ i, choose i ∈ (M.learner (learners.get i)).quorums

namespace QuorumFamily

variable {M : Model S P} {ls : List S.Value}

/-- The chosen quorums have a common member. -/
@[simp] def IntersectionNonempty (F : QuorumFamily M ls) : Prop :=
  ∃ p, ∀ i, p ∈ F.choose i

/-- The quorum family over the empty learner list. -/
@[simp] def nil (M : Model S P) : QuorumFamily M [] where
  choose := Fin.elim0
  valid i := i.elim0

variable {l : Signature.Value S} {ls' : List S.Value}

/-- The quorum chosen for the first learner. -/
@[simp] def head (F : QuorumFamily M (l :: ls')) : Set P :=
  F.choose ⟨0, Nat.succ_pos _⟩

/-- The head of a family is a quorum of the first learner. -/
theorem head_mem (F : QuorumFamily M (l :: ls')) :
    head (M := M) F ∈ (M.learner l).quorums :=
  F.valid ⟨0, Nat.succ_pos _⟩

/-- The family with the first learner's quorum dropped. -/
@[simp] def tail (F : QuorumFamily M (l :: ls')) :
    QuorumFamily M ls' where
  choose i := F.choose i.succ
  valid i := F.valid i.succ

/-- The family that chooses `O` for `l` and then follows `F`. -/
@[simp] def cons
    (O : Set P) (hO : O ∈ (M.learner l).quorums)
    (F : QuorumFamily M ls') :
    QuorumFamily M (l :: ls') where
  choose := Fin.cases O F.choose
  valid := Fin.cases hO F.valid

@[simp] theorem cons_choose_zero
    {O : Set P} {hO : O ∈ (M.learner l).quorums}
    {F : QuorumFamily M ls'} :
    (cons (M := M) (l := l) O hO F).choose ⟨0, Nat.succ_pos _⟩ = O := rfl

/-- A common member of a family over `l :: ls'` is a member of its head and a
common member of its tail. -/
@[simp] theorem forall_choose_cons
    (F : QuorumFamily M (l :: ls')) (p : P) :
    (∀ i, p ∈ F.choose i) ↔
      p ∈ F.head ∧ ∀ i, p ∈ (F.tail).choose i :=
  ⟨fun h => ⟨h ⟨0, Nat.succ_pos _⟩, fun i => h i.succ⟩,
    fun ⟨hHead, hTail⟩ i => Fin.cases hHead hTail i⟩

end QuorumFamily

end Logic
end ModalDistribution
