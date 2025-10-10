import ModalDistribution.Logic.Semantics
import ModalDistribution.Core.Semifilter
import ModalDistribution.Core.History

/-!
# Quorum families

This file defines quorum families and operations on them for reasoning about
multiple learners and their quorum intersections.
-/

namespace ModalDistribution
namespace Logic

open Set
open scoped Semifilter Formula History PreHistory Model

set_option autoImplicit false

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

section QuorumFamilySection

/-! ## Auxiliaries for quorum families -/

/-- Index a family of quorums against a sequence of learner values. -/
structure QuorumFamily (M : Model S P)
    (learners : List S.Value) where
  choose : Fin learners.length → Set P
  valid : ∀ i, choose i ∈ (M.learner (learners.get i)).quorums

namespace QuorumFamily

variable {M : Model S P} {ls : List S.Value}

/-- Nonemptiness of the intersection. -/
@[simp] def intersectionNonempty (F : QuorumFamily M ls) : Prop :=
  ∃ p, ∀ i, p ∈ F.choose i

/-- Trivial quorum family over the empty learner list. -/
@[simp] def nil (M : Model S P) : QuorumFamily M [] where
  choose i := Fin.elim0 i
  valid := by
    intro i
    have : False := Nat.not_lt_zero _ i.isLt
    exact this.elim

variable {l : Signature.Value S} {ls' : List S.Value}

/-- Head quorum of a non-empty quorum family. -/
@[simp] def head (F : QuorumFamily M (l :: ls')) : Set P :=
  F.choose ⟨0, Nat.succ_pos _⟩

lemma head_mem (F : QuorumFamily M (l :: ls')) :
    head (M := M) F ∈ (M.learner l).quorums := by
  classical
  simpa [head, List.get_cons_zero] using F.valid ⟨0, Nat.succ_pos _⟩

/-- Tail quorum family obtained by discarding the first learner. -/
@[simp] def tail (F : QuorumFamily M (l :: ls')) :
    QuorumFamily M ls' where
  choose i := F.choose (Fin.succ i)
  valid i := by
    classical
    simpa [List.get_cons_succ] using F.valid (Fin.succ i)

@[simp] lemma tail_choose
    (F : QuorumFamily M (l :: ls')) (i : Fin ls'.length) :
    (tail (M := M) F).choose i = F.choose (Fin.succ i) := rfl

/-- Extend a quorum family by prepending a quorum. -/
@[simp] def cons
    (O : Set P) (hO : O ∈ (M.learner l).quorums)
    (F : QuorumFamily M ls') :
    QuorumFamily M (l :: ls') where
  choose i := Fin.cases O (fun j => F.choose j) i
  valid i := by
    classical
    refine Fin.cases ?_ ?_ i
    · simpa using hO
    · intro j
      simpa [List.get_cons_succ] using F.valid j

@[simp] lemma cons_choose_zero
    {O : Set P} {hO : O ∈ (M.learner l).quorums}
    {F : QuorumFamily M ls'} :
    (cons (M := M) (l := l) O hO F).choose ⟨0, Nat.succ_pos _⟩ = O := rfl

@[simp] lemma cons_choose_succ
    {O : Set P} {hO : O ∈ (M.learner l).quorums}
    {F : QuorumFamily M ls'} (i : Fin ls'.length) :
    (cons (M := M) (l := l) O hO F).choose (Fin.succ i) = F.choose i := rfl

@[simp] lemma forall_choose_cons
    (F : QuorumFamily M (l :: ls')) (p : P) :
    (∀ i, p ∈ F.choose i) ↔
      p ∈ F.head ∧ ∀ i, p ∈ (F.tail).choose i := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [QuorumFamily.head] using h ⟨0, Nat.succ_pos _⟩
    · intro i
      simpa [QuorumFamily.tail_choose] using h (Fin.succ i)
  · rintro ⟨hpHead, hpTail⟩ i
    classical
    refine Fin.cases ?_ ?_ i
    · simpa [QuorumFamily.head] using hpHead
    · intro j
      simpa [QuorumFamily.tail_choose] using hpTail j

@[simp] lemma cons_forall_choose
    {O : Set P} {hO : O ∈ (M.learner l).quorums}
    {F : QuorumFamily M ls'} {p : P} :
    (∀ i, p ∈ (cons (M := M) (l := l) O hO F).choose i) ↔
      p ∈ O ∧ ∀ i, p ∈ F.choose i := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [cons_choose_zero] using h ⟨0, Nat.succ_pos _⟩
    · intro i
      simpa [cons_choose_succ] using h (Fin.succ i)
  · rintro ⟨hpO, hpAll⟩ i
    refine Fin.cases ?_ ?_ i
    · simpa [cons_choose_zero] using hpO
    · intro j
      simpa [cons_choose_succ] using hpAll j

lemma exists_forall_choose_cons
    (F : QuorumFamily M (l :: ls'))
    {acc : Set P} {R : P → Prop} :
    (∃ p, p ∈ acc ∧ (∀ i, p ∈ F.choose i) ∧ R p) ↔
      ∃ p, p ∈ acc ∧ p ∈ F.head ∧ (∀ i, p ∈ (F.tail).choose i) ∧ R p := by
  classical
  constructor
  · rintro ⟨p, hpAcc, hpAll, hR⟩
    obtain ⟨hpHead, hpTail⟩ :=
      (QuorumFamily.forall_choose_cons (F := F) (p := p)).1 hpAll
    exact ⟨p, hpAcc, hpHead, hpTail, hR⟩
  · rintro ⟨p, hpAcc, hpHead, hpTail, hR⟩
    refine ⟨p, hpAcc, ?_, hR⟩
    exact (QuorumFamily.forall_choose_cons (F := F) (p := p)).2
      ⟨hpHead, hpTail⟩

lemma exists_forall_choose_cons_cons
    {O : Set P} {hO : O ∈ (M.learner l).quorums}
    {F : QuorumFamily M ls'}
    {acc : Set P} {R : P → Prop} :
    (∃ p, p ∈ acc ∧ (∀ i, p ∈
        (cons (M := M) (l := l) O hO F).choose i) ∧ R p) ↔
      ∃ p, p ∈ acc ∧ p ∈ O ∧ (∀ i, p ∈ F.choose i) ∧ R p := by
  classical
  constructor
  · rintro ⟨p, hpAcc, hpAll, hR⟩
    obtain ⟨hpO, hpTail⟩ :=
      (QuorumFamily.cons_forall_choose
        (M := M) (l := l) (ls' := ls') (F := F)
        (O := O) (p := p) (hO := hO)).1 hpAll
    exact ⟨p, hpAcc, hpO, hpTail, hR⟩
  · rintro ⟨p, hpAcc, hpO, hpTail, hR⟩
    refine ⟨p, hpAcc, ?_, hR⟩
    exact (QuorumFamily.cons_forall_choose
        (M := M) (l := l) (ls' := ls') (F := F)
        (O := O) (p := p) (hO := hO)).2 ⟨hpO, hpTail⟩

@[simp] lemma exists_forall_choose_cons_inter
    (F : QuorumFamily M (l :: ls'))
    {acc : Set P} {R : P → Prop} :
    (∃ p, p ∈ acc ∧ (∀ i, p ∈ F.choose i) ∧ R p) ↔
      ∃ p ∈ acc ∩ F.head, (∀ i, p ∈ (F.tail).choose i) ∧ R p := by
  classical
  constructor
  · intro h
    obtain ⟨p, hpAcc, hpHead, hpTail, hR⟩ :=
      (QuorumFamily.exists_forall_choose_cons
        (M := M) (ls' := ls') (F := F)
        (acc := acc) (R := R)).1 h
    exact ⟨p, ⟨hpAcc, hpHead⟩, hpTail, hR⟩
  · rintro ⟨p, hpAccHead, hpTail, hR⟩
    obtain ⟨hpAcc, hpHead⟩ := hpAccHead
    exact
      (QuorumFamily.exists_forall_choose_cons
        (M := M) (ls' := ls') (F := F)
        (acc := acc) (R := R)).2
        ⟨p, hpAcc, hpHead, hpTail, hR⟩

end QuorumFamily

end QuorumFamilySection

end Logic
end ModalDistribution
