import ModalDistribution.Logic.Semantics
import ModalDistribution.Core.Semifilter
import ModalDistribution.Core.History

/-!
# Modal logic properties (Sections 4 and 5)

This file records the logical infrastructure from Sections 4 and 5 of the HBB
paper.  We introduce the modal shorthands from Notation 4.1.2, formalise the
liveness theory ThyLive (Definition 5.2.3), and state the key lemmas and
propositions about quorum intersections and sequentiality.  Proofs are deferred
(`sorry`) until subsequent issues.
-/

namespace ModalDistribution
namespace Logic

open Set
open scoped Semifilter Formula History PreHistory Model

set_option autoImplicit false

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {S : Signature} {P : Type u₆} [Nonempty P]

section QuorumFamilySection

/-! ## Auxiliaries for quorum families -/

/-- Index a family of quorums against a sequence of learner values. -/
structure QuorumFamily (M : Model S P)
    (learners : List (Signature.Value S)) where
  choose : Fin learners.length → Set P
  valid : ∀ i, choose i ∈ (M.learner (learners.get i)).quorums

namespace QuorumFamily

variable {M : Model S P} {ls : List (Signature.Value S)}

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

variable {l : Signature.Value S} {ls' : List (Signature.Value S)}

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

@[simp] lemma ofValues_cons
    (v : Signature.Value S) (ls : List (Signature.Value S)) :
    Term.ofValues (v :: ls) = Term.ofValue v :: Term.ofValues ls := rfl

section DiamondSection

variable [DecidableEq S.VarSymb]

/-- Witness property for `♢` modalities (Lemma 4.1.1). -/
@[simp] def hasQuorumWitness
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) : Prop :=
  ∀ F : QuorumFamily M ls,
    ∃ p, (∀ i, p ∈ F.choose i) ∧
      ⟨M.history,p⟩ ⊨[M,σ]φ

lemma hasQuorumWitness.of_imp
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) {φ ψ : Formula S}
    (h : ∀ p,
        (⟨M.history,p⟩ ⊨[M,σ]φ) →
          ⟨M.history,p⟩ ⊨[M,σ]ψ) :
    hasQuorumWitness (M := M) σ ls φ →
      hasQuorumWitness (M := M) σ ls ψ := by
  intro hWitness F
  obtain ⟨p, hpAll, hpSat⟩ := hWitness F
  exact ⟨p, hpAll, h p hpSat⟩

lemma hasQuorumWitness.congr
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) {φ ψ : Formula S}
    (h : ∀ p,
        (⟨M.history,p⟩ ⊨[M,σ]φ) ↔
          ⟨M.history,p⟩ ⊨[M,σ]ψ) :
    hasQuorumWitness (M := M) σ ls φ ↔
      hasQuorumWitness (M := M) σ ls ψ := by
  constructor
  · intro hWitness
    exact hasQuorumWitness.of_imp (M := M) (σ := σ)
      (ls := ls) (φ := φ) (ψ := ψ)
      (h := fun p => (h p).1) hWitness
  · intro hWitness
    exact hasQuorumWitness.of_imp (M := M) (σ := σ)
      (ls := ls) (φ := ψ) (ψ := φ)
      (h := fun p => (h p).2) hWitness

/-- Nonempty intersection property. -/
@[simp] def hasQuorumNonempty
    (M : Model S P)
    (ls : List (Signature.Value S)) : Prop :=
  ∀ F : QuorumFamily M ls, QuorumFamily.intersectionNonempty F

/- The recursive semantics of `♢` following Figure 3. -/
private def diamondCheck
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S))
    (φ : Formula S) (acc : Set P) : Prop :=
  match ls with
  | [] =>
      ∃ p, p ∈ acc ∧ ⟨M.history,p⟩ ⊨[M,σ]φ
  | v :: vs =>
      ∀ O ∈ (M.learner v).quorums,
        diamondCheck M σ vs φ (acc ∩ O)

private lemma diamondCheck_of_imp
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S))
    (φ ψ : Formula S) (acc : Set P)
    (h : ∀ p, (⟨M.history,p⟩ ⊨[M,σ]φ) →
        ⟨M.history,p⟩ ⊨[M,σ]ψ) :
    diamondCheck M σ ls φ acc →
      diamondCheck M σ ls ψ acc := by
  classical
  induction ls generalizing acc with
  | nil =>
      intro hCheck
      rcases hCheck with ⟨p, hpAcc, hpSat⟩
      exact ⟨p, hpAcc, h p hpSat⟩
  | cons l ls ih =>
      intro hCheck O hO
      exact ih (acc := acc ∩ O) (hCheck O hO)

private lemma diamondCheck_congr
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S))
    (φ ψ : Formula S) (acc : Set P)
    (h : ∀ p,
        (⟨M.history,p⟩ ⊨[M,σ]φ) ↔
         ⟨M.history,p⟩ ⊨[M,σ]ψ) :
    diamondCheck M σ ls φ acc ↔
      diamondCheck M σ ls ψ acc := by
  classical
  constructor
  · intro hCheck
    exact
      diamondCheck_of_imp (M := M) (σ := σ)
        (ls := ls) (φ := φ) (ψ := ψ) (acc := acc)
        (h := fun p => (h p).1) hCheck
  · intro hCheck
    exact
      diamondCheck_of_imp (M := M) (σ := σ)
        (ls := ls) (φ := ψ) (ψ := φ) (acc := acc)
        (h := fun p => (h p).2) hCheck

private def quorumWitnessAcc
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S))
    (φ : Formula S) (acc : Set P) : Prop :=
  ∀ F : QuorumFamily M ls,
    ∃ p, p ∈ acc ∧ (∀ i, p ∈ F.choose i) ∧
      ⟨M.history,p⟩ ⊨[M,σ]φ

private lemma diamondCheck_iff_quorumWitnessAcc
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S)
    (acc : Set P) :
    diamondCheck M σ ls φ acc ↔
      quorumWitnessAcc M σ ls φ acc := by
  classical
  induction ls generalizing acc with
  | nil =>
      constructor
      · intro h F
        rcases h with ⟨p, hpacc, hpSat⟩
        refine ⟨p, hpacc, ?_, hpSat⟩
        simp [List.length_nil]
      · intro h
        obtain ⟨p, hpacc, _, hpSat⟩ :=
          h (QuorumFamily.nil (M := M))
        exact ⟨p, hpacc, hpSat⟩
  | cons l ls ih =>
      constructor
      · intro h F
        have hTail :=
          h (QuorumFamily.head (F := F))
            (QuorumFamily.head_mem (F := F))
        obtain ⟨p, hpAccHead, hpTail, hpSat⟩ :=
          (ih (acc := acc ∩ QuorumFamily.head (F := F))).1 hTail
            (QuorumFamily.tail (F := F))
        exact
          (QuorumFamily.exists_forall_choose_cons_inter
            (M := M) (l := l) (ls' := ls) (F := F)
            (acc := acc)
            (R := fun q => ⟨M.history,q⟩ ⊨[M,σ] φ)).mpr
            ⟨p, hpAccHead, hpTail, hpSat⟩
      · intro h O hO
        have hWitnessTail :
            quorumWitnessAcc M σ ls φ (acc ∩ O) := by
          intro Ftail
          obtain ⟨p, hpAcc, hpO, hpTail, hpSat⟩ :=
            (QuorumFamily.exists_forall_choose_cons_cons
              (M := M) (ls' := ls) (F := Ftail)
              (acc := acc) (O := O)
              (R := fun q => ⟨M.history,q⟩ ⊨[M,σ] φ)).1
              (h (QuorumFamily.cons (M := M) (l := l) O hO Ftail))
          refine ⟨p, ⟨hpAcc, hpO⟩, hpTail, hpSat⟩
        exact (ih (acc := acc ∩ O)).2 hWitnessTail

private lemma sat_check_iff_diamondCheck
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S)
    (acc : Set P) :
    Sat.check M σ M.history φ (Term.ofValues ls) acc ↔
      diamondCheck M σ ls φ acc := by
  classical
  induction ls generalizing acc with
  | nil =>
      simp [diamondCheck, Term.ofValues, Sat.check]
  | cons l ls ih =>
      simp [Sat.check, diamondCheck]
      constructor
      · intro h O hO
        have := h O hO
        simpa using (ih (acc := acc ∩ O)).1 this
      · intro h O hO
        have := h O hO
        simpa using (ih (acc := acc ∩ O)).2 this

private lemma sat_diamond_iff_diamondCheck
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S)
    (p : P) :
    (⟨M.history,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues ls] φ) ↔
      diamondCheck M σ ls φ Set.univ := by
  classical
  simpa [Sat, Term.ofValues, Term.ofValues]
    using sat_check_iff_diamondCheck (M := M) (σ := σ)
      (ls := ls) (φ := φ) (acc := Set.univ)

lemma sat_diamond_singleton_iff
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P)
    (l : Signature.Value S) (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l]] φ) ↔
      ∀ O ∈ (M.learner l).quorums,
        ∃ q ∈ O, ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] φ := by
  classical
  constructor <;> intro h
  · simpa [Sat, Term.ofValues, Term.ofValues, Term.ofValue, Term.eval,
      Set.inter_comm, Set.inter_left_comm, Set.inter_assoc, Set.univ_inter,
      Set.inter_univ, Sat.check]
      using h
  · simpa [Sat, Term.ofValues, Term.ofValues, Term.ofValue, Term.eval,
      Set.inter_comm, Set.inter_left_comm, Set.inter_assoc, Set.univ_inter,
      Set.inter_univ, Sat.check]
      using h

/-- Expand a pair of learner diamonds into quorum-intersection witnesses. -/
lemma sat_diamond_pair_iff
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P)
    (l l' : Signature.Value S) (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l, l']] φ) ↔
      ∀ O ∈ (M.learner l).quorums,
        ∀ O' ∈ (M.learner l').quorums,
          ∃ q ∈ O ∩ O', ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] φ := by
  classical
  constructor <;> intro h
  · simpa [Sat, Term.ofValues, Term.ofValues, Term.ofValue, Term.eval,
      Set.inter_comm, Set.inter_left_comm, Set.inter_assoc,
      Set.inter_univ, Set.univ_inter, Sat.check]
      using h
  · simpa [Sat, Term.ofValues, Term.ofValues, Term.ofValue, Term.eval,
      Set.inter_comm, Set.inter_left_comm, Set.inter_assoc,
      Set.inter_univ, Set.univ_inter, Sat.check]
      using h

/-- Singleton learner boxes exhibit a quorum whose members satisfy the guard. -/
lemma sat_box_singleton_exists
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P)
    (l : Signature.Value S) (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] □ᶠ[Term.ofValues [l]] φ) ↔
      ∃ O ∈ (M.learner l).quorums,
        ∀ q ∈ O, ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] φ := by
  classical
  constructor
  · intro hBox
    by_contra hNo
    have hAll :
        ∀ O ∈ (M.learner l).quorums,
          ∃ q ∈ O, ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] ¬ᶠ φ := by
      intro O hO
      have hNotAll : ¬ ∀ q ∈ O, ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] φ := by
        intro hAllφ
        exact hNo ⟨O, hO, hAllφ⟩
      obtain ⟨q, hq⟩ := not_forall.mp hNotAll
      obtain ⟨hqO, hqNotφ⟩ := Classical.not_imp.mp hq
      have hqNot : ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] ¬ᶠ φ :=
        Sat.not_intro (M := M ∣ᵥ H) (σ := σ)
          (H := H) (p := q) (φ := φ)
          (by
            intro hφ
            exact hqNotφ hφ)
      exact ⟨q, hqO, hqNot⟩
    have hDiamond :
        ⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l]] (¬ᶠ φ) :=
      (sat_diamond_singleton_iff (M := M) (σ := σ)
        (H := H) (p := p) (l := l) (φ := ¬ᶠ φ)).2 hAll
    have hNoDiamond :
        (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l]] (¬ᶠ φ)) → False :=
      (Sat.not (M := M) (σ := σ) (H := H) (p := p)
        (φ := ♢ᶠ[Term.ofValues [l]] (¬ᶠ φ))).1
        (by
          simpa [Formula.box, Formula.not]
            using hBox)
    exact hNoDiamond hDiamond
  · rintro ⟨O, hO, hAll⟩
    have hNoDiamond :
        (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l]] (¬ᶠ φ)) → False := by
      intro hDiamond
      obtain ⟨q, hqO, hqNotφ⟩ :=
        (sat_diamond_singleton_iff (M := M) (σ := σ)
          (H := H) (p := p) (l := l) (φ := ¬ᶠ φ)).1 hDiamond
          O hO
      have hφ := hAll q hqO
      exact
        (Sat.not_elim (M := M ∣ᵥ H) (σ := σ)
          (H := H) (p := q) (φ := φ)) hqNotφ hφ
    have hNot :=
      Sat.not_intro (M := M) (σ := σ) (H := H) (p := p)
        (φ := ♢ᶠ[Term.ofValues [l]] (¬ᶠ φ)) hNoDiamond
    simpa [Formula.box, Formula.not] using hNot

/-- Helper lemma for transporting empty diamonds from the local view. -/
lemma sat_diamondEmpty_of_local
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P) (φ : Formula S) :
    (∃ q, ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] φ) →
      (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[] φ) := by
  classical
  intro hWitness
  rcases hWitness with ⟨q, hq⟩
  simpa [Formula.diamondEmpty, Sat, Sat.check] using
    (⟨q, Set.mem_univ q, hq⟩ :
      ∃ r ∈ Set.univ, ⟨H,r⟩ ⊨[M ∣ᵥ H, σ] φ)

/-- Lift past-event satisfaction from a local view to the ambient history. -/
lemma sat_past_event_of_subset_to_history
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P) (evt : Signature.EventType S)
    (hSubset : H.val ⊆trn M.history.val)
    (hPast : ⟨H,p⟩ ⊨[M ∣ᵥ H,σ]↓ᶠ (Formula.ofEvent evt)) :
    ⟨M.history,p⟩ ⊨[M,σ] ↓ᶠ (Formula.ofEvent evt) := by
  classical
  unfold Sat at hPast
  rcases hPast with ⟨K, hBefore, hEvent⟩
  have hBefore' :
      K.val ≺ₚ[p] M.history.val :=
    happensBeforeAt_of_subsetTrn
      (P := P) (Event := Signature.EventType S)
      hBefore hSubset
  have hSubset' :
      H.val ⊆ M.history.val :=
    transitiveSubset_subset (P := P)
      (Event := Signature.EventType S) hSubset
  have hEvent' :
      ⟨K,p⟩ ⊨[M ∣ᵥ M.history, σ] Formula.ofEvent evt :=
    Sat.ofEvent_of_subset (M := M) (σ := σ)
      (H := M.history) (H₁ := H) (H₂ := K)
      (p := p) (evt := evt) (hSubset := hSubset') hEvent
  have hEvent'' :
      ⟨K,p⟩ ⊨[M, σ] Formula.ofEvent evt := by
    simpa [ModalDistribution.Model.localView_full] using hEvent'
  exact
    Sat.past_intro_of_prefix (M := M) (σ := σ) (H := M.history)
      (p := p) (H' := K) (φ := Formula.ofEvent evt)
      (hBefore := hBefore') (hφ := hEvent'')

/-- Transport a denial of past-event satisfaction along a transitive subset. -/
lemma sat_notPast_event_subset
    (M : Model S P) (σ : Assignment S)
    (H H' : History P (Signature.EventType S))
    (hSub : H'.val ⊆trn H.val) (q : P)
    (evt : Signature.EventType S) :
    (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]
        ¬ᶠ (↓ᶠ (Formula.ofEvent evt))) →
      (⟨H',q⟩ ⊨[M ∣ᵥ H',σ]
        ¬ᶠ (↓ᶠ (Formula.ofEvent evt))) := by
  classical
  intro hNot
  refine Sat.not_intro (M := M ∣ᵥ H') (σ := σ) (H := H') (p := q)
      (φ := ↓ᶠ (Formula.ofEvent evt)) ?_
  intro hPast
  obtain ⟨K, hBefore, hMem⟩ :=
    (by
      simpa [Formula.past, Sat, Formula.ofEvent] using hPast)
  have hEvent :
      ⟨K,q⟩ ⊨[M ∣ᵥ H',σ] Formula.ofEvent evt :=
    by simpa [Formula.ofEvent, Sat] using hMem
  obtain ⟨e, he⟩ := hBefore
  have hSubset : H'.val ⊆ H.val := hSub.1
  have he' :
      (q,
          e,
          K.val) ∈ H.val := hSubset _ he
  have hBeforeH : K.val ≺ₚ[q] H.val := ⟨e, he'⟩
  have hEvent' :
      ⟨K,q⟩ ⊨[M ∣ᵥ H,σ] Formula.ofEvent evt :=
    Sat.ofEvent_of_subset (M := M) (σ := σ) (H := H) (H₁ := H')
      (H₂ := K) (p := q) (evt := evt)
      (hSubset := hSubset) hEvent
  have hMem' :
      (q,
          MaybeEvent.some
            ⟨evt.sym, List.map (Term.eval σ ∘ Term.ofValue) evt.args⟩,
          K.val) ∈ H.val :=
    by simpa [Formula.ofEvent, Sat, Term.evalList, List.map_map, Function.comp]
      using hEvent'
  have hPastH :
      ⟨H,q⟩ ⊨[M ∣ᵥ H,σ]
        ↓ᶠ (Formula.ofEvent evt) :=
    by
      simpa [Formula.past, Sat, Formula.ofEvent,
        Term.evalList, List.map_map, Function.comp]
        using ⟨K, hBeforeH, hMem'⟩
  exact
    (Sat.not_elim (M := M ∣ᵥ H) (σ := σ) (H := H) (p := q)
      (φ := ↓ᶠ (Formula.ofEvent evt))) hNot hPastH

/-- Lift singleton-quorum diamonds along a pointwise transfer principle. -/
lemma sat_diamond_singleton_transfer
    (M : Model S P) (σ : Assignment S)
    (H H' : History P (Signature.EventType S)) (p : P)
    (l : Signature.Value S) (φ : Formula S)
    (hTransfer : ∀ q,
        (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]φ) →
          (⟨H',q⟩ ⊨[M ∣ᵥ H',σ]φ)) :
    (⟨H,p⟩ ⊨[M, σ]
        ♢ᶠ[Term.ofValues [l]] φ) →
      (⟨H',p⟩ ⊨[M, σ]
        ♢ᶠ[Term.ofValues [l]] φ) := by
  classical
  intro hDiamond
  have hWitness :=
    (sat_diamond_singleton_iff (M := M) (σ := σ)
      (H := H) (p := p) (l := l) (φ := φ)).1 hDiamond
  have hWitness' :
      ∀ O ∈ (M.learner l).quorums,
        ∃ q ∈ O,
          ⟨H',q⟩ ⊨[M ∣ᵥ H',σ]φ := by
    intro O hO
    rcases hWitness O hO with ⟨q, hqO, hqSat⟩
    exact ⟨q, hqO, hTransfer q hqSat⟩
  exact
    (sat_diamond_singleton_iff (M := M) (σ := σ)
      (H := H') (p := p) (l := l) (φ := φ)).2 hWitness'

/-- Singleton learner diamonds do not depend on the distinguished participant. -/
lemma sat_diamond_singleton_participant_iff
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p q : P) (l : Signature.Value S) (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l]] φ) ↔
      (⟨H,q⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l]] φ) := by
  classical
  constructor
  · intro hDiamond
    have hWitness :=
      (sat_diamond_singleton_iff (M := M) (σ := σ)
        (H := H) (p := p) (l := l) (φ := φ)).1 hDiamond
    exact
      (sat_diamond_singleton_iff (M := M) (σ := σ)
        (H := H) (p := q) (l := l) (φ := φ)).2 hWitness
  · intro hDiamond
    have hWitness :=
      (sat_diamond_singleton_iff (M := M) (σ := σ)
        (H := H) (p := q) (l := l) (φ := φ)).1 hDiamond
    exact
      (sat_diamond_singleton_iff (M := M) (σ := σ)
        (H := H) (p := p) (l := l) (φ := φ)).2 hWitness

/-- Restricting the model preserves singleton learner diamonds. -/
lemma sat_diamond_singleton_localView
    (M : Model S P) (σ : Assignment S)
    (H K : History P (Signature.EventType S)) (p : P)
    (l : Signature.Value S) (φ : Formula S) :
    (⟨K,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l]] φ) →
      (⟨K,p⟩ ⊨[M ∣ᵥ H, σ]
        ♢ᶠ[Term.ofValues [l]] φ) := by
  classical
  intro hDiamond
  have hWitness :=
    (sat_diamond_singleton_iff (M := M) (σ := σ)
      (H := K) (p := p) (l := l) (φ := φ)).1 hDiamond
  have hLocalWitness :
      ∀ O ∈ ((M ∣ᵥ H).learner l).quorums,
        ∃ r ∈ O,
          ⟨K,r⟩ ⊨[(M ∣ᵥ H) ∣ᵥ K, σ] φ := by
    intro O hO
    have hO' : O ∈ (M.learner l).quorums := by simpa using hO
    obtain ⟨r, hrO, hrSat⟩ := hWitness O hO'
    exact ⟨r, hrO, by simpa [Model.localView_comp] using hrSat⟩
  exact
    (sat_diamond_singleton_iff (M := M ∣ᵥ H) (σ := σ)
      (H := K) (p := p) (l := l) (φ := φ)).2 hLocalWitness

/-- Expand an empty learner past diamond into an explicit past witness. -/
lemma sat_diamondPast_nil_iff
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P)
    (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ↓[Term.ofValues []] φ) ↔
      ∃ q : P,
        ∃ H' : History P (Signature.EventType S),
          (H'.val ≺ₚ[q] H.val) ∧
            ((H'.val ⊆trn H.val) ∧
              ⟨H',q⟩ ⊨[M ∣ᵥ H, σ] φ) := by
  classical
  constructor
  · intro hDiamond
    have hData :
        ∃ q : P,
          ∃ H' : History P (Signature.EventType S),
            (∃ e, (q, e, H'.val) ∈ H.val) ∧
              ⟨H',q⟩ ⊨[M ∣ᵥ H,σ] φ :=
      by
        classical
        simpa [Formula.diamondPast, Term.ofValues, Sat, Sat.check,
          Formula.past, Set.mem_univ]
          using hDiamond
    rcases hData with ⟨q, H', hBefore, hLocal⟩
    have hSubset : H'.val ⊆trn H.val :=
      happensBeforeAt_implies_transitiveSubset (h1 := H') (h2 := H) (p := q)
        (by simpa [PreHistory.happensBeforeAt] using hBefore)
    exact ⟨q, H', hBefore, hSubset, hLocal⟩
  · rintro ⟨q, H', hBefore, hSubset, hLocal⟩
    have hData :
        ∃ q' : P,
          ∃ H'' : History P (Signature.EventType S),
            (∃ e, (q', e, H''.val) ∈ H.val) ∧
              ⟨H'',q'⟩ ⊨[M ∣ᵥ H,σ] φ :=
      ⟨q, H', by simpa [PreHistory.happensBeforeAt] using hBefore, hLocal⟩
    have hDiamond :
        ⟨H,p⟩ ⊨[M, σ] ♢ᶠ↓[Term.ofValues []] φ :=
      by
        classical
        simpa [Formula.diamondPast, Term.ofValues, Sat, Sat.check,
          Formula.past, Set.mem_univ]
          using hData
    exact hDiamond

private lemma diamond_valid_eventuallyPast_not_iff
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] ♢ᶠ[Term.ofValues ls]
        (Formula.eventuallyPast (¬ᶠ φ))) ↔
      (⊨[M, σ] ♢ᶠ[Term.ofValues ls]
        (¬ᶠ (Formula.past φ))) := by
  classical
  exact
    Logic.EndValid.congr (M := M) (σ := σ)
      (φ := ♢ᶠ[Term.ofValues ls]
        (Formula.eventuallyPast (¬ᶠ φ)))
      (ψ := ♢ᶠ[Term.ofValues ls]
        (¬ᶠ (Formula.past φ)))
      (fun p =>
        Sat.diamond_eventuallyPast_not_iff
          (M := M) (σ := σ) (H := M.history)
          (ts := Term.ofValues ls) (φ := φ) (p := p))

private lemma valid_not_not_iff
    (M : Model S P) (σ : Assignment S) (φ : Formula S) :
    (⊨[M, σ] ¬ᶠ (¬ᶠ φ)) ↔ (⊨[M,σ]φ) := by
  classical
  unfold EndValid
  constructor
  · intro h p
    have hSat := h p
    exact
      (Sat.not_not_iff (M := M) (σ := σ)
        (H := M.history) (p := p) (φ := φ)).1 hSat
  · intro h p
    have hSat := h p
    exact
      (Sat.not_not_iff (M := M) (σ := σ)
        (H := M.history) (p := p) (φ := φ)).2 hSat

private lemma valid_not_box_iff_diamond_not
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] ¬ᶠ (□ᶠ[Term.ofValues ls] φ)) ↔
      (⊨[M, σ] ♢ᶠ[Term.ofValues ls] (¬ᶠ φ)) := by
  classical
  simpa [Formula.box, Formula.not] using
    (valid_not_not_iff (M := M) (σ := σ)
      (φ := ♢ᶠ[Term.ofValues ls] (¬ᶠ φ)))

/-! ### Remark 3.7.7: dualities between derived modalities -/

/-- `♢` and `□` are De Morgan duals (Remark 3.7.7(1)). -/
lemma diamond_valid_iff_not_box_not
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] ♢ᶠ[Term.ofValues ls] φ) ↔
      (⊨[M, σ] ¬ᶠ (□ᶠ[Term.ofValues ls] (¬ᶠ φ))) :=
  by
    classical
    have hBD :
        (⊨[M, σ] ¬ᶠ (□ᶠ[Term.ofValues ls] (¬ᶠ φ))) ↔
          (⊨[M, σ] ♢ᶠ[Term.ofValues ls] (¬ᶠ (¬ᶠ φ))) := by
      simpa [Formula.box, Formula.not] using
        (valid_not_not_iff (M := M) (σ := σ)
          (φ := ♢ᶠ[Term.ofValues ls] (¬ᶠ (¬ᶠ φ))))
    have hAD :
        (⊨[M, σ] ♢ᶠ[Term.ofValues ls] φ) ↔
          (⊨[M, σ] ♢ᶠ[Term.ofValues ls] (¬ᶠ (¬ᶠ φ))) := by
      unfold EndValid
      constructor
      · intro h p
        exact
          Sat.diamond_of_imp (M := M) (σ := σ)
            (H := M.history) (ts := Term.ofValues ls)
            (φ := φ) (ψ := ¬ᶠ (¬ᶠ φ)) (p := p)
            (h := fun q =>
              (Sat.not_not_iff (M := M) (σ := σ)
                (H := M.history) (p := q) (φ := φ)).2)
            (h p)
      · intro h p
        exact
          Sat.diamond_of_imp (M := M) (σ := σ)
            (H := M.history) (ts := Term.ofValues ls)
            (φ := ¬ᶠ (¬ᶠ φ)) (ψ := φ) (p := p)
            (h := fun q =>
              (Sat.not_not_iff (M := M) (σ := σ)
                (H := M.history) (p := q) (φ := φ)).1)
            (h p)
    exact hAD.trans hBD.symm

/-- `□` and `♢` are De Morgan duals (Remark 3.7.7(2)). -/
lemma box_valid_iff_not_diamond_not
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] □ᶠ[Term.ofValues ls] φ) ↔
      (⊨[M, σ] ¬ᶠ (♢ᶠ[Term.ofValues ls] (¬ᶠ φ))) := by
  classical
  have h :=
    (diamond_valid_iff_not_box_not (M := M) (σ := σ)
      (ls := ls) (φ := ¬ᶠ φ)).symm
  simp [Formula.not, Formula.box]

/-- `♢ᶠ↓` is the De Morgan dual of `□ᶠ⇓` (Remark 3.7.7(3)). -/
lemma diamondPast_valid_iff_not_boxEventually_not
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] ♢ᶠ↓[Term.ofValues ls] φ) ↔
      (⊨[M, σ] ¬ᶠ (□ᶠ⇓[Term.ofValues ls] (¬ᶠ φ))) :=
  by
    classical
    have hEquiv :
        ∀ p,
          (⟨M.history,p⟩ ⊨[M, σ] ♢ᶠ↓[Term.ofValues ls] φ) ↔
            (⟨M.history,p⟩ ⊨[M, σ]
              ¬ᶠ (□ᶠ⇓[Term.ofValues ls] (¬ᶠ φ))) := by
      intro p
      simpa using
        Sat.diamondPast_not_boxEventually_not
          (M := M) (σ := σ) (H := M.history) (ts := Term.ofValues ls)
          (φ := φ) (p := p)
    exact
    Logic.EndValid.congr (M := M) (σ := σ)
        (φ := ♢ᶠ↓[Term.ofValues ls] φ)
        (ψ := ¬ᶠ (□ᶠ⇓[Term.ofValues ls] (¬ᶠ φ))) hEquiv

private lemma quorumWitnessAcc_univ
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    quorumWitnessAcc M σ ls φ Set.univ ↔
      hasQuorumWitness (M := M) σ ls φ := by
  classical
  constructor
  · intro h F
    obtain ⟨p, _, hpAll, hpSat⟩ := h F
    exact ⟨p, hpAll, hpSat⟩
  · intro h F
    obtain ⟨p, hpAll, hpSat⟩ := h F
    exact ⟨p, by simp, hpAll, hpSat⟩

/-- `□ᶠ⇓` is the De Morgan dual of `♢ᶠ↓` (Remark 3.7.7(4)). -/
lemma boxEventually_valid_iff_not_diamondPast_not
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] □ᶠ⇓[Term.ofValues ls] φ) ↔
      (⊨[M, σ] ¬ᶠ (♢ᶠ↓[Term.ofValues ls] (¬ᶠ φ))) :=
  by
    classical
    unfold EndValid
    constructor
    · intro h p
      exact
        (Sat.boxEventually_not_diamondPast_not
          (M := M) (σ := σ) (H := M.history)
          (ts := Term.ofValues ls) (φ := φ) (p := p)).1 (h p)
    · intro h p
      exact
        (Sat.boxEventually_not_diamondPast_not
          (M := M) (σ := σ) (H := M.history)
          (ts := Term.ofValues ls) (φ := φ) (p := p)).2 (h p)

/-- `♢ᶠ⇓` and `□ᶠ↓` are De Morgan duals (Remark 3.7.7(5)). -/
lemma diamondEventually_valid_iff_not_boxPast_not
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] ♢ᶠ⇓[Term.ofValues ls] φ) ↔
      (⊨[M, σ] ¬ᶠ (□ᶠ↓[Term.ofValues ls] (¬ᶠ φ))) :=
  by
    classical
    have hEquiv :
        ∀ p,
          (⟨M.history,p⟩ ⊨[M, σ] ♢ᶠ⇓[Term.ofValues ls] φ) ↔
            (⟨M.history,p⟩ ⊨[M, σ]
              ¬ᶠ (□ᶠ↓[Term.ofValues ls] (¬ᶠ φ))) := by
      intro p
      simpa using
        Sat.diamondEventually_not_boxPast_not
          (M := M) (σ := σ) (H := M.history) (ts := Term.ofValues ls)
          (φ := φ) (p := p)
    exact
    Logic.EndValid.congr (M := M) (σ := σ)
        (φ := ♢ᶠ⇓[Term.ofValues ls] φ)
        (ψ := ¬ᶠ (□ᶠ↓[Term.ofValues ls] (¬ᶠ φ))) hEquiv

/-- `□ᶠ↓` and `♢ᶠ⇓` are De Morgan duals (Remark 3.7.7(6)). -/
lemma boxPast_valid_iff_not_diamondEventually_not
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] □ᶠ↓[Term.ofValues ls] φ) ↔
      (⊨[M, σ] ¬ᶠ (♢ᶠ⇓[Term.ofValues ls] (¬ᶠ φ))) :=
  by
    classical
    unfold EndValid
    constructor
    · intro h p
      exact
        (Sat.boxPast_not_diamondPast_not
          (M := M) (σ := σ) (H := M.history)
          (ts := Term.ofValues ls) (φ := φ) (p := p)).1 (h p)
    · intro h p
      exact
        (Sat.boxPast_not_diamondPast_not
          (M := M) (σ := σ) (H := M.history)
          (ts := Term.ofValues ls) (φ := φ) (p := p)).2 (h p)

lemma eventValid_atEnd_exists
    (M : Model S P) (σ : Assignment S) {φ : Formula S}
    (hEvent : EventValid M σ (⤒ᶠφ))
    (hNonempty : ∃ t : EventTuple P (Signature.EventType S),
      t ∈ M.history.val) :
    ∃ p : P, ⟨M.history,p⟩ ⊨[M,σ] φ := by
  classical
  obtain ⟨t, ht⟩ := hNonempty
  let h_before : PreHistory.happensBefore (P := P)
      (Event := Signature.EventType S) t.2.2 M.history.val :=
    ⟨t.1, t.2.1, ht⟩
  let h_hered :=
    (History.predecessor_data (P := P)
      (Event := Signature.EventType S)
      (H := M.history) (h_before := h_before)).2
  let Hloc : History P (Signature.EventType S) := ⟨t.2.2, h_hered⟩
  have hSat : ⟨Hloc, t.1⟩ ⊨[M,σ] ⤒ᶠφ := by
    dsimp [EventValid] at hEvent
    simpa [h_before, h_hered, Hloc] using hEvent ht
  refine ⟨t.1, ?_⟩
  exact
    (Sat.atEnd (M := M) (σ := σ)
      (H := Hloc) (p := t.1) (φ := φ)).1 hSat

lemma eventValid_predecessor
    (M : Model S P) (σ : Assignment S) {φ : Formula S}
    (hEvent : EventValid M σ φ)
    {p : P} {e : MaybeEvent (Signature.EventType S)}
    {H : PreHistory P (Signature.EventType S)}
    (hMem : (p, e, H) ∈ M.history.val) :
    ⟨History.predecessorHistory (H := M.history)
        (happensBefore_of_mem (P := P)
          (Event := Signature.EventType S) hMem), p⟩
      ⊨[M,σ] φ := by
  classical
  dsimp [EventValid] at hEvent
  have h := hEvent (ht := hMem)
  simpa [History.predecessorHistory] using h

/-- Satisfaction of an empty box at the full history forces the guard everywhere. -/
lemma sat_boxEmpty_full_iff_local
    (M : Model S P) (σ : Assignment S)
    (p : P) (φ : Formula S) :
    (⟨M.history,p⟩ ⊨[M, σ] □ᶠ[] φ) ↔
      (∀ q : P,
        ⟨M.history,q⟩ ⊨[M, σ] φ) := by
  classical
  simpa [Sat.boxEmpty, Formula.boxEmpty, Formula.box]
    using
      (Sat.boxEmpty (M := M) (σ := σ)
        (H := M.history) (p := p) (φ := φ))

lemma EndValid.boxEmpty_guard
    (M : Model S P) (σ : Assignment S) (φ : Formula S) :
    (⊨[M, σ] □ᶠ[] φ) → ∀ p : P, ⟨M.history,p⟩ ⊨[M, σ] φ := by
  intro h p
  have hBox := h p
  have hLocal :=
    (sat_boxEmpty_full_iff_local (M := M) (σ := σ)
      (p := p) (φ := φ)).1 hBox
  exact hLocal p

lemma hasQuorumWitness.seq_to_past
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) :
    (⊨[M, σ] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (hasQuorumWitness (M := M) σ ls Formula.seq →
        hasQuorumWitness (M := M) σ ls (↓ᶠ Formula.seq)) := by
  classical
  intro hActive hWitness F
  obtain ⟨p, hpAll, hpSeq⟩ := hWitness F
  have hGuard :=
    (EndValid.boxEmpty_guard (M := M) (σ := σ)
      (φ := ↓ᶠ ⊤ᶠ)) hActive p
  obtain ⟨H', evt, hMem⟩ :=
    (by
      simpa [Formula.past, Sat, Formula.top]
        using hGuard)
  let hBeforeRel : H'.val ≺ₚ[p] M.history.val := ⟨evt, hMem⟩
  have hSeqGlobal :
      isSequential (P := P) (Event := Signature.EventType S) p
        M.history.val := by
    simpa [Sat] using hpSeq
  have hBeforeStrict : H'.val ≺− M.history.val :=
    PreHistory.happensBefore_of_happensBeforeAt (P := P)
      (Event := Signature.EventType S) hBeforeRel
  have hSeqH' :
      isSequential (P := P) (Event := Signature.EventType S) p H'.val :=
    sequentiality_of_predecessor (p := p) (H := M.history)
      (h' := H'.val) hBeforeStrict hSeqGlobal
  have hSeqPast :
      ⟨M.history,p⟩ ⊨[M,σ] ↓ᶠ Formula.seq := by
    unfold Sat
    refine ⟨H', hBeforeRel, ?_⟩
    unfold Sat
    exact hSeqH'
  exact ⟨p, hpAll, hSeqPast⟩

/-! ## Results from Section 4 -/

/-- Lemma 4.1.1(1): characterisation of `♢` via quorum witnesses. -/
theorem lemma_4_1_1_witness
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] (♢ᶠ[Term.ofValues ls] φ)) ↔ hasQuorumWitness (M := M) σ ls φ := by
  classical
  constructor
  · intro h
    have hSat :=
      h (Classical.choice (show Nonempty P from inferInstance))
    have hCheck :=
      (sat_diamond_iff_diamondCheck (M := M) (σ := σ)
        (ls := ls) (φ := φ) _).1 hSat
    have hWitnessAcc :=
      (diamondCheck_iff_quorumWitnessAcc (M := M) (σ := σ)
        (ls := ls) (φ := φ) (acc := Set.univ)).1 hCheck
    exact
      (quorumWitnessAcc_univ (M := M) (σ := σ)
        (ls := ls) (φ := φ)).1 hWitnessAcc
  · intro hWitness
    have hWitnessAcc :=
      (quorumWitnessAcc_univ (M := M) (σ := σ)
        (ls := ls) (φ := φ)).2 hWitness
    have hCheck :=
      (diamondCheck_iff_quorumWitnessAcc (M := M) (σ := σ)
        (ls := ls) (φ := φ) (acc := Set.univ)).2 hWitnessAcc
    intro p
    exact
      (sat_diamond_iff_diamondCheck (M := M) (σ := σ)
        (ls := ls) (φ := φ) p).2 hCheck

/-- Lemma 4.1.1(2): nonemptiness under `♢ … ⊤`. -/
theorem lemma_4_1_1_nonempty
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) :
    (⊨[M, σ] (♢ᶠ[Term.ofValues ls] ⊤ᶠ)) ↔ hasQuorumNonempty (M := M) ls := by
  classical
  refine
    (lemma_4_1_1_witness (M := M) (σ := σ) (ls := ls) (φ := ⊤ᶠ)).trans ?_
  constructor
  · intro hWitness F
    rcases hWitness F with ⟨p, hpAll, _⟩
    exact ⟨p, hpAll⟩
  · intro hNonempty F
    rcases hNonempty F with ⟨p, hpAll⟩
    refine ⟨p, hpAll, ?_⟩
    simp [Sat, Formula.top]

/-- Lemma 4.1.1(3): witnesses imply nonemptiness. -/
lemma lemma_4_1_1_imp_nonempty
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    (⊨[M, σ] (♢ᶠ[Term.ofValues ls] φ)) →
      (⊨[M, σ] (♢ᶠ[Term.ofValues ls] ⊤ᶠ)) := by
  intro h
  have hWitness :=
    (lemma_4_1_1_witness (M := M) (σ := σ) (ls := ls) (φ := φ)).1 h
  have hNonempty : hasQuorumNonempty (M := M) ls := by
    intro F
    obtain ⟨p, hpAll, _⟩ := hWitness F
    exact ⟨p, hpAll⟩
  exact
    (lemma_4_1_1_nonempty (M := M) (σ := σ) (ls := ls)).2 hNonempty

/-- Nonempty quorum intersections from Notation 4.1.2. -/
@[simp] def hasNonemptyIntersections
    (M : Model S P) (ls : List (Signature.Value S)) : Prop :=
  ∀ σ, ⊨[M, σ] (♢ᶠ[Term.ofValues ls] ⊤ᶠ)

/-- Sequential quorum intersections from Notation 4.1.2. -/
@[simp] def hasSequentialIntersections
    (M : Model S P) (ls : List (Signature.Value S)) : Prop :=
  ∀ σ, ⊨[M, σ] (♢ᶠ[Term.ofValues ls] Formula.seq)

/-- The `live` predicate viewed as a nullary formula. -/
@[simp] def liveFormula (liveSymb : Signature.PredSymb S) : Formula S :=
  Formula.predicate0 liveSymb

/-- Live quorum intersections from Notation 4.1.2. -/
@[simp] def hasLiveIntersections
    (M : Model S P) (liveSymb : Signature.PredSymb S)
    (ls : List (Signature.Value S)) : Prop :=
  ∀ σ, ⊨[M, σ] (♢ᶠ[Term.ofValues ls] (liveFormula liveSymb))

/-- Lemma 4.1.3(1↔2): quorum witnesses correspond to present-time diamonds. -/
theorem lemma_4_1_3_present
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    hasQuorumWitness (M := M) σ ls φ ↔
      (⊨[M, σ] ♢ᶠ[Term.ofValues ls] φ) :=
  by
    classical
    simpa using
      (lemma_4_1_1_witness (M := M) (σ := σ)
        (ls := ls) (φ := φ)).symm

private lemma localSat_eventuallyPast_top_eq
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P) :
    (⟨H,p⟩ ⊨[M ∣ᵥ H, σ] (⇓ᶠ ⊤ᶠ)) ↔
      ⟨H,p⟩ ⊨[M ∣ᵥ H, σ] ⊤ᶠ := by
  classical
  simp [Formula.eventuallyPast, Formula.not, Formula.top, Sat]

/-- Lemma 4.1.3(1↔3) for `⊤ᶠ`:
nonempty quorum intersections correspond to eventually-past diamonds. -/
theorem lemma_4_1_3_past_top
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) :
    hasQuorumWitness (M := M) σ ls ⊤ᶠ ↔
      (⊨[M, σ] ♢ᶠ⇓[Term.ofValues ls] ⊤ᶠ) :=
  by
    classical
    have hPresent :=
      lemma_4_1_3_present (M := M) (σ := σ)
        (ls := ls) (φ := ⊤ᶠ)
    refine hPresent.trans ?_
    unfold EndValid
    apply forall_congr'
    intro p
    exact
      (Sat.diamond_congr (M := M) (σ := σ) (H := M.history)
        (ts := Term.ofValues ls)
        (φ := ⊤ᶠ) (ψ := ⇓ᶠ ⊤ᶠ) (p := p)
        (h := fun q =>
          (localSat_eventuallyPast_top_eq (M := M) (σ := σ)
            (H := M.history) (p := q)).symm))

/-- Lemma 4.1.3(1↔3) for `⊤ᶠ` (paper Lemma 4.1.3).
The activity assumption corresponds to the learner-independent guard `□ ↓ ⊤`. -/
theorem lemma_4_1_3_past_top_down
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) :
    (⊨[M, σ] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (hasQuorumWitness (M := M) σ ls ⊤ᶠ ↔
        (⊨[M, σ] ♢ᶠ↓[Term.ofValues ls] ⊤ᶠ)) := by
  classical
  intro hActive
  have hPresentTop :=
    lemma_4_1_3_present (M := M) (σ := σ) (ls := ls) (φ := ⊤ᶠ)
  have hPresentPast :=
    lemma_4_1_3_present (M := M) (σ := σ) (ls := ls) (φ := ↓ᶠ ⊤ᶠ)
  have hActiveLocal :=
    (EndValid.boxEmpty_guard (M := M) (σ := σ)
      (φ := ↓ᶠ ⊤ᶠ)) hActive
  constructor
  · intro hWitness
    have hWitnessPast :=
      hasQuorumWitness.of_imp (M := M) (σ := σ) (ls := ls)
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
      hasQuorumWitness.of_imp (M := M) (σ := σ) (ls := ls)
        (φ := ↓ᶠ ⊤ᶠ) (ψ := ⊤ᶠ)
        (h := fun p _ => by simp [Sat, Formula.top])
        hWitnessPast

/-- Lemma 4.1.3(1 → 3) for `Formula.seq` under the `□ ↓ ⊤` activity assumption.
The reverse implication fails in our semantics: a participant can satisfy
`↓ Formula.seq` via an earlier sequential prefix even when the current
history contains incomparable events. -/
theorem lemma_4_1_3_past_seq_down
    (M : Model S P) (σ : Assignment S)
    (ls : List (Signature.Value S)) :
    (⊨[M, σ] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (hasQuorumWitness (M := M) σ ls Formula.seq →
        (⊨[M, σ] ♢ᶠ↓[Term.ofValues ls] Formula.seq)) := by
  classical
  intro hActive hWitness
  have hWitnessPast :=
    hasQuorumWitness.seq_to_past (M := M) (σ := σ) (ls := ls)
      hActive hWitness
  exact
    (lemma_4_1_3_present (M := M) (σ := σ) (ls := ls)
      (φ := ↓ᶠ Formula.seq)).1 hWitnessPast

/-! ## Section 4.2: Interplay between `↓`, `↕`, and quorum modalities -/

/-- Lemma 4.2.1(1): events imply the sometime modality. -/
lemma lemma_4_2_1_part1
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P)
    (E : Signature.EventType S) :
    (⟨H,p⟩ ⊨[M, σ] Formula.ofEvent E) →
      (⟨H,p⟩ ⊨[M, σ] ↕ᶠ (Formula.ofEvent E)) := by
  classical
  intro hEvent
  exact
    (Sat.event_sometime (M := M) (σ := σ) (H := H) (p := p) (E := E)) hEvent

private def binarySignature : Signature :=
  { VarSymb := ULift Unit
    , EventSymb := ULift Unit
    , PredSymb := ULift Empty
    , Value := ULift Bool }

namespace Counterexample

noncomputable section

@[simp] def uniformSignature : Signature :=
  { VarSymb := ULift Unit
    , EventSymb := ULift Unit
    , PredSymb := ULift Empty
    , Value := ULift Unit }

noncomputable instance instDecidableEq_var :
    DecidableEq (Signature.VarSymb uniformSignature) := by
  classical
  infer_instance

@[simp] def uniformSemifilter : Semifilter Unit :=
  { quorums := {O : Set Unit | () ∈ O}
    nonempty := ⟨Set.univ, by simp⟩
    upwardClosed := by
      intro O O' hO hSubset
      exact hSubset hO
    pairwiseInter := by
      intro O O' hO hO'
      refine ⟨(), ?_⟩
      exact ⟨hO, hO'⟩ }

@[simp] def uniformModel : Model uniformSignature Unit :=
  { history := History.emptyHistory Unit (Signature.EventType uniformSignature)
    predInterp := fun _ _ => ∅
    learner := fun _ => uniformSemifilter }

@[simp] def uniformAssignment : Assignment uniformSignature :=
  fun _ => ⟨()⟩

@[simp] def uniformHistory :
    History Unit (Signature.EventType uniformSignature) :=
  uniformModel.history

@[simp] def uniformParticipant : Unit := ()

@[simp] def uniformTop : Formula uniformSignature := ⊤ᶠ

lemma uniform_top_holds :
    (⟨uniformHistory, uniformParticipant⟩ ⊨[uniformModel, uniformAssignment]
      uniformTop) := by
  classical
  simp [uniformTop, Formula.top, Sat]

lemma uniform_not_past :
    ¬ (⟨uniformHistory, uniformParticipant⟩
        ⊨[uniformModel, uniformAssignment]
          ↓ᶠ uniformTop) := by
  classical
  simp [uniformHistory, uniformParticipant, uniformModel,
    uniformTop, Formula.top, Sat, History.emptyHistory]

end

end Counterexample

/-- Lemma 4.2.1(2): `ϕ ⇒ ↓ϕ` need not hold for arbitrary formulas. -/
lemma lemma_4_2_1_part2 :
    ∃ (S : Signature) (P : Type) (hP : Nonempty P),
        let _ := Classical.decEq (Signature.VarSymb S)
        let _ : Nonempty P := hP
        ∃ (M : Model S P) (σ : Assignment S)
          (H : History P (Signature.EventType S)) (p : P) (φ : Formula S),
          (⟨H,p⟩ ⊨[M,σ]φ) ∧ ¬ (⟨H,p⟩ ⊨[M, σ] ↓ᶠ φ) := by
  classical
  refine
    (⟨Counterexample.uniformSignature, Unit, ⟨()⟩, ?_⟩ :
      ∃ (S : Signature) (P : Type) (hP : Nonempty P),
        let _ := Classical.decEq (Signature.VarSymb S)
        let _ : Nonempty P := hP
        ∃ (M : Model S P) (σ : Assignment S)
          (H : History P (Signature.EventType S)) (p : P) (φ : Formula S),
          (⟨H,p⟩ ⊨[M,σ]φ) ∧ ¬ (⟨H,p⟩ ⊨[M, σ] ↓ᶠ φ))
  refine ⟨Counterexample.uniformModel, Counterexample.uniformAssignment,
    Counterexample.uniformHistory, Counterexample.uniformParticipant,
    Counterexample.uniformTop, ?_⟩
  exact ⟨Counterexample.uniform_top_holds, Counterexample.uniform_not_past⟩

/-- Lemma 4.2.1(3): `ϕ ⇒ ↕ϕ` need not hold for arbitrary formulas. -/
lemma lemma_4_2_1_part3 :
    ∃ (S : Signature) (P : Type) (hP : Nonempty P),
        let _ := Classical.decEq (Signature.VarSymb S)
        let _ : Nonempty P := hP
        ∃ (M : Model S P) (σ : Assignment S)
          (H : History P (Signature.EventType S)) (p : P) (φ : Formula S),
          (⟨H,p⟩ ⊨[M,σ]φ) ∧ ¬ (⟨H,p⟩ ⊨[M, σ] ↕ᶠ φ) := by
  classical
  refine
    ⟨Counterexample.uniformSignature, Unit, ⟨()⟩, ?_⟩
  intro _ _
  refine
    ⟨Counterexample.uniformModel, Counterexample.uniformAssignment,
      Counterexample.uniformHistory, Counterexample.uniformParticipant,
      Counterexample.uniformTop, ?_⟩
  have hTop := Counterexample.uniform_top_holds
  have hSome :
      ¬ (⟨Counterexample.uniformHistory, Counterexample.uniformParticipant⟩
          ⊨[Counterexample.uniformModel, Counterexample.uniformAssignment]
            ↕ᶠ Counterexample.uniformTop) := by
    have hAtEnd :
        (⟨Counterexample.uniformHistory, Counterexample.uniformParticipant⟩
          ⊨[Counterexample.uniformModel, Counterexample.uniformAssignment]
            ↕ᶠ Counterexample.uniformTop) ↔
          (⟨Counterexample.uniformHistory, Counterexample.uniformParticipant⟩
            ⊨[Counterexample.uniformModel, Counterexample.uniformAssignment]
              ↓ᶠ Counterexample.uniformTop) := by
      simpa [Formula.sometime]
        using (Sat.atEnd (M := Counterexample.uniformModel)
          (σ := Counterexample.uniformAssignment)
          (H := Counterexample.uniformHistory)
          (p := Counterexample.uniformParticipant)
          (φ := Formula.past Counterexample.uniformTop))
    have hNot := Counterexample.uniform_not_past
    exact fun h => hNot ((hAtEnd.mp h))
  exact ⟨hTop, hSome⟩

/-- Lemma 4.2.2(1): quorum boxes yield empty-list diamonds. -/
lemma lemma_4_2_2_part1
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P)
    (l : Signature.Value S) (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] □ᶠ[Term.ofValues [l]] φ) →
      (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[] φ) := by
  classical
  intro hBox
  have hNoDiamond :
      (⟨H,p⟩ ⊨[M, σ]
        ♢ᶠ[Term.ofValues [l]] (¬ᶠ φ)) → False :=
    (Sat.not (M := M) (σ := σ) (H := H) (p := p)
      (φ := ♢ᶠ[Term.ofValues [l]] (¬ᶠ φ))).1
      (by simpa [Formula.box] using hBox)
  have hNoAll :
      ¬ ∀ O ∈ (M.learner l).quorums,
          ∃ q ∈ O, ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] (¬ᶠ φ) := by
    intro hAll
    exact hNoDiamond
      ((sat_diamond_singleton_iff (M := M) (σ := σ)
        (H := H) (p := p) (l := l) (φ := ¬ᶠ φ)).2 hAll)
  obtain ⟨O, hOmem, hNo⟩ :=
    Semifilter.exists_quorum_forall_not
      (L := M.learner l) hNoAll
  have hAll : ∀ q ∈ O, ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] φ := by
    intro q hq
    have hNoSat := (hNo q hq)
    have hDoubleNot :=
      Sat.not_intro (M := M ∣ᵥ H) (σ := σ)
        (H := H) (p := q) (φ := ¬ᶠ φ) hNoSat
    exact
      (Sat.not_not_iff (M := M ∣ᵥ H) (σ := σ)
        (H := H) (p := q) (φ := φ)).1 hDoubleNot
  obtain ⟨q, hq⟩ := Semifilter.quorum_nonempty (L := M.learner l) hOmem
  exact
    sat_diamondEmpty_of_local (M := M) (σ := σ)
      (H := H) (p := p) (φ := φ) ⟨q, hAll q hq⟩

/-- Lemma 4.2.2(2): the implication from multi-quorum boxes to diamonds can fail. -/
lemma lemma_4_2_2_part2 :
    ∃ (S : Signature) (P : Type) (hP : Nonempty P),
        let _ := Classical.decEq (Signature.VarSymb S)
        let _ : Nonempty P := hP
        ∃ (M : Model S P) (σ : Assignment S)
          (H : History P (Signature.EventType S)) (p : P)
          (ls : List (Signature.Value S)) (φ : Formula S),
          (⟨H,p⟩ ⊨[M, σ] □ᶠ[Term.ofValues ls] φ) ∧
            ¬ (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[] φ) := by
  classical
  refine
    (⟨binarySignature, Bool, ⟨true⟩, ?_⟩ :
      ∃ (S : Signature) (P : Type) (hP : Nonempty P),
        let _ := Classical.decEq (Signature.VarSymb S)
        let _ : Nonempty P := hP
        ∃ (M : Model S P) (σ : Assignment S)
          (H : History P (Signature.EventType S)) (p : P)
          (ls : List (Signature.Value S)) (φ : Formula S),
          (⟨H,p⟩ ⊨[M, σ] □ᶠ[Term.ofValues ls] φ) ∧
            ¬ (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[] φ))
  let learnerBase : Bool → Semifilter Bool := fun b =>
    { quorums := {O : Set Bool | b ∈ O}
      nonempty := ⟨Set.univ, by simp⟩
      upwardClosed := by
        intro O O' hb hSubset
        exact hSubset hb
      pairwiseInter := by
        intro O O' hO hO'
        refine ⟨b, ?_⟩
        exact ⟨hO, hO'⟩ }
  let M : Model binarySignature Bool :=
    { history := History.emptyHistory Bool (Signature.EventType binarySignature)
      predInterp := fun _ _ => ∅
      learner := fun v => learnerBase v.down }
  let σ : Assignment binarySignature := fun _ => ⟨true⟩
  let H : History Bool (Signature.EventType binarySignature) := M.history
  let p : Bool := true
  let ls : List (Signature.Value binarySignature) := [⟨true⟩, ⟨false⟩]
  let φ : Formula binarySignature := ⊥ᶠ
  refine ⟨M, σ, H, p, ls, φ, ?_⟩
  constructor
  · have hNoDiamond :
      ¬ (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues ls] (¬ᶠ φ)) := by
      intro hDiamond
      have hCheck :=
        (sat_diamond_iff_diamondCheck (M := M) (σ := σ)
          (ls := ls) (φ := ¬ᶠ φ) (p := p)).1 hDiamond
      have hFirst :=
        hCheck ({true} : Set Bool)
          (by
            simp [M, learnerBase])
      have hSecond :=
        hFirst ({false} : Set Bool)
          (by
            simp [M, learnerBase])
      obtain ⟨q, hqMem, _⟩ :=
        (by
          simp [diamondCheck] at hSecond :
            ∃ q, q ∈ ({true} : Set Bool) ∩ ({false} : Set Bool) ∧
              ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] (¬ᶠ φ))
      have hqTrue : q = true := by
        have : q ∈ ({true} : Set Bool) :=
          Set.mem_of_mem_inter_left hqMem
        simpa using this
      have hqFalse : q = false := by
        have : q ∈ ({false} : Set Bool) :=
          Set.mem_of_mem_inter_right hqMem
        simpa using this
      exact (by decide : true ≠ false) (hqTrue.symm.trans hqFalse)
    simpa [Formula.box, Formula.not, Sat] using hNoDiamond
  · have : ¬ (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[] φ) := by
      simp [Formula.diamondEmpty, Sat, Sat.check, φ]
    exact this

/-- Lemma 4.2.2(3): validity of ϕ does not force quorum diamonds. -/
lemma lemma_4_2_2_part3 :
    ∃ (S : Signature) (P : Type) (hP : Nonempty P),
        let _ := Classical.decEq (Signature.VarSymb S)
        let _ : Nonempty P := hP
        ∃ (M : Model S P) (σ : Assignment S)
          (H : History P (Signature.EventType S)) (p : P)
          (ls : List (Signature.Value S)) (φ : Formula S),
          (⟨H,p⟩ ⊨[M,σ]φ) ∧
            ¬ (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues ls] φ) := by
  classical
  let counterSignature : Signature :=
    { VarSymb := ULift Unit
      EventSymb := ULift Unit
      PredSymb := ULift Unit
      Value := ULift Unit }
  letI : DecidableEq (Signature.VarSymb counterSignature) :=
    Classical.decEq _
  refine
    (⟨counterSignature, Bool, ⟨false⟩, ?_⟩ :
      ∃ (S : Signature) (P : Type) (hP : Nonempty P),
        let _ := Classical.decEq (Signature.VarSymb S)
        let _ : Nonempty P := hP
        ∃ (M : Model S P) (σ : Assignment S)
          (H : History P (Signature.EventType S)) (p : P)
          (ls : List (Signature.Value S)) (φ : Formula S),
          (⟨H,p⟩ ⊨[M,σ]φ) ∧
            ¬ (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues ls] φ))
  let goodPred : Signature.AtomicPredType counterSignature :=
    ⟨⟨()⟩, []⟩
  let baseSemifilter : Semifilter Bool :=
    { quorums := {O : Set Bool | false ∈ O}
      nonempty := ⟨{false}, by simp⟩
      upwardClosed := by
        intro O O' hO hSubset
        exact hSubset hO
      pairwiseInter := by
        intro O O' hO hO'
        refine ⟨false, ?_⟩
        exact ⟨hO, hO'⟩ }
  let M : Model counterSignature Bool :=
    { history :=
        History.emptyHistory Bool
          (Signature.EventType counterSignature)
      predInterp := fun p' _ =>
        if p' then ({goodPred} : Set (Signature.AtomicPredType counterSignature))
        else ∅
      learner := fun _ => baseSemifilter }
  let σ : Assignment counterSignature := fun _ => ⟨()⟩
  let H : History Bool (Signature.EventType counterSignature) := M.history
  let p : Bool := true
  let ls : List (Signature.Value counterSignature) := [⟨()⟩]
  let φ : Formula counterSignature :=
    Formula.predicate ⟨⟨()⟩, []⟩
  refine ⟨M, σ, H, p, ls, φ, ?_⟩
  constructor
  · -- `φ` holds for participant `true`.
    simp [φ, Sat, M, H, p, goodPred]
  · -- The quorum diamond fails on the singleton quorum `{false}`.
    have hCounter :
        (∀ O ∈ (M.learner ⟨()⟩).quorums,
            ∃ q ∈ O, ⟨H,q⟩ ⊨[M ∣ᵥ H, σ] φ) → False := by
      intro hAll
      have hOmem : ({false} : Set Bool) ∈ (M.learner ⟨()⟩).quorums := by
        simp [M, baseSemifilter]
      obtain ⟨q, hqO, hqSat⟩ := hAll ({false} : Set Bool) hOmem
      have hqFalse : q = false := by
        simpa using hqO
      subst hqFalse
      have : False := by
        simp [Sat, φ, M, H, goodPred] at hqSat
      exact this
    intro hDiamond
    have hSingleton :
        (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [⟨()⟩]] φ) := by
      simpa [ls]
        using hDiamond
    exact hCounter
      ((sat_diamond_singleton_iff
          (M := M) (σ := σ) (H := H) (p := p)
          (l := ⟨()⟩) (φ := φ)).1 hSingleton)

/-- Lemma 4.2.3: past diamonds are idempotent. -/
lemma lemma_4_2_3
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P)
    (evt : Signature.EventType S) :
    (⟨H,p⟩ ⊨[M, σ]
        ♢ᶠ↓[Term.ofValues []]
          (♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt))) →
      (⟨H,p⟩ ⊨[M, σ]
        ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) := by
  classical
  intro hDiamond
  obtain ⟨q, H₁, hData₁⟩ :=
    (sat_diamondPast_nil_iff
        (M := M) (σ := σ) (H := H) (p := p)
        (φ := ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt))).1
      (by simpa using hDiamond)
  rcases hData₁ with ⟨hBefore₁, hRest₁⟩
  rcases hRest₁ with ⟨hSubset₁, hDiamond₁⟩
  obtain ⟨r, H₂, hData₂⟩ :=
    (sat_diamondPast_nil_iff
        (M := M ∣ᵥ H) (σ := σ) (H := H₁) (p := q)
        (φ := Formula.ofEvent evt)).1
      (by simpa using hDiamond₁)
  rcases hData₂ with ⟨hBefore₂, hRest₂⟩
  rcases hRest₂ with ⟨hSubset₂, hEvent₂⟩
  have hBefore₂' :
      H₂.val ≺ₚ[r] H.val :=
    happensBeforeAt_of_subsetTrn
      (P := P) (Event := Signature.EventType S)
      hBefore₂ hSubset₁
  have hSubset₂' :
      H₂.val ⊆trn H.val :=
    transitiveSubset_trans
      (P := P) (Event := Signature.EventType S)
      hSubset₂ hSubset₁
  have hEvent₂' :
      ⟨H₂,r⟩ ⊨[M ∣ᵥ H₁, σ] Formula.ofEvent evt := by
    simpa [Model.localView_comp] using hEvent₂
  have hEvent_final :
      ⟨H₂,r⟩ ⊨[M ∣ᵥ H, σ] Formula.ofEvent evt :=
    Sat.ofEvent_of_subset
      (M := M) (σ := σ) (H := H) (H₁ := H₁) (H₂ := H₂)
      (p := r) (evt := evt)
      (transitiveSubset_subset (P := P)
        (Event := Signature.EventType S) hSubset₁) hEvent₂'
  exact
    (sat_diamondPast_nil_iff
        (M := M) (σ := σ) (H := H) (p := p)
        (φ := Formula.ofEvent evt)).2
      ⟨r, H₂, hBefore₂', ⟨hSubset₂', hEvent_final⟩⟩

/-- Lemma 4.2.4(1): past boxes collapse to present boxes. -/
lemma lemma_4_2_4_part1
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P)
    (l : Signature.Value S) (evt : Signature.EventType S) :
    (⟨H,p⟩ ⊨[M, σ]
        ↓ᶠ (□ᶠ↓[Term.ofValues [l]] (Formula.ofEvent evt))) →
      (⟨H,p⟩ ⊨[M, σ]
        □ᶠ↓[Term.ofValues [l]] (Formula.ofEvent evt)) := by
  classical
  intro hPastBox
  have hPastBox' := hPastBox
  unfold Formula.past at hPastBox'
  unfold Sat at hPastBox'
  rcases hPastBox' with ⟨H', hBefore_p, hBoxPast⟩
  have hSubset : H'.val ⊆trn H.val :=
    happensBeforeAt_implies_transitiveSubset
      (h1 := H') (h2 := H) (p := p) hBefore_p
  obtain ⟨O, hOmem, hAll⟩ :=
    (sat_box_singleton_exists (M := M) (σ := σ)
      (H := H') (p := p) (l := l)
      (φ := ↓ᶠ (Formula.ofEvent evt))).1 hBoxPast
  refine
    (sat_box_singleton_exists (M := M) (σ := σ)
      (H := H) (p := p) (l := l)
      (φ := ↓ᶠ (Formula.ofEvent evt))).2 ⟨O, hOmem, ?_⟩
  intro q hqO
  have hLocal := hAll q hqO
  obtain ⟨K, hBefore_q, hWitnessEvent⟩ :=
    (by
      simpa [Formula.past, Sat]
        using hLocal)
  have hBefore_q' : K.val ≺ₚ[q] H.val :=
    happensBeforeAt_of_subsetTrn
      (P := P) (Event := Signature.EventType S)
      hBefore_q hSubset
  have hEvent :
      (q,
        MaybeEvent.some
          ⟨evt.sym, List.map (Term.eval σ ∘ Term.ofValue) evt.args⟩,
        K.val) ∈ H'.val :=
    by simpa [Formula.ofEvent, Sat]
      using hWitnessEvent
  have hEventSat :
      ⟨K,q⟩ ⊨[M ∣ᵥ H', σ] Formula.ofEvent evt :=
    by simpa [Formula.ofEvent, Sat]
      using hWitnessEvent
  have hEvent' :
      ⟨K,q⟩ ⊨[M ∣ᵥ H, σ] Formula.ofEvent evt :=
    Sat.ofEvent_of_subset (M := M) (σ := σ)
      (H := H) (H₁ := H') (H₂ := K) (p := q) (evt := evt)
      (hSubset := transitiveSubset_subset hSubset) hEventSat
  unfold Sat
  exact ⟨K, hBefore_q', hEvent'⟩

/-- Lemma 4.2.4(2): past diamonds collapse to present diamonds. -/
lemma lemma_4_2_4_part2
    (M : Model S P) (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P)
    (l : Signature.Value S) (evt : Signature.EventType S) :
    (⟨H,p⟩ ⊨[M, σ]
        ♢ᶠ↓[Term.ofValues []]
          (□ᶠ↓[Term.ofValues [l]] (Formula.ofEvent evt))) →
      (⟨H,p⟩ ⊨[M, σ]
        □ᶠ↓[Term.ofValues [l]] (Formula.ofEvent evt)) := by
  classical
  intro hDiamondPast
  obtain ⟨q, H', hWitness⟩ :=
    (sat_diamondPast_nil_iff
        (M := M) (σ := σ) (H := H) (p := p)
        (φ := □ᶠ↓[Term.ofValues [l]] (Formula.ofEvent evt))).1
      (by simpa using hDiamondPast)
  rcases hWitness with ⟨hBefore, hRest⟩
  rcases hRest with ⟨hSubset, hBoxPast⟩
  set φ := ¬ᶠ (↓ᶠ (Formula.ofEvent evt)) with hφ
  have transfer_notPast :
      ∀ r,
        (⟨H,r⟩ ⊨[M ∣ᵥ H, σ] φ) →
          (⟨H',r⟩ ⊨[M ∣ᵥ H', σ] φ) :=
    fun r h =>
      sat_notPast_event_subset (M := M) (σ := σ)
        (H := H) (H' := H') hSubset r evt (by simpa [hφ])
  have liftDiamond :
      (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l]] φ) →
        (⟨H',p⟩ ⊨[M, σ] ♢ᶠ[Term.ofValues [l]] φ) :=
    sat_diamond_singleton_transfer (M := M) (σ := σ)
      (H := H) (H' := H') (p := p) (l := l)
      (φ := φ) transfer_notPast
  have hNoDiamond :
      (⟨H',q⟩ ⊨[M ∣ᵥ H, σ] ♢ᶠ[Term.ofValues [l]] φ) → False :=
    (Sat.not (M := M ∣ᵥ H) (σ := σ)
      (H := H') (p := q)
      (φ := ♢ᶠ[Term.ofValues [l]] φ)).1
      (by
        simpa [Formula.boxPast, Formula.box, Formula.not, hφ]
          using hBoxPast)
  have hNot :
      (⟨H,p⟩ ⊨[M, σ]
        ¬ᶠ (♢ᶠ[Term.ofValues [l]] φ)) :=
    Sat.not_intro (M := M) (σ := σ)
      (H := H) (p := p)
      (φ := ♢ᶠ[Term.ofValues [l]] φ)
      (by
        intro hDiamond
        have hDiamond' := liftDiamond hDiamond
        have hDiamondLocal :=
          sat_diamond_singleton_localView (M := M) (σ := σ)
            (H := H) (K := H') (p := p) (l := l) (φ := φ)
            hDiamond'
        have hDiamond_q :=
          (sat_diamond_singleton_participant_iff
            (M := M ∣ᵥ H) (σ := σ)
            (H := H') (p := p) (q := q)
            (l := l) (φ := φ)).1 hDiamondLocal
        exact hNoDiamond hDiamond_q)
  simpa [Formula.boxPast, Formula.box, Formula.not, hφ] using hNot

end DiamondSection

end Logic
end ModalDistribution
