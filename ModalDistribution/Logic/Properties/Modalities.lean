import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties.Quorums
import ModalDistribution.Core.Semifilter
import ModalDistribution.Core.History

/-!
# Modal operator properties

This file contains properties and lemmas about modal operators (diamond ♢ and box □)
in the modal logic framework. It includes:

- `hasQuorumWitness` definition and characterization lemmas
- Diamond and box modality satisfaction lemmas (sat_diamond_*, sat_box_*)
- De Morgan duality lemmas between ♢ and □ operators
- EventValid lemmas for reasoning about event satisfaction
- Results from Section 4 of the HBB paper (lemma_4_1_1_*, lemma_4_1_3_*, etc.)
- Counterexamples demonstrating limitations of certain implications
- Lemmas about the interplay between temporal operators (↓, ↕) and quorum modalities
-/

namespace ModalDistribution
namespace Logic

open Set
open History
open scoped Semifilter Formula History PreHistory Model

set_option autoImplicit false

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

section DiamondSection

/-- Witness property for `♢` modalities (Lemma~\ref{lemm.n.quorum.intersection}). -/
@[simp] def hasQuorumWitness
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) : Prop :=
  ∀ F : QuorumFamily M ls,
    ∃ p, (∀ i, p ∈ F.choose i) ∧
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] φ

lemma hasQuorumWitness.of_imp
    (M : Model S P)
    (ls : List S.Value) {φ ψ : Formula S}
    (h : ∀ p,
        (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ) →
          ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]ψ) :
    hasQuorumWitness (M := M) ls φ →
      hasQuorumWitness (M := M) ls ψ := by
  intro hWitness F
  obtain ⟨p, hpAll, hpSat⟩ := hWitness F
  exact ⟨p, hpAll, h p hpSat⟩

lemma hasQuorumWitness.congr
    (M : Model S P)
    (ls : List S.Value) {φ ψ : Formula S}
    (h : ∀ p,
        (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ) ↔
          (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]ψ)) :
    hasQuorumWitness (M := M) ls φ ↔
      hasQuorumWitness (M := M) ls ψ := by
  constructor
  · intro hWitness
    exact hasQuorumWitness.of_imp (M := M)
      (ls := ls) (φ := φ) (ψ := ψ)
      (h := fun p => (h p).1) hWitness
  · intro hWitness
    exact hasQuorumWitness.of_imp (M := M)
      (ls := ls) (φ := ψ) (ψ := φ)
      (h := fun p => (h p).2) hWitness

/-- Nonempty intersection property. -/
@[simp] def hasQuorumNonempty
    (M : Model S P)
    (ls : List S.Value) : Prop :=
  ∀ F : QuorumFamily M ls, QuorumFamily.intersectionNonempty F

lemma diamondCheck_of_imp
    (M : Model S P)
    (ls : List S.Value)
    (φ ψ : Formula S) (acc : Set P)
    (h : ∀ p,
        (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ) →
          ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]ψ) :
    Sat.check M M.history.val φ ls acc →
      Sat.check M M.history.val ψ ls acc := by
  classical
  induction ls generalizing acc with
  | nil =>
      intro hCheck
      obtain ⟨p, hpAcc, hpSat⟩ :=
        (Sat.Sat_check_nil (M := M)
          (H := M.history.val) (φ := φ) (acc := acc)).1 hCheck
      exact
        (Sat.Sat_check_nil (M := M)
          (H := M.history.val) (φ := ψ) (acc := acc)).2
          ⟨p, hpAcc, h p hpSat⟩
  | cons l ls ih =>
      intro hCheck
      have hCons :=
        (Sat.Sat_check_cons (M := M)
          (H := M.history.val) (φ := φ)
          (v := l) (vs := ls) (acc := acc)).1 hCheck
      refine
        (Sat.Sat_check_cons (M := M)
          (H := M.history.val) (φ := ψ)
          (v := l) (vs := ls) (acc := acc)).2 ?_
      intro O hO
      exact ih (acc := acc ∩ O) (hCons O hO)

lemma diamondCheck_congr
    (M : Model S P)
    (ls : List S.Value)
    (φ ψ : Formula S) (acc : Set P)
    (h : ∀ p,
        (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ) ↔
         (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]ψ)) :
    Sat.check M M.history.val φ ls acc ↔
      Sat.check M M.history.val ψ ls acc := by
  classical
  constructor
  · intro hCheck
    exact
      diamondCheck_of_imp (M := M)
        (ls := ls) (φ := φ) (ψ := ψ) (acc := acc)
        (h := fun p => (h p).1) hCheck
  · intro hCheck
    exact
      diamondCheck_of_imp (M := M)
        (ls := ls) (φ := ψ) (ψ := φ) (acc := acc)
        (h := fun p => (h p).2) hCheck

def quorumWitnessAcc
    (M : Model S P)
    (ls : List S.Value)
    (φ : Formula S) (acc : Set P) : Prop :=
  ∀ F : QuorumFamily M ls,
    ∃ p, p ∈ acc ∧ (∀ i, p ∈ F.choose i) ∧
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] φ

lemma diamondCheck_iff_quorumWitnessAcc
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S)
    (acc : Set P) :
    Sat.check M M.history.val φ ls acc ↔
      quorumWitnessAcc M ls φ acc := by
  classical
  induction ls generalizing acc with
  | nil =>
      constructor
      · intro h F
        obtain ⟨p, hpacc, hpSat⟩ :=
          (Sat.Sat_check_nil (M := M)
            (H := M.history.val) (φ := φ) (acc := acc)).1 h
        refine ⟨p, hpacc, ?_, hpSat⟩
        simp [List.length_nil]
      · intro h
        obtain ⟨p, hpacc, _, hpSat⟩ :=
          h (QuorumFamily.nil (M := M))
        exact
          (Sat.Sat_check_nil (M := M)
            (H := M.history.val) (φ := φ) (acc := acc)).2
            ⟨p, hpacc, hpSat⟩
  | cons l ls ih =>
      constructor
      · intro h F
        have hCons :=
          (Sat.Sat_check_cons (M := M)
            (H := M.history.val) (φ := φ)
            (v := l) (vs := ls) (acc := acc)).1 h
        have hTail :=
          hCons (QuorumFamily.head (F := F))
            (QuorumFamily.head_mem (F := F))
        obtain ⟨p, hpAccHead, hpTail, hpSat⟩ :=
          (ih (acc := acc ∩ QuorumFamily.head (F := F))).1 hTail
            (QuorumFamily.tail (F := F))
        exact
          (QuorumFamily.exists_forall_choose_cons_inter
            (M := M) (l := l) (ls' := ls) (F := F)
            (acc := acc)
            (R := fun q => ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] φ)).mpr
            ⟨p, hpAccHead, hpTail, hpSat⟩
      · intro h
        refine
          (Sat.Sat_check_cons (M := M)
            (H := M.history.val) (φ := φ)
            (v := l) (vs := ls) (acc := acc)).2 ?_
        intro O hO
        have hWitnessTail :
            quorumWitnessAcc M ls φ (acc ∩ O) := by
          intro Ftail
          obtain ⟨p, hpAcc, hpO, hpTail, hpSat⟩ :=
            (QuorumFamily.exists_forall_choose_cons_cons
              (M := M) (ls' := ls) (F := Ftail)
              (acc := acc) (O := O)
              (R := fun q => ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] φ)).1
              (h (QuorumFamily.cons (M := M) (l := l) O hO Ftail))
          refine ⟨p, ⟨hpAcc, hpO⟩, hpTail, hpSat⟩
        exact (ih (acc := acc ∩ O)).2 hWitnessTail

lemma sat_diamond_iff_diamondCheck
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S)
    (w : World P (Signature.EventType S)) :
    (⟪w⟫ ⊨[M] ♢ᶠ[ls] φ) ↔
      Sat.check M w.time φ ls Set.univ := by
  classical
  simp [Sat]

@[simp] lemma sat_diamond_singleton_iff
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S) :
    (⟪w⟫ ⊨[M] ♢ᶠ[[l]] φ) ↔
      ∀ O ∈ (M.learner l).quorums,
        ∃ q ∈ O, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ := by
  classical
  constructor
  · intro h O hO
    have hCheck :=
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := [l]) (φ := φ) (w := w)).1 h
    have hCons :=
      (Sat.Sat_check_cons (M := M)
        (H := w.time) (φ := φ)
        (v := l) (vs := []) (acc := Set.univ)).1 hCheck
    have hNil := hCons O hO
    obtain ⟨q, hqAcc, hSat⟩ :=
      (Sat.Sat_check_nil (M := M)
        (H := w.time) (φ := φ) (acc := Set.univ ∩ O)).1 hNil
    obtain ⟨_, hqO⟩ := hqAcc
    refine ⟨q, hqO, ?_⟩
    simpa using hSat
  · intro h
    have hCons : Sat.check M w.time φ [l] Set.univ :=
      (Sat.Sat_check_cons (M := M)
        (H := w.time) (φ := φ)
        (v := l) (vs := []) (acc := Set.univ)).2
        (by
          intro O hO
          obtain ⟨q, hqO, hSat⟩ := h O hO
          refine
            (Sat.Sat_check_nil (M := M)
              (H := w.time) (φ := φ) (acc := Set.univ ∩ O)).2
              ⟨q, ?_, hSat⟩
          exact ⟨Set.mem_univ _, hqO⟩)
    exact
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := [l]) (φ := φ) (w := w)).2 hCons

/-- Expand a pair of learner diamonds into quorum-intersection witnesses. -/
@[simp] lemma sat_diamond_pair_iff
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l l' : Signature.Value S) (φ : Formula S) :
    (⟪w⟫ ⊨[M] ♢ᶠ[[l, l']] φ) ↔
      ∀ O ∈ (M.learner l).quorums,
        ∀ O' ∈ (M.learner l').quorums,
          ∃ q ∈ O ∩ O', ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ := by
  classical
  constructor
  · intro h O hO O' hO'
    have hCheck :=
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := [l, l']) (φ := φ) (w := w)).1 h
    have hCons :=
      (Sat.Sat_check_cons (M := M)
        (H := w.time) (φ := φ)
        (v := l) (vs := [l']) (acc := Set.univ)).1 hCheck
    have hCons' :=
      (Sat.Sat_check_cons (M := M)
        (H := w.time) (φ := φ)
        (v := l') (vs := []) (acc := Set.univ ∩ O)).1
        (hCons O hO)
    have hNil := hCons' O' hO'
    obtain ⟨q, hmem, hSat⟩ :=
      (Sat.Sat_check_nil (M := M)
        (H := w.time) (φ := φ)
        (acc := (Set.univ ∩ O) ∩ O')).1 hNil
    have hmem' : q ∈ O ∩ O' := by
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_univ]
        using hmem
    refine ⟨q, hmem', ?_⟩
    simpa using hSat
  · intro h
    have hCons :
        Sat.check M w.time φ [l, l'] Set.univ :=
      (Sat.Sat_check_cons (M := M)
        (H := w.time) (φ := φ)
        (v := l) (vs := [l']) (acc := Set.univ)).2
        (by
          intro O hO
          refine
            (Sat.Sat_check_cons (M := M)
              (H := w.time) (φ := φ)
              (v := l') (vs := []) (acc := Set.univ ∩ O)).2
              (by
                intro O' hO'
                obtain ⟨q, hq, hSat⟩ := h O hO O' hO'
                have hq' : q ∈ (Set.univ ∩ O) ∩ O' := by
                  simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_univ]
                    using hq
                exact
                  (Sat.Sat_check_nil (M := M)
                    (H := w.time) (φ := φ)
                    (acc := (Set.univ ∩ O) ∩ O')).2
                    ⟨q, hq', hSat⟩))
    exact
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := [l, l']) (φ := φ) (w := w)).2 hCons

/-- Singleton learner boxes exhibit a quorum whose members satisfy the guard. -/
@[simp] lemma sat_box_singleton_exists
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S) :
    (⟪w⟫ ⊨[M] □ᶠ[[l]] φ) ↔
      ∃ O ∈ (M.learner l).quorums,
        ∀ q ∈ O, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ := by
  classical
  constructor
  · intro hBox
    by_contra hNo
    have hAll :
        ∀ O ∈ (M.learner l).quorums,
          ∃ q ∈ O, ⟪⟨q, †, w.time⟩⟫ ⊨[M] ¬ᶠ φ := by
      intro O hO
      have hNotAll : ¬ ∀ q ∈ O, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ := by
        intro hAllφ
        exact hNo ⟨O, hO, hAllφ⟩
      obtain ⟨q, hq⟩ := not_forall.mp hNotAll
      obtain ⟨hqO, hqNotφ⟩ := Classical.not_imp.mp hq
      have hqNot : ⟪⟨q, †, w.time⟩⟫ ⊨[M] ¬ᶠ φ :=
        Sat.not_intro (M := M) (w := ⟨q, †, w.time⟩) (φ := φ)
          (by
            intro hφ
            exact hqNotφ hφ)
      exact ⟨q, hqO, hqNot⟩
    have hDiamond :
        ⟪w⟫ ⊨[M] ♢ᶠ[[l]] (¬ᶠ φ) :=
      (sat_diamond_singleton_iff (M := M)
        (w := w) (l := l) (φ := ¬ᶠ φ)).2 hAll
    have hNoDiamond :
        (⟪w⟫ ⊨[M] ♢ᶠ[[l]] (¬ᶠ φ)) → False :=
      (Sat.not (M := M) (w := w)
        (φ := ♢ᶠ[[l]] (¬ᶠ φ))).1
        (by
          simpa [Formula.box, Formula.not] using hBox)
    exact hNoDiamond hDiamond
  · rintro ⟨O, hO, hAll⟩
    have hNoDiamond :
        (⟪w⟫ ⊨[M] ♢ᶠ[[l]] (¬ᶠ φ)) → False := by
      intro hDiamond
      obtain ⟨q, hqO, hqNotφ⟩ :=
        (sat_diamond_singleton_iff (M := M)
          (w := w) (l := l) (φ := ¬ᶠ φ)).1 hDiamond
          O hO
      have hφ := hAll q hqO
      exact
        (Sat.not_elim (M := M) (w := ⟨q, †, w.time⟩) (φ := φ)) hqNotφ hφ
    have hNot :=
      Sat.not_intro (M := M) (w := w)
        (φ := ♢ᶠ[[l]] (¬ᶠ φ)) hNoDiamond
    simpa [Formula.box, Formula.not] using hNot

/-- Helper lemma for transporting empty diamonds from the local view. -/
lemma sat_diamondEmpty_of_local
    (M : Model S P)
    (w : World P (Signature.EventType S)) (φ : Formula S) :
    (∃ q, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ) →
      (⟪w⟫ ⊨[M] ♢ᶠ[] φ) := by
  classical
  intro hWitness
  rcases hWitness with ⟨q, hq⟩
  simpa [Formula.diamondEmpty, Sat, Sat.check] using
    (⟨q, Set.mem_univ q, hq⟩ :
      ∃ r ∈ Set.univ, ⟪⟨r, †, w.time⟩⟫ ⊨[M] φ)

/-- Lift past-event satisfaction from a local view to the ambient history. -/
lemma sat_past_event_of_subset_to_history
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (evt : Signature.EventType S)
    (hSubset : w.time ⊆trn M.history.val)
    (hPast : ⟪w⟫ ⊨[M]↓ᶠ (Formula.ofEvent evt)) :
    ⟪⟨w.place, w.event, M.history.val⟩⟫ ⊨[M]↓ᶠ (Formula.ofEvent evt) := by
  classical
  rcases w with ⟨p, evt', H⟩
  rcases (Sat.past (M := M)
      (w := ⟨p, evt', H⟩) (φ := Formula.ofEvent evt)).1 hPast with
    ⟨t, ht, hp, hEvt⟩
  have ht' : t ∈ M.history.val :=
    (History.transitiveSubset_subset
      (P := P) (Event := Signature.EventType S) hSubset) t ht
  refine
    (Sat.past (M := M)
      (w := ⟨p, evt', M.history.val⟩)
      (φ := Formula.ofEvent evt)).2 ?_
  exact ⟨t, ht', by simpa using hp, hEvt⟩

/-- Lift past satisfaction along an inclusion of prehistories. -/
lemma sat_past_of_subset
    (M : Model S P)
    {q : P}
    {H H' : PreHistory P (Signature.EventType S)}
    {φ : Formula S}
    (hSubset : H ⊆ H') :
    (⟪⟨q, †, H⟩⟫ ⊨[M] ↓ᶠ φ) →
      (⟪⟨q, †, H'⟩⟫ ⊨[M] ↓ᶠ φ) := by
  intro hPast
  rcases (Sat.past (M := M)
      (w := ⟨q, †, H⟩) (φ := φ)).1 hPast with
    ⟨t, ht, hp, hφ⟩
  have ht' : t ∈ H' := hSubset t ht
  exact
    (Sat.past (M := M)
      (w := ⟨q, †, H'⟩) (φ := φ)).2
      ⟨t, ht', hp, hφ⟩

/-- Lift singleton-quorum diamonds along a pointwise transfer principle. -/
lemma sat_diamond_singleton_transfer
    (M : Model S P)
    (w w' : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S)
    (hTransfer : ∀ q,
        (⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) →
          (⟪⟨q, †, w'.time⟩⟫ ⊨[M]φ)) :
    (⟪w⟫ ⊨[M] ♢ᶠ[[l]] φ) →
      (⟪w'⟫ ⊨[M] ♢ᶠ[[l]] φ) := by
  classical
  intro hDiamond
  rcases w with ⟨p, evt, H⟩
  rcases w' with ⟨p', evt', H'⟩
  have hWitness :=
    (sat_diamond_singleton_iff (M := M)
      (w := ⟨p, evt, H⟩) (l := l) (φ := φ)).1 hDiamond
  have hWitness' :
      ∀ O ∈ (M.learner l).quorums,
        ∃ q ∈ O,
          ⟪⟨q, †, H'⟩⟫ ⊨[M] φ := by
    intro O hO
    rcases hWitness O hO with ⟨q, hqO, hqSat⟩
    exact ⟨q, hqO, hTransfer q hqSat⟩
  exact
    (sat_diamond_singleton_iff (M := M)
      (w := ⟨p', evt', H'⟩) (l := l) (φ := φ)).2 hWitness'

/-- Transfer singleton-quorum boxes along a pointwise implication. -/
lemma sat_box_singleton_transfer
    (M : Model S P)
    (w w' : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S)
    (hTransfer : ∀ q,
        (⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) →
          (⟪⟨q, †, w'.time⟩⟫ ⊨[M]φ)) :
    (⟪w⟫ ⊨[M] □ᶠ[[l]] φ) →
      (⟪w'⟫ ⊨[M] □ᶠ[[l]] φ) := by
  classical
  intro hBox
  rcases w with ⟨p, evt, H⟩
  rcases w' with ⟨p', evt', H'⟩
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := ⟨p, evt, H⟩) (l := l) (φ := φ)).1 hBox
  refine
    (sat_box_singleton_exists (M := M)
      (w := ⟨p', evt', H'⟩) (l := l) (φ := φ)).2 ?_
  refine ⟨O, hO, ?_⟩
  intro q hqO
  have hφ := hAll q hqO
  exact hTransfer q hφ

/-- Singleton learner diamonds do not depend on the distinguished participant. -/
lemma sat_diamond_singleton_participant_iff
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (p q : P) (l : Signature.Value S) (φ : Formula S) :
    (⟪⟨p, w.event, w.time⟩⟫ ⊨[M] ♢ᶠ[[l]] φ) ↔
      (⟪⟨q, w.event, w.time⟩⟫ ⊨[M] ♢ᶠ[[l]] φ) := by
  classical
  rcases w with ⟨_, evt, H⟩
  constructor
  · intro hDiamond
    have hWitness :=
      (sat_diamond_singleton_iff (M := M)
        (w := ⟨p, evt, H⟩) (l := l) (φ := φ)).1 hDiamond
    exact
      (sat_diamond_singleton_iff (M := M)
        (w := ⟨q, evt, H⟩) (l := l) (φ := φ)).2 hWitness
  · intro hDiamond
    have hWitness :=
      (sat_diamond_singleton_iff (M := M)
        (w := ⟨q, evt, H⟩) (l := l) (φ := φ)).1 hDiamond
    exact
      (sat_diamond_singleton_iff (M := M)
        (w := ⟨p, evt, H⟩) (l := l) (φ := φ)).2 hWitness

/-- Transport empty-guard past diamonds of event formulas along transitive subsets. -/
lemma sat_diamondPast_nil_event_subset
    (M : Model S P)
    (w w' : World P (Signature.EventType S))
    (symb : Signature.EventSymb S)
    (args : List S.Value)
    (hSubset : w'.time ⊆trn w.time)
    (hDiamond : ⟪w'⟫ ⊨[M]♢ᶠ↓[[]](Formula.event ⟨symb, args⟩)) :
    ⟪w⟫ ⊨[M]♢ᶠ↓[[]](Formula.event ⟨symb, args⟩) := by
  classical
  have transfer :
      ∀ q : P,
        Sat M q † w'.time (↓ᶠ (Formula.event ⟨symb, args⟩)) →
          Sat M q † w.time (↓ᶠ (Formula.event ⟨symb, args⟩)) := by
    intro q hPast
    rcases (Sat.past (M := M)
        (w := ⟨q, †, w'.time⟩)
        (φ := Formula.event ⟨symb, args⟩)).1 hPast with
      ⟨t, ht, hp, hEvt⟩
    have ht' : t ∈ w.time :=
      (History.transitiveSubset_subset
        (P := P) (Event := Signature.EventType S) hSubset) t ht
    exact
      (Sat.past (M := M)
        (w := ⟨q, †, w.time⟩)
        (φ := Formula.event ⟨symb, args⟩)).2
        ⟨t, ht', hp, hEvt⟩
  obtain ⟨q, hPast⟩ :=
    (Sat.Sat_diamond_nil (M := M)
      (w := w')
      (φ := ↓ᶠ (Formula.event ⟨symb, args⟩))).1
      (by simpa [Formula.diamondPast]
        using hDiamond)
  have hPast' := transfer q hPast
  exact
    (Sat.Sat_diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ (Formula.event ⟨symb, args⟩))).2
      ⟨q, hPast'⟩

lemma diamond_valid_eventuallyPast_not_iff
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] ♢ᶠ[ls]
        (Formula.eventuallyPast (¬ᶠ φ))) ↔
      (⊨[M] ♢ᶠ[ls]
        (¬ᶠ (Formula.past φ))) := by
  classical
  exact
    Logic.EndValid.congr (M := M)
      (φ := ♢ᶠ[ls]
        (Formula.eventuallyPast (¬ᶠ φ)))
      (ψ := ♢ᶠ[ls]
        (¬ᶠ (Formula.past φ)))
      (fun p =>
        Sat.diamond_eventuallyPast_not_iff
          (M := M)
          (w := ⟨p, †, M.history.val⟩)
          (ts := ls) (φ := φ))

lemma valid_not_not_iff
    (M : Model S P) (φ : Formula S) :
    (⊨[M] ¬ᶠ (¬ᶠ φ)) ↔ (⊨[M]φ) := by
  classical
  unfold EndValid
  constructor
  · intro h p
    have hSat := h p
    exact
      (Sat.not_not_iff (M := M)
        (w := ⟨p, †, M.history.val⟩) (φ := φ)).1 hSat
  · intro h p
    have hSat := h p
    exact
      (Sat.not_not_iff (M := M)
        (w := ⟨p, †, M.history.val⟩) (φ := φ)).2 hSat

lemma valid_not_box_iff_diamond_not
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] ¬ᶠ (□ᶠ[ls] φ)) ↔
      (⊨[M] ♢ᶠ[ls] (¬ᶠ φ)) := by
  classical
  unfold EndValid
  constructor
  · intro h p
    have hSat := h p
    exact
      (Sat.not_not_iff (M := M)
        (w := ⟨p, †, M.history.val⟩)
        (φ := ♢ᶠ[ls] (¬ᶠ φ))).1
        (by
          simpa [Formula.box]
            using hSat)
  · intro h p
    have hSat := h p
    exact
      (Sat.not_not_iff (M := M)
        (w := ⟨p, †, M.history.val⟩)
        (φ := ♢ᶠ[ls] (¬ᶠ φ))).2 hSat

/-! ### Remark 3.7.7: dualities between derived modalities -/

/-- `♢` and `□` are De Morgan duals (Remark 3.7.7(1)). -/
lemma diamond_valid_iff_not_box_not
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] ♢ᶠ[ls] φ) ↔
      (⊨[M] ¬ᶠ (□ᶠ[ls] (¬ᶠ φ))) :=
  by
    classical
    have hDiamondEquiv :
        (⊨[M] ♢ᶠ[ls] φ) ↔
          (⊨[M] ♢ᶠ[ls] (¬ᶠ (¬ᶠ φ))) :=
      Logic.EndValid.congr (M := M)
        (φ := ♢ᶠ[ls] φ)
        (ψ := ♢ᶠ[ls] (¬ᶠ (¬ᶠ φ)))
        (fun p =>
          Sat.diamond_congr (M := M)
            (w := ⟨p, †, M.history.val⟩)
            (ts := ls)
            (φ := φ) (ψ := ¬ᶠ (¬ᶠ φ))
            (h := fun q =>
              (Sat.not_not_iff (M := M)
                (w := ⟨q, †, M.history.val⟩)
                (φ := φ)).symm))
    have hNotBox :=
      (valid_not_box_iff_diamond_not (M := M)
        (ls := ls) (φ := ¬ᶠ φ)).symm
    exact hDiamondEquiv.trans hNotBox

/-- `□` and `♢` are De Morgan duals (Remark 3.7.7(2)). -/
lemma box_valid_iff_not_diamond_not
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] □ᶠ[ls] φ) ↔
      (⊨[M] ¬ᶠ (♢ᶠ[ls] (¬ᶠ φ))) := by
  classical
  have h :=
    (diamond_valid_iff_not_box_not (M := M)
      (ls := ls) (φ := ¬ᶠ φ)).symm
  simp [Formula.not, Formula.box]

/-- `♢ᶠ↓` is the De Morgan dual of `□ᶠ⇓` (Remark 3.7.7(3)). -/
lemma diamondPast_valid_iff_not_boxEventually_not
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] ♢ᶠ↓[ls] φ) ↔
      (⊨[M] ¬ᶠ (□ᶠ⇓[ls] (¬ᶠ φ))) :=
  by
    classical
    have hEquiv :
        ∀ p,
          (⟪⟨p, †, M.history.val⟩⟫ ⊨[M] ♢ᶠ↓[ls] φ) ↔
            (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
              ¬ᶠ (□ᶠ⇓[ls] (¬ᶠ φ))) := by
      intro p
      simpa using
        Sat.diamondPast_not_boxEventually_not
          (M := M) (w := ⟨p, †, M.history.val⟩)
          (ts := ls) (φ := φ)
    exact
    Logic.EndValid.congr (M := M)
        (φ := ♢ᶠ↓[ls] φ)
        (ψ := ¬ᶠ (□ᶠ⇓[ls] (¬ᶠ φ))) hEquiv

lemma quorumWitnessAcc_univ
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    quorumWitnessAcc M ls φ Set.univ ↔
      hasQuorumWitness (M := M) ls φ := by
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
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] □ᶠ⇓[ls] φ) ↔
      (⊨[M] ¬ᶠ (♢ᶠ↓[ls] (¬ᶠ φ))) :=
  by
    classical
    unfold EndValid
    constructor
    · intro h p
      have hSat := h p
      exact
        (Sat.boxEventually_not_diamondPast_not
          (M := M) (w := ⟨p, †, M.history.val⟩)
          (ts := ls) (φ := φ)).1 hSat
    · intro h p
      have hSat := h p
      exact
        (Sat.boxEventually_not_diamondPast_not
          (M := M) (w := ⟨p, †, M.history.val⟩)
          (ts := ls) (φ := φ)).2 hSat

/-- `♢ᶠ⇓` and `□ᶠ↓` are De Morgan duals (Remark 3.7.7(5)). -/
lemma diamondEventually_valid_iff_not_boxPast_not
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] ♢ᶠ⇓[ls] φ) ↔
      (⊨[M] ¬ᶠ (□ᶠ↓[ls] (¬ᶠ φ))) :=
  by
    classical
    have hEquiv :
        ∀ p,
          (⟪⟨p, †, M.history.val⟩⟫ ⊨[M] ♢ᶠ⇓[ls] φ) ↔
            (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
              ¬ᶠ (□ᶠ↓[ls] (¬ᶠ φ))) := by
      intro p
      simpa using
        Sat.diamondEventually_not_boxPast_not
          (M := M) (w := ⟨p, †, M.history.val⟩)
          (ts := ls) (φ := φ)
    exact
    Logic.EndValid.congr (M := M)
        (φ := ♢ᶠ⇓[ls] φ)
        (ψ := ¬ᶠ (□ᶠ↓[ls] (¬ᶠ φ))) hEquiv

/-- `□ᶠ↓` and `♢ᶠ⇓` are De Morgan duals (Remark 3.7.7(6)). -/
lemma boxPast_valid_iff_not_diamondEventually_not
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] □ᶠ↓[ls] φ) ↔
      (⊨[M] ¬ᶠ (♢ᶠ⇓[ls] (¬ᶠ φ))) :=
  by
    classical
    unfold EndValid
    constructor
    · intro h p
      have hSat := h p
      exact
        (Sat.boxPast_not_diamondPast_not
          (M := M) (w := ⟨p, †, M.history.val⟩)
          (ts := ls) (φ := φ)).1 hSat
    · intro h p
      have hSat := h p
      exact
        (Sat.boxPast_not_diamondPast_not
          (M := M) (w := ⟨p, †, M.history.val⟩)
          (ts := ls) (φ := φ)).2 hSat

lemma eventValid_atEnd_exists
    (M : Model S P) {φ : Formula S}
    (hEvent : EventValid M (⤒ᶠφ))
    (hNonempty : ∃ t : World P (Signature.EventType S),
      t ∈ M.history.val) :
    ∃ w : World P (Signature.EventType S),
      w.time = M.history.val ∧ ⟪w⟫ ⊨[M] φ := by
  classical
  obtain ⟨t, ht⟩ := hNonempty
  have hAtEnd := hEvent ht
  have hSat : Sat M t.place † M.history.val φ := by
    simpa [Formula.atEnd, Sat] using hAtEnd
  refine ⟨⟨t.place, †, M.history.val⟩, rfl, ?_⟩
  simpa using hSat

lemma eventValid_predecessor
    (M : Model S P) {φ : Formula S}
    (hEvent : EventValid M φ)
    {p : P} {e : MaybeEvent (Signature.EventType S)}
    {H : PreHistory P (Signature.EventType S)}
    (hMem : (p, e, H) ∈ M.history.val) :
    ⟪⟨p, e,
        (History.predecessorHistory (H := M.history)
          (happensBefore_of_mem (P := P)
            (Event := Signature.EventType S) hMem)).val⟩⟫
      ⊨[M] φ := by
  classical
  dsimp [EventValid] at hEvent
  have h := hEvent hMem
  simpa [History.predecessorHistory, happensBefore_of_mem] using h

/-- Satisfaction of an empty box at the full history forces the guard everywhere. -/
lemma sat_boxEmpty_full_iff_local
    (M : Model S P)
    (w : World P (Signature.EventType S)) (φ : Formula S)
    (hTime : w.time = M.history.val) (hEvent : w.event = †) :
    (⟪w⟫ ⊨[M] □ᶠ[] φ) ↔
      (∀ q : P,
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] φ) := by
  classical
  -- `hEvent` is unused but keeps the lemma specialised to end-of-time events.
  cases w with
  | mk p rest =>
      cases rest with
      | mk evt H =>
          have hTime' : H = M.history.val := by simpa using hTime
          have hEvent' : evt = † := by simpa using hEvent
          subst hTime'
          subst hEvent'
          simpa using
            (Sat.boxEmpty (M := M)
              (w := ⟨p, †, M.history.val⟩) (φ := φ))

lemma EndValid.boxEmpty_guard
    (M : Model S P) (φ : Formula S) :
    (⊨[M] □ᶠ[] φ) → ∀ p : P, ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] φ := by
  intro h p
  have hBox := h p
  have hLocal :=
    (sat_boxEmpty_full_iff_local (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := φ) (hTime := rfl) (hEvent := rfl)).1 hBox
  exact hLocal p

lemma hasQuorumWitness.seq_to_past
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (hasQuorumWitness (M := M) ls Formula.seq →
        hasQuorumWitness (M := M) ls (↓ᶠ Formula.seq)) := by
  classical
  intro hActive hWitness F
  obtain ⟨p, hpAll, hpSeq⟩ := hWitness F
  have hGuard :=
    (EndValid.boxEmpty_guard (M := M)
      (φ := ↓ᶠ ⊤ᶠ)) hActive p
  obtain ⟨t, htMem, hpPlace, _⟩ :=
    (Sat.past (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := ⊤ᶠ)).1 hGuard
  let Hlocal := World.time t
  have hpPlace' : t.place = p := hpPlace
  have hSeqGlobal :
      isSequential (P := P) (Event := Signature.EventType S) p
        M.history.val := by
    simpa [Sat] using hpSeq
  have hSeqLocal :
      isSequential (P := P) (Event := Signature.EventType S) p (World.time t) :=
    sequentiality_of_predecessor (p := p) (H := M.history)
      (h' := World.time t)
      (happensBefore_of_mem (P := P)
        (Event := Signature.EventType S) htMem)
      hSeqGlobal
  have hSeqLocal' :
      isSequential (P := P) (Event := Signature.EventType S) t.place (World.time t) := by
    intro t₁ t₂ ht₁ ht₂ hplace₁ hplace₂
    have hplace₁'' : t₁.place = t.place := by
      simpa using hplace₁
    have hplace₂'' : t₂.place = t.place := by
      simpa using hplace₂
    have hplace₁' : t₁.place = p := by
      calc
        t₁.place = t.place := hplace₁''
        _ = p := hpPlace'
    have hplace₂' : t₂.place = p := by
      calc
        t₂.place = t.place := hplace₂''
        _ = p := hpPlace'
    have hLocal := hSeqLocal ht₁ ht₂ hplace₁' hplace₂'
    simpa using hLocal
  have hSeqWorld :
      ⟪t⟫ ⊨[M] Formula.seq :=
    (Sat.seq (M := M) (w := t)).2
      hSeqLocal'
  have hSeqPast :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] ↓ᶠ Formula.seq :=
    (Sat.past (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := Formula.seq)).2
      ⟨t,
        htMem,
        hpPlace',
        hSeqWorld⟩
  exact ⟨p, hpAll, hSeqPast⟩

/-! ## Results from Section 4 -/

/-- Lemma~\ref{lemm.n.quorum.intersection}(1): characterisation of `♢` via quorum witnesses. -/
theorem lemma_4_1_1_witness
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
        (ls := ls) (φ := φ) (acc := Set.univ)).1 hCheck
    exact
      (quorumWitnessAcc_univ (M := M)
        (ls := ls) (φ := φ)).1 hWitnessAcc
  · intro hWitness
    have hWitnessAcc :=
      (quorumWitnessAcc_univ (M := M)
        (ls := ls) (φ := φ)).2 hWitness
    have hCheck :=
      (diamondCheck_iff_quorumWitnessAcc (M := M)
        (ls := ls) (φ := φ) (acc := Set.univ)).2 hWitnessAcc
    intro p
    exact
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := ls) (φ := φ)
        (w := ⟨p, †, M.history.val⟩)).2 hCheck

/-- Lemma~\ref{lemm.n.quorum.intersection}(2): nonemptiness under `♢ … ⊤`. -/
theorem lemma_4_1_1_nonempty
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] (♢ᶠ[ls] ⊤ᶠ)) ↔ hasQuorumNonempty (M := M) ls := by
  classical
  refine
    (lemma_4_1_1_witness (M := M) (ls := ls) (φ := ⊤ᶠ)).trans ?_
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

/-- Lemma~\ref{lemm.n.quorum.intersection}(3): witnesses imply nonemptiness. -/
lemma lemma_4_1_1_imp_nonempty
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] (♢ᶠ[ls] φ)) →
      (⊨[M] (♢ᶠ[ls] ⊤ᶠ)) := by
  intro h
  have hWitness :=
    (lemma_4_1_1_witness (M := M) (ls := ls) (φ := φ)).1 h
  have hNonempty : hasQuorumNonempty (M := M) ls := by
    intro F
    obtain ⟨p, hpAll, _⟩ := hWitness F
    exact ⟨p, hpAll⟩
  exact
    (lemma_4_1_1_nonempty (M := M) (ls := ls)).2 hNonempty

/-- Nonempty quorum intersections from Notation~\ref{nttn.intersecting.quorums}. -/
@[simp] def hasNonemptyIntersections
    (M : Model S P) (ls : List S.Value) : Prop :=
  ⊨[M] (♢ᶠ[ls] ⊤ᶠ)

/-- Sequential quorum intersections from Notation~\ref{nttn.intersecting.quorums}. -/
@[simp] def hasSequentialIntersections
    (M : Model S P) (ls : List S.Value) : Prop :=
  ⊨[M] (♢ᶠ[ls] Formula.seq)

/-- Live quorum intersections from Notation~\ref{nttn.intersecting.quorums}. -/
@[simp] def hasLiveIntersections
    (M : Model S P) (liveSymb : Signature.PredSymb S)
    (ls : List S.Value) : Prop :=
  ⊨[M] (♢ᶠ[ls] (Formula.predicate0 liveSymb))

/-- Quorum witnesses correspond to present-time diamonds
(Lemma~\ref{lemm.n.quorum.intersection}). -/
theorem lemma_4_1_3_present
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    hasQuorumWitness (M := M) ls φ ↔
      (⊨[M] ♢ᶠ[ls] φ) :=
  by
    classical
    simpa using
      (lemma_4_1_1_witness (M := M)
        (ls := ls) (φ := φ)).symm

lemma localSat_eventuallyPast_top_eq
    (M : Model S P)
    (w : World P (Signature.EventType S)) :
    (⟪w⟫ ⊨[M] (⇓ᶠ ⊤ᶠ)) ↔ ⟪w⟫ ⊨[M] ⊤ᶠ := by
  classical
  simp [Formula.eventuallyPast, Formula.not, Formula.top, Sat]

/-- Nonempty quorum intersections correspond to eventually-past diamonds
(cf. Lemma~\ref{lemm.n.quorum.intersection}).
nonempty quorum intersections correspond to eventually-past diamonds. -/
theorem lemma_4_1_3_past_top
    (M : Model S P)
    (ls : List S.Value) :
    hasQuorumWitness (M := M) ls ⊤ᶠ ↔
      (⊨[M] ♢ᶠ⇓[ls] ⊤ᶠ) :=
  by
    classical
    have hPresent :=
      lemma_4_1_3_present (M := M)
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
          (localSat_eventuallyPast_top_eq (M := M)
            (w := ⟨q, †, M.history.val⟩)).symm))

/-- Activity assumption transfers present-time witnesses to past-guarded diamonds
(cf. Lemma~\ref{lemm.n.quorum.intersection}). -/
theorem lemma_4_1_3_past_top_down
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (hasQuorumWitness (M := M) ls ⊤ᶠ ↔
        (⊨[M] ♢ᶠ↓[ls] ⊤ᶠ)) := by
  classical
  intro hActive
  have hPresentTop :=
    lemma_4_1_3_present (M := M) (ls := ls) (φ := ⊤ᶠ)
  have hPresentPast :=
    lemma_4_1_3_present (M := M) (ls := ls) (φ := ↓ᶠ ⊤ᶠ)
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

/-- Sequential witnesses persist under the activity assumption
(cf. Lemma~\ref{lemm.n.quorum.intersection}).
The reverse implication fails in our semantics: a participant can satisfy
`↓ Formula.seq` via an earlier sequential prefix even when the current
history contains incomparable events. -/
theorem lemma_4_1_3_past_seq_down
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
    (lemma_4_1_3_present (M := M) (ls := ls)
      (φ := ↓ᶠ Formula.seq)).1 hWitnessPast

/-! ## Section 4.2: Interplay between `↓`, `↕`, and quorum modalities -/

/-- Lemma~\ref{lemm.atd.implies.someone}(1): singleton quorum boxes imply singleton diamonds. -/
lemma lemma_4_2_1_part1
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

lemma lemma_4_2_1_part2
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

/-- Lemma~\ref{lemm.atd.implies.someone}(2): quorum boxes yield empty-list diamonds. -/
lemma lemma_4_2_2_part1
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
private lemma sat_boxPast_of_predecessor
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

/-- Lemma~\ref{lemm.atedot.idempotent}: past diamonds are idempotent. -/
lemma lemma_4_2_2
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

/-- Lemma~\ref{lemm.itp.atddot}(1): past boxes collapse to present boxes. -/
lemma lemma_4_2_4_part1
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

/-- Lemma~\ref{lemm.itp.atddot}(2): past diamonds collapse to present diamonds. -/
lemma lemma_4_2_4_part2
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

end DiamondSection

end Logic
end ModalDistribution
