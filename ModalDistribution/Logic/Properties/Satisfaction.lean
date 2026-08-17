import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties.Quorums

/-!
# Satisfaction machinery for the quorum modalities

Infrastructure for evaluating `♢`/`□` satisfaction; the paper does not state
these lemmas, except where labelled. The pipeline is:

* `Sat.check` (the recursion inside the `♢` clause of `Sat`) is bridged to
  `quorumWitnessAcc` (a `QuorumFamily` accumulator form, which the induction
  needs) and then to `hasQuorumWitness` (the accumulator-free surface form).
* Singleton/pair/triple instances unfold the diamond and box for short learner
  lists, which is how the protocol proofs consume them.
* Transfer and lifting lemmas move satisfaction between worlds with related
  times, and between event-tuples and the end of time.
-/

namespace ModalDistribution
namespace Logic

open ModalDistribution
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open Set
open scoped Formula History PreHistory

set_option autoImplicit false

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

section DiamondMachinery

/-- Witness property for `♢` modalities. -/
@[simp] def hasQuorumWitness
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) : Prop :=
  ∀ F : QuorumFamily M ls,
    ∃ p, (∀ i, p ∈ F.choose i) ∧
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] φ

theorem hasQuorumWitness.of_imp
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

/-- Nonempty intersection property. -/
@[simp] def hasQuorumNonempty
    (M : Model S P)
    (ls : List S.Value) : Prop :=
  ∀ F : QuorumFamily M ls, QuorumFamily.intersectionNonempty F

def quorumWitnessAcc
    (M : Model S P)
    (ls : List S.Value)
    (Q : P → Prop) (acc : Set P) : Prop :=
  ∀ F : QuorumFamily M ls,
    ∃ p, p ∈ acc ∧ (∀ i, p ∈ F.choose i) ∧ Q p

theorem diamondCheck_iff_quorumWitnessAcc
    (M : Model S P)
    (ls : List S.Value) (Q : P → Prop)
    (acc : Set P) :
    Sat.check M Q ls acc ↔
      quorumWitnessAcc M ls Q acc := by
  classical
  induction ls generalizing acc with
  | nil =>
      constructor
      · intro h F
        obtain ⟨p, hpacc, hpSat⟩ :=
          (Sat.check_nil (M := M)
            (Q := Q) (acc := acc)).1 h
        refine ⟨p, hpacc, ?_, hpSat⟩
        exact fun i => i.elim0
      · intro h
        obtain ⟨p, hpacc, _, hpSat⟩ :=
          h (QuorumFamily.nil (M := M))
        exact
          (Sat.check_nil (M := M)
            (Q := Q) (acc := acc)).2
            ⟨p, hpacc, hpSat⟩
  | cons l ls ih =>
      constructor
      · intro h F
        have hCons :=
          (Sat.check_cons (M := M)
            (Q := Q)
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
            (R := Q)).mpr
            ⟨p, hpAccHead, hpTail, hpSat⟩
      · intro h
        refine
          (Sat.check_cons (M := M)
            (Q := Q)
            (v := l) (vs := ls) (acc := acc)).2 ?_
        intro O hO
        have hWitnessTail :
            quorumWitnessAcc M ls Q (acc ∩ O) := by
          intro Ftail
          obtain ⟨p, hpAcc, hpO, hpTail, hpSat⟩ :=
            (QuorumFamily.exists_forall_choose_cons_cons
              (M := M) (ls' := ls) (F := Ftail)
              (acc := acc) (O := O)
              (R := Q)).1
              (h (QuorumFamily.cons (M := M) (l := l) O hO Ftail))
          refine ⟨p, ⟨hpAcc, hpO⟩, hpTail, hpSat⟩
        exact (ih (acc := acc ∩ O)).2 hWitnessTail

theorem sat_diamond_iff_diamondCheck
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S)
    (w : World P (Signature.EventType S)) :
    (⟪w⟫ ⊨[M] ♢ᶠ[ls] φ) ↔
      Sat.check M (fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) ls Set.univ := by
  classical
  simp [Sat]

/-- Extract a triple intersection witness from `♢ᶠ[[l₁,l₂,l₃]] ⊤ᶠ`. -/
theorem sat_diamond_three_intersection
    (M : Model S P)
    (w : World P (Signature.EventType S))
    {l₁ l₂ l₃ : Signature.Value S}
    {O₁ O₂ O₃ : Set P}
    (hDiamond : ⟪w⟫ ⊨[M]♢ᶠ[[l₁, l₂, l₃]]⊤ᶠ)
    (hO₁ : O₁ ∈ (M.learner l₁).quorums)
    (hO₂ : O₂ ∈ (M.learner l₂).quorums)
    (hO₃ : O₃ ∈ (M.learner l₃).quorums) :
    ∃ p, p ∈ O₁ ∧ p ∈ O₂ ∧ p ∈ O₃ := by
  classical
  have hCheck :=
    (sat_diamond_iff_diamondCheck (M := M)
      (ls := [l₁, l₂, l₃]) (φ := ⊤ᶠ)
      (w := w)).1 hDiamond
  have hCons₁ :=
    (Sat.check_cons (M := M)
      (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]⊤ᶠ)
      (v := l₁) (vs := [l₂, l₃]) (acc := Set.univ)).1 hCheck
  have hCons₂ :=
    (Sat.check_cons (M := M)
      (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]⊤ᶠ)
      (v := l₂) (vs := [l₃]) (acc := Set.univ ∩ O₁)).1
      (hCons₁ O₁ hO₁)
  have hNil :=
    (Sat.check_cons (M := M)
      (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]⊤ᶠ)
      (v := l₃) (vs := []) (acc := (Set.univ ∩ O₁) ∩ O₂)).1
      (hCons₂ O₂ hO₂)
  obtain ⟨p, hpMem, _⟩ :=
    (Sat.check_nil (M := M)
      (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]⊤ᶠ)
      (acc := ((Set.univ ∩ O₁) ∩ O₂) ∩ O₃)).1 (hNil O₃ hO₃)
  have hpInter : p ∈ (Set.univ ∩ O₁) ∩ O₂ := hpMem.1
  have hpO₃ : p ∈ O₃ := by
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_univ]
      using hpMem.2
  have hpO₂ : p ∈ O₂ := by
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_univ]
      using hpInter.2
  have hpO₁ : p ∈ O₁ := by
    simpa [Set.inter_univ] using hpInter.1.2
  exact ⟨p, hpO₁, hpO₂, hpO₃⟩

@[simp] theorem sat_diamond_singleton_iff
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
      (Sat.check_cons (M := M)
        (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ)
        (v := l) (vs := []) (acc := Set.univ)).1 hCheck
    have hNil := hCons O hO
    obtain ⟨q, hqAcc, hSat⟩ :=
      (Sat.check_nil (M := M)
        (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) (acc := Set.univ ∩ O)).1 hNil
    obtain ⟨_, hqO⟩ := hqAcc
    refine ⟨q, hqO, ?_⟩
    simpa using hSat
  · intro h
    have hCons : Sat.check M (fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) [l] Set.univ :=
      (Sat.check_cons (M := M)
        (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ)
        (v := l) (vs := []) (acc := Set.univ)).2
        (by
          intro O hO
          obtain ⟨q, hqO, hSat⟩ := h O hO
          refine
            (Sat.check_nil (M := M)
              (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) (acc := Set.univ ∩ O)).2
              ⟨q, ?_, hSat⟩
          exact ⟨Set.mem_univ _, hqO⟩)
    exact
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := [l]) (φ := φ) (w := w)).2 hCons

/-- Expand a pair of learner diamonds into quorum-intersection witnesses. -/
@[simp] theorem sat_diamond_pair_iff
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
      (Sat.check_cons (M := M)
        (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ)
        (v := l) (vs := [l']) (acc := Set.univ)).1 hCheck
    have hCons' :=
      (Sat.check_cons (M := M)
        (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ)
        (v := l') (vs := []) (acc := Set.univ ∩ O)).1
        (hCons O hO)
    have hNil := hCons' O' hO'
    obtain ⟨q, hmem, hSat⟩ :=
      (Sat.check_nil (M := M)
        (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ)
        (acc := (Set.univ ∩ O) ∩ O')).1 hNil
    have hmem' : q ∈ O ∩ O' := by
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_univ]
        using hmem
    refine ⟨q, hmem', ?_⟩
    simpa using hSat
  · intro h
    have hCons :
        Sat.check M (fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) [l, l'] Set.univ :=
      (Sat.check_cons (M := M)
        (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ)
        (v := l) (vs := [l']) (acc := Set.univ)).2
        (by
          intro O hO
          refine
            (Sat.check_cons (M := M)
              (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ)
              (v := l') (vs := []) (acc := Set.univ ∩ O)).2
              (by
                intro O' hO'
                obtain ⟨q, hq, hSat⟩ := h O hO O' hO'
                have hq' : q ∈ (Set.univ ∩ O) ∩ O' := by
                  simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_univ]
                    using hq
                exact
                  (Sat.check_nil (M := M)
                    (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ)
                    (acc := (Set.univ ∩ O) ∩ O')).2
                    ⟨q, hq', hSat⟩))
    exact
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := [l, l']) (φ := φ) (w := w)).2 hCons

/-- Singleton learner boxes exhibit a quorum whose members satisfy the guard. -/
@[simp] theorem sat_box_singleton_exists
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S) :
    (⟪w⟫ ⊨[M] □ᶠ[[l]] φ) ↔
      ∃ O ∈ (M.learner l).quorums,
        ∀ q ∈ O, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ := by
  classical
  constructor
  · intro hBox
    refine Classical.byContradiction fun hNo => ?_
    have hAll :
        ∀ O ∈ (M.learner l).quorums,
          ∃ q ∈ O, ⟪⟨q, †, w.time⟩⟫ ⊨[M] ¬ᶠ φ := by
      intro O hO
      have hNotAll : ¬ ∀ q ∈ O, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ := by
        intro hAllφ
        exact hNo ⟨O, hO, hAllφ⟩
      obtain ⟨q, hqO, hqNotφ⟩ :
          ∃ q, q ∈ O ∧ ¬ (⟪⟨q, †, w.time⟩⟫ ⊨[M] φ) := by
        refine Classical.byContradiction fun hne => hNotAll ?_
        intro q hqO
        exact Classical.byContradiction fun hnφ => hne ⟨q, hqO, hnφ⟩
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

/-- An end-of-time past box guarantees that the global history contains a witness. -/
theorem exists_history_mem_of_end_boxPast
    (M : Model S P)
    {l : Signature.Value S} {φ : Formula S}
    (hBox : ⊨[M]□ᶠ↓[[l]]φ) :
    ∃ t : World P (Signature.EventType S),
      t ∈ M.history.val := by
  classical
  let p : P := Classical.ofNonempty
  have hBoxTop :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ[[l]] (↓ᶠ φ) :=
    by simpa [Formula.boxPast] using hBox p
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (l := l) (φ := ↓ᶠ φ)).1 hBoxTop
  obtain ⟨q, hq⟩ :=
    (Semifilter.quorum_nonempty (L := M.learner l)
      (O := O) hO)
  have hPast :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] ↓ᶠ φ :=
    hAll q hq
  obtain ⟨t, ht_mem, _, _⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := φ)).1 hPast
  exact ⟨t, by simpa using ht_mem⟩

/-- If a world lies in the global history, an always-past fact at that world
forces the underlying proposition to hold immediately. -/
theorem everytime_now_of_mem
    (M : Model S P)
    {w : World P (Signature.EventType S)} {φ : Formula S}
    (hMem : w ∈ M.history.val)
    (hAlways : ⟪w⟫ ⊨[M]⇕ᶠφ) :
    ⟪w⟫ ⊨[M] φ :=
  (Sat.everytime (M := M) (w := w) (φ := φ)).1 hAlways w hMem rfl

/-- Helper lemma for transporting empty diamonds from the local view. -/
theorem sat_diamondEmpty_of_local
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
theorem sat_past_event_of_subset_to_history
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
theorem sat_past_of_subset
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

/-- Transfer singleton-quorum boxes along a pointwise implication. -/
theorem sat_box_singleton_transfer
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

/-- Transport empty-guard past diamonds of event formulas along transitive subsets. -/
theorem sat_diamondPast_nil_event_subset
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
    (Sat.diamond_nil (M := M)
      (w := w')
      (φ := ↓ᶠ (Formula.event ⟨symb, args⟩))).1
      (by simpa [Formula.diamondPast]
        using hDiamond)
  have hPast' := transfer q hPast
  exact
    (Sat.diamond_nil (M := M)
      (w := w)
      (φ := ↓ᶠ (Formula.event ⟨symb, args⟩))).2
      ⟨q, hPast'⟩

theorem quorumWitnessAcc_univ
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    quorumWitnessAcc M ls
        (fun q => ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]φ) Set.univ ↔
      hasQuorumWitness (M := M) ls φ := by
  classical
  constructor
  · intro h F
    obtain ⟨p, _, hpAll, hpSat⟩ := h F
    exact ⟨p, hpAll, hpSat⟩
  · intro h F
    obtain ⟨p, hpAll, hpSat⟩ := h F
    exact ⟨p, by simp, hpAll, hpSat⟩

/-- Witnesses for `⊤ᶠ` coincide with nonempty intersections. -/
theorem hasQuorumWitness_top_iff_nonempty
    (M : Model S P)
    (ls : List S.Value) :
    hasQuorumWitness (M := M) ls ⊤ᶠ ↔
      hasQuorumNonempty (M := M) ls := by
  classical
  constructor
  · intro hWitness F
    obtain ⟨p, hpAll, _⟩ := hWitness F
    exact ⟨p, hpAll⟩
  · intro hNonempty F
    obtain ⟨p, hpAll⟩ := hNonempty F
    refine ⟨p, hpAll, ?_⟩
    simpa [Formula.top]
      using Sat.top (M := M)
        (w := ⟨p, †, M.history.val⟩)

theorem AllWorldValid_predecessor
    (M : Model S P) {φ : Formula S}
    (hEvent : AllWorldValid M φ)
    {p : P} {e : MaybeEvent (Signature.EventType S)}
    {H : PreHistory P (Signature.EventType S)}
    (hMem : (p, e, H) ∈ M.history.val) :
    ⟪⟨p, e,
        (History.predecessorHistory (H := M.history)
          (happensBefore_of_mem (P := P)
            (Event := Signature.EventType S) hMem)).val⟩⟫
      ⊨[M] φ := by
  classical
  dsimp [AllWorldValid] at hEvent
  have hBefore :
      (History.predecessorHistory (H := M.history)
          (happensBefore_of_mem (P := P)
            (Event := Signature.EventType S) hMem)).val
        ⪯ M.history.val :=
    PreHistory.happensBeforeEq_of_mem
      (P := P) (Event := Signature.EventType S)
      (hmem := by
        simpa [History.predecessorHistory, happensBefore_of_mem,
          World.place, World.event, World.time] using hMem)
  have h :=
    hEvent
      (t :=
        ⟨p, e,
          (History.predecessorHistory (H := M.history)
              (happensBefore_of_mem (P := P)
                (Event := Signature.EventType S) hMem)).val⟩)
      hBefore
  simpa [History.predecessorHistory, happensBefore_of_mem] using h

/-- A world whose local history occurs before the model history inherits a transitive subset. -/
theorem time_subset_trn_history
    (M : Model S P) {t : World P S.EventType}
    (ht : t.time ⪯ M.history.val) :
    t.time ⊆trn M.history.val := by
  classical
  have h := (PreHistory.happensBeforeEq_iff
      (P := P) (Event := Signature.EventType S)
      t.time M.history.val).mp ht
  cases h with
  | inl hBefore =>
      refine ⟨
        History.subset_of_happensBefore (H := M.history) hBefore,
        (History.predecessor_data (H := M.history)
            (h_before := hBefore)).2⟩
  | inr hEq =>
      refine ⟨?subset, ?hered⟩
      · intro x hx
        exact hEq ▸ hx
      · have hTrans := History.hereditarilyTransitive M.history
        exact Eq.subst
          (motive := fun H => isHereditarilyTransitive H)
          hEq.symm hTrans

/-- Satisfaction of an empty box at the full history forces the guard everywhere. -/
theorem sat_boxEmpty_full_iff_local
    (M : Model S P)
    (w : World P (Signature.EventType S)) (φ : Formula S)
    (hTime : w.time = M.history.val) :
    (⟪w⟫ ⊨[M] □ᶠ[] φ) ↔
      (∀ q : P,
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] φ) := by
  classical
  cases w with
  | mk p rest =>
      cases rest with
      | mk evt H =>
          have hTime' : H = M.history.val := by simpa using hTime
          subst hTime'
          simpa using
            (Sat.boxEmpty (M := M)
              (w := ⟨p, evt, M.history.val⟩) (φ := φ))

theorem EndValid.boxEmpty_guard
    (M : Model S P) (φ : Formula S) :
    (⊨[M] □ᶠ[] φ) → ∀ p : P, ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] φ := by
  intro h p
  have hBox := h p
  have hLocal :=
    (sat_boxEmpty_full_iff_local (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := φ) (hTime := rfl)).1 hBox
  exact hLocal p

theorem hasQuorumWitness.seq_to_past
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
  have hpPlace' : t.place = p := hpPlace
  have hSeqGlobal :
      isSequential (P := P) (Event := Signature.EventType S) p
        M.history.val := by
    exact (Sat.seq (M := M) (w := ⟨p, †, M.history.val⟩)).1 hpSeq
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
    have hLocal := hSeqLocal t₁ t₂ ht₁ ht₂ hplace₁' hplace₂'
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

theorem localSat_allPast_top_eq
    (M : Model S P)
    (w : World P (Signature.EventType S)) :
    (⟪w⟫ ⊨[M] (⇓ᶠ ⊤ᶠ)) ↔ ⟪w⟫ ⊨[M] ⊤ᶠ := by
  classical
  simp [Formula.allPast, Formula.not, Formula.top, Sat]

/-- Evaluation of a `⊤ᶠ`-payload diamond does not depend on the timeline. -/
theorem sat_check_top_congr
    (M : Model S P)
    (ls : List (Signature.Value S))
    {t₁ t₂ : PreHistory P (Signature.EventType S)}
    {acc : Set P} :
    Sat.check M (fun q => ⟪⟨q, †, t₁⟩⟫ ⊨[M]⊤ᶠ) ls acc ↔
      Sat.check M (fun q => ⟪⟨q, †, t₂⟩⟫ ⊨[M]⊤ᶠ) ls acc := by
  classical
  constructor <;>
    exact
      Sat.check_of_imp (M := M)
        (fun q _ => by simp [Formula.top, Sat])

/-- Diamonds with payload `⊤ᶠ` depend only on the learners' quorums. -/
theorem sat_diamond_top_iff_hasQuorumNonempty
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (ls : List (Signature.Value S)) :
    (⟪w⟫ ⊨[M] ♢ᶠ[ls] ⊤ᶠ) ↔ hasQuorumNonempty (M := M) ls := by
  classical
  constructor
  · intro hDiamond
    have hCheck_time :=
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := ls) (φ := ⊤ᶠ)
        (w := w)).1 hDiamond
    have hCheck_hist :=
      (sat_check_top_congr (M := M)
        (ls := ls)
        (t₁ := w.time) (t₂ := M.history.val)
        (acc := Set.univ)).1 hCheck_time
    have hWitness :=
      (diamondCheck_iff_quorumWitnessAcc (M := M)
        (ls := ls)
        (Q := fun q => ⟪⟨q, †, M.history.val⟩⟫ ⊨[M](⊤ᶠ : Formula S))
        (acc := Set.univ)).1
        hCheck_hist
    have hWitness' :=
      (quorumWitnessAcc_univ (M := M)
        (ls := ls) (φ := ⊤ᶠ)).1 hWitness
    exact
      (hasQuorumWitness_top_iff_nonempty (M := M)
        (ls := ls)).1 hWitness'
  · intro hNonempty
    have hWitness :=
      (hasQuorumWitness_top_iff_nonempty (M := M)
        (ls := ls)).2 hNonempty
    have hWitnessAcc :=
      (quorumWitnessAcc_univ (M := M)
        (ls := ls) (φ := ⊤ᶠ)).2 hWitness
    have hCheck_hist :=
      (diamondCheck_iff_quorumWitnessAcc (M := M)
        (ls := ls)
        (Q := fun q => ⟪⟨q, †, M.history.val⟩⟫ ⊨[M](⊤ᶠ : Formula S))
        (acc := Set.univ)).2
        hWitnessAcc
    have hCheck_time :=
      (sat_check_top_congr (M := M)
        (ls := ls)
        (t₁ := M.history.val) (t₂ := w.time)
        (acc := Set.univ)).1 hCheck_hist
    exact
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := ls) (φ := ⊤ᶠ)
        (w := w)).2 hCheck_time

/-- Lift a learner-guarded past box from a world whose time embeds in the
end-of-time history to validity at the end of time. -/
theorem lift_boxPast_to_end
    (M : Model S P)
    {t : World P (Signature.EventType S)}
    {learner : Signature.Value S}
    {φ : Formula S}
    (hSubset : t.time ⊆ M.history.val)
    (hBox : ⟪t⟫ ⊨[M]□ᶠ↓[[learner]]φ) :
    ⊨[M]□ᶠ↓[[learner]]φ := by
  classical
  have hBoxPast_at :
      ⟪t⟫ ⊨[M]□ᶠ[[learner]](↓ᶠ φ) :=
    by simpa [Formula.boxPast] using hBox
  intro p
  have hBoxPast_top :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]□ᶠ[[learner]](↓ᶠ φ) :=
    sat_box_singleton_transfer (M := M)
      (w := t) (w' := ⟨p, †, M.history.val⟩)
      (l := learner)
      (φ := ↓ᶠ φ)
      (hTransfer := fun q hPast =>
        sat_past_of_subset (M := M)
          (q := q)
          (H := t.time)
          (H' := M.history.val)
          (φ := φ)
          (hSubset := hSubset) hPast)
      hBoxPast_at
  simpa [Formula.boxPast]
    using hBoxPast_top

/-- Paper: Lemma 3.6.4(3). Characterisation of the `♢↓` modality: `♢↓[ls]φ` holds at `w` exactly when
every choice of one quorum per learner admits an accessible world whose place
lies in the intersection and which satisfies `φ`. -/
theorem sat_diamondPast_iff_quorum_witness
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (ls : List S.Value) (φ : Formula S) :
    (⟪w⟫ ⊨[M]♢ᶠ↓[ls]φ) ↔
      ∀ F : QuorumFamily M ls,
        ∃ w' : World P (Signature.EventType S),
          w' ≪ w ∧ (∀ i, w'.place ∈ F.choose i) ∧ ⟪w'⟫ ⊨[M]φ := by
  classical
  have hUnfold :
      (⟪w⟫ ⊨[M]♢ᶠ↓[ls]φ) ↔
        Sat.check M (fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M](↓ᶠ φ)) ls Set.univ := by
    simpa [Formula.diamondPast] using
      sat_diamond_iff_diamondCheck (M := M)
        (ls := ls) (φ := ↓ᶠ φ) (w := w)
  rw [hUnfold,
    diamondCheck_iff_quorumWitnessAcc (M := M)
      (ls := ls) (Q := fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M](↓ᶠ φ))
      (acc := Set.univ)]
  constructor
  · intro h F
    obtain ⟨p, _, hpAll, hpPast⟩ := h F
    obtain ⟨t, ht_mem, ht_place, ht_sat⟩ :=
      (Sat.past (M := M) (w := ⟨p, †, w.time⟩) (φ := φ)).1 hpPast
    refine ⟨t, ?_, ?_, ht_sat⟩
    · simpa [World.accessible] using ht_mem
    · intro i
      exact ht_place.symm ▸ hpAll i
  · intro h F
    obtain ⟨w', hAcc, hAll, hSat⟩ := h F
    refine ⟨w'.place, by simp, hAll, ?_⟩
    exact
      (Sat.past (M := M) (w := ⟨w'.place, †, w.time⟩) (φ := φ)).2
        ⟨w', by simpa [World.accessible] using hAcc, rfl, hSat⟩

end DiamondMachinery

end Logic
end ModalDistribution
