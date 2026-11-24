import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties.Quorums

/-!
# Satisfaction of the quorum modalities

Lemmas for evaluating `♢` and `□`; the paper does not state them, except where
labelled.

* `Sat.check_iff_forall_quorumFamily` reads the recursion `Sat.Check` inside
  the `♢` clause of `Sat` as a statement about every choice of one quorum per
  learner (a `QuorumFamily`). `sat_diamond_iff_forall_quorumFamily` is its
  form for a diamond, and `HasQuorumWitness` names it at the end of time.
* The singleton, pair and triple instances unfold `♢` and `□` for short
  learner lists, which is how the protocol proofs use them.
* Transfer lemmas move satisfaction between worlds with related times, and
  between event-tuples and the end of time.
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

/-! ### Diamonds as statements about quorum families -/

/-- At the end of time, every choice of one quorum per learner in `ls` has a
common member satisfying `φ`. -/
@[simp] def HasQuorumWitness
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) : Prop :=
  ∀ F : QuorumFamily M ls,
    ∃ p, (∀ i, p ∈ F.choose i) ∧
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] φ

/-- Every choice of one quorum per learner in `ls` has a common member. -/
@[simp] def HasQuorumNonempty
    (M : Model S P)
    (ls : List S.Value) : Prop :=
  ∀ F : QuorumFamily M ls, QuorumFamily.IntersectionNonempty F

/-- `Sat.Check M Q ls acc` holds exactly when every choice of one quorum per
learner in `ls` has a common member in `acc` satisfying `Q`. -/
theorem Sat.check_iff_forall_quorumFamily
    (M : Model S P) (Q : P → Prop) (ls : List S.Value) (acc : Set P) :
    Sat.Check M Q ls acc ↔
      ∀ F : QuorumFamily M ls, ∃ p ∈ acc, (∀ i, p ∈ F.choose i) ∧ Q p := by
  induction ls generalizing acc with
  | nil =>
      exact ⟨fun ⟨p, hp, hQ⟩ _ => ⟨p, hp, fun i => i.elim0, hQ⟩,
        fun h => let ⟨p, hp, _, hQ⟩ := h (QuorumFamily.nil M); ⟨p, hp, hQ⟩⟩
  | cons l ls ih =>
      simp only [Sat.check_cons, ih]
      constructor
      · -- Use the family's head quorum, then its tail.
        intro h F
        obtain ⟨p, ⟨hpAcc, hpHead⟩, hpTail, hQ⟩ := h F.head F.head_mem F.tail
        exact ⟨p, hpAcc, (F.forall_choose_cons p).2 ⟨hpHead, hpTail⟩, hQ⟩
      · -- Prepend the given quorum to a family over the remaining learners.
        intro h O hO F
        obtain ⟨p, hpAcc, hpAll, hQ⟩ := h (.cons O hO F)
        obtain ⟨hpO, hpF⟩ := ((QuorumFamily.cons O hO F).forall_choose_cons p).1 hpAll
        exact ⟨p, ⟨hpAcc, hpO⟩, hpF, hQ⟩

/-- `♢[ls]φ` unfolds to the quorum check `Sat.Check` of its body at the end of
the current time. -/
theorem sat_diamond_iff_diamond_check
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S)
    (w : World P (Signature.EventType S)) :
    (⟪w⟫ ⊨[M] ♢ᶠ[ls] φ) ↔
      Sat.Check M (fun q => ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) ls Set.univ := Iff.rfl

/-- `♢[ls]φ` holds exactly when every choice of one quorum per learner in `ls`
has a common member satisfying `φ` at the end of the current time. -/
theorem sat_diamond_iff_forall_quorumFamily
    {M : Model S P} {w : World P (Signature.EventType S)}
    {ls : List S.Value} {φ : Formula S} :
    (⟪w⟫ ⊨[M] ♢ᶠ[ls] φ) ↔
      ∀ F : QuorumFamily M ls,
        ∃ p, (∀ i, p ∈ F.choose i) ∧ ⟪⟨p, †, w.time⟩⟫ ⊨[M] φ :=
  (Sat.check_iff_forall_quorumFamily M _ ls univ).trans <| forall_congr' fun _ =>
    ⟨fun ⟨p, _, h⟩ => ⟨p, h⟩, fun ⟨p, h⟩ => ⟨p, trivial, h⟩⟩

/-- Diamonds with body `⊤` hold exactly when every choice of quorums has a
common member; this does not depend on the world. -/
theorem sat_diamond_top_iff_hasQuorumNonempty
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (ls : List (Signature.Value S)) :
    (⟪w⟫ ⊨[M] ♢ᶠ[ls] ⊤ᶠ) ↔ HasQuorumNonempty (M := M) ls :=
  sat_diamond_iff_forall_quorumFamily.trans <| forall_congr' fun _ =>
    ⟨fun ⟨p, hp, _⟩ => ⟨p, hp⟩, fun ⟨p, hp⟩ => ⟨p, hp, Sat.top M _⟩⟩

/-- Paper: Lemma 3.6.4(3). Characterisation of the `♢↓` modality: `♢↓[ls]φ` holds at `w` exactly
when every choice of one quorum per learner admits an accessible world whose place lies in the
intersection and which satisfies `φ`. -/
theorem sat_diamondPast_iff_quorum_witness
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (ls : List S.Value) (φ : Formula S) :
    (⟪w⟫ ⊨[M]♢ᶠ↓[ls]φ) ↔
      ∀ F : QuorumFamily M ls,
        ∃ w' : World P (Signature.EventType S),
          w' ≪ w ∧ (∀ i, w'.place ∈ F.choose i) ∧ ⟪w'⟫ ⊨[M]φ :=
  -- The witness participant of `♢` is the place of the witness world of `↓`.
  sat_diamond_iff_forall_quorumFamily.trans <| forall_congr' fun _ =>
    ⟨fun ⟨_, hp, t, ht, htp, hφ⟩ => ⟨t, ht, htp ▸ hp, hφ⟩,
      fun ⟨t, ht, hp, hφ⟩ => ⟨t.place, hp, t, ht, rfl, hφ⟩⟩

/-! ### Diamonds and boxes over one, two and three learners -/

/-- `♢[l]φ` holds exactly when every `l`-quorum has a member satisfying `φ`. -/
@[simp] theorem sat_diamond_singleton_iff
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S) :
    (⟪w⟫ ⊨[M] ♢ᶠ[[l]] φ) ↔
      ∀ O ∈ (M.learner l).quorums,
        ∃ q ∈ O, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ := by
  simp only [sat_diamond_iff_diamond_check, Sat.check_cons, Sat.check_nil, Set.univ_inter]

/-- `♢[l, l']φ` holds exactly when every `l`-quorum and `l'`-quorum share a
member satisfying `φ`. -/
@[simp] theorem sat_diamond_pair_iff
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l l' : Signature.Value S) (φ : Formula S) :
    (⟪w⟫ ⊨[M] ♢ᶠ[[l, l']] φ) ↔
      ∀ O ∈ (M.learner l).quorums,
        ∀ O' ∈ (M.learner l').quorums,
          ∃ q ∈ O ∩ O', ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ := by
  simp only [sat_diamond_iff_diamond_check, Sat.check_cons, Sat.check_nil, Set.univ_inter]

/-- `♢[l₁, l₂, l₃]⊤` makes any three quorums of these learners share a member. -/
theorem sat_diamond_three_intersection
    (M : Model S P)
    (w : World P (Signature.EventType S))
    {l₁ l₂ l₃ : Signature.Value S}
    {O₁ O₂ O₃ : Set P}
    (hDiamond : ⟪w⟫ ⊨[M]♢ᶠ[[l₁, l₂, l₃]]⊤ᶠ)
    (hO₁ : O₁ ∈ (M.learner l₁).quorums)
    (hO₂ : O₂ ∈ (M.learner l₂).quorums)
    (hO₃ : O₃ ∈ (M.learner l₃).quorums) :
    ∃ p, p ∈ O₁ ∧ p ∈ O₂ ∧ p ∈ O₃ :=
  -- The check yields a member of `univ ∩ O₁ ∩ O₂ ∩ O₃`.
  let ⟨p, ⟨⟨⟨_, h₁⟩, h₂⟩, h₃⟩, _⟩ :=
    (sat_diamond_iff_diamond_check M _ _ w).1 hDiamond O₁ hO₁ O₂ hO₂ O₃ hO₃
  ⟨p, h₁, h₂, h₃⟩

/-- `□[l]φ` holds exactly when some `l`-quorum consists of participants
satisfying `φ`. -/
@[simp] theorem sat_box_singleton_exists
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S) :
    (⟪w⟫ ⊨[M] □ᶠ[[l]] φ) ↔
      ∃ O ∈ (M.learner l).quorums,
        ∀ q ∈ O, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ := by
  simp only [Sat.box, sat_diamond_singleton_iff, Sat.not, Classical.not_forall, not_exists,
    not_and, Classical.not_not, exists_prop]

/-- `□[l]φ` implies `♢φ`: the `l`-quorum is nonempty, and its members satisfy `φ`. -/
theorem sat_diamondEmpty_of_box_singleton
    {M : Model S P} {w : World P (Signature.EventType S)}
    {l : Signature.Value S} {φ : Formula S}
    (hBox : ⟪w⟫ ⊨[M] □ᶠ[[l]] φ) :
    ⟪w⟫ ⊨[M] ♢ᶠ[] φ := by
  obtain ⟨O, hO, hAll⟩ := (sat_box_singleton_exists ..).1 hBox
  obtain ⟨q, hq⟩ := Semifilter.quorum_nonempty hO
  exact (Sat.diamondEmpty ..).2 ⟨q, hAll q hq⟩

/-- `□↓[l]φ` at the end of time puts an event-tuple in the history: a member
of the (nonempty) `l`-quorum has a past witness. -/
theorem exists_history_mem_of_end_boxPast
    (M : Model S P)
    {l : Signature.Value S} {φ : Formula S}
    (hBox : ⊨[M]□ᶠ↓[[l]]φ) :
    ∃ t : World P (Signature.EventType S),
      t ∈ M.history.val := by
  obtain ⟨O, hO, hAll⟩ := (sat_box_singleton_exists ..).1 (hBox Classical.ofNonempty)
  obtain ⟨q, hq⟩ := Semifilter.quorum_nonempty hO
  obtain ⟨t, ht, -⟩ := (Sat.past ..).1 (hAll q hq)
  exact ⟨t, ht⟩

/-- At an event-tuple of the model, `⇕φ` implies `φ`. -/
theorem everytime_now_of_mem
    (M : Model S P)
    {w : World P (Signature.EventType S)} {φ : Formula S}
    (hMem : w ∈ M.history.val)
    (hAlways : ⟪w⟫ ⊨[M]⇕ᶠφ) :
    ⟪w⟫ ⊨[M] φ :=
  (Sat.everytime M w φ).1 hAlways w hMem rfl

/-- A participant satisfying `φ` at the end of the current time witnesses `♢φ`. -/
theorem sat_diamondEmpty_of_local
    (M : Model S P)
    (w : World P (Signature.EventType S)) (φ : Formula S) :
    (∃ q, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ) →
      (⟪w⟫ ⊨[M] ♢ᶠ[] φ) :=
  (Sat.diamondEmpty M w φ).2

/-! ### Moving satisfaction between times -/

/-- `↓E` persists from a world's time into the model history containing it. -/
theorem sat_past_event_of_subset_to_history
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (evt : Signature.EventType S)
    (hSubset : w.time ⊆trn M.history.val)
    (hPast : ⟪w⟫ ⊨[M]↓ᶠ (Formula.ofEvent evt)) :
    ⟪⟨w.place, w.event, M.history.val⟩⟫ ⊨[M]↓ᶠ (Formula.ofEvent evt) :=
  Sat.past_of_time_subset hSubset.1 hPast

/-- `♦E` persists into a larger time. -/
theorem sat_diamondPast_nil_event_subset
    (M : Model S P)
    (w w' : World P (Signature.EventType S))
    (symb : Signature.EventSymb S)
    (args : List S.Value)
    (hSubset : w'.time ⊆trn w.time)
    (hDiamond : ⟪w'⟫ ⊨[M]♢ᶠ↓[[]](Formula.event ⟨symb, args⟩)) :
    ⟪w⟫ ⊨[M]♢ᶠ↓[[]](Formula.event ⟨symb, args⟩) :=
  let ⟨t, ht, hEvt⟩ := Sat.diamondPast_nil.1 hDiamond
  Sat.diamondPast_nil.2 ⟨t, hSubset.1 t ht, hEvt⟩

/-- A world whose time weakly precedes the end of time has a transitive
subset of the model history as its time. -/
theorem time_subset_trn_history
    (M : Model S P) {t : World P S.EventType}
    (ht : t.time ⪯ M.history.val) :
    t.time ⊆trn M.history.val :=
  ⟨PreHistory.subset_of_happensBeforeEq (fun h hb => M.history.transitive h hb) ht,
    History.isHereditarilyTransitive_of_happensBeforeEq ht⟩

/-- An all-world validity holds at an event-tuple of the model, presented with
its time packaged as a predecessor history. -/
theorem allWorldValid_predecessor
    (M : Model S P) {φ : Formula S}
    (hEvent : AllWorldValid M φ)
    {p : P} {e : MaybeEvent (Signature.EventType S)}
    {H : PreHistory P (Signature.EventType S)}
    (hMem : (p, e, H) ∈ M.history.val) :
    ⟪⟨p, e,
        (History.predecessorHistory (H := M.history)
          (happensBefore_of_mem (P := P)
            (Event := Signature.EventType S) hMem)).val⟩⟫
      ⊨[M] φ :=
  AllWorldValid.of_mem_history M hEvent hMem

/-- `□↓[l]φ` at a world whose time is part of the model history holds at the
end of time: the quorum's past witnesses are still there. -/
theorem lift_boxPast_to_end
    (M : Model S P)
    {t : World P (Signature.EventType S)}
    {learner : Signature.Value S}
    {φ : Formula S}
    (hSubset : t.time ⊆ M.history.val)
    (hBox : ⟪t⟫ ⊨[M]□ᶠ↓[[learner]]φ) :
    ⊨[M]□ᶠ↓[[learner]]φ := fun _ =>
  let ⟨O, hO, hAll⟩ := (sat_box_singleton_exists ..).1 hBox
  (sat_box_singleton_exists ..).2
    ⟨O, hO, fun q hq => Sat.past_of_time_subset hSubset (hAll q hq)⟩

/-! ### End-of-time consequences -/

/-- A valid empty box `□φ` makes `φ` hold at every participant at the end of time. -/
theorem EndValid.boxEmpty_guard
    (M : Model S P) (φ : Formula S) :
    (⊨[M] □ᶠ[] φ) → ∀ p : P, ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] φ := fun h p =>
  (Sat.boxEmpty M ⟨p, †, M.history.val⟩ φ).1 (h p) p

/-- If every participant is active (`⊨ □↓⊤`), a quorum witness for `seq` is a
quorum witness for `↓seq`: the witness is sequential at the end of time, hence
at its own earlier event-tuples. -/
theorem HasQuorumWitness.seq_to_past
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (HasQuorumWitness (M := M) ls Formula.seq →
        HasQuorumWitness (M := M) ls (↓ᶠ Formula.seq)) := by
  intro hActive hWitness F
  obtain ⟨p, hpAll, hpSeq⟩ := hWitness F
  obtain ⟨t, ht, hp, -⟩ := (Sat.past ..).1 (EndValid.boxEmpty_guard M _ hActive p)
  refine ⟨p, hpAll, Sat.past_intro_of_prefix ht hp ?_⟩
  exact (Sat.seq M t).2 (hp ▸ History.sequentiality_of_predecessor (happensBefore_of_mem ht) hpSeq)

end DiamondMachinery

end Logic
end ModalDistribution
