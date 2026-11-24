import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# Counterexamples for the modal properties

The paper's Lemma 4.2.1(3,4) and Lemma 4.2.3(3) are negative observations:
certain modal implications do not hold in general. This file realises them in
concrete models.

- `disjointQuorumsModel` (Lemma 4.2.1(3,4)): two participants (`Bool`), the
  empty history, and two learners whose quorum systems are the up-closures of
  `{true}` and `{false}` respectively, so the pair of quorums `{true}`,
  `{false}` has empty intersection.
- `branchingModel` (Lemma 4.2.3(3)): the paper's one-participant model with
  events `E₁`, `E₂`, `F` and history `H = H₃ ∪ H₄`.
-/

namespace ModalDistribution
namespace Examples
namespace Counterexamples

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

/-- The empty prehistory is hereditarily transitive. -/
theorem empty_hered {P E : Type} :
    IsHereditarilyTransitive (PreHistory.mk [] : PreHistory P E) :=
  (isHereditarilyTransitive_unfold _).2
    ⟨fun _ ⟨_, _, hm⟩ => (nomatch hm), fun _ ⟨_, _, hm⟩ => (nomatch hm)⟩

/-! ## Lemma 4.2.1(3,4): boxes and diamonds over disjoint quorums -/

/-- A signature with no symbols and `Bool` as values/learners. -/
def sig : Signature := ⟨Empty, Empty, Bool⟩

/-- The up-closure of `{p}`: all sets containing `p`. A semifilter. -/
def upset (p : Bool) : Semifilter Bool where
  quorums := {O | p ∈ O}
  nonempty := ⟨Set.univ, trivial⟩
  upward_closed := fun _ _ hO hsub => hsub hO
  pairwise_inter := fun _ _ hO hO' => ⟨p, hO, hO'⟩

/-- The model of the Lemma 4.2.1(3,4) counterexamples: the empty history over
two participants, where learner `b` has the quorums containing `b`, so the
`true`-quorum `{true}` and the `false`-quorum `{false}` are disjoint. -/
noncomputable def disjointQuorumsModel : Model sig Bool where
  history := ⟨PreHistory.mk [], empty_hered⟩
  predInterp := fun _ _ => ∅
  learner := fun v => upset v

/-- The world at participant `true` at the (empty) end of time. -/
def disjointQuorumsEnd : World Bool (Signature.EventType sig) :=
  ⟨true, †, PreHistory.mk []⟩

/-- The quorum pair with empty intersection: `{true}` for learner `true`. -/
theorem true_set_mem :
    {b : Bool | b = true} ∈ (disjointQuorumsModel.learner true).quorums := rfl

/-- ... and `{false}` for learner `false`. -/
theorem false_set_mem :
    {b : Bool | b = false} ∈ (disjointQuorumsModel.learner false).quorums := rfl

/-- No formula holds under `♢[true, false]`: the quorums `{true}` and
`{false}` have no common member. -/
theorem not_sat_diamond_true_false (φ : Formula sig) :
    ¬ (⟪disjointQuorumsEnd⟫ ⊨[disjointQuorumsModel] ♢ᶠ[[true, false]] φ) := fun h => by
  obtain ⟨q, ⟨hq, hq'⟩, -⟩ :=
    (sat_diamond_pair_iff _ _ true false φ).1 h _ true_set_mem _ false_set_mem
  exact Bool.noConfusion ((hq : q = true).symm.trans hq')

/-- Paper: Lemma 4.2.1(3). `□l₁…lₙφ` does not imply `♢φ`: with an empty
quorum intersection the box holds vacuously (even of `⊥`), while `♢⊥` fails. -/
theorem box_not_implies_diamondEmpty :
    (⟪disjointQuorumsEnd⟫ ⊨[disjointQuorumsModel] □ᶠ[[true, false]] (⊥ᶠ : Formula sig)) ∧
      ¬ (⟪disjointQuorumsEnd⟫ ⊨[disjointQuorumsModel] ♢ᶠ[] (⊥ᶠ : Formula sig)) :=
  ⟨Sat.not_intro _ (not_sat_diamond_true_false _),
    fun h => ((Sat.diamondEmpty _ _ _).1 h).elim fun _ hBot => hBot⟩

/-- Paper: Lemma 4.2.1(4). `φ` does not imply `♢l₁…lₙφ`: even `⊤` fails under
the diamond when some quorum intersection is empty. -/
theorem sat_not_implies_diamond :
    (⟪disjointQuorumsEnd⟫ ⊨[disjointQuorumsModel] (⊤ᶠ : Formula sig)) ∧
      ¬ (⟪disjointQuorumsEnd⟫ ⊨[disjointQuorumsModel] ♢ᶠ[[true, false]] (⊤ᶠ : Formula sig)) :=
  ⟨Sat.top _ _, not_sat_diamond_true_false _⟩

/-! ## Lemma 4.2.3(3): the collapsing implications do not reverse

The paper's model: one participant, three events `E₁, E₂, F`, one learner
whose quorums are all sets containing the participant, and the history

`H = {(p,F,H₁), (p,E₁,∅), (p,F,H₂), (p,E₂,∅)}` with `H₁ = {(p,E₁,∅)}`,
`H₂ = {(p,E₂,∅)}`.

At the end of time, `□↓F` holds (the participant has a past `F`), but
`↓□↓F` and `♢↓□↓F` both fail: at the time of every event-tuple in `H`, no
`F` has yet occurred.
-/

/-- A signature with three event symbols and a single value/learner. -/
def sig3 : Signature := ⟨Fin 3, Empty, Unit⟩

/-- The three events. -/
def evE₁ : Signature.EventType sig3 := ⟨(0 : Fin 3), []⟩
def evE₂ : Signature.EventType sig3 := ⟨(1 : Fin 3), []⟩
def evF : Signature.EventType sig3 := ⟨(2 : Fin 3), []⟩

/-- The initial event-tuples `(p, E₁, ∅)` and `(p, E₂, ∅)`. -/
def tE₁ : World Unit (Signature.EventType sig3) :=
  ((), MaybeEvent.some evE₁, PreHistory.mk [])
def tE₂ : World Unit (Signature.EventType sig3) :=
  ((), MaybeEvent.some evE₂, PreHistory.mk [])

/-- The paper's `H₁ = {(p, E₁, ∅)}`. -/
def historyE₁ : PreHistory Unit (Signature.EventType sig3) := PreHistory.mk [tE₁]

/-- The paper's `H₂ = {(p, E₂, ∅)}`. -/
def historyE₂ : PreHistory Unit (Signature.EventType sig3) := PreHistory.mk [tE₂]

/-- The two `F` event-tuples `(p, F, H₁)` and `(p, F, H₂)`. -/
def tF₁ : World Unit (Signature.EventType sig3) :=
  ((), MaybeEvent.some evF, historyE₁)
def tF₂ : World Unit (Signature.EventType sig3) :=
  ((), MaybeEvent.some evF, historyE₂)

/-- The paper's history `H = H₃ ∪ H₄` of the counterexample. -/
def branchingHistory : PreHistory Unit (Signature.EventType sig3) :=
  PreHistory.mk [tF₁, tE₁, tF₂, tE₂]

/-- A prehistory of one initial event-tuple is hereditarily transitive. -/
theorem singleton_hered (t : World Unit (Signature.EventType sig3))
    (ht : t.time = PreHistory.mk []) :
    IsHereditarilyTransitive (PreHistory.mk [t]) := by
  -- The only predecessor of `{t}` is `t.time = ∅`.
  have hPred : ∀ h', h' ≺− PreHistory.mk [t] → h' = PreHistory.mk [] :=
    fun _ ⟨_, _, hm⟩ => (congrArg World.time (List.mem_singleton.1 hm)).trans ht
  refine (isHereditarilyTransitive_unfold _).2
    ⟨fun h' hb x hx => ?_, fun h' hb => hPred h' hb ▸ empty_hered⟩
  rw [hPred h' hb] at hx
  nomatch hx

/-- Every event-tuple of `H` happens at time `H₁`, `H₂`, or `∅`. -/
theorem time_of_mem_branchingHistory {t : World Unit (Signature.EventType sig3)}
    (ht : t ∈ branchingHistory) :
    t.time = historyE₁ ∨ t.time = historyE₂ ∨ t.time = PreHistory.mk [] := by
  have ht' : t ∈ [tF₁, tE₁, tF₂, tE₂] := ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
  rcases ht' with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem branchingHistory_hered : IsHereditarilyTransitive branchingHistory := by
  -- `H₁` and `H₂` lie in `H`.
  have hsub₁ : historyE₁ ⊆ branchingHistory := fun x hx => by
    rw [List.mem_singleton.1 hx]
    exact List.Mem.tail _ (List.Mem.head _)
  have hsub₂ : historyE₂ ⊆ branchingHistory := fun x hx => by
    rw [List.mem_singleton.1 hx]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  refine (isHereditarilyTransitive_unfold _).2 ⟨fun h' ⟨p, e, hm⟩ => ?_, fun h' ⟨p, e, hm⟩ => ?_⟩
  · rcases time_of_mem_branchingHistory hm with rfl | rfl | rfl
    · exact hsub₁
    · exact hsub₂
    · exact fun _ hx => nomatch hx
  · rcases time_of_mem_branchingHistory hm with rfl | rfl | rfl
    · exact singleton_hered tE₁ rfl
    · exact singleton_hered tE₂ rfl
    · exact empty_hered

/-- The model of the Lemma 4.2.3(3) counterexample: history `H` and one
learner whose only relevant quorum is the single participant. -/
noncomputable def branchingModel : Model sig3 Unit where
  history := ⟨branchingHistory, branchingHistory_hered⟩
  predInterp := fun _ _ => ∅
  learner := fun _ =>
    { quorums := {O | () ∈ O}
      nonempty := ⟨Set.univ, trivial⟩
      upward_closed := fun _ _ hO hsub => hsub hO
      pairwise_inter := fun _ _ hO hO' => ⟨(), hO, hO'⟩ }

/-- The end-of-time world of the counterexample. -/
def branchingEnd : World Unit (Signature.EventType sig3) := ((), †, branchingHistory)

/-- No `F` occurs at any time strictly inside the counterexample history:
`↓F` fails at any world whose time is `H₁`, `H₂`, or `∅`. -/
theorem no_past_evF (x : MaybeEvent (Signature.EventType sig3))
    (T : PreHistory Unit (Signature.EventType sig3))
    (hT : T = historyE₁ ∨ T = historyE₂ ∨ T = PreHistory.mk []) :
    ¬ (⟪((), x, T)⟫ ⊨[branchingModel] ↓ᶠ (ofEvent evF)) := by
  intro h
  obtain ⟨t, ht, -, htF⟩ := (Sat.past _ _ _).1 h
  have hEvt : t.event = MaybeEvent.some evF := ((Sat.ofEvent _ t evF).1 htF).1
  -- The only event-tuples at those times are `(p, E₁, ∅)` and `(p, E₂, ∅)`.
  rcases hT with rfl | rfl | rfl
  · rw [List.mem_singleton.1 ht] at hEvt
    simp [tE₁, evE₁, evF] at hEvt
    exact (show (0 : Fin 3) ≠ 2 by decide) hEvt
  · rw [List.mem_singleton.1 ht] at hEvt
    simp [tE₂, evE₂, evF] at hEvt
    exact (show (1 : Fin 3) ≠ 2 by decide) hEvt
  · nomatch ht

/-- No event-tuple of `H` satisfies `□↓F`, as no `F` precedes it. -/
theorem not_boxPast_evF_of_mem {t : World Unit (Signature.EventType sig3)}
    (ht : t ∈ branchingHistory) :
    ¬ (⟪t⟫ ⊨[branchingModel] □ᶠ↓[[()]] (ofEvent evF)) := fun h => by
  obtain ⟨O, hO, hOF⟩ := (sat_box_singleton_exists _ t () _).1 h
  exact no_past_evF † t.time (time_of_mem_branchingHistory ht) (hOF () hO)

/-- Paper: Lemma 4.2.3(3). The collapsing implications of Lemma 4.2.3 do not
reverse: at the end of time `□↓F` holds, yet `↓□↓F` and `♢↓□↓F` both fail. -/
theorem past_box_does_not_reverse :
    (⟪branchingEnd⟫ ⊨[branchingModel] □ᶠ↓[[()]] (ofEvent evF)) ∧
      ¬ (⟪branchingEnd⟫ ⊨[branchingModel] ↓ᶠ (□ᶠ↓[[()]] (ofEvent evF))) ∧
      ¬ (⟪branchingEnd⟫ ⊨[branchingModel] ♢ᶠ↓[[()]] (□ᶠ↓[[()]] (ofEvent evF))) := by
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · -- The (only) participant has the past `F` event-tuple `(p, F, H₁)`.
    exact (sat_box_singleton_exists branchingModel branchingEnd () _).2 ⟨Set.univ, trivial,
      fun () _ => (Sat.past branchingModel ((), †, branchingHistory) _).2 ⟨tF₁, List.Mem.head _,
        rfl, (Sat.ofEvent branchingModel tF₁ evF).2 ⟨rfl, List.Mem.head _⟩⟩⟩
  · -- The past event-tuple would satisfy `□↓F`.
    obtain ⟨t, ht, -, htBox⟩ := (Sat.past _ _ _).1 h
    exact not_boxPast_evF_of_mem ht htBox
  · -- The quorum `{p}` has a member whose past event-tuple would satisfy `□↓F`.
    obtain ⟨q, -, hq⟩ := (sat_diamond_singleton_iff branchingModel branchingEnd () _).1 h Set.univ trivial
    obtain ⟨t, ht, -, htBox⟩ := (Sat.past _ _ _).1 hq
    exact not_boxPast_evF_of_mem ht htBox

end Counterexamples
end Examples
end ModalDistribution
