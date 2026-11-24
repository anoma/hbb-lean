import ModalDistribution.Examples.HBBSafe
import ModalDistribution.Examples.HBBSimp
import ModalDistribution.Examples.HBBCorr

/-!
# Non-vacuity of HBBSafe, HBBSimp and HBBCorr

Each theory has a finite model in which the hypotheses of all three of its
correctness properties hold at once and a live participant delivers. So the
correctness theorems are not vacuously true.

The model has one participant, one value (which also serves as the one
learner, whose only quorum is the whole participant set), and a history that is
a single chain of that participant's events

  `propose(v)`, `echo(v)`, `vote(l, v)`, `deliver(…)`, `†`.

The final `†` tuple records knowledge of every event before it, which is what
the Knowledge axioms of `ThyLive` require of a history ending in a live
participant. Every predicate (`live`, `safe`, `≐`) holds everywhere.
-/

namespace ModalDistribution
namespace Examples
namespace NonVacuity

open ModalDistribution.Logic PreHistory History World
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

/-- The event symbols of the protocols. -/
inductive Sym where
  | propose | echo | vote | deliver

/-- The predicate symbols of the protocols. -/
inductive Pred where
  | live | safe | corr

/-- The signature: protocol symbols over a single value. -/
abbrev sig : Signature := ⟨Sym, Pred, Unit⟩

/-- The single value, which is also the single learner. -/
abbrev v : sig.Value := ()

section Chain

-- The argument list of the delivery event: `[l', l, v]` in HBBSafe and
-- HBBSimp, `[l, v]` in HBBCorr.
variable (dargs : List sig.Value)

def h0 : PreHistory Unit sig.EventType := .mk []
def e0 : World Unit sig.EventType := ((), .some ⟨.propose, [v]⟩, h0)
def h1 : PreHistory Unit sig.EventType := .mk [e0]
def e1 : World Unit sig.EventType := ((), .some ⟨.echo, [v]⟩, h1)
def h2 : PreHistory Unit sig.EventType := .mk [e0, e1]
def e2 : World Unit sig.EventType := ((), .some ⟨.vote, [v, v]⟩, h2)
def h3 : PreHistory Unit sig.EventType := .mk [e0, e1, e2]
def e3 : World Unit sig.EventType := ((), .some ⟨.deliver, dargs⟩, h3)
def h4 : PreHistory Unit sig.EventType := .mk [e0, e1, e2, e3 dargs]
def e4 : World Unit sig.EventType := ((), †, h4 dargs)
def h5 : PreHistory Unit sig.EventType := .mk [e0, e1, e2, e3 dargs, e4 dargs]

@[local simp] private theorem subset_iff (a b : PreHistory Unit sig.EventType) :
    a ⊆ b ↔ ∀ t, t ∈ a → t ∈ b := Iff.rfl

@[local simp] private theorem mem_mk (t : World Unit sig.EventType) (xs) :
    t ∈ PreHistory.mk xs ↔ t ∈ xs := Iff.rfl

private theorem extend_hered (h : PreHistory Unit sig.EventType)
    (hs : ∀ t ∈ h, t.time ⊆ h)
    (hh : ∀ t ∈ h, isHereditarilyTransitive t.time) :
    isHereditarilyTransitive h := by
  rw [isHereditarilyTransitive_unfold]
  exact ⟨fun h' ⟨p, e, ht⟩ => hs (p, e, h') ht,
    fun h' ⟨p, e, ht⟩ => hh (p, e, h') ht⟩

private theorem hered5 : isHereditarilyTransitive (h5 dargs) := by
  have hered0 : isHereditarilyTransitive h0 := by
    rw [isHereditarilyTransitive_unfold]
    simp [isTransitive, happensBefore, h0]
  have hered1 : isHereditarilyTransitive h1 :=
    extend_hered _ (by intro t ht; simp_all [h1, e0, h0] )
      (by intro t ht; simp only [h1, mem_mk, List.mem_singleton] at ht; subst ht; exact hered0)
  have hered2 : isHereditarilyTransitive h2 :=
    extend_hered _
      (by intro t ht; simp only [h2, mem_mk, List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl <;> simp [e0, e1, h0, h1, h2] )
      (by intro t ht; simp only [h2, mem_mk, List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hered0
          · exact hered1)
  have hered3 : isHereditarilyTransitive h3 :=
    extend_hered _
      (by intro t ht; simp only [h3, mem_mk, List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl | rfl <;> simp [e0, e1, e2, h0, h1, h2, h3] )
      (by intro t ht; simp only [h3, mem_mk, List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl | rfl
          · exact hered0
          · exact hered1
          · exact hered2)
  have hered4 : isHereditarilyTransitive (h4 dargs) :=
    extend_hered _
      (by intro t ht; simp only [h4, mem_mk, List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl | rfl | rfl <;>
            simp [e0, e1, e2, e3, h0, h1, h2, h3, h4] )
      (by intro t ht; simp only [h4, mem_mk, List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl | rfl | rfl
          · exact hered0
          · exact hered1
          · exact hered2
          · exact hered3)
  exact extend_hered _
    (by intro t ht; simp only [h5, mem_mk, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl <;>
          simp [e0, e1, e2, e3, e4, h0, h1, h2, h3, h4, h5] )
    (by intro t ht; simp only [h5, mem_mk, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · exact hered0
        · exact hered1
        · exact hered2
        · exact hered3
        · exact hered4)

/-- The single-learner semifilter: the one quorum is the whole participant set. -/
def learner : Semifilter Unit where
  quorums := {O | () ∈ O}
  nonempty := ⟨Set.univ, trivial⟩
  upwardClosed := fun {_ _} hO hsub => hsub hO
  pairwiseInter := fun {_ _} hO hO' => ⟨(), hO, hO'⟩

/-- The model: the chain history, every predicate true everywhere. -/
def model : Model sig Unit where
  history := ⟨h5 dargs, hered5 dargs⟩
  predInterp := fun _ _ => Set.univ
  learner := fun _ => learner

@[local simp] theorem model_history : (model dargs).history.val = h5 dargs := rfl
@[local simp] theorem model_pred (p : Unit) (T : PreHistory Unit sig.EventType) :
    (model dargs).predInterp p T = Set.univ := rfl
@[local simp] theorem unit_forall (Q : Unit → Prop) : (∀ u, Q u) ↔ Q () :=
  ⟨fun h => h (), fun h u => by cases u; exact h⟩
@[local simp] theorem unit_exists (Q : Unit → Prop) : (∃ u, Q u) ↔ Q () :=
  ⟨fun ⟨u, h⟩ => by cases u; exact h, fun h => ⟨(), h⟩⟩

/-- The times of the model: the time of each event-tuple, and the end of time. -/
theorem time_cases {T : PreHistory Unit sig.EventType} (hT : T ⪯ h5 dargs) :
    T = h0 ∨ T = h1 ∨ T = h2 ∨ T = h3 ∨ T = h4 dargs ∨ T = h5 dargs := by
  rcases hT with ⟨p, e, hm⟩ | rfl
  · simp only [h5, mem_mk, List.mem_cons, List.not_mem_nil, or_false, e0, e1, e2, e3, e4,
      Prod.mk.injEq] at hm
    rcases hm with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp
  · simp

/-- Quorum checks in the model: every learner's only quorum is the whole
participant set, so a quorum condition holds exactly when it holds at `()`. -/
@[local simp] theorem check (Q : Unit → Prop) (ls : List sig.Value) (acc : Set Unit) :
    Sat.check (model dargs) Q ls acc ↔ (() ∈ acc ∧ Q ()) := by
  induction ls generalizing acc with
  | nil => exact ⟨fun ⟨u, hu, hq⟩ => by cases u; exact ⟨hu, hq⟩, fun ⟨hu, hq⟩ => ⟨(), hu, hq⟩⟩
  | cons l ls ih =>
    simp only [Sat.check, ih]
    constructor
    · intro h
      exact ⟨(h Set.univ trivial).1.1, (h Set.univ trivial).2⟩
    · rintro ⟨ha, hq⟩ O ho
      exact ⟨⟨ha, ho⟩, hq⟩

theorem mem_h5 {t : World Unit sig.EventType} :
    t ∈ h5 dargs ↔ t = e0 ∨ t = e1 ∨ t = e2 ∨ t = e3 dargs ∨ t = e4 dargs := by
  simp only [h5, mem_mk, List.mem_cons, List.not_mem_nil, or_false]

/-- Every event (as opposed to the final `†`) of the model is known at the
final tuple `e4`. -/
theorem mem_h4_of_event {t : World Unit sig.EventType} {E : sig.EventType}
    (ht : t ∈ h5 dargs) (hE : t.event = .some E) : t ∈ h4 dargs := by
  rcases (mem_h5 dargs).1 ht with rfl | rfl | rfl | rfl | rfl
  · simp [h4]
  · simp [h4]
  · simp [h4]
  · simp [h4]
  · simp [e4] at hE

/-- The chain is sequential. -/
theorem seq_h5 : isSequential () (h5 dargs) := by
  intro t₁ t₂ h₁ h₂ _ _
  rcases (mem_h5 dargs).1 h₁ with rfl | rfl | rfl | rfl | rfl <;>
    rcases (mem_h5 dargs).1 h₂ with rfl | rfl | rfl | rfl | rfl <;>
    simp [World.accessible, e0, e1, e2, e3, e4, h0, h1, h2, h3, h4]

/-- The chain is sequential at every time of the model. -/
theorem seq_of_time {T : PreHistory Unit sig.EventType} (hT : T ⪯ h5 dargs) :
    isSequential () T := by
  rcases hT with hT | rfl
  · exact History.sequentiality_of_predecessor (H := (model dargs).history) hT (seq_h5 dargs)
  · exact seq_h5 dargs

/-- An event performed in the model is known (`♦E`) at the final tuple. -/
theorem final_knows {t : World Unit sig.EventType} {E : sig.EventType}
    (ht : t ∈ h5 dargs) (hE : ⟪t⟫ ⊨[model dargs] Formula.ofEvent E) :
    ⟪e4 dargs⟫ ⊨[model dargs] ♢ᶠ↓[[]] (Formula.ofEvent E) := by
  have hEvt : t.event = .some E := ((Sat.ofEvent (model dargs) t E).1 hE).1
  have hPast : ⟪((), †, h4 dargs)⟫ ⊨[model dargs] ↓ᶠ (Formula.ofEvent E) :=
    (Sat.past (model dargs) _ _).2 ⟨t, mem_h4_of_event dargs ht hEvt, rfl, hE⟩
  simpa [Formula.diamondPast] using
    (Sat.diamond_nil (model dargs) (e4 dargs) (↓ᶠ (Formula.ofEvent E))).2 ⟨(), hPast⟩

/-- An event performed in the model is known by a quorum (`■_l E`) at the
final tuple. -/
theorem final_knows_quorum {t : World Unit sig.EventType} {E : sig.EventType}
    (l : sig.Value) (ht : t ∈ h5 dargs) (hE : ⟪t⟫ ⊨[model dargs] Formula.ofEvent E) :
    ⟪e4 dargs⟫ ⊨[model dargs] □ᶠ↓[[l]] (Formula.ofEvent E) := by
  have hEvt : t.event = .some E := ((Sat.ofEvent (model dargs) t E).1 hE).1
  have hBox := (sat_box_singleton_exists (model dargs) (e4 dargs) l (↓ᶠ (Formula.ofEvent E))).2
    ⟨Set.univ, trivial, fun q _ => (Sat.past (model dargs) _ _).2
      ⟨t, mem_h4_of_event dargs ht hEvt, rfl, hE⟩⟩
  simpa [Formula.boxPast] using hBox

/-- `ThyLive` holds in the model. -/
theorem thyLive_valid : model dargs ⊨ᵀ ThyLive (S := sig) .live := by
  rintro ax (rfl | rfl | ⟨E, rfl⟩ | ⟨l, E, rfl⟩) w hw
  · -- (LiveAlways): `live` holds everywhere.
    simp [liveAlwaysAxiom, Formula.iff, Formula.and, Formula.not, Sat]
  · -- (LiveSeq): every time of the model is sequential.
    obtain ⟨p, x, T⟩ := w
    cases p
    exact Sat.imp_intro (model dargs) _ fun _ => seq_of_time dargs hw
  · -- (Knowledge♢↓): the final tuple knows every performed event.
    refine Sat.imp_intro (model dargs) w fun hPrem => Sat.imp_intro (model dargs) w fun _ => ?_
    obtain ⟨q, hq⟩ := (Sat.diamond_nil (model dargs) (w.1, †, h5 dargs)
      (↓ᶠ (Formula.predicate0 Pred.live ∧ᶠ Formula.ofEvent E))).1
      (by simpa [Formula.diamondPast] using (Sat.atEnd (model dargs) w _).1 hPrem)
    obtain ⟨t, ht, -, hConj⟩ := (Sat.past (model dargs) _ _).1 hq
    have hE := ((Sat.and (model dargs) t _ _).1 hConj).2
    exact (Sat.sometime (model dargs) w _).2
      ⟨e4 dargs, by simp [h5], rfl, final_knows dargs ht hE⟩
  · -- (Knowledge□↓): the final tuple knows that a quorum performed every
    -- performed event.
    refine Sat.imp_intro (model dargs) w fun hPrem => Sat.imp_intro (model dargs) w fun _ => ?_
    obtain ⟨O, hO, hAll⟩ := (sat_box_singleton_exists (model dargs) (w.1, †, h5 dargs) l
      (↓ᶠ (Formula.predicate0 Pred.live ∧ᶠ Formula.ofEvent E))).1
      (by simpa [Formula.boxPast] using (Sat.atEnd (model dargs) w _).1 hPrem)
    obtain ⟨t, ht, -, hConj⟩ := (Sat.past (model dargs) _ _).1 (hAll () hO)
    have hE := ((Sat.and (model dargs) t _ _).1 hConj).2
    exact (Sat.sometime (model dargs) w _).2
      ⟨e4 dargs, by simp [h5], rfl, final_knows_quorum dargs l ht hE⟩

attribute [local simp] Formula.ofEvent Formula.ofPredicate Formula.diamondPast
  Formula.boxPast Formula.box Formula.not Formula.and Formula.or Formula.iff Formula.top
  Formula.sometime Formula.everytime Formula.allPast Formula.exists_ Formula.existsAtMostOne
  Formula.existsUnique

/-- The protocol axioms of a theory mention only the events of the chain and
sequentiality, so they are checked by evaluating them at each time of the
model, knowing that the chain is sequential at that time. -/
theorem valid_by_eval {φ : Formula sig}
    (h : ∀ (x : MaybeEvent sig.EventType) (T : PreHistory Unit sig.EventType),
      isSequential () T →
      (T = h0 ∨ T = h1 ∨ T = h2 ∨ T = h3 ∨ T = h4 dargs ∨ T = h5 dargs) →
      Sat (model dargs) () x T φ) :
    □W⊨[model dargs] φ := by
  intro w hw
  obtain ⟨p, x, T⟩ := w
  cases p
  exact h x T (seq_of_time dargs hw) (time_cases dargs hw)

/-- `HBBSimp` holds in the model with ternary deliveries. -/
theorem hbbSimp_valid :
    model [v, v, v] ⊨ᵀ
      HBBSimp.theory (S := sig) .live .propose .echo .vote .deliver := by
  rintro ax (hL | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact thyLive_valid _ hL
  all_goals
    apply valid_by_eval
    rintro x T - (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [Sat, h0, h1, h2, h3, h4, h5, e0, e1, e2, e3, e4]

/-- `HBBSafe` holds in the model with ternary deliveries. -/
theorem hbbSafe_valid :
    model [v, v, v] ⊨ᵀ
      HBBSafe.theory (S := sig) .live .safe .propose .echo .vote .deliver := by
  rintro ax (hL | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact thyLive_valid _ hL
  all_goals
    apply valid_by_eval
    rintro x T - (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [Sat, h0, h1, h2, h3, h4, h5, e0, e1, e2, e3, e4]

/-- `HBBCorr` holds in the model with binary deliveries. -/
theorem hbbCorr_valid :
    model [v, v] ⊨ᵀ
      HBBCorr.theory (S := sig) .live .propose .echo .vote .deliver .corr := by
  rintro ax (hL | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl)
  · exact thyLive_valid _ hL
  all_goals
    apply valid_by_eval
    rintro x T hSeq (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [h0, h1, h2, h3, h4, h5, e0, e1, e2, e3, e4] at hSeq <;>
      simp [Sat, h0, h1, h2, h3, h4, h5, e0, e1, e2, e3, e4, hSeq]

/-- End-of-time validity in the model is satisfaction at its one end-of-time
world. -/
theorem endValid_by_eval {φ : Formula sig}
    (h : Sat (model dargs) () † (h5 dargs) φ) :
    ⊨[model dargs] φ := fun p => by cases p; exact h

/-- The participant's quorum intersections are sequential. -/
theorem seq_intersections (ls : List sig.Value) :
    ⊨[model dargs] ♢ᶠ[ls] Formula.seq :=
  endValid_by_eval dargs (by simpa [Sat] using seq_h5 dargs)

/-- Non-vacuity of HBBSafe: in a model of `HBBSafe`, the hypotheses of
Agreement, Happy Termination and Cascade Termination all hold (with `l` the
one learner and `v` the one value), and a live participant delivers `v`. -/
theorem hbbSafe_nonvacuous :
    (model [v, v, v] ⊨ᵀ
      HBBSafe.theory (S := sig) .live .safe .propose .echo .vote .deliver) ∧
    -- Agreement: sequential quorum intersections.
    (⊨[model [v, v, v]] ♢ᶠ[[v, v]] Formula.seq) ∧
    -- Happy Termination: a live quorum, a unique proposal, and live knowledge of it.
    (⊨[model [v, v, v]] □ᶠ[[v]] predicate0 Pred.live) ∧
    (⊨[model [v, v, v]] ∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨Sym.propose, [w]⟩)) ∧
    (⊨[model [v, v, v]] ♢ᶠ↓[[]](predicate0 Pred.live ∧ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨Sym.propose, [v]⟩))) ∧
    -- Cascade Termination: nonempty quorum intersections and a safe learner.
    (⊨[model [v, v, v]] ♢ᶠ[[v, v]] ⊤ᶠ) ∧
    (⊨[model [v, v, v]] ofPredicate ⟨Pred.safe, [v]⟩) ∧
    -- A live participant delivers.
    (⊨[model [v, v, v]] ♢ᶠ↓[[]](predicate0 Pred.live ∧ᶠ
      ofEvent ⟨Sym.deliver, [v, v, v]⟩)) := by
  refine ⟨hbbSafe_valid, seq_intersections _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply endValid_by_eval <;>
    simp [Sat, h0, h1, h2, h3, h4, h5, e0, e1, e2, e3, e4]

/-- Non-vacuity of HBBSimp: in a model of `HBBSimp`, the hypotheses of
Agreement, Happy Termination and Cascade Termination all hold, and a live
participant delivers `v`. -/
theorem hbbSimp_nonvacuous :
    (model [v, v, v] ⊨ᵀ
      HBBSimp.theory (S := sig) .live .propose .echo .vote .deliver) ∧
    -- Agreement: sequential quorum intersections.
    (⊨[model [v, v, v]] ♢ᶠ[[v, v]] Formula.seq) ∧
    -- Happy Termination: a live quorum, a unique proposal, and live knowledge of it.
    (⊨[model [v, v, v]] □ᶠ[[v]] predicate0 Pred.live) ∧
    (⊨[model [v, v, v]] ∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨Sym.propose, [w]⟩)) ∧
    (⊨[model [v, v, v]] ♢ᶠ↓[[]](predicate0 Pred.live ∧ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨Sym.propose, [v]⟩))) ∧
    -- Cascade Termination: nonempty quorum intersections.
    (⊨[model [v, v, v]] ♢ᶠ[[v, v]] ⊤ᶠ) ∧
    -- A live participant delivers.
    (⊨[model [v, v, v]] ♢ᶠ↓[[]](predicate0 Pred.live ∧ᶠ
      ofEvent ⟨Sym.deliver, [v, v, v]⟩)) := by
  refine ⟨hbbSimp_valid, seq_intersections _ _, ?_, ?_, ?_, ?_, ?_⟩ <;> apply endValid_by_eval <;>
    simp [Sat, h0, h1, h2, h3, h4, h5, e0, e1, e2, e3, e4]

/-- Non-vacuity of HBBCorr: in a model of `HBBCorr`, the hypotheses of
Agreement, Happy Termination and Cascade Termination all hold, and a live
participant delivers `v`. -/
theorem hbbCorr_nonvacuous :
    (model [v, v] ⊨ᵀ
      HBBCorr.theory (S := sig) .live .propose .echo .vote .deliver .corr) ∧
    -- Agreement and Cascade Termination: the learner is always correlated.
    (⊨[model [v, v]] □ᶠ[] (ofPredicate ⟨Pred.corr, [v, v]⟩)) ∧
    -- Happy and Cascade Termination: a live quorum.
    (⊨[model [v, v]] □ᶠ[[v]] predicate0 Pred.live) ∧
    -- Happy Termination: a unique proposal and live knowledge of it.
    (⊨[model [v, v]] ∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨Sym.propose, [w]⟩)) ∧
    (⊨[model [v, v]] ♢ᶠ↓[[]](predicate0 Pred.live ∧ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨Sym.propose, [v]⟩))) ∧
    -- A live participant delivers.
    (⊨[model [v, v]] ♢ᶠ↓[[]](predicate0 Pred.live ∧ᶠ
      ofEvent ⟨Sym.deliver, [v, v]⟩)) := by
  refine ⟨hbbCorr_valid, ?_, ?_, ?_, ?_, ?_⟩ <;> apply endValid_by_eval <;>
    simp [Sat, h0, h1, h2, h3, h4, h5, e0, e1, e2, e3, e4]

end Chain

end NonVacuity
end Examples
end ModalDistribution
