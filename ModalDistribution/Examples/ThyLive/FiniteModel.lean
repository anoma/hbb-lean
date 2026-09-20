import ModalDistribution.Examples.ThyLive

/-! A finite model with a live performed event for event-restricted Knowledge. -/
namespace ModalDistribution.Examples.FiniteModel
open ModalDistribution.Logic PreHistory History World
open scoped Formula

private def sig : Signature := ⟨Unit, Unit, Unit⟩
private def atom : sig.EventType := ⟨(), []⟩
private def h0 : PreHistory Unit sig.EventType := .mk []
private def e0 : World Unit sig.EventType := ⟨(), .some atom, h0⟩
private def h1 : PreHistory Unit sig.EventType := .mk [e0]
private def e1 : World Unit sig.EventType := ⟨(), †, h1⟩
private def h2 : PreHistory Unit sig.EventType := .mk [e0, e1]
private def e2 : World Unit sig.EventType := ⟨(), †, h2⟩
private def h3 : PreHistory Unit sig.EventType := .mk [e0, e1, e2]

@[local simp] private theorem mem_mk (t : World Unit sig.EventType) (xs) :
    t ∈ PreHistory.mk xs ↔ t ∈ xs := Iff.rfl
@[local simp] private theorem subset_iff (a b : PreHistory Unit sig.EventType) :
    a ⊆ b ↔ ∀ t, t ∈ a → t ∈ b := Iff.rfl
@[local simp] private theorem unit_exists (Q : Unit → Prop) :
    (∃ u, Q u) ↔ Q () := ⟨fun ⟨u, h⟩ => by cases u; exact h, fun h => ⟨(), h⟩⟩

private theorem hered0 : isHereditarilyTransitive h0 := by
  rw [isHereditarilyTransitive_unfold]
  simp [isTransitive, happensBefore, h0]

private theorem extend_hered (h : PreHistory Unit sig.EventType)
    (hs : ∀ t ∈ h, t.time ⊆ h)
    (hh : ∀ t ∈ h, isHereditarilyTransitive t.time) :
    isHereditarilyTransitive h := by
  rw [isHereditarilyTransitive_unfold]
  exact ⟨fun h' ⟨p, e, ht⟩ => hs (p, e, h') ht,
    fun h' ⟨p, e, ht⟩ => hh (p, e, h') ht⟩

private theorem hered1 : isHereditarilyTransitive h1 := by
  apply extend_hered
  · simp [h1, e0, h0]
  · simpa only [h1, mem_mk, List.mem_singleton, forall_eq] using hered0

private theorem hered2 : isHereditarilyTransitive h2 := by
  apply extend_hered
  · intro t ht
    have : t = e0 ∨ t = e1 := by simpa [h2] using ht
    rcases this with rfl | rfl <;> simp [e0, e1, h0, h1, h2]
  · intro t ht
    have : t = e0 ∨ t = e1 := by simpa [h2] using ht
    rcases this with rfl | rfl
    · exact hered0
    · exact hered1

private theorem hered3 : isHereditarilyTransitive h3 := by
  apply extend_hered
  · intro t ht
    have : t = e0 ∨ t = e1 ∨ t = e2 := by simpa [h3] using ht
    rcases this with rfl | rfl | rfl <;> simp [e0, e1, e2, h0, h1, h2, h3]
  · intro t ht
    have : t = e0 ∨ t = e1 ∨ t = e2 := by simpa [h3] using ht
    rcases this with rfl | rfl | rfl
    · exact hered0
    · exact hered1
    · exact hered2

private def model : Model sig Unit where
  history := ⟨h3, hered3⟩
  predInterp := fun _ _ => Set.univ
  learner := fun _ => {
    quorums := {O | () ∈ O}
    nonempty := ⟨Set.univ, trivial⟩
    upwardClosed := fun {_ _} hO hsub => hsub hO
    pairwiseInter := fun {_ _} hO hO' => ⟨(), hO, hO'⟩ }

private theorem check (Q : Unit → Prop) (ls : List sig.Value) (acc : Set Unit) :
    Sat.check model Q ls acc ↔ (() ∈ acc ∧ Q ()) := by
  induction ls generalizing acc with
  | nil => simp [Sat.check]
  | cons l ls ih =>
    simp only [Sat.check, ih]
    constructor
    · intro h
      exact ⟨(h Set.univ trivial).1.1, (h Set.univ trivial).2⟩
    · rintro ⟨ha, hq⟩ O ho
      exact ⟨⟨ha, ho⟩, hq⟩

private theorem sequential : isSequential () h3 := by
  intro a b ha hb _ _
  simp only [h3, mem_mk, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp [World.accessible, e0, e1, e2, h0, h1, h2]

/-- Restricted Knowledge admits a finite model with a live performed event. -/
theorem exists_live_event_model :
    ∃ (S : Signature) (M : Model S Unit) (live : S.PredSymb)
      (e : World Unit S.EventType) (E : S.EventType),
      (M ⊨ᵀ ThyLive live) ∧ e ∈ M.history.val ∧
      (⟪e⟫ ⊨[M] Formula.predicate0 live) ∧ (⟪e⟫ ⊨[M] Formula.ofEvent E) := by
  refine ⟨sig, model, (), e0, atom, ?_, ?_, ?_, ?_⟩
  · intro ax hax w hw
    rcases hax with rfl | rfl | ⟨ls, φ, ha, rfl⟩ | ⟨ls, φ, ha, rfl⟩
    · simp [liveAlwaysAxiom, Formula.iff, Formula.and, Formula.not,
        Formula.predicate0, Sat, model, Set.mem_univ]
    · change True → isSequential w.place w.time
      intro _
      have hp : w.place = () := Subsingleton.elim _ _
      rw [hp]
      rcases hw with hw | hw
      · exact History.sequentiality_of_predecessor (H := model.history) hw sequential
      · rw [hw]; exact sequential
    · cases ha <;>
        simp only [knowledgeDiamondAxiom, Formula.diamondPast, Formula.boxPast,
          Formula.box, Formula.and, Formula.not, Formula.sometime, Formula.predicate0,
          Formula.ofEvent, Sat, check] <;>
        simp [model, h3, e0, e1, e2, h2, h1, h0, and_assoc,
          or_and_right, exists_or, exists_and_left]
    · cases ha <;>
        simp only [knowledgeBoxAxiom, Formula.diamondPast, Formula.boxPast,
          Formula.box, Formula.and, Formula.not, Formula.sometime, Formula.predicate0,
          Formula.ofEvent, Sat, check] <;>
        simp [model, h3, e0, e1, e2, h2, h1, h0, and_assoc,
          or_and_right, exists_or, exists_and_left]
  · simp [model, h3]
  · trivial
  · exact ⟨rfl, by simp [model, h3, e0]⟩

end ModalDistribution.Examples.FiniteModel
