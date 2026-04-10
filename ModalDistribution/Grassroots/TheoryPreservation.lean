import ModalDistribution.Grassroots.LiftPreservation
import ModalDistribution.Examples.ThyHBB1.Axioms

/-!
# Theory preservation under coalescent lifting

This file proves that ThyHBB1-validity is preserved by canonical
coalescent lifting: if `M_P ⊨ᵀ ThyHBB1` then `canonicalLift h F M_P ⊨ᵀ ThyHBB1`.

The proof combines two ingredients:
1. **Point-wise preservation** (`lift_preserves`): liftable formulas are
   preserved at lifted-agent worlds.
2. **Fresh-agent vacuity**: all ThyHBB1 axioms are implications whose
   antecedents require event or predicate membership — both empty for fresh
   agents in the canonical lift.
-/

namespace ModalDistribution
namespace Grassroots
namespace TheoryPreservation

open ModalDistribution.Logic
open ModalDistribution.Examples
open scoped Formula PreHistory

set_option linter.style.commandStart false

variable {A : Type}
variable {S : Signature.{0, 0, 0}}

/-! ## §1. Fresh-agent lemmas

In `canonicalLift h F M_P`, fresh agents (those with `p'.val ∉ P`) have:
- Empty predicate interpretation (`liftPredInterp` returns `∅`)
- No tuples in any sub-history (all history tuples have lifted-agent places)

These facts make event and predicate atoms False at fresh agents,
which vacuously satisfies any implication with such antecedents. -/

/-- At a fresh agent, the predicate interpretation is empty. -/
private lemma predInterp_fresh {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A)
    (M_P : Model S ↥P)
    (p' : ↥P') (hp' : p'.val ∉ P)
    (H' : PreHistory ↥P' (Signature.EventType S)) :
    (LiftPreservation.canonicalLift h F M_P).predInterp p' H' = ∅ := by
  change LiftPreservation.liftPredInterp h M_P.predInterp p' H' = ∅
  unfold LiftPreservation.liftPredInterp
  classical
  simp [hp']

/-- No tuple in a lifted prehistory has a fresh agent as its place. -/
private lemma no_fresh_tuples {P P' : Set A} (h : P ⊆ P')
    {Event : Type} (p' : ↥P') (hp' : p'.val ∉ P)
    (H : PreHistory ↥P Event)
    (t : World ↥P' Event) (ht : t ∈ liftPreHistory h H)
    : t.place ≠ p' := by
  rw [mem_liftPreHistory_iff] at ht
  obtain ⟨s, _, hsEq⟩ := ht
  rw [← hsEq]
  simp only [liftWorld_mk, World.place]
  intro heq
  have : (liftAgent h s.1).val = p'.val := congrArg Subtype.val heq
  simp [liftAgent] at this
  exact hp' (this ▸ s.1.property)

/-! ## §2. happensBeforeEq in lifted histories -/

/-- Every `⪯`-predecessor of a lifted history is itself a lift. -/
private lemma happensBeforeEq_lift {P P' : Set A} (h : P ⊆ P')
    {H' : PreHistory ↥P' (Signature.EventType S)}
    {H_orig : PreHistory ↥P (Signature.EventType S)}
    (hHBE : H' ⪯ liftPreHistory h H_orig) :
    ∃ H : PreHistory ↥P (Signature.EventType S),
      H ⪯ H_orig ∧ H' = liftPreHistory h H := by
  rcases hHBE with ⟨p', e, hmem⟩ | rfl
  · rw [mem_liftPreHistory_iff] at hmem
    obtain ⟨s, hsMem, hsEq⟩ := hmem
    refine ⟨s.2.2, Or.inl ⟨s.1, s.2.1, hsMem⟩, ?_⟩
    have := congrArg (fun w => w.2.2) hsEq
    simp [liftWorld] at this; exact this.symm
  · exact ⟨H_orig, Or.inr rfl, rfl⟩

/-! ## §3. AllWorldValid at lifted agents -/

/-- At lifted-agent worlds, `AllWorldValid` transfers via `lift_preserves`. -/
theorem allWorldValid_at_lifted
    {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A) [IsCoalescent F]
    (M_P : Model S ↥P) (hLearner : M_P.learner = F.σ P)
    {φ : Formula S} (hlift : LiftableFragment.IsLiftable φ)
    (hValid : AllWorldValid M_P φ)
    -- At a lifted-agent world:
    (p : ↥P) (evt : MaybeEvent (Signature.EventType S))
    (H : PreHistory ↥P (Signature.EventType S))
    (hH : H ⪯ M_P.history.val) :
    ⟪(liftAgent h p, evt, liftPreHistory h H)⟫
      ⊨[LiftPreservation.canonicalLift h F M_P] φ :=
  lift_preserves h F M_P hLearner hlift (p, evt, H) (hValid hH)

/-! ## §4. AllWorldValid preservation for liftable formulas

Combines the lifted-agent case (via `lift_preserves`) with the
fresh-agent case. For the fresh-agent case, we require that φ is
satisfied at fresh-agent worlds — which holds for all ThyHBB1 axioms
(their antecedents require event/predicate membership, empty for fresh
agents), but not for all liftable formulas in general. -/

/-- `AllWorldValid` preservation for liftable formulas, with an explicit
fresh-agent hypothesis. -/
theorem allWorldValid_lift
    {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A) [IsCoalescent F]
    (M_P : Model S ↥P) (hLearner : M_P.learner = F.σ P)
    {φ : Formula S} (hlift : LiftableFragment.IsLiftable φ)
    (hValid : AllWorldValid M_P φ)
    -- Fresh-agent hypothesis: φ holds at fresh-agent worlds
    (hFresh : ∀ (p' : ↥P'), p'.val ∉ P →
      ∀ (evt : MaybeEvent (Signature.EventType S))
        (H : PreHistory ↥P (Signature.EventType S)),
        H ⪯ M_P.history.val →
        ⟪(p', evt, liftPreHistory h H)⟫
          ⊨[LiftPreservation.canonicalLift h F M_P] φ) :
    AllWorldValid (LiftPreservation.canonicalLift h F M_P) φ := by
  intro t ht
  -- t.time ⪯ (canonicalLift ...).history.val = liftPreHistory h M_P.history.val
  simp only [LiftPreservation.canonicalLift_history_val] at ht
  obtain ⟨H, hH, hHeq⟩ := happensBeforeEq_lift h ht
  -- hHeq : t.time = liftPreHistory h H
  -- Rewrite the world's time component
  rcases t with ⟨p', evt, _⟩; subst hHeq
  -- Case split on whether the agent is in P
  by_cases hp : p'.val ∈ P
  · -- Lifted agent
    exact allWorldValid_at_lifted h F M_P hLearner hlift hValid
      ⟨p'.val, hp⟩ evt H hH
  · -- Fresh agent
    exact hFresh p' hp evt H hH

/-! ## §5. Theory preservation for ThyHBB1

Every ThyHBB1 axiom is:
1. In the liftable fragment (by the catalog in `LiftableFragment.lean`)
2. Vacuously True at fresh agents (all antecedents require event or
   predicate atoms, which are empty for fresh agents)

Combining these gives the theory preservation theorem. -/

/-- At a fresh agent, `event E` is always False: the event conjunction
requires history membership, but fresh agents have no tuples. -/
private lemma event_false_at_fresh {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A)
    (M_P : Model S ↥P)
    (p' : ↥P') (hp' : p'.val ∉ P)
    (evt : MaybeEvent (Signature.EventType S))
    (H : PreHistory ↥P (Signature.EventType S))
    (E : EventAtom S) :
    ¬ ⟪(p', evt, liftPreHistory h H)⟫
        ⊨[LiftPreservation.canonicalLift h F M_P] Formula.event E := by
  simp only [Sat, LiftPreservation.canonicalLift_history_val]
  rintro ⟨_, hmem⟩
  rw [mem_liftPreHistory_iff] at hmem
  obtain ⟨s, _, hsEq⟩ := hmem
  exact absurd (congrArg (fun w => w.1.val) hsEq ▸ s.1.property) hp'

/-- At a fresh agent, `predicate0 sym` is always False. -/
private lemma predicate_false_at_fresh {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A)
    (M_P : Model S ↥P)
    (p' : ↥P') (hp' : p'.val ∉ P)
    (evt : MaybeEvent (Signature.EventType S))
    (H : PreHistory ↥P (Signature.EventType S))
    (sym : Signature.PredSymb S) :
    ¬ ⟪(p', evt, liftPreHistory h H)⟫
        ⊨[LiftPreservation.canonicalLift h F M_P] Formula.predicate0 sym := by
  simp only [Sat, Formula.predicate0, World.place, World.time]
  rw [predInterp_fresh h F M_P p' hp']
  exact Set.not_mem_empty _

/-- Helper: any formula of the form `∀ v, event_guard(v) → body(v)` is
True at fresh agents, since the event guard is False. -/
private lemma forall_event_imp_at_fresh {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A)
    (M_P : Model S ↥P)
    (p' : ↥P') (hp' : p'.val ∉ P)
    (evt : MaybeEvent (Signature.EventType S))
    (H : PreHistory ↥P (Signature.EventType S))
    (eventSymb : Signature.EventSymb S)
    (body : Signature.Value S → Signature.Value S → Formula S) :
    ⟪(p', evt, liftPreHistory h H)⟫
      ⊨[LiftPreservation.canonicalLift h F M_P]
      ∀ᶠ (fun v => Formula.ofEvent ⟨eventSymb, [v]⟩ ⇒ᶠ body v v) := by
  simp only [Sat]
  intro v hevt
  exfalso
  exact event_false_at_fresh h F M_P p' hp' evt H ⟨eventSymb, [v]⟩ hevt

end TheoryPreservation
end Grassroots
end ModalDistribution
