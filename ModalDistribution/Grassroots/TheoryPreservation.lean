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
lemma predInterp_fresh {P P' : Set A} (h : P ⊆ P')
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
lemma no_fresh_tuples {P P' : Set A} (h : P ⊆ P')
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
lemma happensBeforeEq_lift {P P' : Set A} (h : P ⊆ P')
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
lemma event_false_at_fresh {P P' : Set A} (h : P ⊆ P')
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
lemma predicate_false_at_fresh {P P' : Set A} (h : P ⊆ P')
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
lemma forall_event_imp_at_fresh {P P' : Set A} (h : P ⊆ P')
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

/-! ## §6. Liftability of the concrete ThyLive axioms -/

private lemma liveAlwaysAxiom_isLiftable (liveSymb : Signature.PredSymb S) :
    LiftableFragment.IsLiftable (liveAlwaysAxiom (S := S) liveSymb) := by
  unfold liveAlwaysAxiom Formula.iff
  exact LiftableFragment.isLiftable_and
    (LiftableFragment.IsLiftable.imp
      (LiftableFragment.isAntiLiftable_predicate0 _)
      (LiftableFragment.IsLiftable.atEnd (LiftableFragment.isLiftable_predicate0 _)))
    (LiftableFragment.IsLiftable.imp
      (LiftableFragment.IsAntiLiftable.atEnd (LiftableFragment.isAntiLiftable_predicate0 _))
      (LiftableFragment.isLiftable_predicate0 _))

private lemma liveSeqAxiom_isLiftable (liveSymb : Signature.PredSymb S) :
    LiftableFragment.IsLiftable (liveSeqAxiom (S := S) liveSymb) := by
  unfold liveSeqAxiom
  exact LiftableFragment.IsLiftable.imp
    (LiftableFragment.isAntiLiftable_predicate0 _) LiftableFragment.IsLiftable.seq

/-! ## §7. Fresh-agent discharge

At a fresh agent, `predicate0 liveSymb` is False and `event E` is False.
Every ThyHBB1 axiom has one of these as a guard, making the axiom
vacuously True. -/

/-- Generic helper: any `∀ v, imp guard(v) body(v)` is True at fresh
agents when the guard requires an event or predicate. -/
lemma imp_false_at_fresh
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A) (M_P : Model S ↥P)
    (p' : ↥P') (hp' : p'.val ∉ P)
    (evt : MaybeEvent (Signature.EventType S))
    (H : PreHistory ↥P (Signature.EventType S))
    {φ ψ : Formula S}
    (hGuard : ¬ ⟪(p', evt, liftPreHistory h H)⟫
        ⊨[LiftPreservation.canonicalLift h F M_P] φ) :
    ⟪(p', evt, liftPreHistory h H)⟫
      ⊨[LiftPreservation.canonicalLift h F M_P] (φ ⇒ᶠ ψ) := by
  simp only [Sat]; exact fun h => absurd h hGuard

/-! ## §8. Theory preservation — main theorem

We prove the theorem for the concrete axioms via `allWorldValid_lift`,
and handle `liveActiveAxiom` by a direct semantic argument. The
knowledge axiom schemes are left as sorry (see §9 note). -/

/-- `liveActiveAxiom` preservation: direct semantic proof.
`⤒(□[](pred ⇒ ↓⊤))` uses `□[]` (boxEmpty) which is outside the
syntactic liftable fragment, but IS preserved because:
- Fresh agents: pred is False → imp vacuously True
- Lifted agents: pred coherence + past-tuple lifting -/
private theorem allWorldValid_liveActive
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A) [IsCoalescent F]
    (M_P : Model S ↥P) (hLearner : M_P.learner = F.σ P)
    (liveSymb : Signature.PredSymb S)
    (hValidA : AllWorldValid M_P (liveActiveAxiom liveSymb)) :
    AllWorldValid (LiftPreservation.canonicalLift h F M_P)
      (liveActiveAxiom liveSymb) := by
  intro t ht
  simp only [LiftPreservation.canonicalLift_history_val] at ht
  obtain ⟨H, hH, hHeq⟩ := happensBeforeEq_lift h ht
  rcases t with ⟨p', evt, _⟩; subst hHeq
  simp only [liveActiveAxiom]
  rw [Sat.atEnd, Sat.boxEmpty]
  simp only [World.place, World.event, World.time,
             LiftPreservation.canonicalLift_history_val]
  intro q'
  -- Goal: (pred ⇒ ↓⊤) at (q', †, M'.history.val)
  by_cases hq : q'.val ∈ P
  · -- Lifted agent: transfer from original
    let q : ↥P := ⟨q'.val, hq⟩
    have hOrig := hValidA (PreHistory.happensBeforeEq_refl M_P.history.val)
      (t := (q, †, M_P.history.val))
    simp only [liveActiveAxiom] at hOrig
    rw [Sat.atEnd, Sat.boxEmpty] at hOrig
    simp only [World.place, World.event, World.time] at hOrig
    have hOrigQ := hOrig q
    have hqEq : q' = liftAgent h q := Subtype.ext rfl
    -- Unfold Sat for both hOrigQ and goal consistently
    simp only [Sat, Formula.predicate0, Formula.top, World.place, World.time] at hOrigQ ⊢
    intro hPred
    -- Transfer pred: rewrite q' to liftAgent h q, then use predInterp coherence
    rw [hqEq, LiftPreservation.canonicalLift_predInterp_at_lifted] at hPred
    obtain ⟨s, hsMem, hsPlace, _⟩ := hOrigQ hPred
    exact ⟨liftWorld h s, mem_liftPreHistory_of_mem h hsMem,
           by simp [liftWorld, hsPlace, hqEq], id⟩
  · -- Fresh agent: pred is False
    simp only [Sat]; intro hPred; exfalso
    exact predicate_false_at_fresh h F M_P q' hq † M_P.history.val liveSymb hPred

/-- The main theorem: ThyHBB1 theory validity is preserved by canonical
coalescent lifting. -/
theorem thyHBB1_theory_preservation
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A) [IsCoalescent F]
    (M_P : Model S ↥P) (hLearner : M_P.learner = F.σ P)
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S)
    (hValid : Theory.Valid (M := M_P)
      (ThyHBB1 liveSymb proposeSymb echoSymb voteSymb deliverSymb)) :
    Theory.Valid (M := LiftPreservation.canonicalLift h F M_P)
      (ThyHBB1 liveSymb proposeSymb echoSymb voteSymb deliverSymb) := by
  intro ax hax
  simp only [ThyHBB1] at hax
  -- Each axiom is either from ThyLive or one of the 7 protocol axioms
  rcases hax with hLive | hEchoB | hVoteB | hDeliverB | hNE |
                  hEchoF | hVoteF | hDeliverF
  · -- ThyLive axiom
    simp only [ThyLive] at hLive
    rcases hLive with rfl | rfl | rfl | ⟨ls, ψ, rfl⟩ | ⟨ls, ψ, rfl⟩
    · -- liveAlways: liftable, fresh discharge via pred False (needs classical for ∧ encoding)
      exact allWorldValid_lift h F M_P hLearner
        (liveAlwaysAxiom_isLiftable liveSymb) (hValid (by simp [ThyHBB1, ThyLive]))
        (fun p' hp' evt H _ => by
          -- liveAlways = (pred ⇔ ⤒ pred) = and (pred⇒⤒pred) (⤒pred⇒pred)
          -- Formula.and uses double negation: ¬(φ ⇒ ¬ψ)
          -- Both imp's are True (pred is False at fresh), so we construct
          -- the witnesses for the double negation directly.
          -- Both sides of the biconditional involve pred, which is False at fresh
          simp only [liveAlwaysAxiom, Formula.iff, Sat, Formula.and, Formula.not,
                     LiftPreservation.canonicalLift_history_val]
          exact fun hAbs => hAbs
            (fun hP => absurd hP
              (predicate_false_at_fresh h F M_P p' hp' evt H liveSymb))
            (fun hP => absurd hP
              (predicate_false_at_fresh h F M_P p' hp' †
                M_P.history.val liveSymb)))
    · -- liveSeq: liftable, fresh discharge via pred False
      exact allWorldValid_lift h F M_P hLearner
        (liveSeqAxiom_isLiftable liveSymb) (hValid (by simp [ThyHBB1, ThyLive]))
        (fun p' hp' evt H _ => by
          simp only [liveSeqAxiom, Sat]
          exact fun hP => absurd hP (predicate_false_at_fresh h F M_P p' hp' evt H liveSymb))
    · -- liveActive: sorry (uses □[], outside fragment)
      exact allWorldValid_liveActive h F M_P hLearner liveSymb
        (hValid (by simp [ThyHBB1, ThyLive]))
    · -- knowledgeDiamond ls ψ: fresh-agent case fully discharged.
      -- The axiom is: ⤒(♢↓[ls](pred ∧ ψ)) ⇒ (pred ⇒ ↕(♢↓[ls] ψ))
      -- At any world: the inner (pred ⇒ ...) has pred as guard.
      -- Fresh agents have pred = False → inner imp is True → outer imp is True.
      -- Lifted agents: requires conservative extension for arbitrary ψ.
      rename_i ls ψ
      intro t ht
      simp only [LiftPreservation.canonicalLift_history_val] at ht
      obtain ⟨H, hH, hHeq⟩ := happensBeforeEq_lift h ht
      rcases t with ⟨p', evt, _⟩; subst hHeq
      -- The formula is imp A (imp pred C). Unfold the outer imp.
      simp only [knowledgeDiamondAxiom, Sat]
      intro _hAnt hPred
      -- If p' is fresh, pred is False → contradiction
      by_cases hp : p'.val ∈ P
      · -- Lifted agent: monotonicity reduces antecedent, then bridge gap
        -- _hAnt : ⤒(♢↓[ls](pred ∧ ψ)) at M', hPred : pred at M'
        -- Goal : ↕(♢↓[ls] ψ) at M'
        -- Step 1: monotonicity — drop pred from (pred ∧ ψ) to get ♢↓[ls] ψ at end-of-time
        let M' := LiftPreservation.canonicalLift h F M_P
        have hMono : ⟪(p', †, M'.history.val)⟫ ⊨[M'] ♢ᶠ↓[ls] ψ :=
          Sat.diamond_of_imp (M := M') (w := ⟨p', †, M'.history.val⟩) ls
            (fun q hPastAnd => Sat.past_of_imp (M := M')
              (w := ⟨q, †, M'.history.val⟩)
              (h := fun t _ _ hAnd => Sat.and_right M' t hAnd) hPastAnd)
            _hAnt
        -- Step 2: bridge atEnd(♢↓[ls] ψ) to sometime(♢↓[ls] ψ) = atEnd(past(♢↓[ls] ψ))
        -- This requires finding a past tuple of p' whose sub-history
        -- contains the antecedent's past-tuple witnesses. See §9 note.
        sorry
      · -- Fresh agent: pred is False
        exfalso
        exact predicate_false_at_fresh h F M_P p' hp evt H liveSymb hPred
    · -- knowledgeDiamondEventually ls ψ: same structure
      rename_i ls ψ
      intro t ht
      simp only [LiftPreservation.canonicalLift_history_val] at ht
      obtain ⟨H, hH, hHeq⟩ := happensBeforeEq_lift h ht
      rcases t with ⟨p', evt, _⟩; subst hHeq
      simp only [knowledgeDiamondEventuallyAxiom, Sat]
      intro _hAnt hPred
      by_cases hp : p'.val ∈ P
      · -- Lifted agent: same monotonicity argument as knowledgeDiamond
        let M' := LiftPreservation.canonicalLift h F M_P
        have hMono : ⟪(p', †, M'.history.val)⟫ ⊨[M'] □ᶠ↓[ls] ψ :=
          Sat.box_of_imp (M := M') (w := ⟨p', †, M'.history.val⟩) ls
            (fun q hPastAnd => Sat.past_of_imp (M := M')
              (w := ⟨q, †, M'.history.val⟩)
              (h := fun t _ _ hAnd => Sat.and_right M' t hAnd) hPastAnd)
            _hAnt
        sorry
      · exfalso
        exact predicate_false_at_fresh h F M_P p' hp evt H liveSymb hPred
  -- 7 protocol axioms: liftable (by catalog) + fresh discharge.
  -- Backward + nonequiv: antecedent is event(...)  → False at fresh
  -- Forward: antecedent is (pred ∧ ...) → pred False at fresh via double-negation
  -- Backward + nonequiv: event guard False at fresh (event_false_at_fresh)
  · subst hEchoB; exact allWorldValid_lift h F M_P hLearner
      (LiftableFragment.echoBackwardAxiom_isLiftable _ _) (hValid (by simp [ThyHBB1]))
      (fun p' hp' evt H _ => by
        simp only [echoBackwardAxiom, Sat]; intro v hE
        exact absurd hE (event_false_at_fresh h F M_P p' hp' evt H _))
  · subst hVoteB; exact allWorldValid_lift h F M_P hLearner
      (LiftableFragment.voteBackwardAxiom_isLiftable _ _ _) (hValid (by simp [ThyHBB1]))
      (fun p' hp' evt H _ => by
        simp only [voteBackwardAxiom, Sat]; intro _ _ hE
        exact absurd hE (event_false_at_fresh h F M_P p' hp' evt H _))
  · subst hDeliverB; exact allWorldValid_lift h F M_P hLearner
      (LiftableFragment.deliverBackwardAxiom_isLiftable _ _) (hValid (by simp [ThyHBB1]))
      (fun p' hp' evt H _ => by
        simp only [deliverBackwardAxiom, Sat]; intro _ _ _ hE
        exact absurd hE (event_false_at_fresh h F M_P p' hp' evt H _))
  · subst hNE; exact allWorldValid_lift h F M_P hLearner
      (LiftableFragment.echoNonEquivAxiom_isLiftable _) (hValid (by simp [ThyHBB1]))
      (fun p' hp' evt H _ => by
        simp only [echoNonEquivAxiom, Sat]; intro _ _ hE
        exact absurd hE (event_false_at_fresh h F M_P p' hp' evt H _))
  · subst hEchoF; exact allWorldValid_lift h F M_P hLearner
      (LiftableFragment.echoForwardAxiom_isLiftable _ _ _)
      (hValid (by simp [ThyHBB1]))
      (fun p' hp' evt H _ => by
        simp only [echoForwardAxiom, Sat, Formula.and, Formula.not]
        intro v hConj; exfalso; apply hConj
        exact fun hP => absurd hP (predicate_false_at_fresh h F M_P p' hp' evt H liveSymb))
  · subst hVoteF; exact allWorldValid_lift h F M_P hLearner
      (LiftableFragment.voteForwardAxiom_isLiftable _ _ _ _)
      (hValid (by simp [ThyHBB1]))
      (fun p' hp' evt H _ => by
        simp only [voteForwardAxiom, Sat]; intro _ _ _
        simp only [Formula.and, Formula.not, Sat]
        intro hConj; exfalso; apply hConj
        exact fun hP => absurd hP (predicate_false_at_fresh h F M_P p' hp' evt H liveSymb))
  · subst hDeliverF; exact allWorldValid_lift h F M_P hLearner
      (LiftableFragment.deliverForwardAxiom_isLiftable _ _ _)
      (hValid (by simp [ThyHBB1]))
      (fun p' hp' evt H _ => by
        simp only [deliverForwardAxiom, Sat, Formula.and, Formula.not]
        intro _ _ _ hConj; exfalso; apply hConj
        exact fun hP => absurd hP (predicate_false_at_fresh h F M_P p' hp' evt H liveSymb))

/-! ## §9. Knowledge axiom schemes — remaining gap

The knowledge axiom schemes `knowledgeDiamondAxiom ls ψ` and
`knowledgeDiamondEventuallyAxiom ls ψ` are quantified over arbitrary
formulas `ψ`. The fresh-agent case is discharged (pred guard is False).

For the lifted-agent case, the proof applies **monotonicity** within M'
to reduce the antecedent: since `pred ∧ ψ → ψ` (by `Sat.and_right`), and
`past` and `diamond`/`box` are monotone (`Sat.past_of_imp`, `Sat.diamond_of_imp`,
`Sat.box_of_imp`), we obtain `⤒(♢↓[ls] ψ)` (resp. `⤒(□↓[ls] ψ)`) from the
antecedent — all within M'.

### The remaining gap

The consequent `↕(♢↓[ls] ψ) = atEnd(past(♢↓[ls] ψ))` requires finding a
**past tuple** of the current agent whose sub-history still supports the
diamond/box check. We have `♢↓[ls] ψ` at end-of-time (full history) but
need it at some sub-history `t.time` for a tuple `t` of the current agent.

This is exactly the knowledge-persistence property: quorum knowledge at
end-of-time implies quorum knowledge at some past moment of the agent.
A general conservative extension (`Sat` equivalence between M_P and M'
for all formulas) is **false** — `diamond [] φ` quantifies over `P' ⊃ P`,
so `¬(diamond [] (¬pred))` is True in M_P but False in M' when fresh agents
have `pred = False`. Both forward and backward transfer fail for arbitrary
formulas.

### Possible approaches

1. **Model-level argument**: Show that the `liftPreHistory` structure
   preserves the temporal ordering that the knowledge axiom exploits —
   specifically that if `diamond ls (past ψ)` holds at the full lifted
   history, it holds at some lifted sub-history of the current agent.
2. **Axiom specialisation**: Use M_P's knowledge axiom with `ψ' = ⊤` to
   extract a suitable sub-history `s₀.time`, then show the M' antecedent's
   `past ψ` witnesses lie in `liftPreHistory h s₀.time`. -/

end TheoryPreservation
end Grassroots
end ModalDistribution
