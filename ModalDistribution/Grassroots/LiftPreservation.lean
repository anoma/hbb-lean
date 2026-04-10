import ModalDistribution.Logic.Semantics
import ModalDistribution.Grassroots.LiftHistory
import ModalDistribution.Grassroots.Coalescent
import ModalDistribution.Grassroots.LiftableFragment

set_option linter.style.commandStart false

/-!
# Lifting preservation — Session 2: foundation and trivial cases

This file is the second session in the four-session plan to prove that
formulas in the `IsLiftable` fragment are preserved by canonical
coalescent lifting of HBB models.

## Session 2 deliverables

1. **The round-trip lemma** `projectPreHistory_liftPreHistory_eq`:
   `projectPreHistory h ∘ liftPreHistory h = id`. Foundational for the
   `predicate` case (and several others).
2. **`liftPredInterp`**: how to lift a predicate interpretation along
   a participant-set inclusion. Uses `projectPreHistory` to recover the
   small-universe history at lifted agents.
3. **`canonicalLift`**: the canonical lift of an HBB `Model S ↥P` to a
   `Model S ↥P'`, parameterised by a coalescent learner family.
4. **Coherence lemmas**: `canonicalLift_history_val`,
   `canonicalLift_predInterp_at_lifted`, `canonicalLift_learner`.
5. **The preservation theorem signature**, with proofs for the trivial
   cases (`bot`, `eq`, `event`, `predicate`, `seq`) and `sorry`s for the
   inductive cases (to be filled in Sessions 3 and 4).

The trivial cases here are exactly those that don't recurse — they only
need the lift coherence lemmas (history mems, predInterp at lifted
agents, sequentiality lifting from `LiftHistory.lean`).
-/

namespace ModalDistribution
namespace Grassroots
namespace LiftPreservation

open ModalDistribution.Logic
open scoped Formula PreHistory

universe u v
variable {A : Type u}

/-! ## §1. The round-trip: project ∘ lift = id

Lifting a prehistory and then projecting it back recovers the original.
This is the "left inverse" relationship: lifting injects every tuple
into the larger universe by re-tagging its agent, and projecting drops
exactly those tuples whose place is not in the smaller set. Since lifting
re-tags all agents to lifted-from-`P` form (whose underlying values are
already in `P`), projection drops nothing — recovering the input. -/

mutual

private theorem projectListAux_liftListAux
    {P P' : Set A} (h : P ⊆ P') {Event : Type v} :
    ∀ (l : List (World ↥P Event)),
      projectListAux h (liftListAux h l) = l
  | [] => rfl
  | (q, e, t) :: rest => by
      classical
      rw [liftListAux_cons]
      -- Goal: projectListAux h ((liftAgent h q, e, liftPreHistory h t) :: liftListAux h rest)
      --     = (q, e, t) :: rest
      -- The head's first component is liftAgent h q = ⟨q.val, h q.property⟩
      -- which is in P (since q.val ∈ P by q.property)
      rw [show (liftAgent h q, e, liftPreHistory h t) =
            ((⟨q.val, h q.property⟩ : ↥P'), e, liftPreHistory h t) from rfl,
          projectListAux_cons_in h (h q.property) q.property,
          projectPreHistory_liftPreHistory h t,
          projectListAux_liftListAux h rest]

theorem projectPreHistory_liftPreHistory
    {P P' : Set A} (h : P ⊆ P') {Event : Type v} :
    ∀ (H : PreHistory ↥P Event),
      projectPreHistory h (liftPreHistory h H) = H
  | .mk l => by
      rw [liftPreHistory_mk, projectPreHistory_mk,
          projectListAux_liftListAux h l]

end

/-- The round-trip on `History` (wrapping the prehistory version). -/
theorem projectHistory_liftHistory {P P' : Set A} (h : P ⊆ P')
    {Event : Type v} (H : History ↥P Event) :
    (projectHistory h (liftHistory h H)).val = H.val := by
  change projectPreHistory h (liftPreHistory h H.val) = H.val
  exact projectPreHistory_liftPreHistory h H.val

/-! ## §2. Lifting predicate interpretations

`Model.predInterp` has type `(p : P) → PreHistory P Event → Set AtomicPred`.
For the canonical lift to `↥P'`, we need a function on `↥P'` and prehistories
over `↥P'`. The natural lift: at lifted agents (those whose underlying value
is in `P`), project the input prehistory back to `↥P` and use the original
predInterp; at fresh agents, return the empty set. -/

variable {S : Signature.{0, 0, 0}}

/-- Lift a predicate interpretation along an inclusion `P ⊆ P'`. Uses
classical case-analysis on whether the agent's underlying value is in
the smaller participant set. -/
noncomputable def liftPredInterp {P P' : Set A} (h : P ⊆ P')
    (predInterp : (p : ↥P) →
      PreHistory ↥P (Signature.EventType S) →
      Set (Signature.AtomicPredType S)) :
    (a : ↥P') → PreHistory ↥P' (Signature.EventType S) →
      Set (Signature.AtomicPredType S) := fun a H => by
  classical
  exact (if h_in : a.val ∈ P then
          predInterp ⟨a.val, h_in⟩ (projectPreHistory h H)
        else
          ∅)

/-- At a lifted agent and lifted history, the lifted predInterp recovers
the original. This is the key coherence lemma — combines the round-trip
identity with `Subtype.ext` for the agent. -/
lemma liftPredInterp_at_lifted {P P' : Set A} (h : P ⊆ P')
    (predInterp : (p : ↥P) →
      PreHistory ↥P (Signature.EventType S) →
      Set (Signature.AtomicPredType S))
    (p : ↥P) (H : PreHistory ↥P (Signature.EventType S)) :
    liftPredInterp h predInterp (liftAgent h p) (liftPreHistory h H) =
      predInterp p H := by
  classical
  unfold liftPredInterp
  -- After unfolding, the function body is the if-then-else.
  -- The `(liftAgent h p).val ∈ P` is `p.val ∈ P`, which is `p.property`.
  simp only [liftAgent, dif_pos p.property, projectPreHistory_liftPreHistory]

/-! ## §3. The canonical lift of an HBB model

Given a coalescent learner family `F : LearnerFamily V A` and a model
`M_P : Model S ↥P` whose learner agrees with `F.σ P`, we construct the
canonical lifted model `canonicalLift F h M_P : Model S ↥P'`.

* The lifted history is `liftHistory h M_P.history`.
* The lifted predInterp is `liftPredInterp h M_P.predInterp`.
* The lifted learner is `F.σ P'` (provided by the coalescent family).

Note: we do *not* require `M_P.learner = F.σ P` as a hypothesis at the
construction level — that constraint becomes a hypothesis of the eventual
preservation theorem in §5. -/

noncomputable def canonicalLift {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A)
    (M_P : Model S ↥P) : Model S ↥P' where
  history := liftHistory h M_P.history
  predInterp := liftPredInterp h M_P.predInterp
  learner := F.σ P'

/-! ## §4. Coherence lemmas about `canonicalLift` -/

@[simp] lemma canonicalLift_history_val {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A)
    (M_P : Model S ↥P) :
    (canonicalLift h F M_P).history.val =
      liftPreHistory h M_P.history.val := rfl

@[simp] lemma canonicalLift_learner {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A)
    (M_P : Model S ↥P) :
    (canonicalLift h F M_P).learner = F.σ P' := rfl

lemma canonicalLift_predInterp_at_lifted {P P' : Set A} (h : P ⊆ P')
    [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A)
    (M_P : Model S ↥P)
    (p : ↥P) (H : PreHistory ↥P (Signature.EventType S)) :
    (canonicalLift h F M_P).predInterp (liftAgent h p) (liftPreHistory h H) =
      M_P.predInterp p H := by
  change liftPredInterp h M_P.predInterp (liftAgent h p) (liftPreHistory h H) =
    M_P.predInterp p H
  exact liftPredInterp_at_lifted h M_P.predInterp p H

end LiftPreservation

/-! ## §5. Injectivity of the lift

`liftWorld` is injective, which we derive from `liftAgent_injective`
(Coalescent) and `projectPreHistory_liftPreHistory` (the round-trip).
This is the key tool for the anti-lift direction of the preservation
theorem: if a tuple belongs to a lifted history, it must itself be a
lift from the original history. -/

universe u in
private lemma liftWorld_injective {A : Type u} {P P' : Set A} (h : P ⊆ P')
    {Event : Type} {t₁ t₂ : World ↥P Event}
    (heq : liftWorld h t₁ = liftWorld h t₂) : t₁ = t₂ := by
  rcases t₁ with ⟨a₁, e₁, H₁⟩; rcases t₂ with ⟨a₂, e₂, H₂⟩
  simp only [liftWorld_mk, Prod.mk.injEq] at heq
  obtain ⟨ha, he, hH⟩ := heq
  exact Prod.ext (liftAgent_injective h ha)
    (Prod.ext he (by rw [← LiftPreservation.projectPreHistory_liftPreHistory h H₁,
                         ← LiftPreservation.projectPreHistory_liftPreHistory h H₂, hH]))

open ModalDistribution.Logic
open scoped Formula PreHistory

/-! ## §6. The mutual preservation theorem (Session 3)

The Sat-level preservation theorem: liftable formulas are preserved by
canonical coalescent lifting (`lift_preserves`), and anti-liftable
formulas are preserved by projection (`anti_lift_preserves`). These are
mutually recursive because `Formula.imp φ ψ` is liftable when `φ` is
anti-liftable and `ψ` is liftable (and vice versa).

**Universe note.** The `Sat` definition in `Logic/Semantics.lean` has
`{P : Type}` (= `Type 0`). To match this, the theorems below use
`{A : Type}` instead of the universe-polymorphic `{A : Type u}` used
in §§1–4.

**Notation caveat.** The `⊨` notation has trailing precedence that
greedily consumes `→`, so `(⟪w⟫ ⊨[M] φ) → ψ` must be parenthesised.
Inside the mutual block we avoid this by using `simp only [Sat]` to
unfold `Sat` before introducing assumptions.

### Session 3 deliverables

Proved (no `sorry`):
  `bot`, `eq`, `event`, `predicate`, `seq`, `forall_`, `past`, `atEnd`,
  `imp` — for both lift and anti-lift directions.

### Session 4 deliverables

Diamond cases proved using `[IsCoalescent F]` and `hLearner` hypotheses:
  Lift: `diamondEmpty` (witness via liftAgent), `diamondSeq` and
  `diamondNotPastEvent` (via `check_lift_of_witness_lift`).
  Anti-lift: `diamond` for nonempty learner lists (via lifted-quorum
  specialisation, `check_anti_lift`). The `diamond []` anti-lift
  case remains `sorry` — see §7 note. -/

section PreservationType0
-- Must match Sat's {P : Type} (= Type 0)
variable {A : Type}
variable {S : Signature.{0, 0, 0}}

/-! ### §6a. Coalescence forces nonempty quorum restrictions -/

/-- Under coalescence, every P'-quorum has nonempty restriction to P.
Proof: `lift_quorum` gives a P'-quorum inside `range(liftAgent h)`.
Pairwise intersection forces every other P'-quorum to intersect it. -/
private lemma restrict_nonempty_of_coalescent
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P']
    {V : Type} (F : LearnerFamily V A) [IsCoalescent F]
    (v : V) (O' : Set ↥P') (hO' : O' ∈ (F.σ P' v).quorums) :
    (restrictQuorumSet h O').Nonempty := by
  obtain ⟨O₀, hO₀⟩ := (F.σ P v).nonempty
  have hLift := IsCoalescent.lift_quorum h v hO₀
  obtain ⟨q', hq'O', hq'L⟩ := (F.σ P' v).pairwiseInter hO' hLift
  rw [mem_liftQuorumSet] at hq'L
  obtain ⟨q, _, hqEq⟩ := hq'L
  exact ⟨q, by rw [mem_restrictQuorumSet, hqEq]; exact hq'O'⟩

/-! ### §6b. Check-transfer lemma (lift direction) -/

/-- If every Sat-witness at `(p, †, H)` transfers from the original model
to the lifted model via `liftAgent`, then `Sat.check` transfers too —
provided the learner family is coalescent and `M_P.learner = F.σ P`. -/
private lemma check_lift_of_witness_lift
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A) [IsCoalescent F]
    (M_P : Model S ↥P) (hLearner : M_P.learner = F.σ P)
    (H : PreHistory ↥P (Signature.EventType S))
    {φ : Formula S}
    (hWitness : ∀ (p : ↥P),
      (⟪(p, †, H)⟫ ⊨[M_P] φ) →
      (⟪(liftAgent h p, †, liftPreHistory h H)⟫
        ⊨[LiftPreservation.canonicalLift h F M_P] φ))
    (ls : List (Signature.Value S))
    (acc : Set ↥P) (acc' : Set ↥P')
    (hAcc : ∀ q : ↥P, q ∈ acc → liftAgent h q ∈ acc')
    (hCheck : Sat.check M_P H φ ls acc) :
    Sat.check (LiftPreservation.canonicalLift h F M_P)
      (liftPreHistory h H) φ ls acc' := by
  induction ls generalizing acc acc' with
  | nil =>
      simp only [Sat.Sat_check_nil] at hCheck ⊢
      obtain ⟨p, hpAcc, hpSat⟩ := hCheck
      exact ⟨liftAgent h p, hAcc p hpAcc, hWitness p hpSat⟩
  | cons l ls' ih =>
      simp only [Sat.Sat_check_cons] at hCheck ⊢
      simp only [LiftPreservation.canonicalLift_learner]
      intro O' hO'
      have hR := restrict_nonempty_of_coalescent h F l O' hO'
      have hRQ := IsCoalescent.restrict_quorum h l hO' hR
      apply ih (acc ∩ restrictQuorumSet h O') (acc' ∩ O')
      · intro q ⟨hqAcc, hqR⟩
        exact ⟨hAcc q hqAcc, by rwa [mem_restrictQuorumSet] at hqR⟩
      · rw [hLearner] at hCheck; exact hCheck _ hRQ

/-! ### §6c. Check-transfer lemma (anti-lift direction)

For the anti-lift diamond, we specialise the universal over P'-quorums
to lifted P-quorums. Key invariant: every member of `acc'` is
`liftAgent h q` for some `q ∈ acc`. This is established after the first
intersection with a lifted quorum in the outer diamond case. -/

/-- Anti-lift check transfer with the strong "all-members-are-lifted"
invariant. -/
private lemma check_anti_lift_strong
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A) [IsCoalescent F]
    (M_P : Model S ↥P) (hLearner : M_P.learner = F.σ P)
    (H : PreHistory ↥P (Signature.EventType S))
    {φ : Formula S}
    (hWitness : ∀ (p : ↥P),
      (⟪(liftAgent h p, †, liftPreHistory h H)⟫
        ⊨[LiftPreservation.canonicalLift h F M_P] φ) →
      (⟪(p, †, H)⟫ ⊨[M_P] φ))
    (ls : List (Signature.Value S))
    (acc : Set ↥P) (acc' : Set ↥P')
    (hAcc : ∀ q' ∈ acc', ∃ q ∈ acc, liftAgent h q = q')
    (hCheck : Sat.check (LiftPreservation.canonicalLift h F M_P)
      (liftPreHistory h H) φ ls acc') :
    Sat.check M_P H φ ls acc := by
  induction ls generalizing acc acc' with
  | nil =>
      simp only [Sat.Sat_check_nil] at hCheck ⊢
      obtain ⟨p', hp'Acc, hp'Sat⟩ := hCheck
      obtain ⟨p, hpAcc, hpEq⟩ := hAcc p' hp'Acc
      exact ⟨p, hpAcc, hWitness p (hpEq ▸ hp'Sat)⟩
  | cons l ls' ih =>
      simp only [Sat.Sat_check_cons] at hCheck ⊢
      simp only [LiftPreservation.canonicalLift_learner] at hCheck
      rw [hLearner]; intro O hO
      have hO'Q := IsCoalescent.lift_quorum h l hO
      apply ih (acc ∩ O) (acc' ∩ liftQuorumSet h O)
      · intro q' ⟨hq'Acc, hq'Lift⟩
        rw [mem_liftQuorumSet] at hq'Lift
        obtain ⟨q₀, hq₀O, hq₀Eq⟩ := hq'Lift
        obtain ⟨q₁, hq₁Acc, hq₁Eq⟩ := hAcc q' hq'Acc
        have : q₀ = q₁ := liftAgent_injective h (hq₀Eq.trans hq₁Eq.symm)
        exact ⟨q₀, ⟨this ▸ hq₁Acc, hq₀O⟩, hq₀Eq⟩
      · exact hCheck (liftQuorumSet h O) hO'Q

mutual
/-- Liftable formulas are preserved by canonical coalescent lifting.
Point-wise version: if `⟪w⟫ ⊨[M_P] φ` at a world `w` over `↥P`, then
`⟪liftWorld h w⟫ ⊨[canonicalLift h F M_P] φ` at the lifted world over `↥P'`. -/
theorem lift_preserves
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A) [IsCoalescent F]
    (M_P : Model S ↥P) (hLearner : M_P.learner = F.σ P)
    {φ : Formula S} (hlift : LiftableFragment.IsLiftable φ)
    (w : World ↥P (Signature.EventType S))
    (h_sat : ⟪w⟫ ⊨[M_P] φ) :
    ⟪liftWorld h w⟫ ⊨[LiftPreservation.canonicalLift h F M_P] φ := by
  cases hlift with
  | bot => simp [Sat] at h_sat
  | eq v₁ v₂ => simp only [Sat] at h_sat ⊢; exact h_sat
  | event E =>
      rcases w with ⟨p, evt, H⟩
      simp only [Sat, liftWorld_mk, World.place, World.event, World.time,
                 LiftPreservation.canonicalLift_history_val] at *
      exact ⟨h_sat.1, mem_liftPreHistory_of_mem h h_sat.2⟩
  | predicate pred =>
      rcases w with ⟨p, evt, H⟩
      simp only [Sat, liftWorld_mk, World.place, World.time] at *
      rw [LiftPreservation.canonicalLift_predInterp_at_lifted]; exact h_sat
  | seq =>
      rcases w with ⟨p, evt, H⟩
      simp only [Sat, liftWorld_mk, World.place, World.time] at *
      exact isSequential_lift h p H h_sat
  | forall_ hbody =>
      simp only [Sat] at h_sat ⊢
      intro v; exact lift_preserves h F M_P hLearner (hbody v) w (h_sat v)
  | past hφ =>
      rcases w with ⟨p, evt, H⟩
      rw [Sat.past] at h_sat ⊢
      obtain ⟨t, htMem, htPlace, htSat⟩ := h_sat
      exact ⟨liftWorld h t, mem_liftPreHistory_of_mem h htMem,
             congrArg (liftAgent h) htPlace,
             lift_preserves h F M_P hLearner hφ t htSat⟩
  | atEnd hφ =>
      rcases w with ⟨p, evt, H⟩
      rw [Sat.atEnd] at h_sat ⊢
      simp only [liftWorld_mk, World.place,
                 LiftPreservation.canonicalLift_history_val] at *
      exact lift_preserves h F M_P hLearner hφ (p, †, M_P.history.val) h_sat
  | imp hφ hψ =>
      simp only [Sat] at h_sat ⊢; intro h_ante
      exact lift_preserves h F M_P hLearner hψ w
        (h_sat (anti_lift_preserves h F M_P hLearner hφ w h_ante))
  | diamondEmpty hφ =>
      simp only [Sat.Sat_diamond_nil] at h_sat ⊢
      simp only [liftWorld_mk, World.time] at *
      obtain ⟨q, hq⟩ := h_sat
      exact ⟨liftAgent h q,
             lift_preserves h F M_P hLearner hφ (q, †, w.time) hq⟩
  | diamondSeq ls =>
      rcases w with ⟨p, evt, H⟩
      have h1 : Sat.check M_P H (Formula.seq : Formula S) ls Set.univ := by
        simp [Sat] at h_sat; exact h_sat
      have h2 := check_lift_of_witness_lift h F M_P hLearner H
        (fun q (hq : Sat M_P q † H Formula.seq) =>
          show Sat _ (liftAgent h q) † (liftPreHistory h H) Formula.seq from
          (Sat.seq (LiftPreservation.canonicalLift h F M_P)
            (liftAgent h q, †, liftPreHistory h H)).mpr
            (isSequential_lift h q H ((Sat.seq M_P (q, †, H)).mp hq)))
        ls Set.univ Set.univ (fun _ _ => Set.mem_univ _) h1
      simp [Sat]; exact h2
  | diamondNotPastEvent ls E =>
      rcases w with ⟨p, evt, H⟩
      have h1 : Sat.check M_P H
          (Formula.imp (Formula.past (Formula.event E)) Formula.bot) ls Set.univ := by
        simp [Sat] at h_sat; exact h_sat
      have h2 := check_lift_of_witness_lift h F M_P hLearner H
        (fun q hq => by
          -- Transfer ¬past(event E): unfold imp then past then event
          simp only [Sat] at hq ⊢  -- unfold imp to → and past to ∃ and event to ∧
          intro ⟨t, htMem, htPlace, htEvt, htHist⟩
          simp only [World.time, World.place,
                     LiftPreservation.canonicalLift_history_val] at htMem htPlace htHist ⊢
          apply hq
          rw [mem_liftPreHistory_iff] at htMem
          obtain ⟨s, hsMem, hsEq⟩ := htMem
          subst hsEq
          refine ⟨s, hsMem, liftAgent_injective h htPlace, htEvt, ?_⟩
          -- htHist mentions (liftWorld h s).1 etc. — normalize to liftWorld form
          rw [show ((liftWorld h s).1, MaybeEvent.some ⟨E.sym, E.args⟩, (liftWorld h s).2.2)
                = liftWorld h (s.1, MaybeEvent.some ⟨E.sym, E.args⟩, s.2.2) from by
                  simp [liftWorld]] at htHist
          rw [mem_liftPreHistory_iff] at htHist
          obtain ⟨u, huMem, huEq⟩ := htHist
          exact liftWorld_injective h huEq ▸ huMem)
        ls Set.univ Set.univ (fun _ _ => Set.mem_univ _) h1
      simp [Sat]; exact h2

/-- Anti-liftable formulas are preserved by the reverse direction:
if `⟪liftWorld h w⟫ ⊨[canonicalLift h F M_P] φ` then `⟪w⟫ ⊨[M_P] φ`. -/
theorem anti_lift_preserves
    {P P' : Set A} (h : P ⊆ P') [Nonempty ↥P] [Nonempty ↥P']
    (F : LearnerFamily (Signature.Value S) A) [IsCoalescent F]
    (M_P : Model S ↥P) (hLearner : M_P.learner = F.σ P)
    {φ : Formula S} (hanti : LiftableFragment.IsAntiLiftable φ)
    (w : World ↥P (Signature.EventType S))
    (h_sat : ⟪liftWorld h w⟫ ⊨[LiftPreservation.canonicalLift h F M_P] φ) :
    ⟪w⟫ ⊨[M_P] φ := by
  cases hanti with
  | bot => simp [Sat] at h_sat
  | eq v₁ v₂ => simp only [Sat] at h_sat ⊢; exact h_sat
  | event E =>
      rcases w with ⟨p, evt, H⟩
      simp only [Sat, liftWorld_mk, World.place, World.event, World.time,
                 LiftPreservation.canonicalLift_history_val] at *
      obtain ⟨hevt, hmem⟩ := h_sat
      refine ⟨hevt, ?_⟩
      rw [mem_liftPreHistory_iff] at hmem
      obtain ⟨t, htMem, htEq⟩ := hmem
      have : liftWorld h t =
          liftWorld h (p, MaybeEvent.some ⟨E.sym, E.args⟩, H) := by
        simpa [liftWorld_mk] using htEq
      exact liftWorld_injective h this ▸ htMem
  | predicate pred =>
      rcases w with ⟨p, evt, H⟩
      simp only [Sat, liftWorld_mk, World.place, World.time] at *
      rw [LiftPreservation.canonicalLift_predInterp_at_lifted] at h_sat
      exact h_sat
  | seq =>
      rcases w with ⟨p, evt, H⟩
      have h1 : isSequential (Event := S.EventType) (liftAgent h p)
          (liftPreHistory h H) :=
        (Sat.seq (LiftPreservation.canonicalLift h F M_P)
           (liftWorld h (p, evt, H))).mp h_sat
      have h2 : isSequential (Event := S.EventType) p
          (projectPreHistory h (liftPreHistory h H)) :=
        isSequential_projection h p (liftPreHistory h H) h1
      rw [LiftPreservation.projectPreHistory_liftPreHistory] at h2
      exact (Sat.seq M_P (p, evt, H)).mpr h2
  | forall_ hbody =>
      simp only [Sat] at h_sat ⊢
      intro v; exact anti_lift_preserves h F M_P hLearner (hbody v) w (h_sat v)
  | past hφ =>
      rcases w with ⟨p, evt, H⟩
      rw [Sat.past] at h_sat ⊢
      simp only [liftWorld_mk, World.place, World.time] at *
      obtain ⟨t', ht'Mem, ht'Place, ht'Sat⟩ := h_sat
      rw [mem_liftPreHistory_iff] at ht'Mem
      obtain ⟨t, htMem, htEq⟩ := ht'Mem
      subst htEq
      exact ⟨t, htMem, liftAgent_injective h ht'Place,
             anti_lift_preserves h F M_P hLearner hφ t ht'Sat⟩
  | atEnd hφ =>
      rcases w with ⟨p, evt, H⟩
      rw [Sat.atEnd] at h_sat ⊢
      simp only [liftWorld_mk, World.place,
                 LiftPreservation.canonicalLift_history_val] at *
      exact anti_lift_preserves h F M_P hLearner hφ (p, †, M_P.history.val) h_sat
  | imp hφ hψ =>
      simp only [Sat] at h_sat ⊢; intro h_ante
      exact anti_lift_preserves h F M_P hLearner hψ w
        (h_sat (lift_preserves h F M_P hLearner hφ w h_ante))
  | diamond l ls' hφ =>
      -- ♢[l :: ls'] anti-lift: first step establishes lifted invariant
      rcases w with ⟨p, evt, H⟩
      simp only [Sat, liftWorld_mk, World.place, World.event, World.time] at *
      simp only [Sat.Sat_check_cons] at h_sat ⊢
      simp only [LiftPreservation.canonicalLift_learner] at h_sat
      rw [hLearner]; intro O hO
      have hCheckO' := h_sat (liftQuorumSet h O) (IsCoalescent.lift_quorum h l hO)
      apply check_anti_lift_strong h F M_P hLearner H
        (fun q hq => anti_lift_preserves h F M_P hLearner hφ (q, †, H) hq)
        ls' (Set.univ ∩ O) (Set.univ ∩ liftQuorumSet h O)
      · intro q' ⟨_, hq'L⟩
        rw [mem_liftQuorumSet] at hq'L
        obtain ⟨q, hqO, hqEq⟩ := hq'L
        exact ⟨q, ⟨Set.mem_univ _, hqO⟩, hqEq⟩
      · exact hCheckO'
  | diamondEmptyPast hφ =>
      -- ♢[] (past φ) anti-lift: the past modality grounds witnesses to the
      -- history. Every member of liftPreHistory h H is liftWorld h s for some
      -- s ∈ H, so the existential witness projects back.
      rcases w with ⟨p, evt, H⟩
      simp only [Sat.Sat_diamond_nil] at h_sat ⊢
      obtain ⟨p', hp'⟩ := h_sat
      rw [Sat.past] at hp'
      simp only [liftWorld_mk, World.place, World.time] at hp'
      obtain ⟨t, htMem, htPlace, htSat⟩ := hp'
      rw [mem_liftPreHistory_iff] at htMem
      obtain ⟨s, hsMem, hsEq⟩ := htMem; subst hsEq
      refine ⟨s.1, ?_⟩
      rw [Sat.past]; simp only [World.place, World.time]
      exact ⟨s, hsMem, rfl,
             anti_lift_preserves h F M_P hLearner hφ s htSat⟩
end

end PreservationType0

end Grassroots
end ModalDistribution
