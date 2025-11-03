import Mathlib.Data.Set.Lattice
import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.History
import ModalDistribution.Core.Model
import ModalDistribution.Logic.Syntax

/-!
# Modal logic semantics

We formalise the satisfaction relation from
the validity figure.  Satisfaction is defined for a model, a
participant, a local history, and a variable assignment.  We also introduce
end-of-time validity, event-driven validity, and the notion of active
participants .
-/

namespace ModalDistribution
namespace Logic

open Set
open ModalDistribution
open History
open PreHistory
open World
open scoped PreHistory Formula

set_option autoImplicit false

-- Fix at Type 0 to match Syntax.lean
variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

/-- Depth measure for formulas. Needed for termination of Sat. -/
@[simp] private noncomputable def depth : Formula S → ℕ
  | .bot => 0
  | .imp φ ψ => 1 + max (depth φ) (depth ψ)
  | .eq _ _ => 0
  | .forall body =>
      open Classical in
      if h : Nonempty S.Value then
        1 + depth (body (choice h))
      else
        0
  | .event _ => 0
  | .predicate _ => 0
  | .past φ => 1 + depth φ
  | .atEnd φ => 1 + depth φ
  | .diamond _ φ => 1 + depth φ
  | .seq => 0

/-- Axiom: depth is uniform across body applications (parametricity).
    Note: This is only true so long as body is parametrically polymorphic in v;
          which it is for all reasonable formulas. We can get rid of this axiom by,
          for example, using de Bruijin indices, but we have to make some compromise
          like this for the convenience of HOAS. -/
private axiom depth_uniform [Nonempty S.Value] (body : S.Value → Formula S) (v₁ v₂ : S.Value) :
  depth (body v₁) = depth (body v₂)

/-- Depth of forall body is bounded (follows from depth_uniform). -/
private lemma depth_forall_body (body : S.Value → Formula S) (v : S.Value) :
  depth (body v) < depth (.forall body) := by
  open Classical in
  simp only [depth]
  by_cases h : Nonempty S.Value
  · simp only [h, ↓reduceDIte]
    rw [depth_uniform body v (choice h)]
    omega
  · -- If S.Value is empty, there's no v to consider, contradiction
    exact absurd ⟨v⟩ h

/-- Satisfaction relation `p \dx H ⊨[M]φ`. -/
def Sat (M : Model S P)
    (p : P)
    (evt : MaybeEvent S.EventType)
    (H : PreHistory P (S.EventType)) : Formula S → Prop
  | .bot => False
  | .imp φ ψ => Sat M p evt H φ → Sat M p evt H ψ
  | .eq v₁ v₂ => v₁ = v₂
  | .forall body => ∀ v : Signature.Value S, Sat M p evt H (body v)
  | .event atom =>
      evt = MaybeEvent.some ⟨atom.sym, atom.args⟩ ∧
        (p, MaybeEvent.some ⟨atom.sym, atom.args⟩, H) ∈ M.history.val
  | .predicate pred =>
      ⟨pred.sym, pred.args⟩ ∈ M.predInterp p H
  | .past φ =>
      ∃ t ∈ H,
        t.place = p ∧
          Sat M (t.place) (World.event t) (World.time t) φ
  | .atEnd φ => Sat M p † M.history.val φ
  | .diamond learners φ =>
      let rec check : List S.Value → Set P → Prop
        | [], acc => ∃ p' ∈ acc, Sat M p' † H φ
        | ℓ :: ls, acc =>
            ∀ O ∈ (M.learner ℓ).quorums,
              check ls (acc ∩ O)
      termination_by learners _ => (depth φ, 1, learners.length)
      check learners Set.univ
  | .seq =>
      isSequential (Event := S.EventType) p H
termination_by φ => (depth φ, 0, 0)
decreasing_by
  all_goals simp_wf
  all_goals (try decreasing_trivial)
  have := depth_forall_body body v
  apply Prod.Lex.left
  exact this

notation:65 "⟪" w "⟫" " ⊨[" M "]" φ =>
  Sat M (place w) (event w) (time w) φ

namespace Sat

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {w : World P S.EventType}
variable {p : P} {evt : MaybeEvent S.EventType}
variable {H : PreHistory P (S.EventType)}

open Set

/-- Satisfaction of `⊥` is never witnessed. -/
@[simp] lemma bot (M : Model S P) (w : World P S.EventType) :
    (⟪w⟫ ⊨[M]⊥ᶠ) ↔ False := by
  simp [Sat]

/-- Satisfaction of a negated formula coincides with refuting any witness of the body. -/
@[simp] lemma not (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]¬ᶠ φ) ↔ ¬(⟪w⟫ ⊨[M]φ) := by
  simp [Formula.not, Sat]

/-- Satisfaction of `¬φ` witnesses the failure of `φ`. -/
lemma not_elim (M : Model S P) {w : World P S.EventType} {φ : Formula S} :
    (⟪w⟫ ⊨[M]¬ᶠ φ) → (⟪w⟫ ⊨[M]φ) → False := by
  classical
  intro hnot hφ
  exact ((not (M := M) (w := w) (φ := φ)).1 hnot) hφ

/-- To establish `¬φ`, it suffices to refute any hypothetical proof of `φ`. -/
lemma not_intro (M : Model S P) {w : World P S.EventType} {φ : Formula S}
    (h : (⟪w⟫ ⊨[M]φ) → False) :
    ⟪w⟫ ⊨[M]¬ᶠ φ := by
  classical
  exact (not (M := M) (w := w) (φ := φ)).2 h

/-- The negation of truth is never satisfiable. -/
lemma not_top (M : Model S P) (w : World P S.EventType) :
    (⟪w⟫ ⊨[M]¬ᶠ ⊤ᶠ) ↔ False := by
  simp [Formula.not, Formula.top, Sat]

/-- The negation of `⊥` always holds. -/
lemma not_bot (M : Model S P) (w : World P S.EventType) :
    ⟪w⟫ ⊨[M]¬ᶠ ⊥ᶠ := by
  simp [Formula.not, Sat]

/-- A universally quantified formula can be specialised to any value (HOAS version). -/
lemma forall_elim
    (M : Model S P) (w : World P S.EventType)
    (body : S.Value → Formula S)
    (v : Signature.Value S)
    (h : ⟪w⟫ ⊨[M].forall body) :
    ⟪w⟫ ⊨[M]body v := by
  simp [Sat] at h
  exact h v

/--
Version of `Sat.forall_elim` with implicit parameters, useful for chaining.
-/
lemma forall_elim'
    {M : Model S P} {w : World P S.EventType}
    {body : S.Value → Formula S}
    (v : Signature.Value S)
    (h : ⟪w⟫ ⊨[M].forall body) :
    ⟪w⟫ ⊨[M] (body v) :=
  forall_elim (M := M) (w := w) (body := body) (v := v) h

/-- To show a universal formula holds, show the body holds for every value (HOAS version). -/
lemma forall_intro
    (M : Model S P) (w : World P S.EventType)
    (body : S.Value → Formula S)
    (h : ∀ v : Signature.Value S, ⟪w⟫ ⊨[M]body v) :
    ⟪w⟫ ⊨[M].forall body := by
  simp [Sat]
  exact h

/-- Existentials are satisfied as soon as a witness value realises the body (HOAS version). -/
lemma exists_intro
    (M : Model S P) (w : World P S.EventType)
    (body : S.Value → Formula S)
    (h : ∃ v : Signature.Value S, ⟪w⟫ ⊨[M]body v) :
    ⟪w⟫ ⊨[M].exists_ body := by
  classical
  rcases w with w
  rcases h with ⟨v, hv⟩
  refine not_intro (M := M) (w := w)
    (φ := .forall fun x => ¬ᶠ (body x)) ?_
  intro hforall
  have hnot :=
    forall_elim (M := M) (w := w)
      (body := fun x => ¬ᶠ (body x)) (v := v) hforall
  have hneg :=
    (not (M := M) (w := w) (φ := body v)).1 hnot hv
  exact hneg

/-- Simp lemma: Sat.check for empty list. -/
@[simp] theorem Sat_check_nil (M : Model S P)
    (H : PreHistory P (S.EventType)) (φ : Formula S) (acc : Set P) :
    Sat.check M H φ [] acc ↔ ∃ p' ∈ acc, ⟪⟨p', †, H⟩⟫ ⊨[M]φ := by
  simp [Sat.check]

/-- Simp lemma: `Sat.check` for the inductive step. -/
@[simp] theorem Sat_check_cons (M : Model S P)
    (H : PreHistory P (S.EventType)) (φ : Formula S)
    (v : S.Value) (vs : List S.Value) (acc : Set P) :
    Sat.check M H φ (v :: vs) acc ↔
      ∀ O ∈ (M.learner v).quorums, Sat.check M H φ vs (acc ∩ O) := by
  simp [Sat.check]

/-- Diamonds over the empty learner list are witnessed by some participant.
    This is the unfolded base case of the quorum recursion. -/
@[simp] theorem Sat_diamond_nil
    (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]♢ᶠ[[]] φ) ↔
      ∃ p' : P, ⟪⟨p', †, w.time⟩⟫ ⊨[M]φ := by
  rcases w with w
  simp [Sat]

/-- Diamonds over empty quorum lists are characterised by any participant
carrying the witness. -/
lemma diamond_nil
    (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]♢ᶠ[[]] φ) ↔
      ∃ p' : P, ⟪⟨p', †, w.time⟩⟫ ⊨[M]φ :=
  Sat_diamond_nil (M := M) (w := w) (φ := φ)

/-- The derived `♢ᶠ[]` notation shares the same semantics. -/
lemma diamondEmpty
    (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]♢ᶠ[] φ) ↔
      ∃ p' : P, ⟪⟨p', †, w.time⟩⟫ ⊨[M]φ := by
  classical
  simp [Sat]

/-- Satisfaction of an empty box coincides with the guard holding for every
participant at the same time slice. -/
lemma boxEmpty
    (M : Model S P)
    (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]□ᶠ[] φ) ↔ ∀ q : P, ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ := by
  classical
  rcases w with ⟨p, evt, H⟩
  constructor
  · intro hBox q
    have hNotDiamond : ¬ (⟪⟨p, evt, H⟩⟫ ⊨[M]♢ᶠ[] (¬ᶠ φ)) := by
      have hNeg : ⟪⟨p, evt, H⟩⟫ ⊨[M]¬ᶠ (♢ᶠ[] (¬ᶠ φ)) :=
        by simpa [Formula.boxEmpty, Formula.box] using hBox
      exact (Sat.not (M := M) (w := ⟨p, evt, H⟩)
        (φ := ♢ᶠ[] (¬ᶠ φ))).1 hNeg
    by_contra hContra
    have hNot : ⟪⟨q, †, H⟩⟫ ⊨[M]¬ᶠ φ :=
      (Sat.not (M := M) (w := ⟨q, †, H⟩) (φ := φ)).2 hContra
    have hDiamond : ⟪⟨p, evt, H⟩⟫ ⊨[M]♢ᶠ[] (¬ᶠ φ) :=
      (diamondEmpty (M := M) (w := ⟨p, evt, H⟩)
        (φ := ¬ᶠ φ)).2 ⟨q, hNot⟩
    exact hNotDiamond hDiamond
  · intro hAll
    have hImp : (⟪⟨p, evt, H⟩⟫ ⊨[M]♢ᶠ[] (¬ᶠ φ)) → False := by
      intro hDiamond
      obtain ⟨q, hNot⟩ :=
        (diamondEmpty (M := M) (w := ⟨p, evt, H⟩)
          (φ := ¬ᶠ φ)).1 hDiamond
      have hφ : ⟪⟨q, †, H⟩⟫ ⊨[M]φ := hAll q
      exact (Sat.not_elim (M := M) (w := ⟨q, †, H⟩)
        (φ := φ) hNot hφ)
    have hNotDiamond : ⟪⟨p, evt, H⟩⟫ ⊨[M]¬ᶠ (♢ᶠ[] (¬ᶠ φ)) :=
      (Sat.not (M := M) (w := ⟨p, evt, H⟩)
        (φ := ♢ᶠ[] (¬ᶠ φ))).2 hImp
    simpa [Formula.boxEmpty, Formula.box] using hNotDiamond

/-- Events witnessed at a history automatically satisfy sometime. -/
lemma event_sometime
    (M : Model S P)
    (p : P)
    (H : PreHistory P (S.EventType))
    (E : S.EventType)
    (hEvent : ⟪⟨p, MaybeEvent.some E, H⟩⟫ ⊨[M]Formula.ofEvent E) :
    ⟪⟨p, MaybeEvent.some E, H⟩⟫ ⊨[M]↕ᶠ (Formula.ofEvent E) := by
  classical
  have hMem : (p, MaybeEvent.some E, H) ∈ M.history.val := by
    simpa [Formula.ofEvent, Sat] using hEvent
  have hPast :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]↓ᶠ (Formula.ofEvent E) := by
    have :
        (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]↓ᶠ (Formula.ofEvent E)) ↔
          ∃ t ∈ M.history.val, t.place = p ∧
            Sat M (t.place) (World.event t) (World.time t)
              (Formula.ofEvent E) := by
      simp [Sat]
    refine this.mpr ?_
    refine ⟨⟨p, MaybeEvent.some E, H⟩, hMem, rfl, ?_⟩
    simpa [Formula.ofEvent, Sat] using hEvent
  simpa [Formula.sometime, Sat] using hPast

/-- The truth constant is satisfied if and only if `True`. -/
@[simp] lemma top_iff (M : Model S P) (w : World P S.EventType) :
    (⟪w⟫ ⊨[M]⊤ᶠ) ↔ True := by
  classical
  simp [Formula.top, Sat]

/-- Satisfaction of implication agrees with pointwise entailment. -/
@[simp] lemma imp
    (M : Model S P) (w : World P S.EventType)
    (φ ψ : Formula S) :
    (⟪w⟫ ⊨[M]φ ⇒ᶠ ψ) ↔
      ((⟪w⟫ ⊨[M]φ) → (⟪w⟫ ⊨[M]ψ)) := by
  simp [Sat]

/-- Conjoin two satisfiable formulas at the same point. -/
lemma and_intro
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S}
    (hφ : ⟪w⟫ ⊨[M]φ)
    (hψ : ⟪w⟫ ⊨[M]ψ) :
    ⟪w⟫ ⊨[M]φ ∧ᶠ ψ := by
  classical
  refine Sat.not_intro (M := M) (w := w)
      (φ := φ ⇒ᶠ ¬ᶠ ψ) ?_
  intro hImp
  have hImpFn :=
    (Sat.imp (M := M) (w := w)
      (φ := φ) (ψ := ¬ᶠ ψ)).1 hImp
  have hNotψ := hImpFn hφ
  exact
    (Sat.not_elim (M := M) (w := w)
      (φ := ψ)) hNotψ hψ

/-- Satisfaction of `⤒ φ` coincides with evaluating `φ` at the full history. -/
@[simp] lemma atEnd
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]⤒ᶠ φ) ↔
      ⟪⟨World.place w, †, M.history.val⟩⟫ ⊨[M]φ := by
  simp [Sat]

/-- Satisfaction of `seq` is equivalent to sequentiality at the given history. -/
@[simp] lemma seq
    (M : Model S P) (w : World P S.EventType) :
    (⟪w⟫ ⊨[M]Formula.seq (S := S)) ↔
      isSequential (Event := S.EventType) (World.place w) (World.time w) := by
  simp [Sat]

/-- Satisfaction of the truth constant holds unconditionally. -/
lemma top
    (M : Model S P)
    (w : World P S.EventType) :
    ⟪w⟫ ⊨[M]⊤ᶠ := by
  simp [Formula.top, Sat]

/-- Satisfaction is monotone with respect to implication hypotheses. -/
lemma imp_elim
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S} :
    (⟪w⟫ ⊨[M]φ ⇒ᶠ ψ) →
      (⟪w⟫ ⊨[M]φ) → ⟪w⟫ ⊨[M]ψ := by
  intro himp hφ
  have h := (imp (M := M) (w := w)
      (φ := φ) (ψ := ψ)).1 himp
  exact h hφ

/-- Introduction form of implication in the satisfaction relation. -/
lemma imp_intro
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S}
    (h : (⟪w⟫ ⊨[M]φ) → ⟪w⟫ ⊨[M]ψ) :
    ⟪w⟫ ⊨[M]φ ⇒ᶠ ψ := by
  exact (imp (M := M) (w := w)
    (φ := φ) (ψ := ψ)).2 h

/-- Eliminate the left conjunct from `φ ∧ ψ`. -/
lemma and_left
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S} :
    (⟪w⟫ ⊨[M]φ ∧ᶠ ψ) →
      (⟪w⟫ ⊨[M]φ) := by
  classical
  intro hAnd
  have hNotImp : ⟪w⟫ ⊨[M]¬ᶠ (φ ⇒ᶠ ¬ᶠ ψ) := by
    simpa [Formula.and] using hAnd
  by_contra hNotφ
  have hImp : ⟪w⟫ ⊨[M]φ ⇒ᶠ ¬ᶠ ψ :=
    imp_intro (M := M) (w := w)
      (φ := φ) (ψ := ¬ᶠ ψ)
      (fun hφ => False.elim (hNotφ hφ))
  have hFalse : False :=
    not_elim (M := M) (w := w)
      (φ := φ ⇒ᶠ ¬ᶠ ψ) hNotImp hImp
  exact hFalse

/-- Eliminate the right conjunct from `φ ∧ ψ`. -/
lemma and_right
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S} :
    (⟪w⟫ ⊨[M]φ ∧ᶠ ψ) →
      (⟪w⟫ ⊨[M]ψ) := by
  classical
  intro hAnd
  have hNotImp : ⟪w⟫ ⊨[M]¬ᶠ (φ ⇒ᶠ ¬ᶠ ψ) := by
    simpa [Formula.and] using hAnd
  by_contra hNotψ
  have hNotψSat : ⟪w⟫ ⊨[M]¬ᶠ ψ :=
    not_intro (M := M) (w := w)
      (φ := ψ) (fun hψ => hNotψ hψ)
  have hImp : ⟪w⟫ ⊨[M]φ ⇒ᶠ ¬ᶠ ψ :=
    imp_intro (M := M) (w := w)
      (φ := φ) (ψ := ¬ᶠ ψ) (fun _ => hNotψSat)
  have hFalse : False :=
    not_elim (M := M) (w := w)
      (φ := φ ⇒ᶠ ¬ᶠ ψ) hNotImp hImp
  exact hFalse

/-- Eliminate the forward implication from an `iff`. -/
lemma iff_mp
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S}
    (hIff : ⟪w⟫ ⊨[M]φ ⇔ᶠ ψ) :
    (⟪w⟫ ⊨[M]φ) → (⟪w⟫ ⊨[M]ψ) := by
  classical
  have hAnd :
      ⟪w⟫ ⊨[M]
        ((φ ⇒ᶠ ψ) ∧ᶠ (ψ ⇒ᶠ φ)) := by
    simpa [Formula.iff] using hIff
  have hImp : ⟪w⟫ ⊨[M]φ ⇒ᶠ ψ :=
    and_left (M := M) (w := w) hAnd
  intro hφ
  exact
    imp_elim (M := M) (w := w)
      (φ := φ) (ψ := ψ) hImp hφ

/-- Eliminate the backward implication from an `iff`. -/
lemma iff_mpr
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S}
    (hIff : ⟪w⟫ ⊨[M]φ ⇔ᶠ ψ) :
    (⟪w⟫ ⊨[M]ψ) → (⟪w⟫ ⊨[M]φ) := by
  classical
  have hAnd :
      ⟪w⟫ ⊨[M]
        ((φ ⇒ᶠ ψ) ∧ᶠ (ψ ⇒ᶠ φ)) := by
    simpa [Formula.iff] using hIff
  have hImp : ⟪w⟫ ⊨[M]ψ ⇒ᶠ φ :=
    and_right (M := M) (w := w) hAnd
  intro hψ
  exact
    imp_elim (M := M) (w := w)
      (φ := ψ) (ψ := φ) hImp hψ

/-- Equality atoms are satisfied when the underlying values coincide. -/
@[simp] lemma eq (M : Model S P) (w : World P S.EventType)
    (v₁ v₂ : S.Value) :
    (⟪w⟫ ⊨[M]v₁ ≃ᶠ v₂) ↔ v₁ = v₂ := by
  simp [Sat]

/-- Equality atoms witness reflexivity. -/
lemma eq_refl (M : Model S P) (w : World P S.EventType) (v : S.Value) :
    ⟪w⟫ ⊨[M](v ≃ᶠ v) := by
  simp [Sat]

/-- Event clauses are witnessed by membership in the ambient history. -/
lemma event_of_mem
    (M : Model S P)
    (w : World P S.EventType)
    (evt : EventAtom S)
    (hmem : (place w, MaybeEvent.some ⟨evt.sym, evt.args⟩, time w) ∈ M.history.val) :
    ⟪⟨place w, MaybeEvent.some ⟨evt.sym, evt.args⟩, time w⟩⟫ ⊨[M]Formula.event evt := by
  simpa [Sat]

/-- Event atoms reduce to membership in the enclosing history. -/
@[simp] lemma event
    (M : Model S P)
    (w : World P S.EventType)
    (evt : EventAtom S) :
    (⟪⟨place w, MaybeEvent.some ⟨evt.sym, evt.args⟩, time w⟩⟫ ⊨[M]Formula.event evt) ↔
      (place w, MaybeEvent.some ⟨evt.sym, evt.args⟩, time w) ∈ M.history.val := by
  simp [Sat]

/-! ### Simp lemmas for derived connectives -/

/-- ofEvent satisfaction unfolds to event membership. -/
@[simp] lemma ofEvent
    (M : Model S P)
    (w : World P S.EventType)
    (E : S.EventType) :
    (⟪w⟫ ⊨[M]Formula.ofEvent E) ↔
      (World.event w = MaybeEvent.some E ∧
        (World.place w, MaybeEvent.some E, World.time w) ∈ M.history.val) := by
  classical
  rcases w with ⟨p, evt, H⟩
  constructor
  · intro h
    simpa [Formula.ofEvent, Sat]
      using h
  · intro h
    simpa [Formula.ofEvent, Sat]
      using h

/-- Past modality satisfaction. -/
lemma past
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]↓ᶠ φ) ↔
      ∃ t ∈ w.time, t.place = w.place ∧ ⟪t⟫ ⊨[M]φ := by
  classical
  rcases w with ⟨p, evt, H⟩
  simp [Sat]

/-- Sometime (eventually in the future at end of time) unfolds. -/
lemma sometime
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]Formula.sometime φ) ↔
      ∃ t ∈ M.history.val, t.place = w.place ∧ ⟪t⟫ ⊨[M]φ := by
  classical
  rcases w with ⟨p, evt, H⟩
  simp [Formula.sometime, Sat]

/-- Box with past guard unfolds. -/
lemma boxPast
    (M : Model S P)
    (w : World P S.EventType)
    (ls : List S.Value)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]Formula.boxPast ls φ) ↔
      (⟪w⟫ ⊨[M]Formula.box ls (↓ᶠ φ)) := by
  simp [Formula.boxPast]

/-- Diamond with past guard unfolds. -/
lemma diamondPast
    (M : Model S P)
    (w : World P S.EventType)
    (ls : List S.Value)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]Formula.diamondPast ls φ) ↔
      (⟪w⟫ ⊨[M]♢ᶠ[ls] (↓ᶠ φ)) := by
  simp [Formula.diamondPast]

/-- Conjunction satisfaction unfolds to both conjuncts. -/
@[simp] lemma and
    (M : Model S P)
    (w : World P S.EventType)
    (φ ψ : Formula S) :
    (⟪w⟫ ⊨[M]φ ∧ᶠ ψ) ↔
      (⟪w⟫ ⊨[M]φ) ∧ (⟪w⟫ ⊨[M]ψ) := by
  constructor
  · intro h
    exact ⟨and_left (M := M) (w := w) h,
           and_right (M := M) (w := w) h⟩
  · intro hφψ
    exact and_intro (M := M) (w := w) hφψ.1 hφψ.2

/-- Disjunction satisfaction unfolds to either disjunct. -/
@[simp] lemma or
    (M : Model S P)
    (w : World P S.EventType)
    (φ ψ : Formula S) :
    (⟪w⟫ ⊨[M]φ ∨ᶠ ψ) ↔
      (⟪w⟫ ⊨[M]φ) ∨ (⟪w⟫ ⊨[M]ψ) := by
  classical
  simp [Formula.or, Formula.not, Sat]
  tauto

/-- Universal quantification unfolds to satisfaction for all values. -/
@[simp] lemma forall_sat
    (M : Model S P)
    (w : World P S.EventType)
    (body : S.Value → Formula S) :
    (⟪w⟫ ⊨[M].forall body) ↔
      (∀ v, ⟪w⟫ ⊨[M]body v) := by
  simp [Sat]

/-- Existential quantification satisfaction unfolds to witness existence. -/
@[simp] lemma exists_sat
    (M : Model S P)
    (w : World P S.EventType)
    (body : S.Value → Formula S) :
    (⟪w⟫ ⊨[M].exists_ body) ↔
      (∃ v, ⟪w⟫ ⊨[M]body v) := by
  simp only [Formula.exists_, not, forall_sat]
  push_neg
  rfl

lemma check_of_imp {ts : List S.Value} {acc : Set P} {φ ψ : Formula S}
    (h : ∀ q, (⟪⟨q, †, H⟩⟫ ⊨[M]φ) → (⟪⟨q, †, H⟩⟫ ⊨[M]ψ)) :
    Sat.check M H φ ts acc → Sat.check M H ψ ts acc := by
  classical
  induction ts generalizing acc with
  | nil =>
      intro hCheck
      simp only [Sat.check] at hCheck ⊢
      rcases hCheck with ⟨q, hacc, hSat⟩
      exact ⟨q, hacc, h q hSat⟩
  | cons v vs ih =>
      intro hCheck
      simp only [Sat.check] at hCheck ⊢
      intro O hO
      exact ih (hCheck O hO)

lemma diamond_of_imp
    (ts : List S.Value) {φ ψ : Formula S}
    (h : ∀ q, (⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) → (⟪⟨q, †, w.time⟩⟫ ⊨[M]ψ)) :
    (⟪w⟫ ⊨[M]♢ᶠ[ts] φ) → (⟪w⟫ ⊨[M]♢ᶠ[ts] ψ) := by
  classical
  intro hSat
  simp [Sat] at hSat ⊢
  exact check_of_imp (M := M) (H := w.time) (ts := ts) (acc := Set.univ) h hSat

lemma diamond_congr
    (ts : List S.Value) {φ ψ : Formula S}
    (h : ∀ q,
        (⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) ↔ (⟪⟨q, †, w.time⟩⟫ ⊨[M]ψ)) :
    (⟪w⟫ ⊨[M]♢ᶠ[ts] φ) ↔
      (⟪w⟫ ⊨[M]♢ᶠ[ts] ψ) := by
  classical
  constructor
  · intro hSat
    exact diamond_of_imp (M := M) (w := w)
      (ts := ts) (φ := φ) (ψ := ψ)
      (h := fun q => (h q).1) hSat
  · intro hSat
    exact diamond_of_imp (M := M) (w := w)
      (ts := ts) (φ := ψ) (ψ := φ)
      (h := fun q => (h q).2) hSat

lemma not_not_iff
    {φ : Formula S} :
    (⟪w⟫ ⊨[M]¬ᶠ (¬ᶠ φ)) ↔
      (⟪w⟫ ⊨[M]φ) := by
  classical
  constructor
  · intro h
    have : ¬¬ (⟪w⟫ ⊨[M]φ) := by
      simpa [Formula.not, Sat] using h
    exact not_not.mp this
  · intro h
    have : ¬¬ (⟪w⟫ ⊨[M]φ) := not_not.mpr h
    simpa [Formula.not, Sat] using this

lemma not_of_imp
    {φ ψ : Formula S}
    (h : (⟪w⟫ ⊨[M]φ) →
        (⟪w⟫ ⊨[M]ψ)) :
    (⟪w⟫ ⊨[M]¬ᶠ ψ) →
      (⟪w⟫ ⊨[M]¬ᶠ φ) := by
  classical
  intro hNot
  simp only [Formula.not, Sat] at hNot ⊢
  intro hφ
  exact hNot (h hφ)

lemma not_congr
    {φ ψ : Formula S}
    (h : (⟪w⟫ ⊨[M]φ) ↔
           (⟪w⟫ ⊨[M]ψ)) :
    (⟪w⟫ ⊨[M]¬ᶠ φ) ↔
      (⟪w⟫ ⊨[M]¬ᶠ ψ) := by
  classical
  constructor
  · intro hNot
    exact not_of_imp (M := M) (w := w)
      (φ := ψ) (ψ := φ) (h := fun hψ => (h.mpr hψ)) hNot
  · intro hNot
    exact not_of_imp (M := M) (w := w)
      (φ := φ) (ψ := ψ) (h := fun hφ => (h.mp hφ)) hNot

lemma atEnd_of_imp
    {φ ψ : Formula S}
    (h : (⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M]φ) →
        (⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M]ψ)) :
    (⟪w⟫ ⊨[M]⤒ᶠ φ) →
      (⟪w⟫ ⊨[M]⤒ᶠ ψ) := by
  classical
  intro hEnd
  simpa [Formula.atEnd, Sat] using
    h (by simpa [Formula.atEnd, Sat] using hEnd)

lemma atEnd_congr
    {φ ψ : Formula S}
    (h : (⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M]φ) ↔
        (⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M]ψ)) :
    (⟪w⟫ ⊨[M]⤒ᶠ φ) ↔
      (⟪w⟫ ⊨[M]⤒ᶠ ψ) := by
  classical
  constructor
  · intro hEnd
    exact atEnd_of_imp (M := M) (w := w)
      (φ := φ) (ψ := ψ) (h := fun hφ => (h.mp hφ)) hEnd
  · intro hEnd
    exact atEnd_of_imp (M := M) (w := w)
      (φ := ψ) (ψ := φ) (h := fun hψ => (h.mpr hψ)) hEnd

lemma past_of_imp
    {φ ψ : Formula S}
    (h : ∀ (t : World P S.EventType), t ∈ w.time → t.place = w.place →
        (⟪t⟫ ⊨[M]φ) → ⟪t⟫ ⊨[M]ψ) :
    (⟪w⟫ ⊨[M] ↓ᶠ φ) → (⟪w⟫ ⊨[M] ↓ᶠ ψ) := by
  classical
  intro hPast
  rcases (Sat.past (M := M) (w := w) (φ := φ)).1 hPast with ⟨t, ht, hp, hφ⟩
  have hψ := h t (by simpa using ht) (by simpa using hp) hφ
  exact (Sat.past (M := M) (w := w) (φ := ψ)).2 ⟨t, by simpa using ht, by simpa using hp, hψ⟩

/-- A witness in the past establishes the past modality. -/
lemma past_intro_of_prefix
    {t : World P S.EventType}
    {φ : Formula S}
    (ht : t ∈ w.time)
    (hp : t.place = w.place)
    (hφ : ⟪t⟫ ⊨[M]φ) :
    ⟪w⟫ ⊨[M] ↓ᶠ φ := by
  classical
  rcases w with ⟨p, evt, H⟩
  have ht' : t ∈ H := by simpa using ht
  have hp' : t.place = p := by simpa using hp
  refine (Sat.past (M := M) (w := ⟨p, evt, H⟩) (φ := φ)).2 ?_
  exact ⟨t, ht', hp', hφ⟩

lemma past_congr
    {φ ψ : Formula S}
    (h : ∀ ⦃t : World P S.EventType⦄, t ∈ w.time → t.place = w.place →
        ((⟪t⟫ ⊨[M]φ) ↔ (⟪t⟫ ⊨[M]ψ))) :
    (⟪w⟫ ⊨[M] ↓ᶠ φ) ↔ (⟪w⟫ ⊨[M] ↓ᶠ ψ) := by
  classical
  rcases w with ⟨p, evt, H⟩
  constructor
  · intro hPast
    have hImp : ∀ {t : World P S.EventType}, t ∈ H → t.place = p →
        (⟪t⟫ ⊨[M] φ) → ⟪t⟫ ⊨[M] ψ := by
      intro t ht hp hφ
      exact (h (t := t) (by simpa using ht) (by simpa using hp)).1 hφ
    have hPast' : ⟪⟨p, evt, H⟩⟫ ⊨[M] ↓ᶠ φ := by simpa using hPast
    have hRes := past_of_imp (M := M) (w := ⟨p, evt, H⟩)
      (φ := φ) (ψ := ψ)
      (h := fun t ht hp hφ => hImp ht hp hφ) hPast'
    simpa using hRes
  · intro hPast
    have hImp : ∀ {t : World P S.EventType}, t ∈ H → t.place = p →
        (⟪t⟫ ⊨[M] ψ) → ⟪t⟫ ⊨[M] φ := by
      intro t ht hp hψ
      exact (h (t := t) (by simpa using ht) (by simpa using hp)).2 hψ
    have hPast' : ⟪⟨p, evt, H⟩⟫ ⊨[M] ↓ᶠ ψ := by simpa using hPast
    have hRes := past_of_imp (M := M) (w := ⟨p, evt, H⟩)
      (φ := ψ) (ψ := φ)
      (h := fun t ht hp hψ => hImp ht hp hψ) hPast'
    simpa using hRes

lemma sometime_of_imp
    {φ ψ : Formula S}
    (h : ∀ {t : World P S.EventType},
        t ∈ M.history.val → t.place = w.place →
        (⟪t⟫ ⊨[M]φ) → ⟪t⟫ ⊨[M]ψ) :
    (⟪w⟫ ⊨[M]↕ᶠ φ) → (⟪w⟫ ⊨[M]↕ᶠ ψ) := by
  classical
  intro hSome
  have hPast :
      (⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M]↓ᶠ φ) →
      (⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M]↓ᶠ ψ) := by
    intro hPastφ
    have hImp : ∀ (t : World P S.EventType),
        t ∈ M.history.val → t.place = w.place →
        (⟪t⟫ ⊨[M]φ) → ⟪t⟫ ⊨[M]ψ := by
      intro t ht hp hφ
      exact h (t := t) ht hp hφ
    have := past_of_imp (M := M) (w := ⟨w.place, †, M.history.val⟩)
      (φ := φ) (ψ := ψ)
      (h := fun t ht hp hφ => hImp t ht hp hφ) hPastφ
    simpa using this
  have hAtEnd :=
    atEnd_of_imp (M := M) (w := w)
      (φ := Formula.past φ) (ψ := Formula.past ψ)
      (h := fun hPastφ =>
        hPast (by simpa [Formula.past, Sat] using hPastφ))
      (by simpa [Formula.sometime] using hSome)
  simpa [Formula.sometime] using hAtEnd

lemma sometime_congr
    {φ ψ : Formula S}
    (h : ∀ {t : World P S.EventType},
        t ∈ M.history.val → t.place = w.place →
        ((⟪t⟫ ⊨[M]φ) ↔ (⟪t⟫ ⊨[M]ψ))) :
    (⟪w⟫ ⊨[M]↕ᶠ φ) ↔ (⟪w⟫ ⊨[M]↕ᶠ ψ) := by
  classical
  constructor
  · intro hSome
    exact sometime_of_imp (M := M) (w := w)
      (φ := φ) (ψ := ψ)
      (h := fun {t} ht hp => (h ht hp).1) hSome
  · intro hSome
    exact sometime_of_imp (M := M) (w := w)
      (φ := ψ) (ψ := φ)
      (h := fun {t} ht hp => (h ht hp).2) hSome

lemma eventuallyPast_of_imp
    {φ ψ : Formula S}
    (h : ∀ {t : World P S.EventType},
        t ∈ w.time → t.place = w.place →
        (⟪t⟫ ⊨[M]φ) → ⟪t⟫ ⊨[M]ψ) :
    (⟪w⟫ ⊨[M]⇓ᶠ φ) → (⟪w⟫ ⊨[M]⇓ᶠ ψ) := by
  classical
  have hNot : ∀ {t : World P S.EventType},
      t ∈ w.time → t.place = w.place →
      (⟪t⟫ ⊨[M]¬ᶠ ψ) →
        ⟪t⟫ ⊨[M]¬ᶠ φ := by
    intro t ht hp hψ
    exact not_of_imp (M := M) (w := t)
      (φ := φ) (ψ := ψ) (h := h ht hp) hψ
  have hPast :=
    past_of_imp (M := M) (w := w)
      (φ := ¬ᶠ ψ) (ψ := ¬ᶠ φ)
      (h := fun {t} ht hp => hNot ht hp)
  have hNotPast := not_of_imp (M := M) (w := w)
      (φ := ↓ᶠ (¬ᶠ ψ)) (ψ := ↓ᶠ (¬ᶠ φ)) hPast
  intro hEv
  simpa [Formula.eventuallyPast]
    using hNotPast
      (by simpa [Formula.eventuallyPast] using hEv)

lemma eventuallyPast_congr
    {φ ψ : Formula S}
    (h : ∀ {t : World P S.EventType},
        t ∈ w.time → t.place = w.place →
        ((⟪t⟫ ⊨[M]φ) ↔ (⟪t⟫ ⊨[M]ψ))) :
    (⟪w⟫ ⊨[M]⇓ᶠ φ) ↔ (⟪w⟫ ⊨[M]⇓ᶠ ψ) := by
  classical
  constructor
  · intro hEv
    exact eventuallyPast_of_imp (M := M) (w := w)
      (φ := φ) (ψ := ψ)
      (h := fun {t} ht hp => (h ht hp).1) hEv
  · intro hEv
    exact eventuallyPast_of_imp (M := M) (w := w)
      (φ := ψ) (ψ := φ)
      (h := fun {t} ht hp => (h ht hp).2) hEv

lemma alwaysPast_of_imp
    {φ ψ : Formula S}
    (h : ∀ {t : World P S.EventType},
        t.place = w.place →
        (⟪t⟫ ⊨[M]φ) → ⟪t⟫ ⊨[M]ψ) :
    (⟪w⟫ ⊨[M]⇕ᶠ φ) → (⟪w⟫ ⊨[M]⇕ᶠ ψ) := by
  classical
  have hNot : ∀ {t : World P S.EventType},
      t ∈ M.history.val → t.place = w.place →
      (⟪t⟫ ⊨[M]¬ᶠ ψ) →
        ⟪t⟫ ⊨[M]¬ᶠ φ := by
    intro t ht hp hψ
    exact not_of_imp (M := M) (w := t)
      (φ := φ) (ψ := ψ)
      (h := fun hφ => h (by simpa [hp]) hφ) hψ
  have hSome := sometime_of_imp (M := M) (w := w)
      (φ := ¬ᶠ ψ) (ψ := ¬ᶠ φ)
      (h := fun {t} ht hp => hNot ht hp)
  have hNotSome := not_of_imp (M := M) (w := w)
      (φ := ↕ᶠ (¬ᶠ ψ)) (ψ := ↕ᶠ (¬ᶠ φ)) hSome
  intro hAlways
  simpa [Formula.alwaysPast]
    using hNotSome
      (by simpa [Formula.alwaysPast] using hAlways)

lemma alwaysPast_congr
    {φ ψ : Formula S}
    (h : ∀ {t : World P S.EventType},
        t.place = w.place →
        ((⟪t⟫ ⊨[M]φ) ↔ (⟪t⟫ ⊨[M]ψ))) :
    (⟪w⟫ ⊨[M]⇕ᶠ φ) ↔ (⟪w⟫ ⊨[M]⇕ᶠ ψ) := by
  classical
  constructor
  · intro hAlways
    exact alwaysPast_of_imp (M := M) (w := w)
      (φ := φ) (ψ := ψ)
      (h := fun {t} hp hφ => (h hp).1 hφ) hAlways
  · intro hAlways
    exact alwaysPast_of_imp (M := M) (w := w)
      (φ := ψ) (ψ := φ)
      (h := fun {t} hp hψ => (h hp).2 hψ) hAlways

lemma past_not_not_iff
    {φ : Formula S} :
    (⟪w⟫ ⊨[M] ↓ᶠ (¬ᶠ (¬ᶠ φ))) ↔ (⟪w⟫ ⊨[M] ↓ᶠ φ) := by
  classical
  refine past_congr (M := M) (w := w)
    (φ := ¬ᶠ (¬ᶠ φ)) (ψ := φ)
    (fun {t} ht hp =>
      not_not_iff (M := M) (w := t) (φ := φ))

lemma eventuallyPast_not_iff
    {φ : Formula S} :
    (⟪w⟫ ⊨[M] ⇓ᶠ (¬ᶠ φ)) ↔ (⟪w⟫ ⊨[M] ¬ᶠ (↓ᶠ φ)) := by
  classical
  have hPast := past_not_not_iff (M := M) (w := w) (φ := φ)
  have hNot := not_congr (M := M) (w := w)
      (φ := ↓ᶠ (¬ᶠ (¬ᶠ φ))) (ψ := ↓ᶠ φ) hPast
  simpa [Formula.eventuallyPast, Formula.not]
    using hNot

lemma box_of_imp
    (ts : List S.Value) {φ ψ : Formula S}
    (h : ∀ q, (⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) → ⟪⟨q, †, w.time⟩⟫ ⊨[M]ψ) :
    (⟪w⟫ ⊨[M]□ᶠ[ts] φ) →
      (⟪w⟫ ⊨[M]□ᶠ[ts] ψ) := by
  classical
  rcases w with ⟨p, evt, H⟩
  intro hBox
  have hNoDiamondφ : ¬ (⟪⟨p, evt, H⟩⟫ ⊨[M] ♢ᶠ[ts] (¬ᶠ φ)) :=
    (Sat.not (M := M) (w := ⟨p, evt, H⟩)
      (φ := ♢ᶠ[ts] (¬ᶠ φ))).1
      (by simpa [Formula.box, Formula.not] using hBox)
  have hNot : ∀ q,
      (⟪⟨q, †, H⟩⟫ ⊨[M] ¬ᶠ ψ) →
        ⟪⟨q, †, H⟩⟫ ⊨[M] ¬ᶠ φ := by
    intro q hNotψ
    refine (Sat.not (M := M) (w := ⟨q, †, H⟩) (φ := φ)).2 ?_
    intro hφ
    have hψ := h q hφ
    exact (Sat.not (M := M) (w := ⟨q, †, H⟩) (φ := ψ)).1 hNotψ hψ
  have hDiamond := diamond_of_imp (M := M) (w := ⟨p, evt, H⟩)
      (ts := ts) (φ := ¬ᶠ ψ) (ψ := ¬ᶠ φ)
      (h := hNot)
  have hNoDiamondψ : ¬ (⟪⟨p, evt, H⟩⟫ ⊨[M] ♢ᶠ[ts] (¬ᶠ ψ)) :=
    by intro hDiamψ
       exact hNoDiamondφ (hDiamond hDiamψ)
  exact (Sat.not (M := M) (w := ⟨p, evt, H⟩)
      (φ := ♢ᶠ[ts] (¬ᶠ ψ))).2 hNoDiamondψ

lemma box_congr
    (ts : List S.Value) {φ ψ : Formula S}
    (h : ∀ q, (⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) ↔ (⟪⟨q, †, w.time⟩⟫ ⊨[M]ψ)) :
    (⟪w⟫ ⊨[M]□ᶠ[ts] φ) ↔ (⟪w⟫ ⊨[M]□ᶠ[ts] ψ) := by
  classical
  constructor
  · intro hBox
    exact box_of_imp (M := M) (w := w)
      (ts := ts) (φ := φ) (ψ := ψ)
      (h := fun q => (h q).1) hBox
  · intro hBox
    exact box_of_imp (M := M) (w := w)
      (ts := ts) (φ := ψ) (ψ := φ)
      (h := fun q => (h q).2) hBox

lemma diamond_eventuallyPast_not_iff
    (ts : List S.Value) (φ : Formula S) :
    (⟪w⟫ ⊨[M] ♢ᶠ[ts] (⇓ᶠ (¬ᶠ φ))) ↔
      (⟪w⟫ ⊨[M] ♢ᶠ[ts] (¬ᶠ (↓ᶠ φ))) := by
  classical
  refine diamond_congr (M := M) (w := w) (ts := ts)
    (φ := ⇓ᶠ (¬ᶠ φ)) (ψ := ¬ᶠ (↓ᶠ φ)) ?_
  intro q
  have := eventuallyPast_not_iff (M := M) (w := ⟨q, †, w.time⟩) (φ := φ)
  simpa [Formula.eventuallyPast, Formula.not]
    using this

lemma boxPast_not_diamondPast_not
    (ts : List S.Value) (φ : Formula S) :
    (⟪w⟫ ⊨[M] □ᶠ↓[ts] φ) ↔
      (⟪w⟫ ⊨[M] ¬ᶠ (♢ᶠ⇓[ts] (¬ᶠ φ))) := by
  classical
  constructor
  · intro hBox
    have hNoDiamondPast : ¬ (⟪w⟫ ⊨[M] ♢ᶠ[ts] (¬ᶠ (↓ᶠ φ))) :=
      (Sat.not (M := M) (w := w)
        (φ := ♢ᶠ[ts] (¬ᶠ (↓ᶠ φ)))).1
        (by simpa [Formula.boxPast, Formula.box, Formula.not] using hBox)
    have hNoDiamondEv : ¬ (⟪w⟫ ⊨[M] ♢ᶠ[ts] (⇓ᶠ (¬ᶠ φ))) :=
      by
        intro hDiamEv
        have hDiamPast :=
          (diamond_eventuallyPast_not_iff (M := M) (w := w)
            (ts := ts) (φ := φ)).1 hDiamEv
        exact hNoDiamondPast hDiamPast
    exact (Sat.not (M := M) (w := w)
      (φ := ♢ᶠ[ts] (⇓ᶠ (¬ᶠ φ)))).2 hNoDiamondEv
  · intro hNotDiamond
    have hNoDiamondEv : ¬ (⟪w⟫ ⊨[M] ♢ᶠ[ts] (⇓ᶠ (¬ᶠ φ))) :=
      (Sat.not (M := M) (w := w)
        (φ := ♢ᶠ[ts] (⇓ᶠ (¬ᶠ φ)))).1 hNotDiamond
    have hNoDiamondPast : ¬ (⟪w⟫ ⊨[M] ♢ᶠ[ts] (¬ᶠ (↓ᶠ φ))) :=
      by
        intro hDiamPast
        have hDiamEv :=
          (diamond_eventuallyPast_not_iff (M := M) (w := w)
            (ts := ts) (φ := φ)).2 hDiamPast
        exact hNoDiamondEv hDiamEv
    exact (Sat.not (M := M) (w := w)
      (φ := ♢ᶠ[ts] (¬ᶠ (↓ᶠ φ)))).2 hNoDiamondPast

lemma boxEventually_not_diamondPast_not
    (ts : List S.Value) (φ : Formula S) :
    (⟪w⟫ ⊨[M] □ᶠ⇓[ts] φ) ↔
      (⟪w⟫ ⊨[M] ¬ᶠ (♢ᶠ↓[ts] (¬ᶠ φ))) := by
  classical
  have hDiamond :
      (⟪w⟫ ⊨[M] ♢ᶠ[ts] (¬ᶠ (⇓ᶠ φ))) ↔
        (⟪w⟫ ⊨[M] ♢ᶠ↓[ts] (¬ᶠ φ)) := by
    refine diamond_congr (M := M) (w := w) (ts := ts) ?_
    intro q
    have :=
      (Sat.not_not_iff (M := M) (w := ⟨q, †, w.time⟩)
        (φ := ↓ᶠ (¬ᶠ φ)))
    simpa [Formula.eventuallyPast, Formula.not, Formula.diamondPast]
      using this
  have := Sat.not_congr (M := M) (w := w)
      (φ := ♢ᶠ[ts] (¬ᶠ (⇓ᶠ φ)))
      (ψ := ♢ᶠ↓[ts] (¬ᶠ φ)) hDiamond
  simpa [Formula.boxEventually, Formula.box, Formula.diamondPast,
    Formula.not] using this

lemma diamondPast_not_boxEventually_not
    (ts : List S.Value) (φ : Formula S) :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[ts] φ) ↔
      (⟪w⟫ ⊨[M] ¬ᶠ (□ᶠ⇓[ts] (¬ᶠ φ))) := by
  classical
  have hBox :=
    boxEventually_not_diamondPast_not (M := M) (w := w)
      (ts := ts) (φ := ¬ᶠ φ)
  have hNot :=
    Sat.not_congr (M := M) (w := w)
      (φ := □ᶠ⇓[ts] (¬ᶠ φ))
      (ψ := ¬ᶠ (♢ᶠ↓[ts] (¬ᶠ (¬ᶠ φ))))
      hBox
  have hNot' :
      (⟪w⟫ ⊨[M] ¬ᶠ (□ᶠ⇓[ts] (¬ᶠ φ))) ↔
        (⟪w⟫ ⊨[M] ♢ᶠ↓[ts] (¬ᶠ (¬ᶠ φ))) := by
    exact hNot.trans
      (Sat.not_not_iff (M := M) (w := w)
        (φ := ♢ᶠ↓[ts] (¬ᶠ (¬ᶠ φ))))
  have hDiamond :
      (⟪w⟫ ⊨[M] ♢ᶠ↓[ts] (¬ᶠ (¬ᶠ φ))) ↔
        (⟪w⟫ ⊨[M] ♢ᶠ↓[ts] φ) := by
    refine diamond_congr (M := M) (w := w) (ts := ts) ?_
    intro q
    have := past_congr (M := M)
      (w := ⟨q, †, w.time⟩)
      (φ := ¬ᶠ (¬ᶠ φ)) (ψ := φ)
      (h := fun {t} ht hp =>
        Sat.not_not_iff (M := M) (w := t) (φ := φ))
    simpa [Formula.diamondPast]
      using this
  exact (hDiamond.symm).trans hNot'.symm

lemma diamondEventually_not_boxPast_not
    (ts : List S.Value) (φ : Formula S) :
    (⟪w⟫ ⊨[M] ♢ᶠ⇓[ts] φ) ↔
      (⟪w⟫ ⊨[M] ¬ᶠ (□ᶠ↓[ts] (¬ᶠ φ))) := by
  classical
  have hBox :=
    boxPast_not_diamondPast_not (M := M) (w := w)
      (ts := ts) (φ := ¬ᶠ φ)
  have hNot :=
    Sat.not_congr (M := M) (w := w)
      (φ := □ᶠ↓[ts] (¬ᶠ φ))
      (ψ := ¬ᶠ (♢ᶠ⇓[ts] (¬ᶠ (¬ᶠ φ))))
      hBox
  have hNot' :
      (⟪w⟫ ⊨[M] ¬ᶠ (□ᶠ↓[ts] (¬ᶠ φ))) ↔
        (⟪w⟫ ⊨[M] ♢ᶠ⇓[ts] (¬ᶠ (¬ᶠ φ))) := by
    exact hNot.trans
      (Sat.not_not_iff (M := M) (w := w)
        (φ := ♢ᶠ⇓[ts] (¬ᶠ (¬ᶠ φ))))
  have hDiamond :
      (⟪w⟫ ⊨[M] ♢ᶠ⇓[ts] (¬ᶠ (¬ᶠ φ))) ↔
        (⟪w⟫ ⊨[M] ♢ᶠ⇓[ts] φ) := by
    refine diamond_congr (M := M) (w := w) (ts := ts) ?_
    intro q
    have :=
      eventuallyPast_congr (M := M)
        (w := ⟨q, †, w.time⟩)
        (φ := ¬ᶠ (¬ᶠ φ)) (ψ := φ)
        (h := fun {t} ht hp =>
          Sat.not_not_iff (M := M) (w := t) (φ := φ))
    simpa [Formula.diamondEventually]
      using this
  exact (hDiamond.symm).trans hNot'.symm

end Sat

/-- End-of-time validity. -/
@[simp] def EndValid
    (M : Model S P) (φ : Formula S) : Prop :=
  ∀ p : P,
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ

notation:55 "⊨[" M "]" φ =>
  EndValid M φ

/-- End-of-time validity implies satisfaction for all participants. -/
lemma EndValid.exists
    (M : Model S P) (φ : Formula S) :
    (⊨[M]φ) →
      ∀ p, ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ := by
  intro h
  exact h

lemma EndValid.of_imp
    (M : Model S P) {φ ψ : Formula S}
    (h : ∀ p, (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ) →
        ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]ψ) :
    (⊨[M]φ) → (⊨[M]ψ) := by
  classical
  intro hφ p
  exact h p (hφ p)

lemma EndValid.congr
    (M : Model S P) {φ ψ : Formula S}
    (h : ∀ p, (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ) ↔
        (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]ψ)) :
    (⊨[M]φ) ↔ (⊨[M]ψ) := by
  classical
  constructor
  · intro hφ
    exact EndValid.of_imp (M := M)
      (φ := φ) (ψ := ψ) (h := fun p => (h p).1) hφ
  · intro hψ
    exact EndValid.of_imp (M := M)
      (φ := ψ) (ψ := φ) (h := fun p => (h p).2) hψ

/-- Event-driven validity. -/
@[simp] def AllWorldValid
    (M : Model S P) (φ : Formula S) : Prop :=
  ∀ {t : World P S.EventType},
    t.time ⪯ M.history.val →
      ⟪t⟫ ⊨[M]φ

lemma AllWorldValid.of_mem_history
    (M : Model S P) {φ : Formula S}
    (h : AllWorldValid M φ)
    {t : World P S.EventType}
    (ht : t ∈ M.history.val) :
    ⟪t⟫ ⊨[M]φ :=
  by
    classical
    have hBefore :
        t.time ⪯ M.history.val :=
      PreHistory.happensBeforeEq_of_mem
        (P := P) (Event := Signature.EventType S)
        (hmem := by
          simpa [World.place, World.event, World.time] using ht)
    exact h hBefore

notation:55 "□W⊨[" M "]" φ =>
  AllWorldValid M φ

/-- Active participant predicate . -/
@[simp] def IsActive
    (H : History P (S.EventType))
    (p : P) : Prop :=
  ∃ t : World P (S.EventType), t ∈ H.val ∧ t.place = p

lemma isActive_of_mem_history
    (M : ModalDistribution.Model S P)
    {p : P}
    {evt : MaybeEvent S.EventType}
    {H' : PreHistory P (S.EventType)}
    (hMem : (p, evt, H') ∈ M.history.val) :
    IsActive (H := M.history) p := by
  refine ⟨⟨p, evt, H'⟩, hMem, rfl⟩

lemma history_ne_empty_of_isActive
    (M : ModalDistribution.Model S P)
    {p : P}
    (h : IsActive (H := M.history) p) :
    M.history.val ≠ PreHistory.empty := by
  classical
  intro hEmpty
  rcases h with ⟨t, ht, _⟩
  have : False := by
    simp [PreHistory.empty, hEmpty] at ht
  exact this

lemma exists_active_of_history_ne_empty
    (M : ModalDistribution.Model S P)
    (hne : M.history.val ≠ PreHistory.empty) :
    ∃ p : P,
      IsActive (H := M.history) p := by
  classical
  cases hHistory : M.history.val with
  | mk l =>
      cases l with
      | nil =>
          have : M.history.val = PreHistory.empty := by
            simp [hHistory, PreHistory.empty]
          exact (hne this).elim
      | cons t tl =>
          refine ⟨World.place t, ?_⟩
          exact ⟨t, by simp [hHistory], rfl⟩

/-- Active participants characterization. -/
theorem active_iff_past_top
    (M : Model S P)
    (p : P) :
    IsActive (H := M.history) p ↔
      (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]↓ᶠ ⊤ᶠ) := by
  classical
  constructor
  · intro hActive
    rcases hActive with ⟨t, htMem, htPlace⟩
    have hTop : ⟪t⟫ ⊨[M]⊤ᶠ := Sat.top _ _
    have : ∃ t ∈ M.history.val, World.place t = p ∧ ⟪t⟫ ⊨[M]⊤ᶠ :=
      ⟨t, htMem, htPlace, hTop⟩
    exact
      (Sat.past (M := M) (w := ⟨p, †, M.history.val⟩) (φ := ⊤ᶠ)).2 this
  · intro hPast
    obtain ⟨t, htMem, htPlace, -⟩ :=
      (Sat.past (M := M) (w := ⟨p, †, M.history.val⟩) (φ := ⊤ᶠ)).1 hPast
    exact ⟨t, htMem, htPlace⟩

end Logic
end ModalDistribution
