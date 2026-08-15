import ModalDistribution.Core.Set
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

/-- Quorum-intersection check for the `♢` clause of `Sat`.

`Sat.check M Q ls acc` holds when every choice of one quorum per learner in
`ls` leaves a participant in the accumulated intersection `acc ∩ O₁ ∩ ⋯ ∩ Oₙ`
satisfying `Q`. The recursion is on the learner list only; the satisfaction
predicate `Q` is abstract, which keeps `Sat` itself structurally recursive. -/
def Sat.check (M : Model S P) (Q : P → Prop) : List S.Value → Set P → Prop
  | [], acc => ∃ p' ∈ acc, Q p'
  | ℓ :: ls, acc =>
      ∀ O ∈ (M.learner ℓ).quorums,
        Sat.check M Q ls (acc ∩ O)

/-- Paper: Definition 3.4.10(1) / Figure 3 (possible-world validity). Satisfaction relation `p \dx H ⊨[M]φ`. -/
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
      Sat.check M (fun p' => Sat M p' † H φ) learners Set.univ
  | .seq =>
      isSequential (Event := S.EventType) p H

notation:65 "⟪" w "⟫" " ⊨[" M "]" φ =>
  Sat M (place w) (event w) (time w) φ

namespace Sat

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {w : World P S.EventType}
variable {p : P} {evt : MaybeEvent S.EventType}
variable {H : PreHistory P (S.EventType)}

open Set

/-- Satisfaction of a negated formula coincides with refuting any witness of the body. -/
@[simp] theorem not (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]¬ᶠ φ) ↔ ¬(⟪w⟫ ⊨[M]φ) := by
  simp [Formula.not, Sat]

/-- Satisfaction of `¬φ` witnesses the failure of `φ`. -/
theorem not_elim (M : Model S P) {w : World P S.EventType} {φ : Formula S} :
    (⟪w⟫ ⊨[M]¬ᶠ φ) → (⟪w⟫ ⊨[M]φ) → False := by
  classical
  intro hnot hφ
  exact ((not (M := M) (w := w) (φ := φ)).1 hnot) hφ

/-- To establish `¬φ`, it suffices to refute any hypothetical proof of `φ`. -/
theorem not_intro (M : Model S P) {w : World P S.EventType} {φ : Formula S}
    (h : (⟪w⟫ ⊨[M]φ) → False) :
    ⟪w⟫ ⊨[M]¬ᶠ φ := by
  classical
  exact (not (M := M) (w := w) (φ := φ)).2 h

/-- A universally quantified formula can be specialised to any value (HOAS version). -/
theorem forall_elim
    (M : Model S P) (w : World P S.EventType)
    (body : S.Value → Formula S)
    (v : Signature.Value S)
    (h : ⟪w⟫ ⊨[M].forall body) :
    ⟪w⟫ ⊨[M]body v := by
  simp [Sat] at h
  exact h v

/-- To show a universal formula holds, show the body holds for every value (HOAS version). -/
theorem forall_intro
    (M : Model S P) (w : World P S.EventType)
    (body : S.Value → Formula S)
    (h : ∀ v : Signature.Value S, ⟪w⟫ ⊨[M]body v) :
    ⟪w⟫ ⊨[M].forall body := by
  simp [Sat]
  exact h

/-- Existentials are satisfied as soon as a witness value realises the body (HOAS version). -/
theorem exists_intro
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

/-- Simp lemma: `Sat.check` for the empty learner list. -/
@[simp] theorem Sat_check_nil (M : Model S P)
    (Q : P → Prop) (acc : Set P) :
    Sat.check M Q [] acc ↔ ∃ p' ∈ acc, Q p' := by
  simp [Sat.check]

/-- Simp lemma: `Sat.check` for the inductive step. -/
@[simp] theorem Sat_check_cons (M : Model S P)
    (Q : P → Prop)
    (v : S.Value) (vs : List S.Value) (acc : Set P) :
    Sat.check M Q (v :: vs) acc ↔
      ∀ O ∈ (M.learner v).quorums, Sat.check M Q vs (acc ∩ O) := by
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
theorem diamond_nil
    (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]♢ᶠ[[]] φ) ↔
      ∃ p' : P, ⟪⟨p', †, w.time⟩⟫ ⊨[M]φ :=
  Sat_diamond_nil (M := M) (w := w) (φ := φ)

/-- The derived `♢ᶠ[]` notation shares the same semantics. -/
theorem diamondEmpty
    (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]♢ᶠ[] φ) ↔
      ∃ p' : P, ⟪⟨p', †, w.time⟩⟫ ⊨[M]φ := by
  classical
  simp [Sat]

/-- Satisfaction of an empty box coincides with the guard holding for every
participant at the same time slice. -/
theorem boxEmpty
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
    refine Classical.byContradiction fun hContra => ?_
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

/-- Satisfaction of implication agrees with pointwise entailment. -/
@[simp] theorem imp
    (M : Model S P) (w : World P S.EventType)
    (φ ψ : Formula S) :
    (⟪w⟫ ⊨[M]φ ⇒ᶠ ψ) ↔
      ((⟪w⟫ ⊨[M]φ) → (⟪w⟫ ⊨[M]ψ)) := by
  simp [Sat]

/-- Conjoin two satisfiable formulas at the same point. -/
theorem and_intro
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
@[simp] theorem atEnd
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]⤒ᶠ φ) ↔
      ⟪⟨World.place w, †, M.history.val⟩⟫ ⊨[M]φ := by
  simp [Sat]

/-- Satisfaction of `seq` is equivalent to sequentiality at the given history. -/
@[simp] theorem seq
    (M : Model S P) (w : World P S.EventType) :
    (⟪w⟫ ⊨[M]Formula.seq (S := S)) ↔
      isSequential (Event := S.EventType) (World.place w) (World.time w) := by
  simp [Sat]

/-- Satisfaction of the truth constant holds unconditionally. -/
theorem top
    (M : Model S P)
    (w : World P S.EventType) :
    ⟪w⟫ ⊨[M]⊤ᶠ := by
  simp [Formula.top, Sat]

/-- Satisfaction is monotone with respect to implication hypotheses. -/
theorem imp_elim
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
theorem imp_intro
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S}
    (h : (⟪w⟫ ⊨[M]φ) → ⟪w⟫ ⊨[M]ψ) :
    ⟪w⟫ ⊨[M]φ ⇒ᶠ ψ := by
  exact (imp (M := M) (w := w)
    (φ := φ) (ψ := ψ)).2 h

/-- Eliminate the left conjunct from `φ ∧ ψ`. -/
theorem and_left
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S} :
    (⟪w⟫ ⊨[M]φ ∧ᶠ ψ) →
      (⟪w⟫ ⊨[M]φ) := by
  classical
  intro hAnd
  have hNotImp : ⟪w⟫ ⊨[M]¬ᶠ (φ ⇒ᶠ ¬ᶠ ψ) := by
    simpa [Formula.and] using hAnd
  refine Classical.byContradiction fun hNotφ => ?_
  have hImp : ⟪w⟫ ⊨[M]φ ⇒ᶠ ¬ᶠ ψ :=
    imp_intro (M := M) (w := w)
      (φ := φ) (ψ := ¬ᶠ ψ)
      (fun hφ => False.elim (hNotφ hφ))
  have hFalse : False :=
    not_elim (M := M) (w := w)
      (φ := φ ⇒ᶠ ¬ᶠ ψ) hNotImp hImp
  exact hFalse

/-- Eliminate the right conjunct from `φ ∧ ψ`. -/
theorem and_right
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S} :
    (⟪w⟫ ⊨[M]φ ∧ᶠ ψ) →
      (⟪w⟫ ⊨[M]ψ) := by
  classical
  intro hAnd
  have hNotImp : ⟪w⟫ ⊨[M]¬ᶠ (φ ⇒ᶠ ¬ᶠ ψ) := by
    simpa [Formula.and] using hAnd
  refine Classical.byContradiction fun hNotψ => ?_
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
theorem iff_mp
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
theorem iff_mpr
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
@[simp] theorem eq (M : Model S P) (w : World P S.EventType)
    (v₁ v₂ : S.Value) :
    (⟪w⟫ ⊨[M]v₁ ≃ᶠ v₂) ↔ v₁ = v₂ := by
  simp [Sat]

/-! ### Simp lemmas for derived connectives -/

/-- ofEvent satisfaction unfolds to event membership. -/
@[simp] theorem ofEvent
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
theorem past
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]↓ᶠ φ) ↔
      ∃ t ∈ w.time, t.place = w.place ∧ ⟪t⟫ ⊨[M]φ := by
  classical
  rcases w with ⟨p, evt, H⟩
  simp [Sat]

/-- Paper: Lemma 3.6.4(1). Sometime (eventually in the future at end of time) unfolds. -/
theorem sometime
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]Formula.sometime φ) ↔
      ∃ t ∈ M.history.val, t.place = w.place ∧ ⟪t⟫ ⊨[M]φ := by
  classical
  rcases w with ⟨p, evt, H⟩
  simp [Formula.sometime, Sat]

/-- Paper: Lemma 3.6.4(2). Satisfaction of `⇕` (everytime): the body holds at every event-tuple of the
model at the current place. -/
theorem everytime
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]Formula.everytime φ) ↔
      ∀ t ∈ M.history.val, t.place = w.place → ⟪t⟫ ⊨[M]φ := by
  classical
  constructor
  · intro h t ht hp
    refine Classical.byContradiction fun hContra => ?_
    have hNotBody : ⟪t⟫ ⊨[M]¬ᶠ φ :=
      (not (M := M) (w := t) (φ := φ)).2 hContra
    have hSome : ⟪w⟫ ⊨[M]Formula.sometime (¬ᶠ φ) :=
      (sometime (M := M) (w := w) (φ := ¬ᶠ φ)).2 ⟨t, ht, hp, hNotBody⟩
    exact
      (not (M := M) (w := w) (φ := Formula.sometime (¬ᶠ φ))).1
        (by simpa [Formula.everytime] using h) hSome
  · intro h
    have hNoSome : ¬ (⟪w⟫ ⊨[M]Formula.sometime (¬ᶠ φ)) := by
      intro hSome
      obtain ⟨t, ht, hp, hNot⟩ :=
        (sometime (M := M) (w := w) (φ := ¬ᶠ φ)).1 hSome
      exact (not (M := M) (w := t) (φ := φ)).1 hNot (h t ht hp)
    have := (not (M := M) (w := w)
      (φ := Formula.sometime (¬ᶠ φ))).2 hNoSome
    simpa [Formula.everytime] using this

/-- Conjunction satisfaction unfolds to both conjuncts. -/
@[simp] theorem and
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
@[simp] theorem or
    (M : Model S P)
    (w : World P S.EventType)
    (φ ψ : Formula S) :
    (⟪w⟫ ⊨[M]φ ∨ᶠ ψ) ↔
      (⟪w⟫ ⊨[M]φ) ∨ (⟪w⟫ ⊨[M]ψ) := by
  classical
  simp [Formula.or, Formula.not, Sat]
  constructor
  · intro h
    exact (Classical.em _).elim Or.inl fun hn => Or.inr (h hn)
  · rintro (hφ | hψ) hn
    · exact absurd hφ hn
    · exact hψ

theorem check_of_imp {ts : List S.Value} {acc : Set P} {Q Q' : P → Prop}
    (h : ∀ q, Q q → Q' q) :
    Sat.check M Q ts acc → Sat.check M Q' ts acc := by
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

theorem diamond_of_imp
    (ts : List S.Value) {φ ψ : Formula S}
    (h : ∀ q, (⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) → (⟪⟨q, †, w.time⟩⟫ ⊨[M]ψ)) :
    (⟪w⟫ ⊨[M]♢ᶠ[ts] φ) → (⟪w⟫ ⊨[M]♢ᶠ[ts] ψ) := by
  classical
  intro hSat
  simp [Sat] at hSat ⊢
  exact check_of_imp (M := M) (ts := ts) (acc := Set.univ) h hSat

theorem diamond_congr
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

theorem not_not_iff
    {φ : Formula S} :
    (⟪w⟫ ⊨[M]¬ᶠ (¬ᶠ φ)) ↔
      (⟪w⟫ ⊨[M]φ) := by
  classical
  constructor
  · intro h
    have : ¬¬ (⟪w⟫ ⊨[M]φ) := by
      simpa [Formula.not, Sat] using h
    exact Classical.byContradiction this
  · intro h
    have : ¬¬ (⟪w⟫ ⊨[M]φ) := fun hn => hn h
    simpa [Formula.not, Sat] using this

theorem not_of_imp
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

theorem past_of_imp
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
theorem past_intro_of_prefix
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

theorem past_congr
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

theorem box_of_imp
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

end Sat

/-- Paper: Definition 3.4.10(2) (end-of-time validity ⊨). End-of-time validity. -/
@[simp] def EndValid
    (M : Model S P) (φ : Formula S) : Prop :=
  ∀ p : P,
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ

notation:55 "⊨[" M "]" φ =>
  EndValid M φ

theorem EndValid.of_imp
    (M : Model S P) {φ ψ : Formula S}
    (h : ∀ p, (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ) →
        ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]ψ) :
    (⊨[M]φ) → (⊨[M]ψ) := by
  classical
  intro hφ p
  exact h p (hφ p)

/-- Modus ponens for end-of-time validity. -/
theorem EndValid.imp_elim
    (M : Model S P) {φ ψ : Formula S}
    (hImp : ⊨[M]φ ⇒ᶠ ψ) (hφ : ⊨[M]φ) : ⊨[M]ψ := by
  classical
  intro p
  exact
    Sat.imp_elim (M := M) (w := ⟨p, †, M.history.val⟩)
      (φ := φ) (ψ := ψ) (hImp p) (hφ p)

/-- Paper: Definition 3.4.10(3) (all-world validity □W⊨). Event-driven validity. -/
@[simp] def AllWorldValid
    (M : Model S P) (φ : Formula S) : Prop :=
  ∀ {t : World P S.EventType},
    t.time ⪯ M.history.val →
      ⟪t⟫ ⊨[M]φ

theorem AllWorldValid.of_mem_history
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

/-- Instantiate an event-driven validity at an end-of-time world. -/
theorem AllWorldValid.at_end
    (M : Model S P) {φ : Formula S}
    (h : AllWorldValid M φ)
    (p : P) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ :=
  h (PreHistory.happensBeforeEq_refl
      (P := P) (Event := Signature.EventType S) M.history.val)

notation:55 "□W⊨[" M "]" φ =>
  AllWorldValid M φ

/-- Paper: Definition 3.5.1 (active participants). Active participant predicate . -/
@[simp] def IsActive
    (H : History P (S.EventType))
    (p : P) : Prop :=
  ∃ t : World P (S.EventType), t ∈ H.val ∧ t.place = p

/-- Paper: Lemma 3.5.3. Active participants characterization. -/
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


/-! ### Case analysis helpers for `∨ᶠ` and `∧ᶠ` -/

section CaseAnalysis

variable {M : Model S P} {w : World P S.EventType}

/-- Lift satisfaction of the left disjunct to the disjunction. -/
theorem sat_or_of_left
    {φ ψ : Formula S}
    (hφ : ⟪w⟫ ⊨[M]φ) :
    ⟪w⟫ ⊨[M] (φ ∨ᶠ ψ) := by
  classical
  have hDisj : (⟪w⟫ ⊨[M] φ) ∨ (⟪w⟫ ⊨[M] ψ) := Or.inl hφ
  exact (Sat.or (M := M) (w := w) (φ := φ) (ψ := ψ)).2 hDisj

/-- Lift satisfaction of the right disjunct to the disjunction. -/
theorem sat_or_of_right
    {φ ψ : Formula S}
    (hψ : ⟪w⟫ ⊨[M]ψ) :
    ⟪w⟫ ⊨[M] (φ ∨ᶠ ψ) := by
  classical
  have hDisj : (⟪w⟫ ⊨[M] φ) ∨ (⟪w⟫ ⊨[M] ψ) := Or.inr hψ
  exact (Sat.or (M := M) (w := w) (φ := φ) (ψ := ψ)).2 hDisj

/-- Resolve a satisfied disjunction into propositional alternatives. -/
theorem sat_or_cases
    {φ ψ : Formula S}
    (h : ⟪w⟫ ⊨[M](φ ∨ᶠ ψ)) :
    (⟪w⟫ ⊨[M] φ) ∨ (⟪w⟫ ⊨[M] ψ) := by
  classical
  simpa using (Sat.or (M := M) (w := w) (φ := φ) (ψ := ψ)).1 h

/-- Extract the right conjunct from a satisfied conjunction. -/
theorem sat_and_right
    {φ ψ : Formula S}
    (h : ⟪w⟫ ⊨[M](φ ∧ᶠ ψ)) :
    ⟪w⟫ ⊨[M] ψ := by
  classical
  have := (Sat.and (M := M) (w := w) (φ := φ) (ψ := ψ)).1 h
  exact this.2

end CaseAnalysis

end Logic
end ModalDistribution
