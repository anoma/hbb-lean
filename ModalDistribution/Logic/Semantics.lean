import Mathlib.Data.Set.Lattice
import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.History
import ModalDistribution.Core.Model
import ModalDistribution.Logic.Syntax

/-!
# Modal logic semantics

We formalise the satisfaction relation from Definition 3.4.1 / Figure 3 of the
HBB paper.  Satisfaction is defined for a model, a participant, a local history,
and a variable assignment.  We also introduce end-of-time validity, event-driven
validity, and the notion of active participants (Definition 3.5.1).
-/

namespace ModalDistribution
namespace Logic

open Set
open ModalDistribution
open scoped PreHistory Formula

set_option autoImplicit false

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {S : Signature} {P : Type u₆} [Nonempty P]

/-- Satisfaction relation `p, H ⊨M σ φ` (Definition 3.4.1). -/
def Sat
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P) : Formula S → Prop
  | .bot => False
  | .imp φ ψ => Sat M σ H p φ → Sat M σ H p ψ
  | .eq t₁ t₂ => Term.eval σ t₁ = Term.eval σ t₂
  | .forall a φ => ∀ v : Signature.Value S,
      Sat M (Function.update σ a v) H p φ
  | .event evt =>
      (p, MaybeEvent.some ⟨evt.sym, Term.evalList σ evt.args⟩, H.val) ∈ M.history.val
  | .predicate pred =>
      ⟨pred.sym, Term.evalList σ pred.args⟩ ∈ M.predInterp p H.val
  | .past φ =>
      ∃ (H' : History P (Signature.EventType S))
        (_hBefore : H'.val ≺ₚ[p] H.val),
        Sat M σ H' p φ
  | .atEnd φ => Sat M σ M.history p φ
  | .diamond ls φ =>
      let rec check : List (Term S) → Set P → Prop
        | [], acc =>
            ∃ p' ∈ acc,
              Sat (M.localView H) σ H p' φ
        | t :: ts, acc =>
            let v := Term.eval σ t
            ∀ O ∈ (M.learner v).quorums,
              check ts (acc ∩ O)
      check ls Set.univ
  | .seq =>
      isSequential (P := P) (Event := Signature.EventType S) p H.val

notation:65 "⟨" H "," p "⟩" " ⊨[" M "," σ "]" φ =>
  Sat M σ H p φ

namespace Sat

variable {S : Signature} {P : Type u₆} [Nonempty P]
variable {M : Model S P} {σ : Assignment S}
variable {H : History P (Signature.EventType S)} {p : P}

open Set

/-- Satisfaction of `⊥` is never witnessed. -/
@[simp] lemma bot
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S)) (p : P) :
    (⟨H,p⟩ ⊨[M, σ] ⊥ᶠ) ↔ False := by
  simp [Sat]

/-- Satisfaction of a negated formula coincides with refuting any witness of the body. -/
lemma not
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] ¬ᶠ φ) ↔
      ((⟨H,p⟩ ⊨[M,σ]φ) → False) := by
  classical
  simp [Formula.not, Sat]

/-- Satisfaction of `¬φ` witnesses the failure of `φ`. -/
lemma not_elim
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    {φ : Formula S} :
    (⟨H,p⟩ ⊨[M, σ] ¬ᶠ φ) →
      (⟨H,p⟩ ⊨[M,σ]φ) → False := by
  classical
  intro hnot hφ
  exact (not (M := M) (σ := σ) (H := H) (p := p) (φ := φ)).1 hnot hφ

/-- To establish `¬φ`, it suffices to refute any hypothetical proof of `φ`. -/
lemma not_intro
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    {φ : Formula S}
    (h : (⟨H,p⟩ ⊨[M,σ]φ) → False) :
    ⟨H,p⟩ ⊨[M, σ] ¬ᶠ φ := by
  classical
  exact (not (M := M) (σ := σ) (H := H) (p := p) (φ := φ)).2 h

/-- The negation of truth is never satisfiable. -/
lemma not_top
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P) :
    (⟨H,p⟩ ⊨[M, σ] ¬ᶠ ⊤ᶠ) ↔ False := by
  classical
  simp [Formula.not, Formula.top, Sat]

/-- The negation of `⊥` always holds. -/
lemma not_bot
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P) :
    ⟨H,p⟩ ⊨[M, σ] ¬ᶠ ⊥ᶠ := by
  classical
  simp [Formula.not, Sat]

/-- A universally quantified formula can be specialised to any value. -/
lemma forall_elim
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    (a : S.VarSymb) (φ : Formula S)
    (v : Signature.Value S)
    (h : ⟨H,p⟩ ⊨[M,σ]∀ᶠ a, φ) :
    ⟨H,p⟩ ⊨[M, Function.update σ a v] φ := by
  classical
  unfold Sat at h
  exact h v

/-- To show a universal formula holds, show the body holds for every value. -/
lemma forall_intro
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    (a : S.VarSymb) (φ : Formula S)
    (h : ∀ v : Signature.Value S,
      ⟨H,p⟩ ⊨[M, Function.update σ a v] φ) :
    ⟨H,p⟩ ⊨[M, σ] ∀ᶠ a, φ := by
  classical
  unfold Sat
  exact h

/-- Existentials are satisfied as soon as a witness value realises the body. -/
lemma exists_intro
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    (a : S.VarSymb) (φ : Formula S)
    (h : ∃ v : Signature.Value S,
      ⟨H,p⟩ ⊨[M,Function.update σ a v]φ) :
    ⟨H,p⟩ ⊨[M, σ] ∃ᶠ a, φ := by
  classical
  rcases h with ⟨v, hv⟩
  refine not_intro (M := M) (σ := σ) (H := H) (p := p)
    (φ := ∀ᶠ a, ¬ᶠ φ) ?_
  intro hforall
  have hnot :=
    forall_elim (M := M) (σ := σ) (H := H) (p := p)
      (a := a) (φ := ¬ᶠ φ) (v := v) hforall
  have hneg :=
    (not (M := M) (σ := Function.update σ a v)
      (H := H) (p := p) (φ := φ)).1 hnot hv
  exact hneg

/-- Diamonds over the empty learner list are witnessed by some participant. -/
lemma diamond_nil
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[[]] φ) ↔
      ∃ p' : P, ⟨H, p'⟩ ⊨[M ∣ᵥ H,σ]φ := by
  classical
  simp [Sat, Sat.check, Set.mem_univ]

/-- The derived empty diamond exposes the same existence principle. -/
lemma diamondEmpty
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[] φ) ↔
      ∃ p' : P, ⟨H, p'⟩ ⊨[M ∣ᵥ H,σ]φ := by
  classical
  simp [Formula.diamondEmpty, Sat, Sat.check, Set.mem_univ]

/-- Satisfaction of an empty box is equivalent to every local participant
carrying the guard. -/
lemma boxEmpty
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] □ᶠ[] φ) ↔
      ∀ q : P, ⟨H, q⟩ ⊨[M ∣ᵥ H,σ]φ := by
  classical
  constructor
  · intro hBox q
    by_contra hContra
    have hNot :
        ⟨H, q⟩ ⊨[M ∣ᵥ H, σ] ¬ᶠ φ := by
      simpa [Formula.not, Sat] using hContra
    have hDiamond :
        ⟨H,p⟩ ⊨[M, σ] ♢ᶠ[] (¬ᶠ φ) :=
      (diamondEmpty (M := M) (σ := σ) (H := H) (p := p)
        (φ := ¬ᶠ φ)).2 ⟨q, hNot⟩
    have hFalse : False :=
      not_elim (M := M) (σ := σ) (H := H) (p := p)
        (φ := ♢ᶠ[[]] (¬ᶠ φ))
        (by simpa [Formula.boxEmpty, Formula.box] using hBox)
        (by simpa [Formula.diamondEmpty] using hDiamond)
    exact hFalse.elim
  · intro hAll
    have hNotDiamond :
        ⟨H,p⟩ ⊨[M, σ] ¬ᶠ (♢ᶠ[[]] (¬ᶠ φ)) :=
      not_intro (M := M) (σ := σ) (H := H) (p := p)
        (φ := ♢ᶠ[[]] (¬ᶠ φ))
        (by
          intro hDiamond
          have hDiamond' :
            ⟨H,p⟩ ⊨[M, σ] ♢ᶠ[] (¬ᶠ φ) :=
            by simpa [Formula.diamondEmpty] using hDiamond
          obtain ⟨q, hNot⟩ :=
            (diamondEmpty (M := M) (σ := σ) (H := H) (p := p)
              (φ := ¬ᶠ φ)).1 hDiamond'
          have hφ := hAll q
          exact
            not_elim (M := M ∣ᵥ H) (σ := σ) (H := H) (p := q)
              (φ := φ) hNot hφ)
    simpa [Formula.boxEmpty, Formula.box] using hNotDiamond

/-- Events witnessed at a history automatically satisfy sometime. -/
lemma event_sometime
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P)
    (E : Signature.EventType S)
    (hEvent : ⟨H,p⟩ ⊨[M,σ]Formula.ofEvent E) :
    ⟨H,p⟩ ⊨[M, σ] ↕ᶠ (Formula.ofEvent E) := by
  classical
  have hMem :
      (p,
        MaybeEvent.some
          ⟨E.sym, Term.evalList σ (E.args.map Term.ofValue)⟩,
        H.val) ∈ M.history.val := by
    simpa [Formula.ofEvent, Sat] using hEvent
  have hMem' :
      (p,
        MaybeEvent.some
          ⟨E.sym, (E.args.map Term.ofValue).map (Term.eval σ)⟩,
        H.val) ∈ M.history.val := by
    simpa [Term.evalList] using hMem
  have hMem'' :
      (p,
        MaybeEvent.some
          ⟨E.sym, List.map (Term.eval σ ∘ Term.ofValue) E.args⟩,
        H.val) ∈ M.history.val := by
    simpa [List.map_map, Function.comp] using hMem'
  have hBefore : H.val ≺ₚ[p] M.history.val := ⟨_, hMem''⟩
  simpa [Formula.sometime, Formula.atEnd, Sat, Formula.past, Formula.ofEvent,
    Term.evalList, List.map_map, Function.comp]
    using ⟨H, hBefore, hMem''⟩

/-- The truth constant is satisfied if and only if `True`. -/
lemma top_iff
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (H : History P (Signature.EventType S)) (p : P) :
    (⟨H,p⟩ ⊨[M, σ] ⊤ᶠ) ↔ True := by
  classical
  simp [Formula.top, Sat]

/-- Satisfaction of implication agrees with pointwise entailment. -/
lemma imp
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    (φ ψ : Formula S) :
    (⟨H,p⟩ ⊨[M,σ]φ ⇒ᶠ ψ) ↔
      ((⟨H,p⟩ ⊨[M,σ]φ) → (⟨H,p⟩ ⊨[M,σ]ψ)) := by
  simp [Sat]

/-- Conjoin two satisfiable formulas at the same point. -/
lemma and_intro
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    {φ ψ : Formula S}
    (hφ : ⟨H,p⟩ ⊨[M,σ]φ)
    (hψ : ⟨H,p⟩ ⊨[M,σ]ψ) :
    ⟨H,p⟩ ⊨[M,σ] φ ∧ᶠ ψ := by
  classical
  refine Sat.not_intro (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ ⇒ᶠ ¬ᶠ ψ) ?_
  intro hImp
  have hImpFn :=
    (Sat.imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ) (ψ := ¬ᶠ ψ)).1 hImp
  have hNotψ := hImpFn hφ
  exact
    (Sat.not_elim (M := M) (σ := σ) (H := H) (p := p)
      (φ := ψ)) hNotψ hψ

/-- Satisfaction of `⤒ φ` coincides with evaluating `φ` at the full history. -/
lemma atEnd
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P) (φ : Formula S) :
    (⟨H,p⟩ ⊨[M, σ] ⤒ᶠ φ) ↔
      ⟨M.history,p⟩ ⊨[M,σ]φ := by
  simp [Sat]

/-- Satisfaction of `seq` is equivalent to sequentiality at the given history. -/
lemma seq
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P) :
    (⟨H,p⟩ ⊨[M, σ] (Formula.seq (S := S))) ↔
      isSequential (Event := Signature.EventType S) p H := by
  simp [Sat]

/-- Satisfaction of the truth constant holds unconditionally. -/
lemma top
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P) :
    ⟨H,p⟩ ⊨[M, σ] ⊤ᶠ := by
  simp [Formula.top, Sat]

/-- Satisfaction is monotone with respect to implication hypotheses. -/
lemma imp_elim
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    {φ ψ : Formula S} :
    (⟨H,p⟩ ⊨[M,σ]φ ⇒ᶠ ψ) →
      (⟨H,p⟩ ⊨[M,σ]φ) → ⟨H,p⟩ ⊨[M,σ]ψ := by
  intro himp hφ
  have h := (imp (M := M) (σ := σ) (H := H)
      (p := p) φ ψ).1 himp
  exact h hφ

/-- Introduction form of implication in the satisfaction relation. -/
lemma imp_intro
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    {φ ψ : Formula S}
    (h : (⟨H,p⟩ ⊨[M,σ]φ) → ⟨H,p⟩ ⊨[M,σ]ψ) :
    ⟨H,p⟩ ⊨[M,σ]φ ⇒ᶠ ψ := by
  exact (imp (M := M) (σ := σ) (H := H)
    (p := p) φ ψ).2 h

/-- Eliminate the left conjunct from `φ ∧ ψ`. -/
lemma and_left
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    {φ ψ : Formula S} :
    (⟨H,p⟩ ⊨[M,σ] φ ∧ᶠ ψ) →
      (⟨H,p⟩ ⊨[M,σ] φ) := by
  classical
  intro hAnd
  have hNotImp : ⟨H,p⟩ ⊨[M,σ] ¬ᶠ (φ ⇒ᶠ ¬ᶠ ψ) := by
    simpa [Formula.and] using hAnd
  by_contra hNotφ
  have hImp : ⟨H,p⟩ ⊨[M,σ] φ ⇒ᶠ ¬ᶠ ψ :=
    imp_intro (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ) (ψ := ¬ᶠ ψ)
      (fun hφ => False.elim (hNotφ hφ))
  have hFalse : False :=
    not_elim (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ ⇒ᶠ ¬ᶠ ψ) hNotImp hImp
  exact hFalse

/-- Eliminate the right conjunct from `φ ∧ ψ`. -/
lemma and_right
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    {φ ψ : Formula S} :
    (⟨H,p⟩ ⊨[M,σ] φ ∧ᶠ ψ) →
      (⟨H,p⟩ ⊨[M,σ] ψ) := by
  classical
  intro hAnd
  have hNotImp : ⟨H,p⟩ ⊨[M,σ] ¬ᶠ (φ ⇒ᶠ ¬ᶠ ψ) := by
    simpa [Formula.and] using hAnd
  by_contra hNotψ
  have hNotψSat : ⟨H,p⟩ ⊨[M,σ] ¬ᶠ ψ :=
    not_intro (M := M) (σ := σ) (H := H) (p := p)
      (φ := ψ) (fun hψ => hNotψ hψ)
  have hImp : ⟨H,p⟩ ⊨[M,σ] φ ⇒ᶠ ¬ᶠ ψ :=
    imp_intro (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ) (ψ := ¬ᶠ ψ) (fun _ => hNotψSat)
  have hFalse : False :=
    not_elim (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ ⇒ᶠ ¬ᶠ ψ) hNotImp hImp
  exact hFalse

/-- Eliminate the forward implication from an `iff`. -/
lemma iff_mp
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    {φ ψ : Formula S}
    (hIff : ⟨H,p⟩ ⊨[M,σ]φ ⇔ᶠ ψ) :
    (⟨H,p⟩ ⊨[M,σ] φ) → (⟨H,p⟩ ⊨[M,σ] ψ) := by
  classical
  have hAnd :
      ⟨H,p⟩ ⊨[M,σ]
        ((φ ⇒ᶠ ψ) ∧ᶠ (ψ ⇒ᶠ φ)) := by
    simpa [Formula.iff] using hIff
  have hImp : ⟨H,p⟩ ⊨[M,σ] φ ⇒ᶠ ψ :=
    and_left (M := M) (σ := σ) (H := H) (p := p) hAnd
  intro hφ
  exact
    imp_elim (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ) (ψ := ψ) hImp hφ

/-- Eliminate the backward implication from an `iff`. -/
lemma iff_mpr
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    {φ ψ : Formula S}
    (hIff : ⟨H,p⟩ ⊨[M,σ]φ ⇔ᶠ ψ) :
    (⟨H,p⟩ ⊨[M,σ] ψ) → (⟨H,p⟩ ⊨[M,σ] φ) := by
  classical
  have hAnd :
      ⟨H,p⟩ ⊨[M,σ]
        ((φ ⇒ᶠ ψ) ∧ᶠ (ψ ⇒ᶠ φ)) := by
    simpa [Formula.iff] using hIff
  have hImp : ⟨H,p⟩ ⊨[M,σ] ψ ⇒ᶠ φ :=
    and_right (M := M) (σ := σ) (H := H) (p := p) hAnd
  intro hψ
  exact
    imp_elim (M := M) (σ := σ) (H := H) (p := p)
      (φ := ψ) (ψ := φ) hImp hψ

/-- Equality atoms are satisfied when the underlying terms coincide. -/
lemma eq
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    (t₁ t₂ : Term S) :
    (⟨H,p⟩ ⊨[M, σ] t₁ ≃ᶠ t₂) ↔ Term.eval σ t₁ = Term.eval σ t₂ := by
  simp [Sat]

/-- Equality atoms witness reflexivity of term evaluation. -/
lemma eq_refl
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    (t : Term S) :
    ⟨H,p⟩ ⊨[M, σ] (t ≃ᶠ t) := by
  simp [Sat]

/-- Event clauses are witnessed by membership in the ambient history. -/
lemma event_of_mem
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    (evt : EventAtom S)
    (hmem : (p, MaybeEvent.some ⟨evt.sym, Term.evalList σ evt.args⟩,
      H.val) ∈ M.history.val) :
    ⟨H,p⟩ ⊨[M, σ] (Formula.event evt) := by
  simpa [Sat]

/-- Event atoms reduce to membership in the enclosing history. -/
lemma event
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    (H : History P (Signature.EventType S))
    (p : P)
    (evt : EventAtom S) :
    (⟨H,p⟩ ⊨[M, σ] Formula.event evt) ↔
      (p, MaybeEvent.some ⟨evt.sym, Term.evalList σ evt.args⟩,
        H.val) ∈ M.history.val := by
  simp [Sat]

/-- Transport event satisfaction along an inclusion of local views. -/
lemma ofEvent_of_subset
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S)
    {H H₁ H₂ : History P (Signature.EventType S)}
    (p : P) (evt : Signature.EventType S)
    (hSubset : H₁.val ⊆ H.val)
    (hEvent : ⟨H₂,p⟩ ⊨[M ∣ᵥ H₁,σ]Formula.ofEvent evt) :
    ⟨H₂,p⟩ ⊨[M ∣ᵥ H,σ]Formula.ofEvent evt := by
  classical
  have hMem :
      (p,
        MaybeEvent.some
          ⟨evt.sym, Term.evalList σ (evt.args.map Term.ofValue)⟩,
        H₂.val) ∈ H₁.val := by
    simpa [Formula.ofEvent]
      using
        (event (M := M ∣ᵥ H₁) (σ := σ) (H := H₂) (p := p)
          (evt := ⟨evt.sym, evt.args.map Term.ofValue⟩)).1 hEvent
  have hMem' :
      (p,
        MaybeEvent.some
          ⟨evt.sym, Term.evalList σ (evt.args.map Term.ofValue)⟩,
        H₂.val) ∈ H.val :=
    hSubset _ hMem
  simpa [Formula.ofEvent]
    using
      (event (M := M ∣ᵥ H) (σ := σ) (H := H₂) (p := p)
        (evt := ⟨evt.sym, evt.args.map Term.ofValue⟩)).2 hMem'

variable [DecidableEq S.VarSymb]

/-- Internal recursion used to reason about diamond semantics with an accumulator. -/
def diamondAcc
    (ts : List (Term S)) (φ : Formula S) : Set P → Prop :=
  List.rec
    (fun acc => ∃ q ∈ acc, ⟨H,q⟩ ⊨[M ∣ᵥ H,σ]φ)
    (fun t _ ih acc =>
      ∀ O ∈ (M.learner (Term.eval σ t)).quorums,
        ih (acc ∩ O))
    ts

lemma diamondAcc_of_imp
    {ts : List (Term S)} {acc : Set P}
    {φ ψ : Formula S}
    (h : ∀ q,
        (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]φ) →
          ⟨H,q⟩ ⊨[M ∣ᵥ H,σ]ψ) :
    diamondAcc (M := M) (σ := σ) (H := H) ts φ acc →
      diamondAcc (M := M) (σ := σ) (H := H) ts ψ acc := by
  classical
  induction ts generalizing acc with
  | nil =>
      intro hAcc
      rcases hAcc with ⟨q, hacc, hSat⟩
      exact ⟨q, hacc, h q hSat⟩
  | cons t ts ih =>
      intro hAcc
      refine fun O hO => ?_
      exact ih (acc := acc ∩ O) (hAcc O hO)

lemma diamondAcc_congr
    {ts : List (Term S)} {acc : Set P}
    {φ ψ : Formula S}
    (h : ∀ q,
        (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]φ) ↔
          (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]ψ)) :
    diamondAcc (M := M) (σ := σ) (H := H) ts φ acc ↔
      diamondAcc (M := M) (σ := σ) (H := H) ts ψ acc := by
  classical
  constructor
  · intro hAcc
    exact diamondAcc_of_imp (M := M) (σ := σ) (H := H)
      (ts := ts) (acc := acc) (φ := φ) (ψ := ψ)
      (h := fun q => (h q).1) hAcc
  · intro hAcc
    exact diamondAcc_of_imp (M := M) (σ := σ) (H := H)
      (ts := ts) (acc := acc) (φ := ψ) (ψ := φ)
      (h := fun q => (h q).2) hAcc

lemma diamond_iff_diamondAcc
    (ts : List (Term S)) (φ : Formula S) (p : P) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[ts] φ) ↔
      diamondAcc (M := M) (σ := σ) (H := H) ts φ Set.univ := by
  classical
  have hgeneral :
      ∀ (us : List (Term S)) (acc : Set P),
        Sat.check M σ H φ us acc ↔
          diamondAcc (M := M) (σ := σ) (H := H) us φ acc := by
    intro us
    induction us with
    | nil =>
        intro acc
        simp [Sat.check, diamondAcc]
    | cons t us ih =>
        intro acc
        simp [Sat.check, diamondAcc, ih]
  simpa [Sat, Sat.check] using (hgeneral ts Set.univ)

lemma diamond_of_imp
    (ts : List (Term S)) {φ ψ : Formula S}
    (h : ∀ q,
        (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]φ) →
          ⟨H,q⟩ ⊨[M ∣ᵥ H,σ]ψ) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[ts] φ) →
      (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[ts] ψ) := by
  classical
  intro hSat
  have hAcc :=
    (diamond_iff_diamondAcc (M := M) (σ := σ)
      (H := H) (ts := ts) (φ := φ) (p := p)).1 hSat
  have hAcc' :=
    diamondAcc_of_imp (M := M) (σ := σ) (H := H)
      (ts := ts) (acc := Set.univ)
      (φ := φ) (ψ := ψ) (h := h) hAcc
  exact
    (diamond_iff_diamondAcc (M := M) (σ := σ)
      (H := H) (ts := ts) (φ := ψ) (p := p)).2 hAcc'

lemma diamond_congr
    (ts : List (Term S)) {φ ψ : Formula S}
    (h : ∀ q,
        (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]φ) ↔
          (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[ts] φ) ↔
      (⟨H,p⟩ ⊨[M, σ] ♢ᶠ[ts] ψ) := by
  classical
  constructor
  · intro hSat
    exact diamond_of_imp (M := M) (σ := σ) (H := H)
      (ts := ts) (φ := φ) (ψ := ψ) (p := p)
      (h := fun q => (h q).1) hSat
  · intro hSat
    exact diamond_of_imp (M := M) (σ := σ) (H := H)
      (ts := ts) (φ := ψ) (ψ := φ) (p := p)
      (h := fun q => (h q).2) hSat

lemma not_not_iff
    {φ : Formula S} :
    (⟨H,p⟩ ⊨[M, σ] ¬ᶠ (¬ᶠ φ)) ↔
      (⟨H,p⟩ ⊨[M,σ]φ) := by
  classical
  constructor
  · intro h
    have : ¬¬ (⟨H,p⟩ ⊨[M,σ]φ) := by
      simpa [Formula.not, Sat] using h
    exact not_not.mp this
  · intro h
    have : ¬¬ (⟨H,p⟩ ⊨[M,σ]φ) := not_not.mpr h
    simpa [Formula.not, Sat] using this

lemma not_of_imp
    {φ ψ : Formula S}
    (h : (⟨H,p⟩ ⊨[M,σ]φ) →
        (⟨H,p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ¬ᶠ ψ) →
      (⟨H,p⟩ ⊨[M, σ] ¬ᶠ φ) := by
  classical
  intro hNot
  simp [Formula.not, Sat] at hNot ⊢
  intro hφ
  exact hNot (h hφ)

lemma not_congr
    {φ ψ : Formula S}
    (h : (⟨H,p⟩ ⊨[M,σ]φ) ↔
           (⟨H,p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ¬ᶠ φ) ↔
      (⟨H,p⟩ ⊨[M, σ] ¬ᶠ ψ) := by
  classical
  constructor
  · intro hNot
    exact not_of_imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := ψ) (ψ := φ) (h := fun hψ => (h.mpr hψ)) hNot
  · intro hNot
    exact not_of_imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ) (ψ := ψ) (h := fun hφ => (h.mp hφ)) hNot

lemma atEnd_of_imp
    {φ ψ : Formula S}
    (h : (⟨M.history,p⟩ ⊨[M,σ]φ) →
        (⟨M.history,p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ⤒ᶠ φ) →
      (⟨H,p⟩ ⊨[M, σ] ⤒ᶠ ψ) := by
  classical
  intro hEnd
  simpa [Formula.atEnd, Sat] using
    h (by simpa [Formula.atEnd, Sat] using hEnd)

lemma atEnd_congr
    {φ ψ : Formula S}
    (h : (⟨M.history,p⟩ ⊨[M,σ]φ) ↔
        (⟨M.history,p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ⤒ᶠ φ) ↔
      (⟨H,p⟩ ⊨[M, σ] ⤒ᶠ ψ) := by
  classical
  constructor
  · intro hEnd
    exact atEnd_of_imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ) (ψ := ψ) (h := fun hφ => (h.mp hφ)) hEnd
  · intro hEnd
    exact atEnd_of_imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := ψ) (ψ := φ) (h := fun hψ => (h.mpr hψ)) hEnd

lemma past_of_imp
    {φ ψ : Formula S}
    (h : ∀ H', (⟨H',p⟩ ⊨[M,σ]φ) →
        (⟨H',p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ↓ᶠ φ) →
      (⟨H,p⟩ ⊨[M, σ] ↓ᶠ ψ) := by
  classical
  intro hPast
  unfold Sat at hPast ⊢
  rcases hPast with ⟨H', hBefore, hSat⟩
  have hSat' := h H' hSat
  exact ⟨H', hBefore, hSat'⟩

/-- A formula true at a preceding prefix witnesses its past modality. -/
lemma past_intro_of_prefix
    {H' : History P (Signature.EventType S)}
    {φ : Formula S}
    (hBefore : H'.val ≺ₚ[p]H.val)
    (hφ : ⟨H',p⟩ ⊨[M,σ]φ) :
    ⟨H,p⟩ ⊨[M, σ] ↓ᶠ φ := by
  classical
  unfold Sat
  exact ⟨H', hBefore, hφ⟩

lemma past_congr
    {φ ψ : Formula S}
    (h : ∀ H', (⟨H',p⟩ ⊨[M,σ]φ) ↔
        (⟨H',p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ↓ᶠ φ) ↔
      (⟨H,p⟩ ⊨[M, σ] ↓ᶠ ψ) := by
  classical
  constructor
  · intro hPast
    exact past_of_imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ) (ψ := ψ) (h := fun H' => (h H').1) hPast
  · intro hPast
    exact past_of_imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := ψ) (ψ := φ) (h := fun H' => (h H').2) hPast

lemma sometime_of_imp
    {φ ψ : Formula S}
    (h : ∀ H', (⟨H',p⟩ ⊨[M,σ]φ) →
        (⟨H',p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ↕ᶠ φ) →
      (⟨H,p⟩ ⊨[M, σ] ↕ᶠ ψ) := by
  classical
  have hPast := past_of_imp (M := M) (σ := σ)
      (H := M.history) (p := p) h
  intro hSome
  simpa [Formula.sometime]
    using atEnd_of_imp (M := M) (σ := σ)
      (H := H) (p := p)
      (φ := Formula.past φ) (ψ := Formula.past ψ)
      (h := fun hφ => hPast hφ) hSome

lemma sometime_congr
    {φ ψ : Formula S}
    (h : ∀ H', (⟨H',p⟩ ⊨[M,σ]φ) ↔
        (⟨H',p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ↕ᶠ φ) ↔
      (⟨H,p⟩ ⊨[M, σ] ↕ᶠ ψ) := by
  classical
  constructor
  · intro hSome
    exact sometime_of_imp (M := M) (σ := σ)
      (H := H) (p := p) (φ := φ) (ψ := ψ)
      (h := fun H' => (h H').1) hSome
  · intro hSome
    exact sometime_of_imp (M := M) (σ := σ)
      (H := H) (p := p) (φ := ψ) (ψ := φ)
      (h := fun H' => (h H').2) hSome

lemma eventuallyPast_of_imp
    {φ ψ : Formula S}
    (h : ∀ H', (⟨H',p⟩ ⊨[M,σ]φ) →
        (⟨H',p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ⇓ᶠ φ) →
      (⟨H,p⟩ ⊨[M, σ] ⇓ᶠ ψ) := by
  classical
  have hNot : ∀ H',
      (⟨H',p⟩ ⊨[M, σ] ¬ᶠ ψ) →
        (⟨H',p⟩ ⊨[M, σ] ¬ᶠ φ) := by
    intro H'
    exact not_of_imp (M := M) (σ := σ) (H := H') (p := p)
      (φ := φ) (ψ := ψ) (h := h H')
  have hPast := past_of_imp (M := M) (σ := σ)
      (H := H) (p := p) (φ := ¬ᶠ ψ) (ψ := ¬ᶠ φ) hNot
  have hNotPast := not_of_imp (M := M) (σ := σ)
      (H := H) (p := p)
      (φ := ↓ᶠ (¬ᶠ ψ)) (ψ := ↓ᶠ (¬ᶠ φ)) hPast
  intro hEv
  simpa [Formula.eventuallyPast]
    using hNotPast
      (by simpa [Formula.eventuallyPast] using hEv)

lemma eventuallyPast_congr
    {φ ψ : Formula S}
    (h : ∀ H', (⟨H',p⟩ ⊨[M,σ]φ) ↔
        (⟨H',p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ⇓ᶠ φ) ↔
      (⟨H,p⟩ ⊨[M, σ] ⇓ᶠ ψ) := by
  classical
  constructor
  · intro hEv
    exact eventuallyPast_of_imp (M := M) (σ := σ)
      (H := H) (p := p) (φ := φ) (ψ := ψ)
      (h := fun H' => (h H').1) hEv
  · intro hEv
    exact eventuallyPast_of_imp (M := M) (σ := σ)
      (H := H) (p := p) (φ := ψ) (ψ := φ)
      (h := fun H' => (h H').2) hEv

lemma alwaysPast_of_imp
    {φ ψ : Formula S}
    (h : ∀ H', (⟨H',p⟩ ⊨[M,σ]φ) →
        (⟨H',p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ⇕ᶠ φ) →
      (⟨H,p⟩ ⊨[M, σ] ⇕ᶠ ψ) := by
  classical
  have hNot : ∀ H',
      (⟨H',p⟩ ⊨[M, σ] ¬ᶠ ψ) →
        (⟨H',p⟩ ⊨[M, σ] ¬ᶠ φ) := by
    intro H'
    exact not_of_imp (M := M) (σ := σ) (H := H') (p := p)
      (φ := φ) (ψ := ψ) (h := h H')
  have hSome := sometime_of_imp (M := M) (σ := σ)
      (H := H) (p := p) (φ := ¬ᶠ ψ) (ψ := ¬ᶠ φ) hNot
  have hNotSome := not_of_imp (M := M) (σ := σ)
      (H := H) (p := p)
      (φ := ↕ᶠ (¬ᶠ ψ)) (ψ := ↕ᶠ (¬ᶠ φ)) hSome
  intro hAlways
  simpa [Formula.alwaysPast]
    using hNotSome
      (by simpa [Formula.alwaysPast] using hAlways)

lemma alwaysPast_congr
    {φ ψ : Formula S}
    (h : ∀ H', (⟨H',p⟩ ⊨[M,σ]φ) ↔
        (⟨H',p⟩ ⊨[M,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] ⇕ᶠ φ) ↔
      (⟨H,p⟩ ⊨[M, σ] ⇕ᶠ ψ) := by
  classical
  constructor
  · intro hAlways
    exact alwaysPast_of_imp (M := M) (σ := σ)
      (H := H) (p := p) (φ := φ) (ψ := ψ)
      (h := fun H' => (h H').1) hAlways
  · intro hAlways
    exact alwaysPast_of_imp (M := M) (σ := σ)
      (H := H) (p := p) (φ := ψ) (ψ := φ)
      (h := fun H' => (h H').2) hAlways

lemma past_not_not_iff
    {φ : Formula S} :
    (⟨H,p⟩ ⊨[M, σ] ↓ᶠ (¬ᶠ (¬ᶠ φ))) ↔
      (⟨H,p⟩ ⊨[M, σ] ↓ᶠ φ) :=
  past_congr (M := M) (σ := σ) (H := H) (p := p)
    (φ := ¬ᶠ (¬ᶠ φ)) (ψ := φ)
    (fun H' => not_not_iff (M := M) (σ := σ)
      (H := H') (p := p) (φ := φ))

lemma eventuallyPast_not_iff
    {φ : Formula S} :
    (⟨H,p⟩ ⊨[M, σ] ⇓ᶠ (¬ᶠ φ)) ↔
      (⟨H,p⟩ ⊨[M, σ] ¬ᶠ (↓ᶠ φ)) := by
  classical
  have hPast := past_not_not_iff (M := M) (σ := σ)
      (H := H) (p := p) (φ := φ)
  have hNot := not_congr (M := M) (σ := σ)
      (H := H) (p := p)
      (φ := ↓ᶠ (¬ᶠ (¬ᶠ φ))) (ψ := ↓ᶠ φ) hPast
  simpa [Formula.eventuallyPast, Formula.not]
    using hNot

lemma box_of_imp
    (ts : List (Term S)) {φ ψ : Formula S}
    (h : ∀ q,
        (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]φ) →
          ⟨H,q⟩ ⊨[M ∣ᵥ H,σ]ψ) :
    (⟨H,p⟩ ⊨[M, σ] □ᶠ[ts] φ) →
      (⟨H,p⟩ ⊨[M, σ] □ᶠ[ts] ψ) := by
  classical
  have hNot : ∀ q,
      (⟨H,q⟩ ⊨[M ∣ᵥ H, σ] ¬ᶠ ψ) →
        (⟨H,q⟩ ⊨[M ∣ᵥ H, σ] ¬ᶠ φ) := by
    intro q
    exact not_of_imp (M := M ∣ᵥ H) (σ := σ) (H := H) (p := q)
      (φ := φ) (ψ := ψ) (h := h q)
  have hDiamond := diamond_of_imp (M := M) (σ := σ)
      (H := H) (ts := ts) (φ := ¬ᶠ ψ) (ψ := ¬ᶠ φ)
      (p := p) (h := hNot)
  intro hBox
  have hNotDiamond := not_of_imp (M := M) (σ := σ)
      (H := H) (p := p)
      (φ := ♢ᶠ[ts] (¬ᶠ ψ))
      (ψ := ♢ᶠ[ts] (¬ᶠ φ)) hDiamond
  have := hNotDiamond (by simpa [Formula.box, Formula.not] using hBox)
  simpa [Formula.box, Formula.not] using this

lemma box_congr
    (ts : List (Term S)) {φ ψ : Formula S}
    (h : ∀ q,
        (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]φ) ↔
          (⟨H,q⟩ ⊨[M ∣ᵥ H,σ]ψ)) :
    (⟨H,p⟩ ⊨[M, σ] □ᶠ[ts] φ) ↔
      (⟨H,p⟩ ⊨[M, σ] □ᶠ[ts] ψ) := by
  classical
  constructor
  · intro hBox
    exact box_of_imp (M := M) (σ := σ)
      (H := H) (ts := ts) (φ := φ) (ψ := ψ)
      (p := p) (h := fun q => (h q).1) hBox
  · intro hBox
    exact box_of_imp (M := M) (σ := σ)
      (H := H) (ts := ts) (φ := ψ) (ψ := φ)
      (p := p) (h := fun q => (h q).2) hBox

lemma diamond_eventuallyPast_not_iff
    (ts : List (Term S)) (φ : Formula S) (p : P) :
    (⟨H,p⟩ ⊨[M, σ]
        ♢ᶠ[ts] (⇓ᶠ (¬ᶠ φ))) ↔
      (⟨H,p⟩ ⊨[M, σ]
        ♢ᶠ[ts] (¬ᶠ (↓ᶠ φ))) :=
  diamond_congr (M := M) (σ := σ) (H := H) (p := p)
    (ts := ts) (φ := ⇓ᶠ (¬ᶠ φ)) (ψ := ¬ᶠ (↓ᶠ φ))
    (fun q => eventuallyPast_not_iff (M := M ∣ᵥ H) (σ := σ)
      (H := H) (p := q) (φ := φ))

lemma boxPast_not_diamondPast_not
    (ts : List (Term S)) (φ : Formula S) (p : P) :
    (⟨H,p⟩ ⊨[M, σ] □ᶠ↓[ts] φ) ↔
      (⟨H,p⟩ ⊨[M, σ]
        ¬ᶠ (♢ᶠ⇓[ts] (¬ᶠ φ))) := by
  classical
  have hDiamond := diamond_congr (M := M) (σ := σ)
      (H := H) (p := p) (ts := ts)
      (φ := ¬ᶠ (↓ᶠ φ)) (ψ := ⇓ᶠ (¬ᶠ φ))
      (h := fun q =>
        (eventuallyPast_not_iff (M := M ∣ᵥ H) (σ := σ)
          (H := H) (p := q) (φ := φ)).symm)
  have hNot := not_congr (M := M) (σ := σ) (H := H)
      (p := p)
      (φ := ♢ᶠ[ts] (¬ᶠ (↓ᶠ φ)))
      (ψ := ♢ᶠ[ts] (⇓ᶠ (¬ᶠ φ))) hDiamond
  constructor
  · intro hBox
    have hImp :
        (⟨H,p⟩ ⊨[M, σ]
          ¬ᶠ (♢ᶠ[ts] (¬ᶠ (↓ᶠ φ)))) :=
      by
        simpa [Formula.boxPast, Formula.box, Formula.not]
          using hBox
    have hRes := (hNot).1 hImp
    simpa [Formula.diamondEventually]
      using hRes
  · intro hNotDiamond
    have hImp :
        (⟨H,p⟩ ⊨[M, σ]
          ¬ᶠ (♢ᶠ[ts] (¬ᶠ (↓ᶠ φ)))) :=
      (hNot).2
        (by
          simpa [Formula.diamondEventually]
            using hNotDiamond)
    simpa [Formula.boxPast, Formula.box, Formula.not]
      using hImp

lemma boxEventually_not_diamondPast_not
    (ts : List (Term S)) (φ : Formula S) (p : P) :
    (⟨H,p⟩ ⊨[M, σ] □ᶠ⇓[ts] φ) ↔
      (⟨H,p⟩ ⊨[M, σ]
        ¬ᶠ (♢ᶠ↓[ts] (¬ᶠ φ))) := by
  classical
  have hDiamond := diamond_congr (M := M) (σ := σ)
      (H := H) (p := p) (ts := ts)
      (φ := ¬ᶠ (⇓ᶠ φ)) (ψ := ↓ᶠ (¬ᶠ φ))
      (h := fun q =>
        by
          have := not_not_iff (M := M ∣ᵥ H) (σ := σ)
            (H := H) (p := q)
            (φ := Formula.past (Formula.not φ))
          simpa [Formula.eventuallyPast, Formula.not]
            using this)
  have hNot := not_congr (M := M) (σ := σ) (H := H)
      (p := p)
      (φ := ♢ᶠ[ts] (¬ᶠ (⇓ᶠ φ)))
      (ψ := ♢ᶠ↓[ts] (¬ᶠ φ)) hDiamond
  constructor
  · intro hBox
    have hExpand :
        (⟨H,p⟩ ⊨[M, σ] ¬ᶠ
          (♢ᶠ[ts] (¬ᶠ (⇓ᶠ φ)))) := by
      simpa [Formula.boxEventually, Formula.box,
        Formula.eventuallyPast, Formula.not, Sat]
        using hBox
    exact (hNot).1 hExpand
  · intro hNotDiamond
    have hExpand :
        (⟨H,p⟩ ⊨[M, σ] ¬ᶠ
          (♢ᶠ[ts] (¬ᶠ (⇓ᶠ φ)))) :=
      (hNot).2 hNotDiamond
    simpa [Formula.boxEventually, Formula.box,
      Formula.eventuallyPast, Formula.not, Sat]
      using hExpand

lemma diamondPast_not_boxEventually_not
    (ts : List (Term S)) (φ : Formula S) (p : P) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ↓[ts] φ) ↔
      (⟨H,p⟩ ⊨[M, σ]
        ¬ᶠ (□ᶠ⇓[ts] (¬ᶠ φ))) := by
  classical
  have hBox :=
    boxEventually_not_diamondPast_not (M := M) (σ := σ) (H := H)
      (ts := ts) (φ := ¬ᶠ φ) (p := p)
  have hNot :=
    Sat.not_congr (M := M) (σ := σ) (H := H) (p := p) hBox
  have hDouble :=
    Sat.not_not_iff (M := M) (σ := σ) (H := H) (p := p)
      (φ := ♢ᶠ↓[ts] (¬ᶠ (¬ᶠ φ)))
  have hPast :=
    Sat.diamond_congr (M := M) (σ := σ) (H := H) (p := p) (ts := ts)
      (φ := ↓ᶠ (¬ᶠ (¬ᶠ φ))) (ψ := ↓ᶠ φ)
      (fun q =>
        Sat.past_congr (M := M ∣ᵥ H) (σ := σ) (H := H) (p := q)
          (φ := ¬ᶠ (¬ᶠ φ)) (ψ := φ)
          (fun H' =>
            Sat.not_not_iff (M := M ∣ᵥ H) (σ := σ)
              (H := H') (p := q) (φ := φ)))
  have hFinal := (hNot.trans hDouble).trans hPast
  exact hFinal.symm

lemma diamondEventually_not_boxPast_not
    (ts : List (Term S)) (φ : Formula S) (p : P) :
    (⟨H,p⟩ ⊨[M, σ] ♢ᶠ⇓[ts] φ) ↔
      (⟨H,p⟩ ⊨[M, σ]
        ¬ᶠ (□ᶠ↓[ts] (¬ᶠ φ))) := by
  classical
  have hBox :=
    boxPast_not_diamondPast_not (M := M) (σ := σ) (H := H)
      (ts := ts) (φ := ¬ᶠ φ) (p := p)
  have hNot :=
    Sat.not_congr (M := M) (σ := σ) (H := H) (p := p) hBox
  have hDouble :=
    Sat.not_not_iff (M := M) (σ := σ) (H := H) (p := p)
      (φ := ♢ᶠ⇓[ts] (¬ᶠ (¬ᶠ φ)))
  have hEv :=
    Sat.diamond_congr (M := M) (σ := σ) (H := H) (p := p) (ts := ts)
      (φ := ⇓ᶠ (¬ᶠ (¬ᶠ φ))) (ψ := ⇓ᶠ φ)
      (fun q =>
        Sat.eventuallyPast_congr (M := M ∣ᵥ H) (σ := σ)
          (H := H) (p := q)
          (φ := ¬ᶠ (¬ᶠ φ)) (ψ := φ)
          (fun H' =>
            Sat.not_not_iff (M := M ∣ᵥ H) (σ := σ)
              (H := H') (p := q) (φ := φ)))
  have hFinal := (hNot.trans hDouble).trans hEv
  exact hFinal.symm

end Sat

/-- End-of-time validity (Definition 3.4.1 / Figure 3). -/
@[simp] def EndValid
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (φ : Formula S) : Prop :=
  ∀ p : P,
    ⟨M.history,p⟩ ⊨[M,σ]φ

notation:55 "⊨[" M "," σ "]" φ =>
  EndValid M σ φ

/-- End-of-time validity implies satisfaction for all participants. -/
lemma EndValid.exists
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (φ : Formula S) :
    (⊨[M,σ]φ) →
      ∀ p, ⟨M.history,p⟩ ⊨[M,σ]φ := by
  intro h
  exact h

lemma EndValid.of_imp
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) {φ ψ : Formula S}
    (h : ∀ p, (⟨M.history,p⟩ ⊨[M,σ]φ) →
        (⟨M.history,p⟩ ⊨[M,σ]ψ)) :
    (⊨[M,σ]φ) → (⊨[M,σ]ψ) := by
  classical
  intro hφ p
  exact h p (hφ p)

lemma EndValid.congr
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) {φ ψ : Formula S}
    (h : ∀ p, (⟨M.history,p⟩ ⊨[M,σ]φ) ↔
        (⟨M.history,p⟩ ⊨[M,σ]ψ)) :
    (⊨[M,σ]φ) ↔ (⊨[M,σ]ψ) := by
  classical
  constructor
  · intro hφ
    exact EndValid.of_imp (M := M) (σ := σ)
      (φ := φ) (ψ := ψ) (h := fun p => (h p).1) hφ
  · intro hψ
    exact EndValid.of_imp (M := M) (σ := σ)
      (φ := ψ) (ψ := φ) (h := fun p => (h p).2) hψ

/-- Event-driven validity (Definition 3.4.1 / Figure 3). -/
@[simp] def EventValid
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (φ : Formula S) : Prop :=
  ∀ {t : EventTuple P (Signature.EventType S)}
    (ht : t ∈ M.history.val),
      let h_before : PreHistory.happensBefore
          (P := P) (Event := Signature.EventType S)
          t.2.2 M.history.val := ⟨t.1, t.2.1, ht⟩
      let h_hered :=
        (History.predecessor_data (P := P)
          (Event := Signature.EventType S)
          (H := M.history) (h_before := h_before)).2
      let Hloc : History P (Signature.EventType S) :=
        ⟨t.2.2, h_hered⟩
      ⟨Hloc, t.1⟩ ⊨[M,σ]φ

notation:55 "□⇓⊨[" M "," σ "]" φ =>
  EventValid M σ φ

/-- Active participant predicate (Definition 3.5.1). -/
@[simp] def IsActive
    (M : ModalDistribution.Model S P)
    (H : History P (Signature.EventType S))
    (p : P) : Prop :=
  ∃ (H' : History P (Signature.EventType S)),
      (H'.val ≺ₚ[p] M.history.val) ∧
      (H'.val ⊆trn H.val)

lemma isActive_of_mem_history
    (M : ModalDistribution.Model S P)
    {p : P}
    {evt : MaybeEvent (Signature.EventType S)}
    {H' : PreHistory P (Signature.EventType S)}
    (hMem : (p, evt, H') ∈ M.history.val) :
    IsActive M M.history p := by
  classical
  have hBefore : H' ≺ₚ[p] M.history.val :=
    (PreHistory.happensBeforeAt_of_mem (P := P)
      (Event := Signature.EventType S) hMem)
  have hSubset : H' ⊆ M.history.val :=
    (History.transitive (P := P) (Event := Signature.EventType S) M.history)
      H' ⟨p, evt, hMem⟩
  have hHered : isHereditarilyTransitive (P := P)
      (Event := Signature.EventType S) H' :=
    isHereditarilyTransitive.desc
      (History.hereditarilyTransitive
        (P := P) (Event := Signature.EventType S) M.history)
      ⟨p, evt, hMem⟩
  refine ⟨⟨H', hHered⟩, ?_, ?_⟩
  · simpa using hBefore
  · exact ⟨hSubset, hHered⟩

lemma history_ne_empty_of_isActive
    (M : ModalDistribution.Model S P)
    {p : P}
    (h : IsActive M M.history p) :
    M.history.val ≠ PreHistory.empty := by
  classical
  intro hEmpty
  rcases h with ⟨H', hBefore, _⟩
  rcases (PreHistory.happensBeforeAt_iff.mp hBefore) with ⟨evt, hMem⟩
  have : False := by simp [hEmpty] at hMem
  exact this

lemma exists_active_of_history_ne_empty
    (M : ModalDistribution.Model S P)
    (hne : M.history.val ≠ PreHistory.empty) :
    ∃ p : P,
      IsActive M M.history p := by
  classical
  cases hHistory : M.history.val with
  | mk l =>
      cases l with
      | nil =>
          have : M.history.val = PreHistory.empty := by
            simp [hHistory, PreHistory.empty]
          exact (hne this).elim
      | cons t tl =>
          rcases t with ⟨p, evt, H'⟩
          have hMem : (p, evt, H') ∈ M.history.val := by
            simp [hHistory]
          exact ⟨p, isActive_of_mem_history (M := M) hMem⟩

/-- Lemma 3.5.3 in the paper. -/
theorem active_iff_past_top
    (M : ModalDistribution.Model S P)
    [DecidableEq S.VarSymb]
    (p : P) (σ : Assignment S) :
    IsActive M M.history p ↔
      (⟨M.history,p⟩ ⊨[M, σ] ↓ᶠ ⊤ᶠ) := by
  classical
  constructor
  · intro hActive
    rcases hActive with ⟨H', hBefore, _⟩
    have hWitness :
        ∃ H' : History P (Signature.EventType S),
          (H'.val ≺ₚ[p] M.history.val) ∧ True := by
      exact ⟨H', ⟨hBefore, trivial⟩⟩
    simpa [Sat, Formula.top] using hWitness
  · intro hPast
    have hPast' :
        ∃ H' : History P (Signature.EventType S),
          (H'.val ≺ₚ[p] M.history.val) ∧ True := by
      simpa [Sat, Formula.top] using hPast
    rcases hPast' with ⟨H', hBefore, _⟩
    refine ⟨H', hBefore, ?_⟩
    exact happensBeforeAt_implies_transitiveSubset H' M.history p hBefore

end Logic
end ModalDistribution
