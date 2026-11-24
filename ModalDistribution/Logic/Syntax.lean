import ModalDistribution.Core.Model

open Lean

/-!
# Modal logic syntax

This file introduces the syntactic objects of the paper's modal logic. Terms are
built from variable symbols and values, while formulas provide propositional
connectives, equality, quantification, event and predicate atoms, the temporal
modalities `↓` (in the past) and `⤒` (at the end of time), the quorum
intersection modality `♢`, and the distinguished sequentiality predicate `seq`.

## Symbol reference

The constructors and scoped notations in this module realise the paper's
syntax of predicates (Definition 3.1.3) and its derived connectives. The
bullets record the correspondence between Lean identifiers or notations and the
symbols used throughout the paper.

* `Term.var` ↔ a variable symbol `a`.
* `Term.value` ↔ a value literal `v`.
* `Formula.bot` / notation `⊥ᶠ` ↔ `⊥`.
* `Formula.top` / notation `⊤ᶠ` ↔ `⊤`.
* `Formula.imp` / notation `φ ⇒ᶠ ψ` ↔ `φ ⇒ ψ`.
* `Formula.eq` / notation `t ≃ᶠ t'` ↔ `t = t'`.
* `Formula.forall` / notation `∀ᶠ a, φ` ↔ `∀ a.φ`.
* `Formula.exists_` / notation `∃ᶠ a, φ` ↔ `∃ a.φ`.
* `Formula.not` / notation `¬ᶠ φ` ↔ `¬φ`.
* `Formula.and` / notation `φ ∧ᶠ ψ` ↔ `φ ∧ ψ`.
* `Formula.or` / notation `φ ∨ᶠ ψ` ↔ `φ ∨ ψ`.
* `Formula.iff` / notation `φ ⇔ᶠ ψ` ↔ `φ ⇔ ψ`.
* `Formula.event` (and `event0`, `ofEvent`) ↔ `E(t₁,…,tₙ)`.
* `Formula.predicate` (and `predicate0`, `ofPredicate`) ↔ `P(t₁,…,tₙ)`.
* `Formula.past` / notation `↓ᶠ φ` ↔ `↓φ` (in the past).
* `Formula.atEnd` / notation `⤒ᶠ φ` ↔ `⤒φ` (at the end of time).
* `Formula.sometime` / notation `↕ᶠ φ` ↔ `↕φ` (sometime).
* `Formula.everytime` / notation `⇕ᶠ φ` ↔ `⇕φ` (everytime).
* `Formula.allPast` / notation `⇓ᶠ φ` ↔ `⇓φ` (at every past event).
* `Formula.diamond ls φ` / notation `♢ᶠ[ls] φ` ↔ `♢_{l₁…lₙ} φ`.
* `Formula.diamondPast ls φ` / notation `♢ᶠ↓[ls] φ` ↔ `♢↓_{l₁…lₙ} φ`.
* `Formula.diamondAllPast ls φ` / notation `♢ᶠ⇓[ls] φ` ↔ `♢⇓_{l₁…lₙ} φ`.
* `Formula.diamondEmpty φ` / notation `♢ᶠ[] φ` ↔ `♢ φ` (no learners).
* `Formula.box ls φ` / notation `□ᶠ[ls] φ` ↔ `□_{l₁…lₙ} φ`.
* `Formula.boxPast ls φ` / notation `□ᶠ↓[ls] φ` ↔ `□↓_{l₁…lₙ} φ`.
* `Formula.boxAllPast ls φ` / notation `□ᶠ⇓[ls] φ` ↔ `□⇓_{l₁…lₙ} φ`.
* `Formula.boxEmpty φ` / notation `□ᶠ[] φ` ↔ `□ φ` (no learners).
* `Formula.seq` ↔ the distinguished predicate `seq`.
* `World.Accessible` / notation `t' ≪ t` ↔ `t' ≪ t`.
* `World.AccessibleLe` / notation `t' ≪⁻ t` ↔ `t' ≪⁻ t`.

> **Validity notation warning.**  The paper uses three related validity
> judgements (`w ⊨ φ`, `⊨ φ`, `□W ⊨ φ`).  In this
> formalisation they correspond to different Lean notations:
> `⟪w⟫ ⊨[M] φ` for local/world satisfaction, `⊨[M] φ` for end-of-time
> validity, and `□W⊨[M] φ` for all-world validity.  Picking the wrong one
> changes a statement’s meaning, so double-check which modality the paper
> uses before translating it.

## References

* Paper: Definition 3.1.3 (syntax of predicates) and Definition 3.4.10 (validity).
-/

namespace ModalDistribution
namespace Logic

open ModalDistribution

set_option autoImplicit false

-- For HOAS to work without universe issues, we fix everything at Type 0.
-- This is acceptable since in practice all symbol and value types are finite.
variable {S : Signature.{0, 0, 0}}

/-- Paper: Figure 3 (event atoms). Event atoms `E(v₁,…,vₙ)`. -/
structure EventAtom (S : Signature.{0, 0, 0}) where
  sym : S.EventSymb
  args : List S.Value

/-- Paper: Figure 3 (predicate atoms). Predicate atoms `P(v₁,…,vₙ)`. -/
structure PredicateAtom (S : Signature.{0, 0, 0}) where
  sym : S.PredSymb
  args : List S.Value

/-- Paper: Definition 3.1.3 / Figure 3 (syntax of predicates). Modal formulas with HOAS
quantifiers. -/
inductive Formula (S : Signature.{0, 0, 0}) : Type 1 where
  | bot : Formula S
  | imp : Formula S → Formula S → Formula S
  | eq : S.Value → S.Value → Formula S
  | forall : (S.Value → Formula S) → Formula S
  | event : EventAtom S → Formula S
  | predicate : PredicateAtom S → Formula S
  | past : Formula S → Formula S
  | atEnd : Formula S → Formula S
  | diamond : List S.Value → Formula S → Formula S
  | seq : Formula S

namespace Formula

/-- Paper: Figure 5 sugar (⊤). The always-true formula `⊥ ⇒ ⊥`. -/
def top : Formula S := .imp .bot .bot

/-- Paper: Figure 5 sugar (¬). Negation `φ ⇒ ⊥`. -/
def not (φ : Formula S) : Formula S :=
  .imp φ .bot

/-- Paper: Figure 5 sugar (∧). Conjunction. -/
def and (φ ψ : Formula S) : Formula S :=
  not (.imp φ (not ψ))

/-- Paper: Figure 5 sugar (∨). Disjunction. -/
def or (φ ψ : Formula S) : Formula S :=
  .imp (not φ) ψ

/-- Paper: Figure 5 sugar (⇔). Bi-implication. -/
def iff (φ ψ : Formula S) : Formula S :=
  and (.imp φ ψ) (.imp ψ φ)

/-- Paper: Figure 5 sugar (∃). Existential quantification. -/
def exists_ (body : S.Value → Formula S) : Formula S :=
  not (.forall (fun v => not (body v)))

/-- Paper: Figure 5 sugar (↕). Sometime: `φ` holds at some event of the current participant;
sugar for `⤒↓`. -/
def sometime (φ : Formula S) : Formula S :=
  .atEnd (.past φ)

/-- Paper: Figure 5 sugar (⇕). Everytime: `φ` holds at every event of the current
participant; sugar for `¬↕¬`. -/
def everytime (φ : Formula S) : Formula S :=
  not (sometime (not φ))

/-- Paper: Figure 5 sugar (⇓). At every past event of the current participant; sugar for
`¬↓¬`. -/
def allPast (φ : Formula S) : Formula S :=
  not (.past (not φ))

/-- Paper: Figure 5 sugar (□ l₁…lₙ). Box modality; sugar for `¬♢¬`. -/
def box (ls : List S.Value) (φ : Formula S) : Formula S :=
  not (.diamond ls (not φ))

/-- Paper: Figure 5 sugar (♢↓). `♢(↓φ)`. -/
def diamondPast (ls : List S.Value) (φ : Formula S) : Formula S :=
  .diamond ls (.past φ)

/-- Paper: Figure 5 sugar (♢⇓). `♢(⇓φ)`. -/
def diamondAllPast (ls : List S.Value) (φ : Formula S) : Formula S :=
  .diamond ls (allPast φ)

/-- Diamond with empty learner list. -/
@[simp] def diamondEmpty (φ : Formula S) : Formula S :=
  .diamond [] φ

/-- Paper: Figure 5 sugar (□↓). `□(↓φ)`. -/
def boxPast (ls : List S.Value) (φ : Formula S) : Formula S :=
  box ls (.past φ)

/-- Paper: Figure 5 sugar (□⇓). `□(⇓φ)`. -/
def boxAllPast (ls : List S.Value) (φ : Formula S) : Formula S :=
  box ls (Formula.allPast φ)

/-- Box over the empty learner list. -/
@[simp] def boxEmpty (φ : Formula S) : Formula S :=
  box [] φ

/-- Notation for implication in modal formulas. -/
scoped infixr:60 " ⇒ᶠ " => Formula.imp

/-- Notation for bottom in modal formulas. -/
scoped notation "⊥ᶠ" => Formula.bot

/-- Notation for top in modal formulas. -/
scoped notation "⊤ᶠ" => Formula.top

/-- Notation for equality in modal formulas. -/
scoped infix:55 " ≃ᶠ " => Formula.eq

/-- Notation for universal quantification in modal formulas (HOAS style). -/
scoped notation "∀ᶠ " body => Formula.forall body

/-- Notation for the past modality. -/
scoped notation "↓ᶠ " φ => Formula.past φ

/-- Notation for the end-of-time modality. -/
scoped notation "⤒ᶠ" φ => Formula.atEnd φ

/-- Notation for the quorum intersection modality. -/
scoped notation "♢ᶠ[" ls "]" φ => Formula.diamond ls φ

/-- Notation for the box modality. -/
scoped notation "□ᶠ[" ls "]" φ => Formula.box ls φ

/-- Notation for logical negation. -/
scoped notation "¬ᶠ" φ => Formula.not φ

/-- Notation for conjunction. -/
scoped infixl:65 " ∧ᶠ " => Formula.and

/-- Notation for disjunction. -/
scoped infixl:60 " ∨ᶠ " => Formula.or

/-- Notation for bi-implication. -/
scoped infix:55 " ⇔ᶠ " => Formula.iff

/-- Notation for existential quantification (HOAS style). -/
scoped notation "∃ᶠ " body => Formula.exists_ body

/-- Paper: Figure 5 sugar (∃≤1). At-most-one quantifier `∃≤₁` (HOAS version).
    ∃≤₁ x. φ(x) means "for all x, y. φ(x) → φ(y) → x = y" -/
def existsAtMostOne (body : S.Value → Formula S) : Formula S :=
  .forall fun x =>
    .forall fun y =>
      .imp (body x) (.imp (body y) (.eq x y))

/-- Paper: Figure 5 sugar (∃=1). Exact-one quantifier `∃!` (HOAS version). -/
def existsUnique (body : S.Value → Formula S) : Formula S :=
  .and
    (existsAtMostOne body)
    (.exists_ body)

/-- Notation `∃≤ᶠ1 x ↦ φ` for `Formula.existsAtMostOne` (one binder). -/
scoped syntax (name := existsAtMostOneNotation)
  "∃≤ᶠ1 " ident " ↦ " term : term

macro_rules
  | `(∃≤ᶠ1 $boundVar ↦ $body) =>
      `(Formula.existsAtMostOne (fun $boundVar => $body))

/-- Notation `∃!ᶠ x ↦ φ` for `Formula.existsUnique` (one binder). -/
scoped syntax (name := existsUniqueNotation)
  "∃!ᶠ " ident " ↦ " term : term

macro_rules
  | `(∃!ᶠ $boundVar ↦ $body) =>
      `(Formula.existsUnique (fun $boundVar => $body))

/-- Notation for `Formula.allPast` (at every past event). -/
scoped notation "⇓ᶠ" φ => Formula.allPast φ

/-- Notation for `Formula.everytime`. -/
scoped notation "⇕ᶠ" φ => Formula.everytime φ

/-- Notation for `Formula.sometime`. -/
scoped notation "↕ᶠ" φ => Formula.sometime φ

/-- Notation for the past diamond. -/
scoped notation "♢ᶠ↓[" ls "]" φ => Formula.diamondPast ls φ

/-- Notation for `Formula.diamondAllPast`. -/
scoped notation "♢ᶠ⇓[" ls "]" φ => Formula.diamondAllPast ls φ

/-- Notation for the empty diamond. -/
scoped notation "♢ᶠ[]" φ => Formula.diamondEmpty φ

/-- Notation for the past box. -/
scoped notation "□ᶠ↓[" ls "]" φ => Formula.boxPast ls φ

/-- Notation for `Formula.boxAllPast`. -/
scoped notation "□ᶠ⇓[" ls "]" φ => Formula.boxAllPast ls φ

/-- Notation for the empty box. -/
scoped notation "□ᶠ[]" φ => Formula.boxEmpty φ

/-- Convenience for nullary predicates. -/
@[simp] def predicate0 (sym : S.PredSymb) : Formula S :=
  .predicate ⟨sym, []⟩

/-- Promote an event from the signature to an event atom. -/
def ofEvent (E : Signature.EventType S) : Formula S :=
  .event ⟨E.sym, E.args⟩

/-- Promote an atomic predicate from the signature to a formula. -/
def ofPredicate (P : Signature.AtomicPredType S) : Formula S :=
  .predicate ⟨P.sym, P.args⟩

end Formula
end Logic
end ModalDistribution
