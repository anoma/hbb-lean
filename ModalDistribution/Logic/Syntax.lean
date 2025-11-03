import Mathlib.Data.Finset.Basic
import ModalDistribution.Core.Model

open Lean

/-!
# Modal logic syntax

This file introduces the syntactic objects for the modal logic developed in
Modal logic syntax. terms are
built from variable symbols and values, while formulas provide propositional
connectives, equality, quantification, event and predicate atoms, the temporal
modalities `↓` (in the past) and `⤒` (at the end of time), the quorum
intersection modality `♢`, and the distinguished sequentiality predicate `seq`.

## Symbol reference

The constructors and scoped notations in this module realise
The syntax and satisfaction clauses in
the semantics.  The bullets record the
correspondence between Lean identifiers or notations and the LaTeX glyphs used
throughout the paper.

* `Term.var` ↔ the variable symbol `a` range.
* `Term.value` ↔ the value literal `v`.
* `Formula.bot` / notation `⊥ᶠ` ↔ `\tbot`.
* `Formula.top` / notation `⊤ᶠ` ↔ `\ttop`.
* `Formula.imp` / notation `φ ⇒ᶠ ψ` ↔ `\timp`.
* `Formula.eq` / notation `t ≃ᶠ t'` ↔ `t\teq t'`.
* `Formula.forall` / notation `∀ᶠ a, φ` ↔ `\tall a.\,φ`.
* `Formula.exists_` / notation `∃ᶠ a, φ` ↔ `\texi a.\,φ`.
* `Formula.not` / notation `¬ᶠ φ` ↔ `\tneg φ`.
* `Formula.and` / notation `φ ∧ᶠ ψ` ↔ `\tand`.
* `Formula.or` / notation `φ ∨ᶠ ψ` ↔ `\tor`.
* `Formula.iff` / notation `φ ⇔ᶠ ψ` ↔ `\tiff`.
* `Formula.event` (and `event0`, `ofEvent`) ↔ `\tf E(t_1,\dots,t_n)`.
* `Formula.predicate` (and `predicate0`, `ofPredicate`) ↔ `\tf P(t_1,\dots,t_n)`.
* `Formula.past` / notation `↓ᶠ φ` ↔ `\itp φ` (``in the past'').
* `Formula.atEnd` / notation `⤒ᶠ φ` ↔ `\EOT φ` (``at the end of time'').
* `Formula.sometime` / notation `↕ᶠ φ` ↔ `\sometime φ`.
* `Formula.alwaysPast` / notation `⇕ᶠ φ` ↔ `\everytime φ`.
* `Formula.eventuallyPast` / notation `⇓ᶠ φ` ↔ `\allitp φ`.
* `Formula.diamond ls φ` / notation `♢ᶠ[ls] φ` ↔ `\ate{l_1\dots l_n}\phi`.
* `Formula.diamondPast ls φ` / notation `♢ᶠ↓[ls] φ` ↔ `\atedot{l_1\dots l_n}\phi`.
* `Formula.diamondEventually ls φ` / notation `♢ᶠ⇓[ls] φ` ↔ `\atecirc{l_1\dots l_n}\phi`.
* `Formula.diamondEmpty φ` / notation `♢ᶠ[] φ` ↔ `\ate{}\phi`.
* `Formula.box ls φ` / notation `□ᶠ[ls] φ` ↔ `\atd{l_1\dots l_n}\phi`.
* `Formula.boxPast ls φ` / notation `□ᶠ↓[ls] φ` ↔ `\atddot{l_1\dots l_n}\phi`.
* `Formula.boxEventually ls φ` / notation `□ᶠ⇓[ls] φ` ↔ `\atdcirc{l_1\dots l_n}\phi`.
* `Formula.boxEmpty φ` / notation `□ᶠ[] φ` ↔ `\atd{}\phi`.
* `Formula.seq` ↔ the distinguished predicate `\tf{seq}`.
* `World.accessible` / notation `t' ≪ t` ↔ `\accessible` .
* `World.accessibleLe` / notation `t' ≪⁻ t` ↔ `\accessible^{-}` .

> **Validity notation warning.**  The paper uses three related validity
> judgements (`\aworld\mentHφ`, `\mentHφ`, `\alltimeplace\mentHφ`).  In this
> formalisation they correspond to different Lean notations:
> `⟪w⟫ ⊨[M] φ` for local/world satisfaction, `⊨[M] φ` for end-of-time
> validity, and `□W⊨[M] φ` for all-world validity.  Picking the wrong one
> changes a statement’s meaning, so double-check which modality the paper
> uses before translating it.

## References

* Modal logic syntax and semantics.
-/

namespace ModalDistribution
namespace Logic

open ModalDistribution

set_option autoImplicit false

-- For HOAS to work without universe issues, we fix everything at Type 0.
-- This is acceptable since in practice all symbol and value types are finite.
variable {S : Signature.{0, 0, 0}}

/-- Event atoms `E(v₁,…,vₙ)`. -/
structure EventAtom (S : Signature.{0, 0, 0}) where
  sym : S.EventSymb
  args : List S.Value

/-- Predicate atoms `P(v₁,…,vₙ)`. -/
structure PredicateAtom (S : Signature.{0, 0, 0}) where
  sym : S.PredSymb
  args : List S.Value

/-- Modal formulas with HOAS quantifiers. -/
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

/-- Convenience: the always-true formula `⊤`. -/
def top : Formula S := .imp .bot .bot

def not (φ : Formula S) : Formula S :=
  .imp φ .bot

/-- Conjunction. -/
def and (φ ψ : Formula S) : Formula S :=
  not (.imp φ (not ψ))

/-- Disjunction. -/
def or (φ ψ : Formula S) : Formula S :=
  .imp (not φ) ψ

/-- Bi-implication. -/
def iff (φ ψ : Formula S) : Formula S :=
  and (.imp φ ψ) (.imp ψ φ)

/-- Existential quantification. -/
def exists_ (body : S.Value → Formula S) : Formula S :=
  not (.forall (fun v => not (body v)))

/-- Sometimes modality (`↕`) specialised to the current participant; sugar for `⤒↓`. -/
def sometime (φ : Formula S) : Formula S :=
  .atEnd (.past φ)

/-- Always in the past (`⇕`). -/
def alwaysPast (φ : Formula S) : Formula S :=
  not (sometime (not φ))

/-- Eventually in the past (`⇓`). -/
def eventuallyPast (φ : Formula S) : Formula S :=
  not (.past (not φ))

/-- Box modality. -/
def box (ls : List S.Value) (φ : Formula S) : Formula S :=
  not (.diamond ls (not φ))

/-- Diamond with past guard. -/
def diamondPast (ls : List S.Value) (φ : Formula S) : Formula S :=
  .diamond ls (.past φ)

/-- Diamond with eventual past guard. -/
def diamondEventually (ls : List S.Value) (φ : Formula S) : Formula S :=
  .diamond ls (eventuallyPast φ)

/-- Diamond with empty learner list. -/
@[simp] def diamondEmpty (φ : Formula S) : Formula S :=
  .diamond [] φ

/-- Box with past guard. -/
def boxPast (ls : List S.Value) (φ : Formula S) : Formula S :=
  box ls (.past φ)

/-- Box with eventual past guard. -/
def boxEventually (ls : List S.Value) (φ : Formula S) : Formula S :=
  box ls (Formula.eventuallyPast φ)

/-- Box over the empty learner list. -/
@[simp] def boxEmpty (φ : Formula S) : Formula S :=
  box [] φ

/-- Helpful notation for implication in modal formulas. -/
scoped infixr:60 " ⇒ᶠ " => Formula.imp

/-- Helpful notation for bottom in modal formulas. -/
scoped notation "⊥ᶠ" => Formula.bot

/-- Helpful notation for top in modal formulas. -/
scoped notation "⊤ᶠ" => Formula.top

/-- Helpful notation for equality in modal formulas. -/
scoped infix:55 " ≃ᶠ " => Formula.eq

/-- Helpful notation for universal quantification in modal formulas (HOAS style). -/
scoped notation "∀ᶠ " body => Formula.forall body

/-- Helpful notation for the past modality. -/
scoped notation "↓ᶠ " φ => Formula.past φ

/-- Helpful notation for the end-of-time modality. -/
scoped notation "⤒ᶠ" φ => Formula.atEnd φ

/-- Helpful notation for the quorum intersection modality. -/
scoped notation "♢ᶠ[" ls "]" φ => Formula.diamond ls φ

/-- Helpful notation for the box modality. -/
scoped notation "□ᶠ[" ls "]" φ => Formula.box ls φ

/-- Helpful notation for logical negation. -/
scoped notation "¬ᶠ" φ => Formula.not φ

/-- Helpful notation for conjunction. -/
scoped infixl:65 " ∧ᶠ " => Formula.and

/-- Helpful notation for disjunction. -/
scoped infixl:60 " ∨ᶠ " => Formula.or

/-- Helpful notation for bi-implication. -/
scoped infix:55 " ⇔ᶠ " => Formula.iff

/-- Helpful notation for existential quantification (HOAS style). -/
scoped notation "∃ᶠ " body => Formula.exists_ body

/-- At-most-one quantifier `∃≤₁` (HOAS version).
    ∃≤₁ x. φ(x) means "for all x, y. φ(x) → φ(y) → x = y" -/
def existsAtMostOne (body : S.Value → Formula S) : Formula S :=
  .forall fun x =>
    .forall fun y =>
      .imp (body x) (.imp (body y) (.eq x y))

/-- Exact-one quantifier `∃!` (HOAS version). -/
def existsUnique (body : S.Value → Formula S) : Formula S :=
  .and
    (existsAtMostOne body)
    (.exists_ body)

/-- Notation `∃≤ᶠ1` (simplified - single binder). -/
scoped syntax (name := existsAtMostOneNotation)
  "∃≤ᶠ1 " ident " ↦ " term : term

macro_rules
  | `(∃≤ᶠ1 $boundVar ↦ $body) =>
      `(Formula.existsAtMostOne (fun $boundVar => $body))

/-- Notation `∃!ᶠ` (simplified - single binder). -/
scoped syntax (name := existsUniqueNotation)
  "∃!ᶠ " ident " ↦ " term : term

macro_rules
  | `(∃!ᶠ $boundVar ↦ $body) =>
      `(Formula.existsUnique (fun $boundVar => $body))

/-- Helpful notation for the past-eventually modality. -/
scoped notation "⇓ᶠ" φ => Formula.eventuallyPast φ

/-- Helpful notation for the always-in-the-past modality. -/
scoped notation "⇕ᶠ" φ => Formula.alwaysPast φ

/-- Helpful notation for the sometime modality. -/
scoped notation "↕ᶠ" φ => Formula.sometime φ

/-- Helpful notation for the past diamond. -/
scoped notation "♢ᶠ↓[" ls "]" φ => Formula.diamondPast ls φ

/-- Helpful notation for the eventual past diamond. -/
scoped notation "♢ᶠ⇓[" ls "]" φ => Formula.diamondEventually ls φ

/-- Helpful notation for the empty diamond. -/
scoped notation "♢ᶠ[]" φ => Formula.diamondEmpty φ

/-- Helpful notation for the past box. -/
scoped notation "□ᶠ↓[" ls "]" φ => Formula.boxPast ls φ

/-- Helpful notation for the eventual past box. -/
scoped notation "□ᶠ⇓[" ls "]" φ => Formula.boxEventually ls φ

/-- Helpful notation for the empty box. -/
scoped notation "□ᶠ[]" φ => Formula.boxEmpty φ

/-- Convenience for nullary predicates. -/
@[simp] def predicate0 (sym : S.PredSymb) : Formula S :=
  .predicate ⟨sym, []⟩

/-- Convenience for nullary events. -/
@[simp] def event0 (sym : S.EventSymb) : Formula S :=
  .event ⟨sym, []⟩

/-- Promote an event from the signature to a formula. -/
def ofEvent (E : Signature.EventType S) : Formula S :=
  .event ⟨E.sym, E.args⟩

/-- Promote an atomic predicate from the signature to a formula. -/
def ofPredicate (P : Signature.AtomicPredType S) : Formula S :=
  .predicate ⟨P.sym, P.args⟩

end Formula
end Logic
end ModalDistribution
