import Mathlib.Data.Finset.Basic
import ModalDistribution.Core.Model

/-!
# Modal logic syntax

This file introduces the syntactic objects for the modal logic developed in
Section 3 of the HBB paper.  We follow Figure 2 (Definition 3.1.3): terms are
built from variable symbols and values, while formulas provide propositional
connectives, equality, quantification, event and predicate atoms, the temporal
modalities `↓` (in the past) and `⤒` (at the end of time), the quorum
intersection modality `♢`, and the distinguished sequentiality predicate `seq`.

## Symbol reference

The constructors and scoped notations in this module realise
Figure~\ref{fig.syntax} (syntax) and the satisfaction clauses in
Figure~\ref{fig.valid} (semantics) of `paper.txt`.  The bullets record the
correspondence between Lean identifiers or notations and the LaTeX glyphs used
throughout the paper.

* `Term.var` ↔ the variable symbol `a` range in Figure~\ref{fig.syntax}.
* `Term.value` ↔ the value literal `v` in Figure~\ref{fig.syntax}.
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

## References

* Definition 3.1.3 in the HBB paper.
-/

namespace ModalDistribution
namespace Logic

open ModalDistribution

set_option autoImplicit false

universe u₁ u₂ u₃ u₄ u₅

variable {S : Signature}

/-- Variable assignments map symbols to values. -/
abbrev Assignment (S : Signature) := S.VarSymb → S.Value

/-- Definition 3.1.3: terms consist of variable symbols and values. -/
inductive Term (S : Signature) where
  | var : S.VarSymb → Term S
  | value : S.Value → Term S

namespace Term

variable {σ τ : Assignment S}

/-- Evaluate a term with respect to a variable assignment. -/
@[simp] def eval (σ : Assignment S) : Term S → S.Value
  | .var a => σ a
  | .value v => v

/-- Evaluate a list of terms componentwise. -/
@[simp] def evalList (σ : Assignment S) (ts : List (Term S)) :
    List (Signature.Value S) :=
  ts.map (eval (S := S) σ)

/-- Promote a value to a nullary term. -/
@[simp] def ofValue (v : Signature.Value S) : Term S := .value v

/-- Turn a list of values into a list of value-terms. -/
@[simp] def ofValues (vals : List (Signature.Value S)) : List (Term S) :=
  vals.map ofValue

@[simp] lemma evalList_nil (σ : Assignment S) :
    evalList (S := S) σ [] = [] := rfl

@[simp] lemma evalList_cons (σ : Assignment S) (t : Term S)
    (ts : List (Term S)) :
    evalList (S := S) σ (t :: ts) =
      eval (S := S) σ t :: evalList (S := S) σ ts := rfl

/-- Evaluating concatenated term lists concatenates the evaluations. -/
@[simp] lemma evalList_append (σ : Assignment S)
    (ts₁ ts₂ : List (Term S)) :
    evalList (S := S) σ (ts₁ ++ ts₂) =
      evalList (S := S) σ ts₁ ++ evalList (S := S) σ ts₂ := by
  classical
  simp [Term.evalList, List.map_append]

/-- Evaluating a list of value terms returns the underlying values. -/
@[simp] lemma evalList_ofValues (σ : Assignment S)
    (vs : List (Signature.Value S)) :
    evalList (S := S) σ (ofValues (S := S) vs) = vs := by
  classical
  unfold Term.evalList Term.ofValues
  induction vs with
  | nil => simp
  | cons v vs ih =>
      simp [List.map, ih]

@[simp] lemma eval_var (σ : Assignment S) (a : S.VarSymb) :
    eval (S := S) σ (.var a) = σ a := rfl

@[simp] lemma eval_value (σ : Assignment S) (v : S.Value) :
    eval (S := S) σ (.value v) = v := rfl

section

variable [DecidableEq S.VarSymb]

/-- Substitute a single variable by a value inside a term. -/
@[simp] def substValue (a : S.VarSymb) (v : S.Value) : Term S → Term S
  | .var b => if b = a then .value v else .var b
  | .value w => .value w

@[simp] lemma eval_substValue_update
    (σ : Assignment S) (a : S.VarSymb) (v : S.Value) (t : Term S) :
    eval (S := S) (Function.update σ a v) (substValue (S := S) a v t) =
      eval (S := S) (Function.update σ a v) t := by
  classical
  cases t with
  | var b =>
      by_cases h : b = a
      · subst h
        simp [substValue, Function.update]
      · simp [substValue, Function.update, h]
  | value w =>
      simp [substValue]

@[simp] lemma substValue_self (a : S.VarSymb) (v : S.Value) :
    substValue (S := S) a v (.var a) = .value v := by
  classical
  simp [substValue]

@[simp] lemma substValue_ne (a b : S.VarSymb) (v : S.Value)
    (h : a ≠ b) :
    substValue (S := S) a v (.var b) = .var b := by
  classical
  have hb : b ≠ a := by simpa [eq_comm] using h
  simp [substValue, hb]

end

/-- Finite set of free variables of a term. -/
@[simp] def freeVars [DecidableEq S.VarSymb] : Term S → Finset S.VarSymb
  | .var a => {a}
  | .value _ => ∅

/-- Free variables of a variable term recover the variable itself. -/
@[simp] lemma freeVars_var [DecidableEq S.VarSymb]
    (a : S.VarSymb) :
    Term.freeVars (S := S) (.var a) = ({a} : Finset S.VarSymb) := by
  rfl

/-- Value terms contain no free variables. -/
@[simp] lemma freeVars_value [DecidableEq S.VarSymb]
    (v : S.Value) :
    Term.freeVars (S := S) (.value v) = (∅ : Finset S.VarSymb) := by
  rfl

lemma freeVars_substValue_subset
    [DecidableEq S.VarSymb]
    (a : S.VarSymb) (v : S.Value) (t : Term S) :
    (substValue (S := S) a v t).freeVars ⊆
      (freeVars (S := S) t).erase a := by
  classical
  intro x hx
  cases t with
  | var b =>
      by_cases h : b = a
      · subst h
        simp [substValue, Term.freeVars] at hx
      · have hb : b ≠ a := h
        have hx' : x = b := by
          simpa [substValue, hb, Term.freeVars] using hx
        subst hx'
        simp [Term.freeVars, hb]
  | value w =>
      simp [substValue, Term.freeVars] at hx

@[simp] lemma substValue_of_not_mem_freeVars
    [DecidableEq S.VarSymb]
    (a : S.VarSymb) (v : S.Value) (t : Term S)
    (ha : a ∉ Term.freeVars (S := S) t) :
    substValue (S := S) a v t = t := by
  classical
  cases t with
  | var b =>
      have hb : b ≠ a := by
        have : a ∉ ({b} : Finset _) := by simpa [Term.freeVars] using ha
        intro hb_eq
        exact this (by simp [hb_eq])
      simp [substValue, hb]
  | value w =>
      simp [substValue]

theorem eval_respects [DecidableEq S.VarSymb]
    (σ τ : Assignment S)
    (t : Term S)
    (hσ : ∀ a ∈ Term.freeVars (S := S) t, σ a = τ a) :
    eval (S := S) σ t = eval (S := S) τ t := by
  classical
  cases t with
  | var a =>
      have h := hσ a (by simp [Term.freeVars])
      simp [Term.eval, h]
  | value v =>
      simp

/-- Substitution commutes with evaluating a list after updating an assignment. -/
@[simp] lemma evalList_map_substValue_update
    [DecidableEq S.VarSymb]
    (σ : Assignment S) (a : S.VarSymb) (v : S.Value)
    (ts : List (Term S)) :
  Term.evalList (S := S) (Function.update σ a v)
        (ts.map (Term.substValue (S := S) a v)) =
      Term.evalList (S := S) (Function.update σ a v) ts := by
  classical
  unfold Term.evalList
  simp [List.map_map, Function.comp]
  intro t _
  simpa using
    (Term.eval_substValue_update (σ := σ) (a := a) (v := v) (t := t))

end Term

/-- Event atoms `E(t₁,…,tₙ)` from Definition 3.1.3. -/
structure EventAtom (S : Signature) where
  sym : S.EventSymb
  args : List (Term S)

/-- Predicate atoms `P(t₁,…,tₙ)` from Definition 3.1.3. -/
structure PredicateAtom (S : Signature) where
  sym : S.PredSymb
  args : List (Term S)

/-- Definition 3.1.3: modal formulas. -/
inductive Formula (S : Signature) where
  | bot : Formula S
  | imp : Formula S → Formula S → Formula S
  | eq : Term S → Term S → Formula S
  | forall : S.VarSymb → Formula S → Formula S
  | event : EventAtom S → Formula S
  | predicate : PredicateAtom S → Formula S
  | past : Formula S → Formula S
  | atEnd : Formula S → Formula S
  | diamond : List (Term S) → Formula S → Formula S
  | seq : Formula S

namespace Formula

/-- Helper to fold free variables over lists of terms. -/
@[simp] def listFreeVars [DecidableEq S.VarSymb]
    : List (Term S) → Finset S.VarSymb
  | [] => ∅
  | t :: ts => Term.freeVars (S := S) t ∪ listFreeVars ts

lemma listFreeVars_cons [DecidableEq S.VarSymb]
    (t : Term S) (ts : List (Term S)) :
    listFreeVars (S := S) (t :: ts) =
      Term.freeVars (S := S) t ∪ listFreeVars (S := S) ts := by
  simp [listFreeVars]

/-- Free variables distribute over concatenation of term lists. -/
lemma listFreeVars_append [DecidableEq S.VarSymb]
    (ts₁ ts₂ : List (Term S)) :
    listFreeVars (S := S) (ts₁ ++ ts₂) =
      listFreeVars (S := S) ts₁ ∪ listFreeVars (S := S) ts₂ := by
  classical
  induction ts₁ with
  | nil =>
      simp [listFreeVars]
  | cons t ts ih =>
      simp [listFreeVars, ih, Finset.union_left_comm, Finset.union_assoc]

/-- Lists consisting solely of value terms are closed. -/
@[simp] lemma listFreeVars_ofValues [DecidableEq S.VarSymb]
    (vals : List (Signature.Value S)) :
    listFreeVars (S := S) (Term.ofValues (S := S) vals) = ∅ := by
  classical
  induction vals with
  | nil =>
      simp [Term.ofValues, listFreeVars]
  | cons v vals ih =>
      have ih' :
          listFreeVars (S := S) (List.map Term.ofValue vals) = ∅ := by
        simpa [Term.ofValues] using ih
      simp [Term.ofValues, listFreeVars, ih']

/-- Finite set of free variables for formulas (Definition 3.1.3). -/
@[simp] def freeVars [DecidableEq S.VarSymb] : Formula S → Finset S.VarSymb
  | .bot => ∅
  | .imp φ ψ => freeVars φ ∪ freeVars ψ
  | .eq t₁ t₂ => Term.freeVars t₁ ∪ Term.freeVars t₂
  | .forall a φ => (freeVars φ).erase a
  | .event evt => listFreeVars (S := S) evt.args
  | .predicate pred => listFreeVars (S := S) pred.args
  | .past φ => freeVars φ
  | .atEnd φ => freeVars φ
  | .diamond ls φ => listFreeVars (S := S) ls ∪ freeVars φ
  | .seq => ∅

/-- Closed formulas have no free variables. -/
@[simp] def IsClosed [DecidableEq S.VarSymb] (φ : Formula S) : Prop :=
  freeVars (S := S) φ = ∅

/-- Convenience: the always-true formula `⊤`. -/
@[simp] def top : Formula S := .imp .bot .bot

/-- The canonical truth formula is closed. -/
@[simp] lemma freeVars_top [DecidableEq S.VarSymb] :
    freeVars (S := S) (top (S := S)) = ∅ := by
  classical
  simp [top]

/-- Free variables of the past modality mirror the underlying formula. -/
@[simp] lemma freeVars_past [DecidableEq S.VarSymb]
    (φ : Formula S) :
    freeVars (S := S) (.past φ) = freeVars (S := S) φ :=
  rfl

/-- Free variables of the at-end modality mirror the underlying formula. -/
@[simp] lemma freeVars_atEnd [DecidableEq S.VarSymb]
    (φ : Formula S) :
    freeVars (S := S) (.atEnd φ) = freeVars (S := S) φ :=
  rfl

/-- Implication preserves closedness. -/
lemma IsClosed.imp
    [DecidableEq S.VarSymb]
    {φ ψ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) ψ →
      IsClosed (S := S) (.imp φ ψ) := by
  intro hφ hψ
  unfold IsClosed at hφ hψ ⊢
  simp [Formula.freeVars, hφ, hψ]

/-- The past modality preserves closedness. -/
lemma IsClosed.past
    [DecidableEq S.VarSymb]
    {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (.past φ) := by
  intro hφ
  unfold IsClosed at hφ ⊢
  simp [Formula.freeVars, hφ]

/-- The at-end modality preserves closedness. -/
lemma IsClosed.atEnd
    [DecidableEq S.VarSymb]
    {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (.atEnd φ) := by
  intro hφ
  unfold IsClosed at hφ ⊢
  simp [Formula.freeVars, hφ]

/-- Universal quantification preserves closedness. -/
lemma IsClosed.forall
    [DecidableEq S.VarSymb]
    {a : S.VarSymb} {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (.forall a φ) := by
  intro hφ
  unfold IsClosed at hφ ⊢
  simp [Formula.freeVars, hφ]

/-- The diamond modality is closed when both the guard list and body are closed. -/
lemma IsClosed.diamond
    [DecidableEq S.VarSymb]
    {ls : List (Term S)} {φ : Formula S}
    (hls : Formula.listFreeVars (S := S) ls = ∅)
    (hφ : IsClosed (S := S) φ) :
    IsClosed (S := S) (.diamond ls φ) := by
  unfold IsClosed at hφ ⊢
  simp [Formula.freeVars, hls, hφ]

variable [DecidableEq S.VarSymb]

/-- Substitution of a value for a variable inside a formula. -/
@[simp] def substValue (a : S.VarSymb) (v : S.Value) : Formula S → Formula S
  | .bot => .bot
  | .imp φ ψ =>
      .imp (substValue a v φ) (substValue a v ψ)
  | .eq t₁ t₂ =>
      .eq (Term.substValue a v t₁)
        (Term.substValue a v t₂)
  | .forall b φ =>
      if b = a then .forall b φ else
        .forall b (substValue a v φ)
  | .event evt =>
      .event ⟨evt.sym, evt.args.map (Term.substValue a v)⟩
  | .predicate pred =>
      .predicate ⟨pred.sym, pred.args.map (Term.substValue a v)⟩
  | .past φ => .past (substValue a v φ)
  | .atEnd φ => .atEnd (substValue a v φ)
  | .diamond ls φ =>
      .diamond (ls.map (Term.substValue a v)) (substValue a v φ)
  | .seq => .seq

lemma listFreeVars_substValue_subset
    (a : S.VarSymb) (v : S.Value) (ts : List (Term S)) :
    listFreeVars (S := S) (ts.map (Term.substValue (S := S) a v)) ⊆
      (listFreeVars (S := S) ts).erase a := by
  classical
  intro x hx
  induction ts with
  | nil =>
      simp at hx
  | cons t ts ih =>
      simp [List.map, Finset.mem_union] at hx
      rcases hx with hx | hx
      · have hx' := Term.freeVars_substValue_subset (S := S) a v t hx
        rcases Finset.mem_erase.mp hx' with ⟨hxne, hxt⟩
        have hxunion : x ∈ (Term.freeVars (S := S) t ∪ listFreeVars (S := S) ts) :=
          Finset.mem_union.mpr <| Or.inl hxt
        exact Finset.mem_erase.mpr ⟨hxne, hxunion⟩
      · have hx' := ih hx
        rcases Finset.mem_erase.mp hx' with ⟨hxne, hxmem⟩
        have hxunion : x ∈ (Term.freeVars (S := S) t ∪ listFreeVars (S := S) ts) :=
          Finset.mem_union.mpr <| Or.inr hxmem
        exact Finset.mem_erase.mpr ⟨hxne, hxunion⟩

lemma list_map_substValue_eq_self
    (a : S.VarSymb) (v : S.Value) :
    ∀ ts : List (Term S),
      a ∉ listFreeVars (S := S) ts →
        ts.map (Term.substValue (S := S) a v) = ts := by
  classical
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons t ts ih =>
      intro h
      have hUnion :
          a ∉ Term.freeVars (S := S) t ∪ listFreeVars (S := S) ts := by
        simpa [listFreeVars_cons] using h
      have ha_t : a ∉ Term.freeVars (S := S) t := by
        intro ha
        exact hUnion (Finset.mem_union.mpr <| Or.inl ha)
      have ha_ts : a ∉ listFreeVars (S := S) ts := by
        intro ha
        exact hUnion (Finset.mem_union.mpr <| Or.inr ha)
      have hhead := Term.substValue_of_not_mem_freeVars (S := S) a v t ha_t
      have htail := ih ha_ts
      simpa [List.map, hhead, htail]

@[simp] lemma freeVars_substValue_subset
    (a : S.VarSymb) (v : S.Value) (φ : Formula S) :
    (substValue (S := S) a v φ).freeVars ⊆ φ.freeVars.erase a := by
  classical
  have h :
      ∀ φ (a : S.VarSymb) (v : S.Value) (x : S.VarSymb),
        x ∈ (substValue (S := S) a v φ).freeVars →
        x ∈ (freeVars (S := S) φ).erase a := by
    intro φ
    induction φ with
    | bot =>
        intro a v x hx
        simp at hx
    | imp φ ψ ihφ ihψ =>
        intro a v x hx
        simp [Formula.substValue, Formula.freeVars, Finset.mem_union] at hx
        rcases hx with hx | hx
        · have hx' := ihφ a v x hx
          rcases Finset.mem_erase.mp hx' with ⟨hxne, hxmem⟩
          exact Finset.mem_erase.mpr
            ⟨hxne, Finset.mem_union.mpr <| Or.inl hxmem⟩
        · have hx' := ihψ a v x hx
          rcases Finset.mem_erase.mp hx' with ⟨hxne, hxmem⟩
          exact Finset.mem_erase.mpr
            ⟨hxne, Finset.mem_union.mpr <| Or.inr hxmem⟩
    | eq t₁ t₂ =>
        intro a v x hx
        simp [Formula.substValue, Formula.freeVars, Finset.mem_union] at hx
        rcases hx with hx | hx
        · have hx' := Term.freeVars_substValue_subset (S := S) a v t₁ hx
          rcases Finset.mem_erase.mp hx' with ⟨hxne, hxmem⟩
          exact Finset.mem_erase.mpr
            ⟨hxne, Finset.mem_union.mpr <| Or.inl hxmem⟩
        · have hx' := Term.freeVars_substValue_subset (S := S) a v t₂ hx
          rcases Finset.mem_erase.mp hx' with ⟨hxne, hxmem⟩
          exact Finset.mem_erase.mpr
            ⟨hxne, Finset.mem_union.mpr <| Or.inr hxmem⟩
    | «forall» b φ ih =>
        intro a v x hx
        by_cases hba : b = a
        · subst hba
          simpa [Formula.substValue, Formula.freeVars, Finset.erase_idem] using hx
        · simp [Formula.substValue, Formula.freeVars, hba, Finset.mem_erase] at hx
          rcases hx with ⟨hxne, hx⟩
          have hx' := ih a v x hx
          rcases Finset.mem_erase.mp hx' with ⟨hxne', hxmem⟩
          exact Finset.mem_erase.mpr ⟨hxne', Finset.mem_erase.mpr ⟨hxne, hxmem⟩⟩
    | event evt =>
        intro a v x hx
        have hx' :=
          listFreeVars_substValue_subset (S := S) a v evt.args
            (by simpa [Formula.substValue, Formula.freeVars] using hx)
        rcases Finset.mem_erase.mp hx' with ⟨hxne, hxmem⟩
        exact Finset.mem_erase.mpr ⟨hxne, by simpa [Formula.freeVars] using hxmem⟩
    | predicate pred =>
        intro a v x hx
        have hx' :=
          listFreeVars_substValue_subset (S := S) a v pred.args
            (by simpa [Formula.substValue, Formula.freeVars] using hx)
        rcases Finset.mem_erase.mp hx' with ⟨hxne, hxmem⟩
        exact Finset.mem_erase.mpr ⟨hxne, by simpa [Formula.freeVars] using hxmem⟩
    | past φ ih =>
        intro a v x hx
        simpa [Formula.substValue, Formula.freeVars] using ih a v x hx
    | atEnd φ ih =>
        intro a v x hx
        simpa [Formula.substValue, Formula.freeVars] using ih a v x hx
    | diamond ls φ ih =>
        intro a v x hx
        simp [Formula.substValue, Formula.freeVars, Finset.mem_union] at hx
        rcases hx with hx | hx
        · have hx' :=
            listFreeVars_substValue_subset (S := S) a v ls hx
          rcases Finset.mem_erase.mp hx' with ⟨hxne, hxmem⟩
          exact Finset.mem_erase.mpr
            ⟨hxne, Finset.mem_union.mpr <| Or.inl hxmem⟩
        · have hx' := ih a v x hx
          rcases Finset.mem_erase.mp hx' with ⟨hxne, hxmem⟩
          exact Finset.mem_erase.mpr
            ⟨hxne, Finset.mem_union.mpr <| Or.inr hxmem⟩
    | seq =>
        intro a v x hx; simp at hx
  intro x hx
  exact h φ a v x hx

lemma substValue_of_not_mem_freeVars
    (a : S.VarSymb) (v : S.Value) :
    ∀ φ : Formula S,
      a ∉ freeVars (S := S) φ →
        substValue (S := S) a v φ = φ := by
  classical
  intro φ
  induction φ with
  | bot => intro _; rfl
  | imp φ ψ ihφ ihψ =>
      intro ha
      have hφ : a ∉ freeVars (S := S) φ :=
        fun hmem => ha (Finset.mem_union.mpr <| Or.inl hmem)
      have hψ : a ∉ freeVars (S := S) ψ :=
        fun hmem => ha (Finset.mem_union.mpr <| Or.inr hmem)
      simp [Formula.substValue, ihφ hφ, ihψ hψ]
  | eq t₁ t₂ =>
      intro ha
      have ht₁ : a ∉ Term.freeVars (S := S) t₁ :=
        fun hmem => ha (Finset.mem_union.mpr <| Or.inl hmem)
      have ht₂ : a ∉ Term.freeVars (S := S) t₂ :=
        fun hmem => ha (Finset.mem_union.mpr <| Or.inr hmem)
      have h₁ := Term.substValue_of_not_mem_freeVars (S := S) a v t₁ ht₁
      have h₂ := Term.substValue_of_not_mem_freeVars (S := S) a v t₂ ht₂
      calc
        substValue (S := S) a v (.eq t₁ t₂)
            = Formula.eq (Term.substValue (S := S) a v t₁)
                (Term.substValue (S := S) a v t₂) := rfl
        _ = Formula.eq t₁ (Term.substValue (S := S) a v t₂) := by
              simpa [h₁]
        _ = Formula.eq t₁ t₂ := by
              simpa [h₂]
  | «forall» b φ ih =>
      intro ha
      by_cases hba : b = a
      · subst hba
        simp [Formula.substValue]
      · have hne : a ≠ b := by
          simpa [ne_comm] using hba
        have hφ : a ∉ freeVars (S := S) φ := by
          intro hmem
          exact ha (Finset.mem_erase.mpr ⟨hne, hmem⟩)
        simp [Formula.substValue, hba, ih hφ]
  | event evt =>
      intro ha
      have : a ∉ listFreeVars (S := S) evt.args := ha
      simp [Formula.substValue,
        list_map_substValue_eq_self (S := S) a v evt.args this]
  | predicate pred =>
      intro ha
      have : a ∉ listFreeVars (S := S) pred.args := ha
      simp [Formula.substValue,
        list_map_substValue_eq_self (S := S) a v pred.args this]
  | past φ ih =>
      intro ha
      simp [Formula.substValue, ih ha]
  | atEnd φ ih =>
      intro ha
      simp [Formula.substValue, ih ha]
  | diamond ls φ ih =>
      intro ha
      have hls : a ∉ listFreeVars (S := S) ls :=
        fun hmem => ha (Finset.mem_union.mpr <| Or.inl hmem)
      have hφ : a ∉ freeVars (S := S) φ :=
        fun hmem => ha (Finset.mem_union.mpr <| Or.inr hmem)
      simp [Formula.substValue,
        list_map_substValue_eq_self (S := S) a v ls hls, ih hφ]
  | seq => intro _; rfl

@[simp] lemma substValue_closed
    (a : S.VarSymb) (v : S.Value) {φ : Formula S}
    (hφ : φ.IsClosed) :
    (substValue (S := S) a v φ) = φ := by
  classical
  have ha : a ∉ freeVars (S := S) φ := by
    have : freeVars (S := S) φ = (∅ : Finset _) := by
      simpa [Formula.IsClosed] using hφ
    have := congrArg (fun s : Finset _ => a ∈ s) this
    simpa using this
  simpa using substValue_of_not_mem_freeVars (S := S) a v φ ha

/-- The `♢` modality uses exactly the free variables of its arguments and body. -/
lemma freeVars_diamond (ls : List (Term S)) (φ : Formula S) :
    freeVars (S := S) (.diamond ls φ) =
      listFreeVars (S := S) ls ∪ freeVars (S := S) φ := by
  rfl

/-- Logical negation. -/
@[simp] def not (φ : Formula S) : Formula S :=
  .imp φ .bot

/-- Conjunction. -/
@[simp] def and (φ ψ : Formula S) : Formula S :=
  not (.imp φ (not ψ))

/-- Disjunction. -/
@[simp] def or (φ ψ : Formula S) : Formula S :=
  .imp (not φ) ψ

/-- Bi-implication. -/
@[simp] def iff (φ ψ : Formula S) : Formula S :=
  and (S := S) (.imp φ ψ) (.imp ψ φ)

/-- Existential quantification. -/
@[simp] def exists_ (a : S.VarSymb) (φ : Formula S) : Formula S :=
  not (.forall a (not φ))

/-- Sometimes modality (`↕`) specialised to the current participant; sugar for `⤒↓`. -/
@[simp] def sometime (φ : Formula S) : Formula S :=
  atEnd (past φ)

/-- Always in the past (`⇕` in Figure 4). -/
@[simp] def alwaysPast (φ : Formula S) : Formula S :=
  not (sometime (not φ))

/-- Eventually in the past (`⇓` in Figure 4). -/
@[simp] def eventuallyPast (φ : Formula S) : Formula S :=
  not (past (not φ))

/-- Box modality from Figure 4. -/
@[simp] def box (ls : List (Term S)) (φ : Formula S) : Formula S :=
  not (.diamond ls (not φ))

/-- Diamond with past guard. -/
@[simp] def diamondPast (ls : List (Term S)) (φ : Formula S) : Formula S :=
  .diamond ls (.past φ)

/-- Diamond with eventual past guard. -/
@[simp] def diamondEventually (ls : List (Term S)) (φ : Formula S) : Formula S :=
  .diamond ls (eventuallyPast φ)

/-- Diamond with empty learner list. -/
@[simp] def diamondEmpty (φ : Formula S) : Formula S :=
  .diamond [] φ

/-- Box with past guard. -/
@[simp] def boxPast (ls : List (Term S)) (φ : Formula S) : Formula S :=
  box (S := S) ls (Formula.past φ)

/-- Box with eventual past guard. -/
@[simp] def boxEventually (ls : List (Term S)) (φ : Formula S) : Formula S :=
  box (S := S) ls (Formula.eventuallyPast φ)

/-- Box over the empty learner list. -/
@[simp] def boxEmpty (φ : Formula S) : Formula S :=
  box (S := S) [] φ

/-- Helpful notation for implication in modal formulas. -/
scoped infixr:60 " ⇒ᶠ " => Formula.imp

/-- Helpful notation for bottom in modal formulas. -/
scoped notation "⊥ᶠ" => Formula.bot

/-- Helpful notation for top in modal formulas. -/
scoped notation "⊤ᶠ" => Formula.top

/-- Helpful notation for equality in modal formulas. -/
scoped infix:55 " ≃ᶠ " => Formula.eq

/-- Helpful notation for universal quantification in modal formulas. -/
scoped notation "∀ᶠ " a ", " φ => Formula.forall a φ

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

/-- Helpful notation for existential quantification. -/
scoped notation "∃ᶠ " a ", " φ => Formula.exists_ a φ

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
@[simp] def ofEvent (E : Signature.EventType S) : Formula S :=
  .event ⟨E.sym, E.args.map Term.ofValue⟩

/-- Promote an atomic predicate from the signature to a formula. -/
@[simp] def ofPredicate (P : Signature.AtomicPredType S) : Formula S :=
  .predicate ⟨P.sym, P.args.map Term.ofValue⟩

/-- Free variables are preserved by logical negation. -/
@[simp] lemma freeVars_not
    (φ : Formula S) :
    freeVars (S := S) (Formula.not φ) = freeVars (S := S) φ := by
  classical
  simp [Formula.not, Formula.freeVars]

/-- Conjunction carries the union of the component free variables. -/
@[simp] lemma freeVars_and
    (φ ψ : Formula S) :
    freeVars (S := S) (Formula.and φ ψ) =
      freeVars (S := S) φ ∪ freeVars (S := S) ψ := by
  classical
  simp [Formula.and, Formula.not, Formula.freeVars]

/-- Disjunction carries the union of the component free variables. -/
@[simp] lemma freeVars_or
    (φ ψ : Formula S) :
    freeVars (S := S) (Formula.or φ ψ) =
      freeVars (S := S) φ ∪ freeVars (S := S) ψ := by
  classical
  simp [Formula.or, Formula.not, Formula.freeVars]

/-- Bi-implication uses the union of the underlying free variables. -/
@[simp] lemma freeVars_iff
    (φ ψ : Formula S) :
    freeVars (S := S) (Formula.iff φ ψ) =
      freeVars (S := S) φ ∪ freeVars (S := S) ψ := by
  classical
  have h_union :
      freeVars (S := S) φ ∪
        (freeVars (S := S) ψ ∪ freeVars (S := S) φ) =
          freeVars (S := S) φ ∪ freeVars (S := S) ψ := by
    ext x
    simp [Finset.mem_union, or_comm]
  have h :=
    (freeVars_and (S := S) (φ := Formula.imp φ ψ)
      (ψ := Formula.imp ψ φ))
  simp [Formula.freeVars, Formula.not, h_union,
    Finset.union_left_comm, Finset.union_assoc]

/-- Free variables of an existential formula exclude the bound variable. -/
@[simp] lemma freeVars_exists
    (a : S.VarSymb) (φ : Formula S) :
    freeVars (S := S) (Formula.exists_ a φ) =
      (freeVars (S := S) φ).erase a := by
  classical
  simp [Formula.exists_, Formula.not, Formula.freeVars]

/-- The sometime modality preserves free variables. -/
@[simp] lemma freeVars_sometime
    (φ : Formula S) :
    freeVars (S := S) (Formula.sometime φ) =
      freeVars (S := S) φ := by
  classical
  simp [Formula.sometime, Formula.freeVars]

/-- The always-in-the-past modality preserves free variables. -/
@[simp] lemma freeVars_alwaysPast
    (φ : Formula S) :
    freeVars (S := S) (Formula.alwaysPast φ) =
      freeVars (S := S) φ := by
  classical
  simp [Formula.alwaysPast, Formula.sometime, Formula.not, Formula.freeVars]

/-- The eventually-in-the-past modality preserves free variables. -/
@[simp] lemma freeVars_eventuallyPast
    (φ : Formula S) :
    freeVars (S := S) (Formula.eventuallyPast φ) =
      freeVars (S := S) φ := by
  classical
  simp [Formula.eventuallyPast, Formula.not, Formula.freeVars]

/-- The box modality depends on the same variables as its guard and body. -/
@[simp] lemma freeVars_box
    (ls : List (Term S)) (φ : Formula S) :
    freeVars (S := S) (Formula.box ls φ) =
      Formula.listFreeVars (S := S) ls ∪ freeVars (S := S) φ := by
  classical
  simp [Formula.box, Formula.not, Formula.freeVars]

/-- Diamonds guarded by the past modality expose the same variables as the guard and body. -/
@[simp] lemma freeVars_diamondPast
    (ls : List (Term S)) (φ : Formula S) :
    freeVars (S := S) (Formula.diamondPast ls φ) =
      Formula.listFreeVars (S := S) ls ∪ freeVars (S := S) φ := by
  classical
  simp [Formula.diamondPast, Formula.freeVars]

/-- Diamonds guarded by the eventual past modality expose the same variables as
    the guard and body. -/
@[simp] lemma freeVars_diamondEventually
    (ls : List (Term S)) (φ : Formula S) :
    freeVars (S := S) (Formula.diamondEventually ls φ) =
      Formula.listFreeVars (S := S) ls ∪ freeVars (S := S) φ := by
  classical
  simp [Formula.diamondEventually, Formula.eventuallyPast, Formula.not,
    Formula.freeVars]

/-- Diamonds over the empty list share the free variables of their body. -/
@[simp] lemma freeVars_diamondEmpty
    (φ : Formula S) :
    freeVars (S := S) (Formula.diamondEmpty φ) =
      freeVars (S := S) φ := by
  classical
  simp [Formula.diamondEmpty, Formula.freeVars]

/-- Boxes guarded by the past modality expose the same variables as the guard and body. -/
@[simp] lemma freeVars_boxPast
    (ls : List (Term S)) (φ : Formula S) :
    freeVars (S := S) (Formula.boxPast ls φ) =
      Formula.listFreeVars (S := S) ls ∪ freeVars (S := S) φ := by
  classical
  simp [Formula.boxPast, Formula.freeVars]

/-- Boxes guarded by the eventual past modality expose the same variables as the guard and body. -/
@[simp] lemma freeVars_boxEventually
    (ls : List (Term S)) (φ : Formula S) :
    freeVars (S := S) (Formula.boxEventually ls φ) =
      Formula.listFreeVars (S := S) ls ∪ freeVars (S := S) φ := by
  classical
  simp [Formula.boxEventually, Formula.eventuallyPast, Formula.not,
    Formula.freeVars]

/-- Empty boxes share the free variables of their body. -/
@[simp] lemma freeVars_boxEmpty
    (φ : Formula S) :
    freeVars (S := S) (Formula.boxEmpty φ) =
      freeVars (S := S) φ := by
  classical
  simp [Formula.boxEmpty, Formula.freeVars]

/-- Nullary predicate atoms are closed. -/
@[simp] lemma freeVars_predicate0
    (sym : S.PredSymb) :
    freeVars (S := S) (Formula.predicate0 sym) = ∅ := by
  classical
  simp [Formula.predicate0, Formula.freeVars]

/-- Nullary event atoms are closed. -/
@[simp] lemma freeVars_event0
    (sym : S.EventSymb) :
    freeVars (S := S) (Formula.event0 sym) = ∅ := by
  classical
  simp [Formula.event0, Formula.freeVars]

/-- Events promoted from the signature are closed. -/
@[simp] lemma freeVars_ofEvent
    (E : Signature.EventType S) :
    freeVars (S := S) (Formula.ofEvent E) = ∅ := by
  classical
  simpa [Formula.ofEvent, Formula.freeVars, Term.ofValues]
    using
      (listFreeVars_ofValues (S := S) (vals := E.args))

/-- Atomic predicates promoted from the signature are closed. -/
@[simp] lemma freeVars_ofPredicate
    (P : Signature.AtomicPredType S) :
    freeVars (S := S) (Formula.ofPredicate P) = ∅ := by
  classical
  simpa [Formula.ofPredicate, Formula.freeVars, Term.ofValues]
    using
      (listFreeVars_ofValues (S := S) (vals := P.args))

/-- Closed formulas remain closed under logical negation. -/
lemma IsClosed.not
    {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (Formula.not φ) := by
  classical
  intro hφ
  simpa [Formula.IsClosed, freeVars_not]

/-- Conjunction preserves closedness when both operands are closed. -/
lemma IsClosed.and
    {φ ψ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) ψ →
      IsClosed (S := S) (Formula.and φ ψ) := by
  classical
  intro hφ hψ
  unfold Formula.IsClosed at hφ hψ ⊢
  simp [hφ, hψ]

/-- Disjunction preserves closedness when both operands are closed. -/
lemma IsClosed.or
    {φ ψ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) ψ →
      IsClosed (S := S) (Formula.or φ ψ) := by
  classical
  intro hφ hψ
  unfold Formula.IsClosed at hφ hψ ⊢
  simp [hφ, hψ]

/-- Bi-implication preserves closedness. -/
lemma IsClosed.iff
    {φ ψ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) ψ →
      IsClosed (S := S) (Formula.iff φ ψ) := by
  classical
  intro hφ hψ
  unfold Formula.IsClosed at hφ hψ ⊢
  simp [hφ, hψ]

/-- Existential quantification preserves closedness. -/
lemma IsClosed.exists
    {a : S.VarSymb} {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (Formula.exists_ a φ) := by
  classical
  intro hφ
  unfold Formula.IsClosed at hφ ⊢
  simp [hφ]

/-- The sometime modality preserves closedness. -/
lemma IsClosed.sometime
    {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (Formula.sometime φ) := by
  classical
  intro hφ
  unfold Formula.IsClosed at hφ ⊢
  simp [hφ]

/-- The always-in-the-past modality preserves closedness. -/
lemma IsClosed.alwaysPast
    {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (Formula.alwaysPast φ) := by
  classical
  intro hφ
  unfold Formula.IsClosed at hφ ⊢
  simp [hφ]

/-- The eventually-in-the-past modality preserves closedness. -/
lemma IsClosed.eventuallyPast
    {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (Formula.eventuallyPast φ) := by
  classical
  intro hφ
  unfold Formula.IsClosed at hφ ⊢
  simp [hφ]

/-- The box modality preserves closedness when the guard and body are closed. -/
lemma IsClosed.box
    {ls : List (Term S)} {φ : Formula S}
    (hls : Formula.listFreeVars (S := S) ls = ∅)
    (hφ : IsClosed (S := S) φ) :
    IsClosed (S := S) (Formula.box ls φ) := by
  classical
  unfold Formula.IsClosed at hφ ⊢
  simp [hls, hφ]

/-- Diamonds guarded by the past modality preserve closedness. -/
lemma IsClosed.diamondPast
    {ls : List (Term S)} {φ : Formula S}
    (hls : Formula.listFreeVars (S := S) ls = ∅)
    (hφ : IsClosed (S := S) φ) :
    IsClosed (S := S) (Formula.diamondPast ls φ) := by
  classical
  unfold Formula.IsClosed at hφ ⊢
  simp [hls, hφ]

/-- Diamonds guarded by the eventual past modality preserve closedness. -/
lemma IsClosed.diamondEventually
    {ls : List (Term S)} {φ : Formula S}
    (hls : Formula.listFreeVars (S := S) ls = ∅)
    (hφ : IsClosed (S := S) φ) :
    IsClosed (S := S) (Formula.diamondEventually ls φ) := by
  classical
  unfold Formula.IsClosed at hφ ⊢
  simp [hls, hφ]

/-- Diamonds over the empty list inherit closedness from their body. -/
lemma IsClosed.diamondEmpty
    {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (Formula.diamondEmpty φ) := by
  classical
  intro hφ
  unfold Formula.IsClosed at hφ ⊢
  simp [hφ]

/-- The past box preserves closedness when the guard and body are closed. -/
lemma IsClosed.boxPast
    {ls : List (Term S)} {φ : Formula S}
    (hls : Formula.listFreeVars (S := S) ls = ∅)
    (hφ : IsClosed (S := S) φ) :
    IsClosed (S := S) (Formula.boxPast ls φ) := by
  classical
  unfold Formula.IsClosed at hφ ⊢
  simp [hls, hφ]

/-- The eventual past box preserves closedness when the guard and body are closed. -/
lemma IsClosed.boxEventually
    {ls : List (Term S)} {φ : Formula S}
    (hls : Formula.listFreeVars (S := S) ls = ∅)
    (hφ : IsClosed (S := S) φ) :
    IsClosed (S := S) (Formula.boxEventually ls φ) := by
  classical
  unfold Formula.IsClosed at hφ ⊢
  simp [hls, hφ]

/-- Empty boxes preserve closedness. -/
lemma IsClosed.boxEmpty
    {φ : Formula S} :
    IsClosed (S := S) φ → IsClosed (S := S) (Formula.boxEmpty φ) := by
  classical
  intro hφ
  unfold Formula.IsClosed at hφ ⊢
  simp [hφ]

/-- Nullary predicate atoms are closed formulas. -/
lemma IsClosed.predicate0
    (sym : S.PredSymb) :
    IsClosed (S := S) (Formula.predicate0 sym) := by
  classical
  unfold Formula.IsClosed
  simp

/-- Nullary event atoms are closed formulas. -/
lemma IsClosed.event0
    (sym : S.EventSymb) :
    IsClosed (S := S) (Formula.event0 sym) := by
  classical
  unfold Formula.IsClosed
  simp

/-- Promoted events are closed formulas. -/
lemma IsClosed.ofEvent
    (E : Signature.EventType S) :
    IsClosed (S := S) (Formula.ofEvent E) := by
  classical
  unfold Formula.IsClosed Formula.ofEvent Formula.freeVars
  simpa [Term.ofValues]
    using
      (listFreeVars_ofValues (S := S) (vals := E.args))

/-- Promoted atomic predicates are closed formulas. -/
lemma IsClosed.ofPredicate
    (P : Signature.AtomicPredType S) :
    IsClosed (S := S) (Formula.ofPredicate P) := by
  classical
  unfold Formula.IsClosed Formula.ofPredicate Formula.freeVars
  simpa [Term.ofValues]
    using
      (listFreeVars_ofValues (S := S) (vals := P.args))

end Formula

end Logic
end ModalDistribution
