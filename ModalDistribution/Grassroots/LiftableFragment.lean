import ModalDistribution.Logic.Syntax
import ModalDistribution.Examples.ThyHBB1.Axioms

/-!
# The liftable fragment of HBB modal logic

This file defines a syntactic fragment of `Formula S` that captures the
"grassroots-friendly" HBB formulas — those that are preserved by
coalescent lifting of models from a smaller participant set to a larger
one — and then catalogs the existing `ThyHBB1` axioms against it.

## The fragment

Two mutually-recursive inductive predicates:

- `IsLiftable φ` — the *forward* liftable fragment: formulas that are
  preserved by lifting. Intuitively, if `M_P ⊨ φ` then the canonical lift
  `M_{P'} ⊨ φ`.
- `IsAntiLiftable φ` — the *backwards* liftable fragment: formulas that
  are preserved by projection. Intuitively, if `M_{P'} ⊨ φ` then
  `M_P ⊨ φ`.

These interact on implications: `imp φ ψ` is liftable iff `φ` is
anti-liftable and `ψ` is liftable (the standard contravariance for arrow
types). This also makes `not`, `and`, `or`, `exists_`, and the `box`
family derivable.

## The key design choices

1. **`Formula.box ls φ` is LIFTABLE**: Murdoch–Sheff's `□` is
   existential-over-quorums (`∃ quorum, ∀ member`), verified by
   `Logic/Properties/Modalities.lean`'s `sat_box_singleton_exists` lemma
   and the uniform `obtain ⟨O, hO, hAll⟩` pattern across the 9 use sites
   in `Examples/ThyHBB1/{Safety,Liveness_One,Liveness_Two}.lean`. The
   lifted quorum witness works as the existential witness at `P'`.

2. **`Formula.diamond ls φ` is GENERALLY NOT liftable**: it is
   universal-over-quorums, so new `P'`-quorums (those supersets of
   lifted `P`-quorums that include agents from `P' \ P`) may lack
   witnesses. Two exceptions are recognised:
   - `diamond [] φ`: the empty quorum list collapses to a plain
     `∃ p, φ at p`, which is preserved.
   - `diamond ls Formula.seq`: `seq` is vacuously true at new
     (empty-history) agents, so new quorums are satisfied by new agents.

3. **Sugar is handled via derived lemmas**, not directly in the
   inductive predicate. Constructors like `and`, `or`, `box`, `exists_`,
   `sometime`, etc., unfold to compositions of the core constructors
   `imp`, `forall`, `diamond`, etc. The lemmas in §2 show how to build
   `IsLiftable` proofs for the sugar from proofs for the operands.

## The catalog

§3 proves that each axiom of `ThyHBB1` is in the liftable fragment:

- `echoBackwardAxiom` — liftable
- `voteBackwardAxiom` — liftable
- `deliverBackwardAxiom` — liftable
- `echoNonEquivAxiom` — liftable
- `safeFormula` (used inside `voteBackwardAxiom`) — liftable
- `echoForwardAxiom`, `voteForwardAxiom`, `deliverForwardAxiom` — liftable

The aggregate theorem `ThyHBB1_axioms_liftable` records that every axiom
of `ThyHBB1` is in `IsLiftable`.

## What this gives us

If the meta-theorem *"IsLiftable formulas are preserved by canonical
lifting under coalescent learner families"* holds (not formalised here;
future work), then this catalog is precisely the evidence that the
class of ThyHBB1-models is closed under coalescent lifting — and hence
ThyHBB1 gives rise to a structurally `IsOblivious` DTS. This is the
corrected positive `Conjecture C'` from the working notes.

The catalog is *evidence*, not a proof of obliviousness. The preservation
theorem from the syntactic fragment to the semantic property is the
natural next step after this file.
-/

namespace ModalDistribution
namespace Grassroots
namespace LiftableFragment

open ModalDistribution.Logic
open scoped Formula

variable {S : Signature.{0, 0, 0}}

/-! ## §1. Mutual inductive definition of IsLiftable and IsAntiLiftable -/

mutual

/-- The forward liftable fragment: formulas whose truth is preserved by
canonical coalescent lifting of HBB models. -/
inductive IsLiftable : Formula S → Prop
  | bot : IsLiftable Formula.bot
  | eq (v₁ v₂ : S.Value) : IsLiftable (Formula.eq v₁ v₂)
  | event (E : EventAtom S) : IsLiftable (Formula.event E)
  | predicate (P : PredicateAtom S) : IsLiftable (Formula.predicate P)
  | seq : IsLiftable (Formula.seq : Formula S)
  | forall_ {body : S.Value → Formula S}
      (h : ∀ v, IsLiftable (body v)) :
      IsLiftable (Formula.forall body)
  | past {φ : Formula S} (h : IsLiftable φ) : IsLiftable (Formula.past φ)
  | atEnd {φ : Formula S} (h : IsLiftable φ) : IsLiftable (Formula.atEnd φ)
  | imp {φ ψ : Formula S}
      (hφ : IsAntiLiftable φ) (hψ : IsLiftable ψ) :
      IsLiftable (Formula.imp φ ψ)
  | diamondEmpty {φ : Formula S} (h : IsLiftable φ) :
      IsLiftable (Formula.diamond [] φ)
  | diamondSeq (ls : List S.Value) :
      IsLiftable (Formula.diamond ls (Formula.seq : Formula S))
  /- Extension for the forward axioms of ThyHBB1.

  Semantic justification: `diamond ls (not (past (event E)))` means
  "∀ `ls`-quorum, ∃ member without a past `event E`". Under lifting:
  * Any new P'-quorum that contains a new (fresh) agent is witnessed by
    that agent (new agents have empty histories, so `past event E` is
    vacuously false at them, hence `not (past event E)` is true).
  * Any new P'-quorum contained entirely in the lifted P corresponds via
    `IsCoalescent.restrict_quorum` to a P-quorum, which has a witness
    from the small-universe model; that witness's history is unchanged
    so its truth of `past event E` is preserved.

  This constructor is sound for events specifically because events are
  atoms whose truth at an agent depends only on that agent's history. -/
  | diamondNotPastEvent (ls : List S.Value) (E : EventAtom S) :
      IsLiftable (Formula.diamond ls
        (Formula.imp (Formula.past (Formula.event E)) Formula.bot))

/-- The backwards liftable fragment: formulas whose truth is preserved by
projection from a larger participant set to a smaller one. -/
inductive IsAntiLiftable : Formula S → Prop
  | bot : IsAntiLiftable Formula.bot
  | eq (v₁ v₂ : S.Value) : IsAntiLiftable (Formula.eq v₁ v₂)
  | event (E : EventAtom S) : IsAntiLiftable (Formula.event E)
  | predicate (P : PredicateAtom S) : IsAntiLiftable (Formula.predicate P)
  | seq : IsAntiLiftable (Formula.seq : Formula S)
  | forall_ {body : S.Value → Formula S}
      (h : ∀ v, IsAntiLiftable (body v)) :
      IsAntiLiftable (Formula.forall body)
  | past {φ : Formula S} (h : IsAntiLiftable φ) : IsAntiLiftable (Formula.past φ)
  | atEnd {φ : Formula S} (h : IsAntiLiftable φ) : IsAntiLiftable (Formula.atEnd φ)
  | imp {φ ψ : Formula S}
      (hφ : IsLiftable φ) (hψ : IsAntiLiftable ψ) :
      IsAntiLiftable (Formula.imp φ ψ)
  /- Diamond anti-liftability requires a nonempty learner list.
  With at least one quorum intersection step, the coalescence
  pairwise-intersection property forces every witness into
  `range(liftAgent h)`, enabling projection back to `↥P`.
  The empty list `♢[] φ` is a plain existential `∃ p', φ(p')`
  with no quorum constraint, so fresh agents can witness
  vacuously — breaking the downward transfer. -/
  | diamond (l : S.Value) (ls : List S.Value) {φ : Formula S}
      (h : IsAntiLiftable φ) :
      IsAntiLiftable (Formula.diamond (l :: ls) φ)
  /- Special case: `♢[] (past φ)` IS anti-liftable even with an empty
  learner list, because `past` forces the witness to come from the
  history — and every history member is a lift of an original member
  (by `mem_liftPreHistory_iff`), so fresh agents can't contribute. -/
  | diamondEmptyPast {φ : Formula S} (h : IsAntiLiftable φ) :
      IsAntiLiftable (Formula.diamond [] (Formula.past φ))

end

/-! ## §2. Derived sugar lemmas

These lemmas show that the sugar constructors `top`, `not`, `and`, `or`,
`exists_`, `iff`, `sometime`, `box`, `boxPast`, `diamondPast`, and
`existsAtMostOne` all unfold to compositions of the core constructors
and can be proven `IsLiftable` from proofs of their components. -/

section Sugar

/-- `top` is liftable. -/
lemma isLiftable_top : IsLiftable (Formula.top : Formula S) :=
  IsLiftable.imp IsAntiLiftable.bot IsLiftable.bot

/-- `top` is anti-liftable. -/
lemma isAntiLiftable_top : IsAntiLiftable (Formula.top : Formula S) :=
  IsAntiLiftable.imp IsLiftable.bot IsAntiLiftable.bot

/-- `not φ` is liftable iff `φ` is anti-liftable. -/
lemma isLiftable_not {φ : Formula S} (h : IsAntiLiftable φ) :
    IsLiftable (¬ᶠ φ) :=
  IsLiftable.imp h IsLiftable.bot

/-- `not φ` is anti-liftable iff `φ` is liftable. -/
lemma isAntiLiftable_not {φ : Formula S} (h : IsLiftable φ) :
    IsAntiLiftable (¬ᶠ φ) :=
  IsAntiLiftable.imp h IsAntiLiftable.bot

/-- `and φ ψ` is liftable if both conjuncts are. -/
lemma isLiftable_and {φ ψ : Formula S}
    (hφ : IsLiftable φ) (hψ : IsLiftable ψ) :
    IsLiftable (φ ∧ᶠ ψ) :=
  isLiftable_not (IsAntiLiftable.imp hφ (isAntiLiftable_not hψ))

/-- `and φ ψ` is anti-liftable if both conjuncts are. -/
lemma isAntiLiftable_and {φ ψ : Formula S}
    (hφ : IsAntiLiftable φ) (hψ : IsAntiLiftable ψ) :
    IsAntiLiftable (φ ∧ᶠ ψ) :=
  isAntiLiftable_not (IsLiftable.imp hφ (isLiftable_not hψ))

/-- `or φ ψ` is liftable if both disjuncts are. -/
lemma isLiftable_or {φ ψ : Formula S}
    (hφ : IsLiftable φ) (hψ : IsLiftable ψ) :
    IsLiftable (φ ∨ᶠ ψ) :=
  IsLiftable.imp (isAntiLiftable_not hφ) hψ

/-- `or φ ψ` is anti-liftable if both disjuncts are. -/
lemma isAntiLiftable_or {φ ψ : Formula S}
    (hφ : IsAntiLiftable φ) (hψ : IsAntiLiftable ψ) :
    IsAntiLiftable (φ ∨ᶠ ψ) :=
  IsAntiLiftable.imp (isLiftable_not hφ) hψ

/-- `exists_ body` is liftable if each `body v` is. -/
lemma isLiftable_exists {body : S.Value → Formula S}
    (h : ∀ v, IsLiftable (body v)) :
    IsLiftable (Formula.exists_ body) :=
  isLiftable_not (IsAntiLiftable.forall_ (fun v => isAntiLiftable_not (h v)))

/-- `exists_ body` is anti-liftable if each `body v` is. -/
lemma isAntiLiftable_exists {body : S.Value → Formula S}
    (h : ∀ v, IsAntiLiftable (body v)) :
    IsAntiLiftable (Formula.exists_ body) :=
  isAntiLiftable_not (IsLiftable.forall_ (fun v => isLiftable_not (h v)))

/-- `box (l :: ls) φ` is liftable if `φ` is (nonempty learner list).
`box` in Murdoch–Sheff HBB is existential-over-quorums, and under
coalescence the lifted witness quorum carries over. -/
lemma isLiftable_box {l : S.Value} {ls : List S.Value} {φ : Formula S}
    (h : IsLiftable φ) :
    IsLiftable (Formula.box (l :: ls) φ) :=
  isLiftable_not
    (IsAntiLiftable.diamond l ls (isAntiLiftable_not h))

/-- `sometime φ = atEnd (past φ)` is liftable if `φ` is. -/
lemma isLiftable_sometime {φ : Formula S} (h : IsLiftable φ) :
    IsLiftable (Formula.sometime φ) :=
  IsLiftable.atEnd (IsLiftable.past h)

/-- `sometime φ` is anti-liftable if `φ` is. -/
lemma isAntiLiftable_sometime {φ : Formula S} (h : IsAntiLiftable φ) :
    IsAntiLiftable (Formula.sometime φ) :=
  IsAntiLiftable.atEnd (IsAntiLiftable.past h)

/-- `boxPast (l :: ls) φ = box (l :: ls) (past φ)` is liftable if `φ` is. -/
lemma isLiftable_boxPast {l : S.Value} {ls : List S.Value} {φ : Formula S}
    (h : IsLiftable φ) :
    IsLiftable (Formula.boxPast (l :: ls) φ) :=
  isLiftable_box (IsLiftable.past h)

/-- `diamondPast [] φ` is liftable if `φ` is (empty-list diamond collapses
to plain ∃ participant). -/
lemma isLiftable_diamondPast_empty {φ : Formula S}
    (h : IsLiftable φ) :
    IsLiftable (Formula.diamondPast [] φ) :=
  IsLiftable.diamondEmpty (IsLiftable.past h)

/-- `diamondPast [] φ` is anti-liftable if `φ` is (via `diamondEmptyPast`:
the `past` modality grounds witnesses to the history). -/
lemma isAntiLiftable_diamondPast_empty {φ : Formula S}
    (h : IsAntiLiftable φ) :
    IsAntiLiftable (Formula.diamondPast [] φ) :=
  IsAntiLiftable.diamondEmptyPast h

/-- `diamondPast (l :: ls) φ` is anti-liftable if `φ` is (nonempty list). -/
lemma isAntiLiftable_diamondPast {l : S.Value} {ls : List S.Value}
    {φ : Formula S} (h : IsAntiLiftable φ) :
    IsAntiLiftable (Formula.diamondPast (l :: ls) φ) :=
  IsAntiLiftable.diamond l ls (IsAntiLiftable.past h)

/-- `predicate0 sym` is liftable. -/
lemma isLiftable_predicate0 (sym : S.PredSymb) :
    IsLiftable (Formula.predicate0 sym : Formula S) :=
  IsLiftable.predicate ⟨sym, []⟩

/-- `predicate0 sym` is anti-liftable. -/
lemma isAntiLiftable_predicate0 (sym : S.PredSymb) :
    IsAntiLiftable (Formula.predicate0 sym : Formula S) :=
  IsAntiLiftable.predicate ⟨sym, []⟩

/-- `ofEvent E` is liftable. -/
lemma isLiftable_ofEvent (E : Signature.EventType S) :
    IsLiftable (Formula.ofEvent E) :=
  IsLiftable.event ⟨E.sym, E.args⟩

/-- `ofEvent E` is anti-liftable. -/
lemma isAntiLiftable_ofEvent (E : Signature.EventType S) :
    IsAntiLiftable (Formula.ofEvent E) :=
  IsAntiLiftable.event ⟨E.sym, E.args⟩

/-- `existsAtMostOne body` is liftable if each `body v` is anti-liftable. -/
lemma isLiftable_existsAtMostOne {body : S.Value → Formula S}
    (h : ∀ v, IsAntiLiftable (body v)) :
    IsLiftable (Formula.existsAtMostOne body) :=
  IsLiftable.forall_ (fun x =>
    IsLiftable.forall_ (fun y =>
      IsLiftable.imp (h x)
        (IsLiftable.imp (h y) (IsLiftable.eq x y))))

/-- `existsAtMostOne body` is anti-liftable if each `body v` is liftable.
Note the polarity flip: anti-liftability requires forward-liftability of
the body, because of the nested implications inside `existsAtMostOne`. -/
lemma isAntiLiftable_existsAtMostOne {body : S.Value → Formula S}
    (h : ∀ v, IsLiftable (body v)) :
    IsAntiLiftable (Formula.existsAtMostOne body) :=
  IsAntiLiftable.forall_ (fun x =>
    IsAntiLiftable.forall_ (fun y =>
      IsAntiLiftable.imp (h x)
        (IsAntiLiftable.imp (h y) (IsAntiLiftable.eq x y))))

/-- **`boxPast ls (event E)` is anti-liftable.** This is the forward-axiom
enabler: `box (past event)` is backwards-preserved because new agents
with empty histories vacuously fail `past event`, so any large-universe
existential witness quorum must consist of lifted small-universe agents,
which via `IsCoalescent.restrict_quorum` projects to a small-universe
witness. -/
lemma isAntiLiftable_boxPastEvent (ls : List S.Value) (E : EventAtom S) :
    IsAntiLiftable (Formula.boxPast ls (Formula.event E)) := by
  -- boxPast ls φ = box ls (past φ) = imp (diamond ls (imp (past φ) bot)) bot
  change IsAntiLiftable
    (Formula.imp
      (Formula.diamond ls
        (Formula.imp (Formula.past (Formula.event E)) Formula.bot))
      Formula.bot)
  exact IsAntiLiftable.imp
    (IsLiftable.diamondNotPastEvent ls E)
    IsAntiLiftable.bot

/-- The same result specialised to `ofEvent E` for convenience. -/
lemma isAntiLiftable_boxPast_ofEvent (ls : List S.Value)
    (E : Signature.EventType S) :
    IsAntiLiftable (Formula.boxPast ls (Formula.ofEvent E)) :=
  isAntiLiftable_boxPastEvent ls ⟨E.sym, E.args⟩

end Sugar

/-! ## §3. Catalog: every ThyHBB1 axiom is in the liftable fragment -/

section ThyHBB1Catalog

open ModalDistribution.Examples

/-- The `safeFormula` used in `voteBackwardAxiom` is liftable.  It is a
disjunction:

* First disjunct: at most one value has been proposed — an `existsAtMostOne`
  over a past event, which is liftable because the body is anti-liftable.
* Second disjunct: for every learner `l'`, some `(ℓ,l')`-quorum intersection
  has a sequential participant — which uses the `diamondSeq` constructor. -/
theorem safeFormula_isLiftable
    (proposeSymb : Signature.EventSymb S) (learner : S.Value) :
    IsLiftable (safeFormula (S := S) proposeSymb learner) := by
  unfold safeFormula
  apply isLiftable_or
  · -- ∃≤1 v ↦ ♢ᶠ↓[[]] (ofEvent ⟨proposeSymb, [v]⟩)
    apply isLiftable_existsAtMostOne
    intro v
    exact isAntiLiftable_diamondPast_empty (isAntiLiftable_ofEvent _)
  · -- ∀ᶠ l' ↦ ♢ᶠ[[learner, l']] seq
    exact IsLiftable.forall_ (fun l' => IsLiftable.diamondSeq [learner, l'])

/-- `safeFormula` is *also* anti-liftable: the first disjunct's body is
liftable, and the second disjunct's `diamond ls seq` is anti-liftable
via `IsAntiLiftable.diamond`. -/
theorem safeFormula_isAntiLiftable
    (proposeSymb : Signature.EventSymb S) (learner : S.Value) :
    IsAntiLiftable (safeFormula (S := S) proposeSymb learner) := by
  unfold safeFormula
  apply isAntiLiftable_or
  · -- ∃≤1 v ↦ ♢ᶠ↓[[]] (ofEvent ⟨proposeSymb, [v]⟩)
    apply isAntiLiftable_existsAtMostOne
    intro v
    exact isLiftable_diamondPast_empty (isLiftable_ofEvent _)
  · -- ∀ᶠ l' ↦ ♢ᶠ[[learner, l']] seq
    exact IsAntiLiftable.forall_ (fun l' =>
      IsAntiLiftable.diamond learner [l'] IsAntiLiftable.seq)

/-- `echoBackwardAxiom` is liftable. Shape: `∀ v, echo(v) ⇒ ♢↓[[]] propose(v)`.
The implication needs an anti-liftable antecedent (the echo event) and a
liftable consequent (the empty-list past diamond). -/
theorem echoBackwardAxiom_isLiftable
    (proposeSymb echoSymb : Signature.EventSymb S) :
    IsLiftable (echoBackwardAxiom (S := S) proposeSymb echoSymb) := by
  unfold echoBackwardAxiom
  refine IsLiftable.forall_ (fun v => ?_)
  refine IsLiftable.imp ?_ ?_
  · exact isAntiLiftable_ofEvent _
  · exact isLiftable_diamondPast_empty (isLiftable_ofEvent _)

/-- `voteBackwardAxiom` is liftable. Shape:
`∀ learner value, vote(learner,value) ⇒ (safe ∧ □ᶠ↓[[learner]] echo(value))`.
The load-bearing part is the `boxPast` in the consequent — liftable
because Murdoch–Sheff's `□` is existential-over-quorums. -/
theorem voteBackwardAxiom_isLiftable
    (proposeSymb echoSymb voteSymb : Signature.EventSymb S) :
    IsLiftable (voteBackwardAxiom (S := S) proposeSymb echoSymb voteSymb) := by
  unfold voteBackwardAxiom
  refine IsLiftable.forall_ (fun learner => ?_)
  refine IsLiftable.forall_ (fun value => ?_)
  refine IsLiftable.imp ?_ ?_
  · -- antecedent: ofEvent ⟨voteSymb, [learner, value]⟩
    exact isAntiLiftable_ofEvent _
  · -- consequent: safeFormula ∧ᶠ □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)
    apply isLiftable_and
    · exact safeFormula_isLiftable proposeSymb learner
    · exact isLiftable_boxPast (isLiftable_ofEvent _)

/-- `deliverBackwardAxiom` is liftable. Same shape as `voteBackwardAxiom`
but with `deliver` in the antecedent and `vote` under the box-past. -/
theorem deliverBackwardAxiom_isLiftable
    (voteSymb deliverSymb : Signature.EventSymb S) :
    IsLiftable (deliverBackwardAxiom (S := S) voteSymb deliverSymb) := by
  unfold deliverBackwardAxiom
  refine IsLiftable.forall_ (fun reporting => ?_)
  refine IsLiftable.forall_ (fun learner => ?_)
  refine IsLiftable.forall_ (fun value => ?_)
  refine IsLiftable.imp ?_ ?_
  · exact isAntiLiftable_ofEvent _
  · exact isLiftable_boxPast (isLiftable_ofEvent _)

/-- `echoNonEquivAxiom` is liftable. Shape:
`∀ v v', echo(v) ⇒ ↓ echo(v') ⇒ v = v'`. Pure propositional structure
over events, past events, and value equality. -/
theorem echoNonEquivAxiom_isLiftable
    (echoSymb : Signature.EventSymb S) :
    IsLiftable (echoNonEquivAxiom (S := S) echoSymb) := by
  unfold echoNonEquivAxiom
  refine IsLiftable.forall_ (fun value => ?_)
  refine IsLiftable.forall_ (fun altValue => ?_)
  refine IsLiftable.imp ?_ ?_
  · exact isAntiLiftable_ofEvent _
  · refine IsLiftable.imp ?_ ?_
    · exact IsAntiLiftable.past (isAntiLiftable_ofEvent _)
    · exact IsLiftable.eq _ _

/-! ## §4. The forward axioms — now in the fragment via `diamondNotPastEvent`

The forward axioms `echoForwardAxiom`, `voteForwardAxiom`, and
`deliverForwardAxiom` all have an antecedent of the form
`live ∧ □ᶠ↓[[ℓ]] event` (or a variant). The `□ᶠ↓[[ℓ]] event` is handled
by the `diamondNotPastEvent` constructor of `IsLiftable` (added to the
inductive in §1), which reflects the semantic fact that new (empty-
history) agents vacuously fail `past event`. This is exactly the
`IsAntiLiftable (boxPast ls event)` witness, and lets the forward
axioms' antecedents be anti-liftable. -/

/-- `echoForwardAxiom` is liftable. Shape:
`∀ v, (live ∧ ♢↓[[]] propose(v)) ⇒ ∃ witness, ↕ echo(witness)`.
The `♢↓[[]]` is an empty-list diamond past, which is already
anti-liftable via `isAntiLiftable_diamondPast_empty` (no `diamondNotPastEvent`
needed for this axiom — the empty-list diamond is handled structurally). -/
theorem echoForwardAxiom_isLiftable
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb : Signature.EventSymb S) :
    IsLiftable (echoForwardAxiom (S := S) liveSymb proposeSymb echoSymb) := by
  unfold echoForwardAxiom
  refine IsLiftable.forall_ (fun value => ?_)
  refine IsLiftable.imp ?_ ?_
  · -- antecedent: predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]] (ofEvent ⟨proposeSymb, [value]⟩)
    apply isAntiLiftable_and
    · exact isAntiLiftable_predicate0 _
    · exact isAntiLiftable_diamondPast_empty (isAntiLiftable_ofEvent _)
  · -- consequent: ∃ witness, ↕ echo(witness)
    apply isLiftable_exists
    intro _
    exact isLiftable_sometime (isLiftable_ofEvent _)

/-- `voteForwardAxiom` is liftable. Shape:
`∀ ℓ v, (⇕ safe) ⇒ ((live ∧ □ᶠ↓[[ℓ]] echo(v)) ⇒ ↕ vote(ℓ, v))`.
Uses both `safeFormula_isAntiLiftable` (for the `⇕ safe` part) and
`isAntiLiftable_boxPast_ofEvent` (for the `□ᶠ↓[[ℓ]] echo(v)` part) — the
latter is powered by the new `diamondNotPastEvent` constructor. -/
theorem voteForwardAxiom_isLiftable
    (liveSymb : Signature.PredSymb S)
    (proposeSymb echoSymb voteSymb : Signature.EventSymb S) :
    IsLiftable
      (voteForwardAxiom (S := S) liveSymb proposeSymb echoSymb voteSymb) := by
  unfold voteForwardAxiom
  refine IsLiftable.forall_ (fun learner => ?_)
  refine IsLiftable.forall_ (fun _value => ?_)
  refine IsLiftable.imp ?_ ?_
  · -- antecedent: ⇕ᶠ (safeFormula proposeSymb learner)
    -- alwaysPast φ = not (sometime (not φ))
    show IsAntiLiftable
      (Formula.alwaysPast (safeFormula proposeSymb learner))
    unfold Formula.alwaysPast
    apply isAntiLiftable_not
    apply isLiftable_sometime
    apply isLiftable_not
    exact safeFormula_isAntiLiftable proposeSymb learner
  · -- consequent: (live ∧ □ᶠ↓[[learner]] echo(v)) ⇒ ↕ vote(learner, v)
    refine IsLiftable.imp ?_ ?_
    · -- predicate0 liveSymb ∧ᶠ □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩)
      apply isAntiLiftable_and
      · exact isAntiLiftable_predicate0 _
      · exact isAntiLiftable_boxPast_ofEvent _ _
    · -- ↕ vote(learner, value)
      exact isLiftable_sometime (isLiftable_ofEvent _)

/-- `deliverForwardAxiom` is liftable. Shape:
`∀ r ℓ v, (live ∧ □ᶠ↓[[r]] vote(ℓ, v)) ⇒ ↕ deliver(r, ℓ, v)`.
Uses `isAntiLiftable_boxPast_ofEvent` for the `□ᶠ↓[[r]] vote(ℓ, v)`
antecedent. -/
theorem deliverForwardAxiom_isLiftable
    (liveSymb : Signature.PredSymb S)
    (voteSymb deliverSymb : Signature.EventSymb S) :
    IsLiftable
      (deliverForwardAxiom (S := S) liveSymb voteSymb deliverSymb) := by
  unfold deliverForwardAxiom
  refine IsLiftable.forall_ (fun _reporting => ?_)
  refine IsLiftable.forall_ (fun _learner => ?_)
  refine IsLiftable.forall_ (fun _value => ?_)
  refine IsLiftable.imp ?_ ?_
  · apply isAntiLiftable_and
    · exact isAntiLiftable_predicate0 _
    · exact isAntiLiftable_boxPast_ofEvent _ _
  · exact isLiftable_sometime (isLiftable_ofEvent _)

end ThyHBB1Catalog

end LiftableFragment
end Grassroots
end ModalDistribution
