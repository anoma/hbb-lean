import Lean.Parser.Command
import Lean.Elab.Tactic.ElabTerm

/-!
# Syntax extensions

This file provides the `lemma` command and the `set` tactic used throughout the
development.
-/

open Lean

/-- `lemma` means the same as `theorem`. It is used to denote "less important" theorems. -/
syntax (name := lemma) declModifiers
  group("lemma " declId ppIndent(declSig) declVal) : command

/-- Implementation of the `lemma` command, by macro expansion to `theorem`. -/
@[macro «lemma»] def expandLemma : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

namespace ModalDistribution.Tactic

open Elab Elab.Tactic Meta

/-- The arguments of the `set` tactic: the name to introduce, an optional type
ascription, the value, and an optional name for the defining equation. -/
syntax setArgsRest := ppSpace ident (" : " term)? " := " term (" with " "← "? ident)?

/--
`set a := t with h` is a variant of `let a := t`.  It adds the hypothesis
`h : a = t` to the local context and replaces `t` with `a` everywhere it can.

`set a := t with ← h` will add `h : t = a` instead.

`set! a := t with h` does not do any replacing.
-/
syntax (name := setTactic) "set" "!"? setArgsRest : tactic

@[inherit_doc setTactic]
macro "set!" rest:setArgsRest : tactic => `(tactic| set ! $rest:setArgsRest)

elab_rules : tactic
| `(tactic| set%$tk $[!%$rw]? $a:ident $[: $ty:term]? := $val:term $[with $[←%$rev]? $h:ident]?) =>
  withMainContext do
    let (ty, vale) ← match ty with
    | some ty =>
      let ty ← Term.elabType ty
      pure (ty, ← elabTermEnsuringType val ty)
    | none =>
      let val ← elabTerm val none
      pure (← inferType val, val)
    let fvar ← liftMetaTacticAux fun goal => do
      let (fvar, goal) ← (← goal.define a.getId ty vale).intro1P
      pure (fvar, [goal])
    withMainContext <|
      Term.addTermInfo' (isBinder := true) a (mkFVar fvar)
    if rw.isNone then
      evalTactic (← `(tactic| try rewrite [show $(← Term.exprToSyntax vale) = $a from rfl] at *))
    match h, rev with
    | some h, some none =>
      evalTactic (← `(tactic| have%$tk
        $h : $a = ($(← Term.exprToSyntax vale) : $(← Term.exprToSyntax ty)) := rfl))
    | some h, some (some _) =>
      evalTactic (← `(tactic| have%$tk
        $h : ($(← Term.exprToSyntax vale) : $(← Term.exprToSyntax ty)) = $a := rfl))
    | _, _ => pure ()

end ModalDistribution.Tactic
