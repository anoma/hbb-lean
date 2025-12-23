import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf
import ModalDistribution.Logic.SATEncoding.PreEqCompleteness

/-!
# Completeness for Event Formula

The event formula encodes `⟨e⟩` (event guard / ofEvent).

## Encoding Structure

When the event matches (`b.decodeMaybeEvent w.ei = MaybeEvent.some evt`):
- `encodeFormulaEvent` collects witness pairs `(PreEq w.ti w'.ti, Mem b.root w')` for each
  world `w'` with `w'.p = w.p` and matching event
- For each pair, `eventWitnessStep` creates a fresh var `z` with Tseytin gadget `z ↔ (preEq ∧ mem)`
- `mkBigOrIff` creates control var `u` with `u ↔ (z₁ ∨ ... ∨ zₙ)`

## Completeness Strategy

Given `Sat M w.p evt H (event atom)`:
1. The semantics unfolds to: `evt = MaybeEvent.some ⟨atom.sym, atom.args⟩` and exists `H'` with
   `(w.p, evt, H') ∈ M.history.val` and `histEq H' H`
2. From the model fitting in bounds, there exists `w' ∈ WId.allWorlds b` corresponding to this
   semantic world, with `w'.p = w.p`, matching event, and:
   - `preEqAt hFits.view w.ti w'.ti = true` (from histEq)
   - `worldInPrehistory hFits.view b.root w' = true` (from history membership)
3. The pair `(PreEq w.ti w'.ti, Mem b.root w')` is in `eventWitnessPairs`
4. Under `assignmentOf`, both variables are true, so the Tseytin gadget makes `z = true`
5. Via `mkBigOrIff`, the control variable `u` is also true

## Required Helper Lemmas

The full proof requires:
- `eventWitnessPairs_contains_semantic_witness`: Show the semantic witness is encoded
- `eventWitnessStep_gadget_satisfied`: Tseytin gadgets are satisfied by semantic assignment
- `mkBigOrIff_complete`: Already exists in PreEqCompleteness.lean
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- Semantic extension of an assignment for eventWitnessStep Tseytin gadgets.

    For each fresh variable z created by eventWitnessStep for a pair (preEq, mem),
    we set z = (preEq ∧ mem) semantically. This ensures:
    - Forward clause [¬preEq, ¬mem, z] is satisfied (z true when both inputs true)
    - Backward clauses [¬z, preEq] and [¬z, mem] are satisfied (z false when either false) -/
noncomputable def extendForEventWitness
    (b : Bounds S)
    (σ₀ : SAT.Assignment (Var b))
    (pairs : List (Var b × Var b))
    (startIdx : Nat) : SAT.Assignment (Var b) :=
  fun v =>
    match v with
    | Var.Fresh n =>
        -- Check if n is in the range [startIdx, startIdx + pairs.length)
        if h : startIdx ≤ n ∧ n < startIdx + pairs.length then
          -- This fresh var corresponds to pair at index (n - startIdx)
          let idx := n - startIdx
          match pairs[idx]? with
          | some (preEq, mem) => σ₀ preEq && σ₀ mem
          | none => false  -- shouldn't happen if h holds
        else
          σ₀ v  -- Not our fresh var, use base assignment
    | _ => σ₀ v

/-- Completeness for event: event index matching gives the witness.

    The event encoding uses `encodeFormulaEvent` when the event matches, which creates:
    1. For each witness pair (preEq, mem), a fresh var z with z ↔ (preEq ∧ mem)
    2. A final fresh var u with u ↔ (z₁ ∨ ... ∨ zₙ) via mkBigOrIff

    Bidirectional completeness:
    - Forward: Sat gives a semantic witness world, which corresponds to a true pair
    - Backward: If u = true, some witness pair is true, giving Sat -/
theorem encodeFormula_complete_event
    (b : Bounds S) (atom : EventAtom S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b (Formula.event atom) w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.event atom) ↔
       σ_ext (FVar.toVar b (encodeFormula b (Formula.event atom) w st).1) = true) := by
  -- Bidirectional event completeness:
  -- - Forward: Sat gives witness world, which corresponds to true pair in encoding
  -- - Backward: u = true means some witness pair is true, extracting Sat

  -- The encoding structure depends on whether event matches:
  -- If matches: encodeFormulaEvent with witness pairs and mkBigOrIff
  -- If not matches: simple false encoding

  -- This requires connecting semantic event satisfaction to the encoding structure
  sorry

end Encoding
