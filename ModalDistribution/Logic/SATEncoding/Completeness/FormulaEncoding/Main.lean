import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.AssumptionEncoding
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinBot
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinEq
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinImp
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinForall
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinAtEnd
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinPred
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinEvent
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinPast
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinSeq
import ModalDistribution.Logic.SATEncoding.Completeness.FormulaEncoding.TseytinDiamond

/-!
# Formula Encoding Completeness

This file proves that the formula encoding is **complete**: if a formula semantically holds
in a model M that fits within bounds, then there exists a SAT assignment σ that satisfies
the encoding clauses and has the control variable set to true.

## Main Theorem

`encodeFormula_complete`: For any formula φ, world w, and model M fitting in bounds b,
if `Sat M ... φ` holds semantically, then we can extend `assignmentOf` to satisfy
the formula encoding clauses with the control variable true.

## Relationship to Adequacy

- **Adequacy** (Adequacy/Main.lean): σ satisfies clauses → `modelOf b σ` semantically satisfies φ
- **Completeness** (this file): M semantically satisfies φ → ∃ σ satisfying clauses

Together, these establish that the encoding is **adequate and complete**: the Tseytin
encoding faithfully represents the semantics of each formula constructor.

## Strategy

The key insight is that `assignmentOf` sets all non-Fresh variables correctly for the
structural CNF (Mem, Level, Edge, Pred, etc.). For completeness, we need to extend
the assignment to set Fresh (Tseytin control) variables according to semantic satisfaction:

- For `u ↔ φ` encoding, set `σ(u) = (Sat M ... φ)`

This ensures the Tseytin clauses are satisfied:
- Forward clauses: if u is true, the encoded condition holds
- Backward clauses: if the condition holds, u is true

## Per-Constructor Proofs

Each formula constructor has a dedicated file proving its completeness lemma:

| File | Constructor | Key Property |
|------|-------------|--------------|
| TseytinBot | `bot` | Vacuously true (Sat = False) |
| TseytinEq | `eq v1 v2` | u = (v1 = v2), direct |
| TseytinImp | `imp φ₁ φ₂` | u = (¬u₁ ∨ u₂), uses IH |
| TseytinForall | `forall body` | u = ∧ᵢ uᵢ, uses IH |
| TseytinAtEnd | `atEnd φ` | u = u_body at root, uses IH |
| TseytinPred | `predicate atom` | u = predHolds, via assignmentOf |
| TseytinEvent | `event atom` | Witness exists via worldInPrehistory |
| TseytinPast | `past φ` | Witness exists via prehistory membership |
| TseytinSeq | `seq` | u = Seq variable, direct |
| TseytinDiamond | `diamond learners φ` | Quorum + witness, uses IH |

## References

- FormulaEncoding.lean for encoding definitions
- Completeness/AssignmentOf.lean for base assignment construction
- Adequacy/Main.lean for the adequacy direction
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Extended Assignment

For completeness, we need to extend `assignmentOf` to set Fresh variables according
to semantic satisfaction. This creates an assignment that:
1. Agrees with `assignmentOf` on structural variables
2. Sets control variables u to match `Sat M ... φ` -/

/-- Type of extended assignments that track Fresh variable values.
    The base assignment handles structural variables; this extends it for Tseytin variables. -/
structure ExtendedAssignment (b : Bounds S) where
  /-- The underlying assignment -/
  assignment : SAT.Assignment (Var b)
  /-- Evidence that structural variables match assignmentOf -/
  structural_match : ∀ v, ¬isFreshVar v → assignment v = sorry -- assignmentOf component

/-! ## Main Completeness Theorem

The theorem is proven by induction on formula structure, using per-constructor
lemmas from the dedicated files.

### Bidirectional Completeness

For recursive cases like implication, we need the control variable to match the
semantic truth value (not just be true when Sat holds). This is captured by
`encodeFormula_complete_bidir` which doesn't assume Sat but relates u to Sat.

The corollary `encodeFormula_complete_sat` extracts the positive direction when Sat holds. -/

/-- **Formula Encoding Completeness**: For any formula φ, there exists an extended assignment
    that satisfies the encoding clauses, with the control variable matching semantic truth.

    This is the fundamental completeness theorem. It states that for any formula φ,
    there exists an assignment where:
    1. Non-Fresh variables match assignmentOf
    2. All encoding clauses are satisfied
    3. The control variable equals the semantic truth value: `u = true ↔ Sat M ... φ`

    Note: This theorem extends assignmentOf with appropriate Fresh variable values.
    The extended assignment agrees with assignmentOf on all structural variables. -/
theorem encodeFormula_complete
    (b : Bounds S) (φ : Formula S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      -- 1. Extended assignment agrees with base on non-Fresh variables
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      -- 2. All encoding clauses are satisfied
      (encodeFormula b φ w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      -- 3. The control variable matches semantic truth value
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) φ ↔
       σ_ext (FVar.toVar b (encodeFormula b φ w st).1) = true) := by
  -- Prove by induction on formula structure
  induction φ generalizing w st with
  | bot =>
    exact encodeFormula_complete_bot b w st M hFits hBaseClauses hWF
  | eq v1 v2 =>
    exact encodeFormula_complete_eq b w st M hFits v1 v2 hBaseClauses hWF
  | imp φ₁ φ₂ ih₁ ih₂ =>
    exact encodeFormula_complete_imp b φ₁ φ₂ w st M hFits ih₁ ih₂ hBaseClauses hWF
  | predicate atom =>
    exact encodeFormula_complete_pred b atom w st M hFits hBaseClauses hWF
  | event atom =>
    exact encodeFormula_complete_event b atom w st M hFits hBaseClauses hWF
  | seq =>
    exact encodeFormula_complete_seq b w st M hFits hBaseClauses hWF
  | «forall» body ih =>
    exact encodeFormula_complete_forall b body w st M hFits ih hBaseClauses hWF
  | atEnd φ ih =>
    exact encodeFormula_complete_atEnd b φ w st M hFits ih hBaseClauses hWF
  | past φ ih =>
    exact encodeFormula_complete_past b φ w st M hFits ih hBaseClauses hWF
  | diamond learners φ ih =>
    exact encodeFormula_complete_diamond b learners φ w st M hFits ih hBaseClauses hWF

/-- Corollary: If a formula semantically holds, control variable is true.

    This is a simple corollary of the main completeness theorem using `.mp`. -/
theorem encodeFormula_complete_sat
    (b : Bounds S) (φ : Formula S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    (hSat : Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) φ)
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b φ w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      σ_ext (FVar.toVar b (encodeFormula b φ w st).1) = true := by
  have ⟨σ_ext, hAgree, hClauses, hIff⟩ := encodeFormula_complete b φ w st M hFits hBaseClauses hWF
  exact ⟨σ_ext, hAgree, hClauses, hIff.mp hSat⟩

/-! ## Corollary: Full Encoding Completeness

Combining formula completeness with structural completeness gives us full encoding
completeness: if assumptions hold semantically in M, the full encoding is satisfiable. -/

/-- Full encoding completeness: if all assumptions hold in M, then encodeAssumptions is SAT. -/
theorem encodeAssumptions_complete
    (b : Bounds S)
    (Γ : List (Assumption S))
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (hHolds : assumptionsHold M Γ) :
    ∃ σ : SAT.Assignment (Var b),
      (encodeAssumptions b Γ).eval σ = true := by
  sorry -- Combines encodeFormula_complete with structural completeness

end Encoding
