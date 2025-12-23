import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf

/-!
# Completeness for Diamond Formula

The diamond formula encodes `◇ᶠ_{learners} φ` (quorum-based possibility modality).

## Semantics

```lean
Sat M p e H (diamond learners φ) =
  ∃ Q ∈ (⨅ l ∈ learners, M.learner l).quorums,
    ∀ q ∈ Q, ∃ t ∈ H, t.place = q ∧ Sat M t.place t.event t.time φ
```

## Encoding

The encoding creates quorum-witness tuple variables:
- For each minimal quorum Q and tuple of witnesses (one per quorum member)
- Check if all witnesses are in prehistory and satisfy φ

This is the most complex formula encoding due to:
1. Iterating over minimal quorums (exponential in participants)
2. Creating witness tuples for each quorum
3. Connecting quorum membership with witness satisfaction

## Completeness Strategy

If `Sat M ... (diamond learners φ)` holds:
1. Extract the witnessing quorum Q from semantics
2. For each q ∈ Q, get the witness world wq satisfying φ
3. Find the minimal quorum Q' ⊆ Q encoded in MinQ
4. By IH, each witness can have its u' set true
5. The tuple encoding for Q' with correct witnesses satisfies the clauses

Key helpers needed:
- `assignmentOf_minQ_iff`: MinQ encodes minimal quorums correctly
- `worldInPrehistory_of_mem`: Witnesses in prehistory get Mem = true
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- Completeness for diamond: bidirectional IH gives satisfying assignment.

    This is the most complex completeness case due to the quorum structure.

    The bidirectional property is: u = true ↔ Sat M ... (diamond learners φ) -/
theorem encodeFormula_complete_diamond
    (b : Bounds S) (learners : List S.Value) (φ : Formula S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    -- Bidirectional IH: gives witness with u' ↔ Sat φ
    (ih : ∀ (w : WId b) (st : EncState b),
      st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true →
      EncState.WellFormed st →
      ∃ σ_ext : SAT.Assignment (Var b),
        (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
        (encodeFormula b φ w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
        (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) φ ↔
         σ_ext (FVar.toVar b (encodeFormula b φ w st).1) = true))
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b (Formula.diamond learners φ) w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.diamond learners φ) ↔
       σ_ext (FVar.toVar b (encodeFormula b (Formula.diamond learners φ) w st).1) = true) := by
  -- The bidirectional property: u = true ↔ Sat M ... (diamond learners φ)

  -- Sat M ... (diamond learners φ) uses Sat.check recursion
  -- The semantics: check learners Set.univ where
  --   check [] acc = ∃ p' ∈ acc, Sat M p' † H φ
  --   check (ℓ::ls) acc = ∀ O ∈ (M.learner ℓ).quorums, check ls (acc ∩ O)

  -- The diamond encoding creates:
  -- 1. For each minimal quorum Q: a tuple of witness worlds
  -- 2. For each quorum member q and potential witness w': encodes φ at w' with control u'_{q,w'}
  -- 3. Tuple variable: encodes that all members have witnesses in prehistory satisfying φ
  -- 4. u ↔ (tuple₁ ∨ ... ∨ tupleₙ) via mkBigOrIff

  -- Key steps for bidirectional proof:
  -- Forward: If Sat (diamond ...), extract witnessing quorum Q and witness function,
  --          by IH all u'_{q,wq} = true, by Mem correctness witnesses in prehistory,
  --          so tuple_Q = true, so u = true
  -- Backward: If u = true, then some tuple_Q = true, extracting quorum Q with witnesses,
  --           by IH⁻¹ all members have Sat φ at witness, by Mem witnesses in prehistory,
  --           so Sat (diamond ...)

  -- This requires:
  -- 1. Composing IH results across all quorum members and witness options
  -- 2. Showing MinQ variables correctly encode minimal quorums
  -- 3. Showing tuple variables correctly track complete witness tuples
  -- 4. The mkBigOrIff structure works bidirectionally
  sorry

end Encoding
