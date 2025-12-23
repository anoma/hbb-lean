import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf

/-!
# Completeness for Past Formula

The past formula encodes `past φ` (existential past / there exists a witness in prehistory).

## Semantics

```lean
Sat M p e H (past φ) = ∃ t ∈ H, t.place = p ∧ Sat M t.place t.event t.time φ
```

## Encoding (After Fix)

The encoding uses auxiliary variables for correct existential Tseytin:

```lean
-- For each witness w' in prehistory:
aux_i ↔ (Mem(w.ti, w') ∧ u'_i)

-- Main control variable:
u ↔ ∃ i. aux_i
```

Clauses:
1. `(Mem ∧ u') → u`  for each witness: `[¬Mem, ¬u', u]`
2. `(Mem ∧ u') → aux`  for each witness: `[¬Mem, ¬u', aux]`
3. `aux → Mem`: `[¬aux, Mem]`
4. `aux → u'`: `[¬aux, u']`
5. `u → (aux₁ ∨ ... ∨ auxₙ)`: `[¬u, aux₁, ..., auxₙ]`

## Completeness Strategy

If `Sat M ... (past φ)` holds, there exists a witness world w' in prehistory with:
- w'.place = w.p
- Sat M w' φ

By FitsInBounds, this witness has a corresponding WId w'_id with:
- worldInPrehistory ev w.ti w'_id = true (gives Mem = true)
- By IH, u'_{w'_id} can be set true

Setting aux_{w'_id} = true satisfies clause 5 (since one aux is true).
Clauses 1-4 are satisfied because:
- Mem = true, u' = true, aux = true for the witness
- For non-witnesses: we only need (Mem ∧ u') → aux (which holds if aux = false and Mem or u' is false)

The key insight is that we SET u and the witness aux to true, and use IH to get u' = true.
Non-witness auxiliaries can be set to false.
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- Completeness for past: bidirectional IH gives satisfying assignment.

    This is the key completeness lemma for the fixed past encoding.
    The auxiliary variable approach ensures only ONE witness needs φ to hold.

    The bidirectional property is: u = true ↔ ∃ t ∈ H, t.place = w.p ∧ Sat M t φ -/
theorem encodeFormula_complete_past
    (b : Bounds S) (φ : Formula S) (w : WId b) (st : EncState b)
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
      (encodeFormula b (Formula.past φ) w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.past φ) ↔
       σ_ext (FVar.toVar b (encodeFormula b (Formula.past φ) w st).1) = true) := by
  -- The bidirectional property: u = true ↔ ∃ t ∈ H, t.place = w.p ∧ Sat M t φ

  -- The past encoding iterates over all possible witness worlds w' and creates:
  -- - For each w': encodes φ at w' with control variable u'_{w'}
  -- - aux_{w'} ↔ (Mem ∧ u'_{w'}) via Tseytin gadget
  -- - u ↔ (aux₁ ∨ ... ∨ auxₙ) via mkBigOrIff

  -- Key steps for bidirectional proof:
  -- Forward: If Sat (past φ), extract witness t, find corresponding w', by IH u'_{w'} = true,
  --          Mem = true for this witness, so aux_{w'} = true, so u = true
  -- Backward: If u = true, then some aux_{w'} = true, so Mem = true and u'_{w'} = true,
  --           by IH⁻¹ Sat φ at w', and Mem gives w' in prehistory, so Sat (past φ)

  -- This requires:
  -- 1. Composing IH results across all witness worlds
  -- 2. Showing Mem variables correctly track prehistory membership
  -- 3. The aux gadget and mkBigOrIff structures work bidirectionally
  sorry

end Encoding
