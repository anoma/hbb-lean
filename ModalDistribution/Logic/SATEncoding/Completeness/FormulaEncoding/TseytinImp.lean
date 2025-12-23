import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.FormulaEncodingLemmasAll
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf

/-!
# Completeness for Implication Formula

The implication formula encodes `φ₁ → φ₂`.

## Encoding

```lean
encodeFormula b (Formula.imp φ₁ φ₂) w st =
  let (u₁, st1) := encodeFormula b φ₁ w st
  let (u₂, st2) := encodeFormula b φ₂ w st1
  let (u, st3) := EncState.allocFresh b st2
  -- Tseytin clauses for u ↔ (¬u₁ ∨ u₂)
  -- Forward: u → (¬u₁ ∨ u₂)  ≡  [¬u, ¬u₁, u₂]
  -- Backward 1: ¬u₁ → u  ≡  [u₁, u]
  -- Backward 2: u₂ → u  ≡  [¬u₂, u]
  ...
```

## Completeness Strategy

The implication is special because we need **bidirectional** IHs: we need to know what
value u₁ takes based on whether Sat φ₁ holds or not.

Key insight: `Sat (φ₁ → φ₂)` means `Sat φ₁ → Sat φ₂`. By classical logic:
- Either `Sat φ₁` is true, in which case `Sat φ₂` is also true (use IH₂)
- Or `Sat φ₁` is false, in which case we need u₁ = false (but IH only gives u₁ = true when Sat φ₁)

The solution: We need a generalized IH that provides a witness regardless of whether
Sat holds, with the control variable matching the semantic truth value.

For now, we prove this using classical case analysis and assume the more general
bidirectional IH structure is available.
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- Completeness for imp: control variable matches semantic truth value.

    Uses IHs that provide witnesses regardless of whether Sat holds,
    with the control variable matching the semantic truth value.

    ## Strategy

    The key challenge for implication is composing two IH witnesses (σ₁ for φ₁, σ₂ for φ₂)
    into a single σ_ext. The difficulty is that IH₂ requires `assignmentOf` to satisfy
    st1's clauses, but st1 contains Tseytin clauses from φ₁ that aren't satisfied by
    `assignmentOf` (which sets Fresh vars to false).

    Solution: We construct σ_ext by combining σ₁ and a *shifted* σ₂:
    - Fresh vars in [st.nextFresh, st1.nextFresh): from σ₁
    - Fresh vars in [st1.nextFresh, st2.nextFresh): from σ₂ shifted by (st1.nextFresh - st.nextFresh)
    - The final u at freshIdx: set to (¬u₁ ∨ u₂)

    The key insight is that encodeFormula is *structurally deterministic*: encoding φ₂
    starting from st vs st1 produces the same clause STRUCTURE, just with Fresh indices
    shifted by (st1.nextFresh - st.nextFresh). So σ₂'s values for φ₂'s Fresh vars can
    be shifted to give correct values for st1's encoding of φ₂. -/
theorem encodeFormula_complete_imp
    (b : Bounds S) (φ₁ φ₂ : Formula S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    -- Bidirectional IH for φ₁: gives witness with u ↔ Sat
    (ih₁ : ∀ (w : WId b) (st : EncState b),
      st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true →
      EncState.WellFormed st →
      ∃ σ_ext : SAT.Assignment (Var b),
        (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
        (encodeFormula b φ₁ w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
        (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) φ₁ ↔
         σ_ext (FVar.toVar b (encodeFormula b φ₁ w st).1) = true))
    -- Bidirectional IH for φ₂: gives witness with u ↔ Sat
    (ih₂ : ∀ (w : WId b) (st : EncState b),
      st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true →
      EncState.WellFormed st →
      ∃ σ_ext : SAT.Assignment (Var b),
        (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
        (encodeFormula b φ₂ w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
        (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) φ₂ ↔
         σ_ext (FVar.toVar b (encodeFormula b φ₂ w st).1) = true))
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b (Formula.imp φ₁ φ₂) w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.imp φ₁ φ₂) ↔
       σ_ext (FVar.toVar b (encodeFormula b (Formula.imp φ₁ φ₂) w st).1) = true) := by

  -- Get the encoding structure
  let res1 := encodeFormula b φ₁ w st
  let u₁ := res1.1
  let st1 := res1.2
  let res2 := encodeFormula b φ₂ w st1
  let u₂ := res2.1
  let st2 := res2.2
  let freshIdx := st2.nextFresh

  -- Use IH₁ to get σ₁ with u₁ ↔ Sat φ₁
  have ⟨σ₁, hAgree1, hClauses1, hIff1⟩ := ih₁ w st hBaseClauses hWF

  -- Use IH₂ at the ORIGINAL state st (not st1)
  -- This gives us a witness σ₂ that satisfies φ₂'s clauses when started from st
  have ⟨σ₂, hAgree2, hClauses2, hIff2⟩ := ih₂ w st hBaseClauses hWF

  -- The offset for shifting σ₂'s Fresh indices
  let offset := st1.nextFresh - st.nextFresh

  -- The control var for φ₂ when encoded from st
  let u₂_from_st := (encodeFormula b φ₂ w st).1

  -- Construct σ_ext by combining σ₁ and shifted σ₂
  let σ_ext : SAT.Assignment (Var b) := fun v =>
    match v with
    | Var.Fresh n =>
        if n < st.nextFresh then
          -- Fresh vars before our encoding started: use assignmentOf
          assignmentOf b M hFits v
        else if n < st1.nextFresh then
          -- Fresh vars from φ₁ encoding: use σ₁
          σ₁ v
        else if n < st2.nextFresh then
          -- Fresh vars from φ₂ encoding: use σ₂ shifted back by offset
          -- The variable at index n in st1's encoding corresponds to
          -- index (n - offset) in st's encoding
          σ₂ (Var.Fresh (n - offset))
        else if n = freshIdx then
          -- The final u for imp: (¬u₁ ∨ u₂)
          -- u₁ is σ₁(u₁) by construction, u₂ is σ₂(u₂_from_st) shifted
          let u₁_val := σ₁ (FVar.toVar b u₁)
          let u₂_val := σ₂ (FVar.toVar b u₂_from_st)
          !u₁_val || u₂_val
        else
          -- Fresh vars after our encoding: shouldn't matter
          false
    | _ => assignmentOf b M hFits v

  use σ_ext

  refine ⟨?_, ?_, ?_⟩

  · -- Non-fresh vars agree with assignmentOf
    intro v hNotFresh
    cases v with
    | Fresh n =>
        exfalso
        exact hNotFresh (by simp only [isFreshVar, Var.isFresh])
    | _ => rfl

  · -- All clauses satisfied
    -- The encoding structure (from FormulaEncoding.lean):
    -- let (u1, st1) := encodeFormula b φ₁ w st
    -- let (u2, st2) := encodeFormula b φ₂ w st1
    -- let (u, st3) := EncState.allocFresh b st2
    -- st4 := addClause [u1, u]           -- backward 1: ¬u₁ → u
    -- st5 := addClause [¬u2, u]          -- backward 2: u₂ → u
    -- st6 := addClause [¬u, ¬u1, u2]     -- forward: u → (¬u₁ ∨ u₂)
    --
    -- Strategy:
    -- 1. Base clauses (st.clauses): σ_ext agrees with assignmentOf on non-Fresh
    -- 2. φ₁'s clauses: σ_ext agrees with σ₁ on Fresh vars in [st.nextFresh, st1.nextFresh)
    -- 3. φ₂'s clauses: Use structural determinism - σ₂ satisfies clauses from st,
    --    shifted σ₂ satisfies clauses from st1
    -- 4. Tseytin clauses: By construction of σ_ext at freshIdx
    --
    -- For now, this uses the structural determinism lemma (which has a sorry)
    -- to handle the φ₂ clause satisfaction.
    sorry

  · -- Bidirectional property: Sat (φ₁ → φ₂) ↔ σ_ext(u) = true
    -- The encoding returns control var u = Fresh(st2.nextFresh) = Fresh(freshIdx)
    -- σ_ext(Fresh freshIdx) = !σ₁(u₁) || σ₂(u₂_from_st)
    -- By hIff1: Sat φ₁ ↔ σ₁(u₁) = true
    -- By hIff2: Sat φ₂ ↔ σ₂(u₂_from_st) = true
    -- So σ_ext(Fresh freshIdx) = true ↔ (¬Sat φ₁ ∨ Sat φ₂) ↔ (Sat φ₁ → Sat φ₂)

    -- First, establish what the control var is
    have hControlVar : (encodeFormula b (Formula.imp φ₁ φ₂) w st).1.id = freshIdx := by
      simp only [encodeFormula]
      rfl

    -- Monotonicity facts needed for σ_ext computation
    have hMono1 : st.nextFresh ≤ st1.nextFresh :=
      encodeFormula_nextFresh_mono b φ₁ w st
    have hMono2 : st1.nextFresh ≤ st2.nextFresh :=
      encodeFormula_nextFresh_mono b φ₂ w st1

    -- And that σ_ext at the control var equals !u₁_val || u₂_val
    have hSigmaExt : σ_ext (FVar.toVar b (encodeFormula b (Formula.imp φ₁ φ₂) w st).1) =
        (!σ₁ (FVar.toVar b u₁) || σ₂ (FVar.toVar b u₂_from_st)) := by
      simp only [σ_ext, FVar.toVar, hControlVar]
      -- freshIdx = st2.nextFresh, so we need to show the cascading if-then-else evaluates correctly
      -- ¬(freshIdx < st.nextFresh) because st2.nextFresh ≥ st.nextFresh
      have h1 : ¬(freshIdx < st.nextFresh) := Nat.not_lt.mpr (Nat.le_trans hMono1 hMono2)
      -- ¬(freshIdx < st1.nextFresh) because freshIdx = st2.nextFresh ≥ st1.nextFresh
      have h2 : ¬(freshIdx < st1.nextFresh) := Nat.not_lt.mpr hMono2
      -- ¬(freshIdx < st2.nextFresh) because freshIdx = st2.nextFresh
      have h3 : ¬(freshIdx < st2.nextFresh) := Nat.lt_irrefl _
      -- freshIdx = freshIdx is true
      simp only [h1, ↓reduceIte, h2, h3]

    rw [hSigmaExt]
    simp only [Sat]
    -- Note: u₂_from_st = (encodeFormula b φ₂ w st).1 by definition
    have hU2Eq : u₂_from_st = (encodeFormula b φ₂ w st).1 := rfl
    constructor
    · intro hImp
      -- hImp: Sat φ₁ → Sat φ₂
      by_cases hSat1 : Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) φ₁
      · -- Sat φ₁, so Sat φ₂
        have hSat2 := hImp hSat1
        have hu₂_true := hIff2.mp hSat2
        rw [hU2Eq, hu₂_true]
        simp only [Bool.or_true]
      · -- ¬Sat φ₁
        have hu₁_false : σ₁ (FVar.toVar b u₁) = false := by
          rw [Bool.eq_false_iff]
          exact mt hIff1.mpr hSat1
        rw [hu₁_false]
        simp only [Bool.not_false, Bool.true_or]
    · intro hTrue
      intro hSat1
      have hu₁_true := hIff1.mp hSat1
      rw [hu₁_true] at hTrue
      simp only [Bool.not_true, Bool.false_or] at hTrue
      rw [hU2Eq] at hTrue
      exact hIff2.mpr hTrue

end Encoding
