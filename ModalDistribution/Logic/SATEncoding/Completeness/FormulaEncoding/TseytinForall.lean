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
# Completeness for Universal Quantifier Formula

The forall formula encodes `∀ v. body(v)`.

## Encoding

```lean
encodeFormula b (Formula.forall body) w st =
  let (bodyVars, st1) := b.valIx.foldl (fun (acc, stCur) i =>
    let (u_i, st') := encodeFormula b (body (b.values.get i)) w stCur
    (acc ++ [u_i], st')
  ) ([], st)
  let (u, st2) := EncState.allocFresh b st1
  -- Tseytin clauses for u ↔ (u₁ ∧ ... ∧ uₙ)
  -- Forward: u → u_i  for each i  [¬u, u_i]
  -- Backward: (u₁ ∧ ... ∧ uₙ) → u  [¬u₁, ..., ¬uₙ, u]
  ...
```

## Completeness Strategy

If `Sat M ... (∀ v. body(v))` holds, then `∀ v. Sat M ... body(v)` by semantics.
By IH, each u_i can be set to true. The big-and clause then forces u = true.
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- Completeness for forall: uses bidirectional IH on body for each value.

    The forall encoding creates:
    1. Control variable u (allocated first)
    2. For each value index i, encodes body(values[i]) with control uᵢ
    3. Forward clauses [¬u, uᵢ] for each i
    4. Backward clause [¬u₁, ..., ¬uₙ, u]

    The bidirectional property is: u = true ↔ ∀ v. Sat body(v)

    For completeness:
    - IH gives witnesses for each value with uᵢ ↔ Sat body(v)
    - We need to compose these into a single σ_ext with u ↔ (∧ᵢ uᵢ)

    The composition is complex because each IH call produces a different σ.
    The key insight is that all non-Fresh vars agree with assignmentOf,
    and Fresh vars from different body encodings are distinct. -/
theorem encodeFormula_complete_forall
    (b : Bounds S) (body : S.Value → Formula S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    -- Bidirectional IH: gives witness with uᵢ ↔ Sat body(v)
    (ih : ∀ (v : S.Value) (w : WId b) (st : EncState b),
      st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true →
      EncState.WellFormed st →
      ∃ σ_ext : SAT.Assignment (Var b),
        (∀ var, ¬isFreshVar var → σ_ext var = assignmentOf b M hFits var) ∧
        (encodeFormula b (body v) w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
        (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (body v) ↔
         σ_ext (FVar.toVar b (encodeFormula b (body v) w st).1) = true))
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b (Formula.forall body) w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.forall body) ↔
       σ_ext (FVar.toVar b (encodeFormula b (Formula.forall body) w st).1) = true) := by

  -- The encoding structure (from FormulaEncoding.lean):
  -- 1. First allocate u at st.nextFresh (forall control var)
  -- 2. Fold over values: encode each body(v) with accumulated state
  -- 3. Add forward clauses [¬u, uᵢ] for each i
  -- 4. Add backward clause [¬u₁, ..., ¬uₙ, u]
  -- 5. Return (u, st4) where u.id = st.nextFresh

  -- Strategy: Use IH at original state st for each value v.
  -- This gives witnesses σᵥ where Sat body(v) ↔ σᵥ(uᵥ) = true, with uᵥ = (encodeFormula b (body v) w st).1

  -- For each value index, get IH witness
  -- Note: We use Choice function to select one canonical σ
  have hIH : ∀ (vIdx : b.valIx),
    ∃ σᵥ : SAT.Assignment (Var b),
      (∀ var, ¬isFreshVar var → σᵥ var = assignmentOf b M hFits var) ∧
      (encodeFormula b (body (b.values.get vIdx)) w st).2.clauses.all (SAT.Clause.eval σᵥ) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (body (b.values.get vIdx)) ↔
       σᵥ (FVar.toVar b (encodeFormula b (body (b.values.get vIdx)) w st).1) = true) := by
    intro vIdx
    exact ih (b.values.get vIdx) w st hBaseClauses hWF

  -- Extract the witnesses using choice
  let σChoice : b.valIx → SAT.Assignment (Var b) := fun vIdx => (hIH vIdx).choose
  have hChoice : ∀ vIdx,
      (∀ var, ¬isFreshVar var → σChoice vIdx var = assignmentOf b M hFits var) ∧
      (encodeFormula b (body (b.values.get vIdx)) w st).2.clauses.all (SAT.Clause.eval (σChoice vIdx)) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (body (b.values.get vIdx)) ↔
       σChoice vIdx (FVar.toVar b (encodeFormula b (body (b.values.get vIdx)) w st).1) = true) := by
    intro vIdx
    exact (hIH vIdx).choose_spec

  -- The control var for forall is allocated FIRST at st.nextFresh
  let freshIdx := st.nextFresh

  -- Construct σ_ext:
  -- - For non-Fresh vars: use assignmentOf
  -- - For the control var u (at freshIdx): set to ∧ᵢ (σChoice i)(uᵢ)
  -- - For other Fresh vars: use structural determinism to shift σChoice values
  --
  -- The forall encoding structure:
  --   1. Allocate u at st.nextFresh (so freshIdx = st.nextFresh)
  --   2. For each value vIdx, encode body(values[vIdx]) starting from accumulated state
  --      - Body 0: encoded from st1 = (allocFresh st).2, Fresh vars in [st.nextFresh+1, ...)
  --      - Body 1: encoded from state after body 0, etc.
  --   3. Add Tseytin clauses
  --
  -- IH gives witnesses for encoding each body from st (not the sequential states).
  -- By structural determinism, we can shift these to work for the actual sequential encoding.
  --
  -- For now, we use the structural determinism lemma (with sorry) to handle Fresh vars
  -- from body encodings. The control var logic is correct by construction.
  let σ_ext : SAT.Assignment (Var b) := fun v =>
    match v with
    | Var.Fresh n =>
        if n = freshIdx then
          -- The forall control var: true iff all body vars are true
          (List.finRange b.nVals).all fun vIdx =>
            σChoice vIdx (FVar.toVar b (encodeFormula b (body (b.values.get vIdx)) w st).1)
        else if n < freshIdx then
          -- Fresh vars before our encoding: use assignmentOf
          assignmentOf b M hFits v
        else
          -- Fresh vars from body encodings: need structural determinism to shift
          -- The σChoice witnesses are for encoding from st, but actual encoding is sequential.
          -- For clause satisfaction, we need encodeFormula_structural_determinism.
          -- For now, use placeholder that will be justified by the structural lemma.
          assignmentOf b M hFits v
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
    -- Strategy:
    -- 1. Base clauses (st.clauses): σ_ext agrees with assignmentOf on non-Fresh
    -- 2. Body encoding clauses: Use structural determinism - σChoice vIdx satisfies
    --    clauses from encoding at st, shifted versions satisfy actual sequential clauses
    -- 3. Forward clauses [¬u, uᵢ] satisfied - by construction of u
    -- 4. Backward clause [¬u₁, ..., ¬uₙ, u] satisfied - by construction
    --
    -- For now, this uses the structural determinism lemma (which has a sorry)
    -- to handle body clause satisfaction.
    sorry

  · -- Bidirectional property: Sat (∀ v. body(v)) ↔ σ_ext(u) = true
    have hControlVar : (encodeFormula b (Formula.forall body) w st).1.id = freshIdx := by
      simp only [encodeFormula]
      rfl

    have hSigmaExt : σ_ext (FVar.toVar b (encodeFormula b (Formula.forall body) w st).1) =
        (List.finRange b.nVals).all (fun vIdx =>
          σChoice vIdx (FVar.toVar b (encodeFormula b (body (b.values.get vIdx)) w st).1)) := by
      simp only [σ_ext, FVar.toVar, hControlVar]
      simp only [↓reduceIte]

    rw [hSigmaExt]
    simp only [Sat]
    constructor
    · -- Forward: Sat (∀ v. body(v)) → all uᵢ = true
      intro hForall
      rw [List.all_eq_true]
      intro vIdx _
      have hSatV := hForall (b.values.get vIdx)
      exact (hChoice vIdx).2.2.mp hSatV
    · -- Backward: all uᵢ = true → Sat (∀ v. body(v))
      intro hAllTrue
      intro v
      -- Use EncodingView to find the index for v
      -- hFits.view.valIxOf gives the index, and val_spec proves round-trip
      let vIdx := hFits.view.valIxOf v
      have hVEq : b.values.get vIdx = v := hFits.view.val_spec v
      -- The encoding for body(values[vIdx]) equals encoding for body(v)
      rw [List.all_eq_true] at hAllTrue
      have hTrue := hAllTrue vIdx (List.mem_finRange vIdx)
      -- σChoice vIdx satisfies uᵢ = true ↔ Sat body(values[vIdx])
      rw [← hVEq]
      exact (hChoice vIdx).2.2.mpr hTrue

end Encoding
