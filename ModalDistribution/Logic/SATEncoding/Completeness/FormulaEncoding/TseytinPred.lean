import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.TseytinGadgets
import ModalDistribution.Logic.SATEncoding.PreEqEncoding
import ModalDistribution.Logic.SATEncoding.Lemmas.Basic
import ModalDistribution.Logic.SATEncoding.Lemmas.NextFreshMono
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf
import ModalDistribution.Logic.SATEncoding.Completeness.PreEqExtension

/-!
# Completeness for Predicate Formula

The predicate formula encodes `P(args)` (atomic predicate).

## Encoding

```lean
encodeFormula b (Formula.predicate atom) w st =
  let (u, st1) := EncState.allocFresh b st
  -- For each predicate index k:
  --   Forward: Pred(p, ti, k) → u  [¬Pred, u]
  --   Backward: u → (Pred_1 ∨ ... ∨ Pred_n)  [¬u, Pred_1, ..., Pred_n]
  ...
```

## Completeness Strategy

If `Sat M ... (predicate atom)` holds, then `atom ∈ M.predInterp w.p H` for
some H ≃ prehistoryAt w.ti.

By assignmentOf construction, `Pred(p, ti, k) = predHolds ev p ti k`.
If the predicate semantically holds, then predHolds = true for the matching index k.
This satisfies the forward clause, and we set u = true.
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Helper lemmas for clause satisfaction -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkBigOrIff forward clauses are satisfied when u = true. -/
lemma mkBigOrIff_forward_clause_sat (b : Bounds S)
    (vs : List (Var b)) (st : EncState b) (σ : SAT.Assignment (Var b))
    (hU : σ (FVar.toVar b (mkBigOrIff b vs st).1) = true)
    (v : Var b) :
    SAT.Clause.eval σ
      [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (mkBigOrIff b vs st).1)] = true := by
  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
  refine ⟨SAT.Lit.pos (FVar.toVar b (mkBigOrIff b vs st).1), ?_, ?_⟩
  · simp
  · simp [SAT.Lit.eval, hU]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkBigOrIff backward clause is satisfied when u = false. -/
lemma mkBigOrIff_backward_clause_sat_false (b : Bounds S)
    (vs : List (Var b)) (st : EncState b) (σ : SAT.Assignment (Var b))
    (hU : σ (FVar.toVar b (mkBigOrIff b vs st).1) = false) :
    SAT.Clause.eval σ (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b vs st).1) ::
      vs.map SAT.Lit.pos) = true := by
  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
  refine ⟨SAT.Lit.neg (FVar.toVar b (mkBigOrIff b vs st).1), ?_, ?_⟩
  · simp
  · simp [SAT.Lit.eval, hU]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkBigOrIff backward clause is satisfied when some v = true. -/
lemma mkBigOrIff_backward_clause_sat_exists (b : Bounds S)
    (vs : List (Var b)) (st : EncState b) (σ : SAT.Assignment (Var b))
    (v : Var b) (hv : v ∈ vs) (hvTrue : σ v = true) :
    SAT.Clause.eval σ (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b vs st).1) ::
      vs.map SAT.Lit.pos) = true := by
  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
  refine ⟨SAT.Lit.pos v, ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_map]
    right
    exact ⟨v, hv, rfl⟩
  · simp [SAT.Lit.eval, hvTrue]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Guard backward clause [¬PreEq(ti,H'), ¬Pred(p,H',k), Pred(p,ti,k)] is satisfied
    when PreEq transfer preserves Pred truth. -/
lemma guardBackward_clause_sat (b : Bounds S)
    (σ : SAT.Assignment (Var b))
    (ti H' : b.times) (p : Fin b.nParticipants) (k : b.predIx)
    (hInv : σ (Var.PreEq ti H') = true → σ (Var.Pred p H' k) = true →
            σ (Var.Pred p ti k) = true) :
    SAT.Clause.eval σ [SAT.Lit.neg (Var.PreEq ti H'),
                       SAT.Lit.neg (Var.Pred p H' k),
                       SAT.Lit.pos (Var.Pred p ti k)] = true := by
  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
  by_cases hPreEq : σ (Var.PreEq ti H') = true
  · by_cases hPred : σ (Var.Pred p H' k) = true
    · -- Both true, so Pred p ti k must be true
      have hResult := hInv hPreEq hPred
      refine ⟨SAT.Lit.pos (Var.Pred p ti k), ?_, ?_⟩
      · simp
      · simp [SAT.Lit.eval, hResult]
    · -- Pred p H' k false
      refine ⟨SAT.Lit.neg (Var.Pred p H' k), ?_, ?_⟩
      · simp
      · simp [SAT.Lit.eval]
        cases h : σ (Var.Pred p H' k) <;> simp_all
  · -- PreEq false
    refine ⟨SAT.Lit.neg (Var.PreEq ti H'), ?_, ?_⟩
    · simp
    · simp [SAT.Lit.eval]
      cases h : σ (Var.PreEq ti H') <;> simp_all

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Guard forward clause [¬PreEq(ti,H'), ¬Pred(p,ti,k), Pred(p,H',k)] is satisfied
    when PreEq transfer preserves Pred truth (symmetric direction). -/
lemma guardForward_clause_sat (b : Bounds S)
    (σ : SAT.Assignment (Var b))
    (ti H' : b.times) (p : Fin b.nParticipants) (k : b.predIx)
    (hInv : σ (Var.PreEq ti H') = true → σ (Var.Pred p ti k) = true →
            σ (Var.Pred p H' k) = true) :
    SAT.Clause.eval σ [SAT.Lit.neg (Var.PreEq ti H'),
                       SAT.Lit.neg (Var.Pred p ti k),
                       SAT.Lit.pos (Var.Pred p H' k)] = true := by
  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
  by_cases hPreEq : σ (Var.PreEq ti H') = true
  · by_cases hPred : σ (Var.Pred p ti k) = true
    · -- Both true, so Pred p H' k must be true
      have hResult := hInv hPreEq hPred
      refine ⟨SAT.Lit.pos (Var.Pred p H' k), ?_, ?_⟩
      · simp
      · simp [SAT.Lit.eval, hResult]
    · -- Pred p ti k false
      refine ⟨SAT.Lit.neg (Var.Pred p ti k), ?_, ?_⟩
      · simp
      · simp [SAT.Lit.eval]
        cases h : σ (Var.Pred p ti k) <;> simp_all
  · -- PreEq false
    refine ⟨SAT.Lit.neg (Var.PreEq ti H'), ?_, ?_⟩
    · simp
    · simp [SAT.Lit.eval]
      cases h : σ (Var.PreEq ti H') <;> simp_all

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- PreEq reflexivity clause [PreEq(t,t)] is satisfied when PreEq(t,t) = true. -/
lemma preEqRefl_clause_sat (b : Bounds S)
    (σ : SAT.Assignment (Var b)) (t : b.times)
    (hRefl : σ (Var.PreEq t t) = true) :
    SAT.Clause.eval σ [SAT.Lit.pos (Var.PreEq t t)] = true := by
  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
  refine ⟨SAT.Lit.pos (Var.PreEq t t), ?_, ?_⟩
  · simp
  · simp [SAT.Lit.eval, hRefl]

/-- Completeness for predicate: predHolds gives the witness.

    The predicate encoding uses mkBigOrIff on Pred variables.
    The bidirectional property requires:
    - Forward: If `Sat M ... (predicate atom)` holds, then u = true
    - Backward: If u = true, then `Sat M ... (predicate atom)` holds

    The forward direction uses the fact that Sat implies a witness predicate index
    where predHolds = true. The backward direction uses that u = true implies
    some Pred variable is true, which means predHolds is true for that index. -/
theorem encodeFormula_complete_pred
    (b : Bounds S) (atom : PredicateAtom S) (w : WId b) (st : EncState b)
    (M : Model S (Fin b.nParticipants)) (hFits : FitsInBounds b M)
    (hBaseClauses : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true)
    (hWF : EncState.WellFormed st) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬isFreshVar v → σ_ext v = assignmentOf b M hFits v) ∧
      (encodeFormula b (Formula.predicate atom) w st).2.clauses.all (SAT.Clause.eval σ_ext) = true ∧
      (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt hFits.view w.ti) (Formula.predicate atom) ↔
       σ_ext (FVar.toVar b (encodeFormula b (Formula.predicate atom) w st).1) = true) := by
  classical
  let ev := hFits.view
  let σ₀ := assignmentOf b M hFits
  let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
  let idxs := predIxList b pred
  let literals := idxs.map (fun k => Var.Pred w.p w.ti k)
  let freshIdx := st.nextFresh

  -- The semantic value we want u to have
  let semVal : Bool :=
    decide (Sat M w.p (b.decodeMaybeEvent w.ei) (prehistoryAt ev w.ti) (.predicate atom))

  -- Split on whether idxs is empty - this affects the encoding structure
  by_cases hEmpty : idxs = []

  /- EMPTY CASE: idxs = [] -/
  · -- For empty case, the encoding is just mkBigOrIff on []
    -- which adds [¬u] where u = Fresh freshIdx
    -- σ_ext only needs to set u to semVal (which must be false)
    let σ_ext : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n = freshIdx then semVal else σ₀ v
      | _ => σ₀ v

    use σ_ext
    refine ⟨?nonFresh, ?clauses, ?iff⟩

    case nonFresh =>
      intro v hNotFresh
      cases v with
      | Fresh n =>
          exfalso
          apply hNotFresh
          simp only [isFreshVar, Var.isFresh]
      | _ => rfl

    case iff =>
      have hUId : (encodeFormula b (.predicate atom) w st).1.id = freshIdx := by
        simp only [encodeFormula, mkBigOrIff, EncState.allocFresh]
        split <;> rfl
      have hUVar : FVar.toVar b (encodeFormula b (.predicate atom) w st).1 = Var.Fresh freshIdx := by
        simp only [FVar.toVar, hUId]
      constructor
      · intro hSat
        rw [hUVar]
        simp only [σ_ext, ↓reduceIte]
        simp only [semVal, decide_eq_true_eq]
        exact hSat
      · intro hU
        rw [hUVar] at hU
        simp only [σ_ext, ↓reduceIte] at hU
        simp only [semVal, decide_eq_true_eq] at hU
        exact hU

    case clauses =>
      unfold encodeFormula
      simp only [pred, idxs, hEmpty, List.map_nil, ↓reduceDIte]
      rw [List.all_eq_true]
      intro clause hClause
      -- Analyze where clause comes from
      simp only [mkBigOrIff, List.foldl, EncState.addClause, EncState.allocFresh] at hClause
      rw [List.mem_cons] at hClause
      cases hClause with
      | inl hNew =>
          -- New clause: [¬u] where u = Fresh freshIdx
          subst hNew
          -- The clause is [neg (FVar.toVar b ⟨freshIdx⟩)]
          -- Need to show this evaluates to true
          unfold SAT.Clause.eval SAT.Lit.eval FVar.toVar
          simp only [List.foldl, List.map_nil, Bool.false_or]
          -- σ_ext (Fresh freshIdx) = semVal
          -- Note: freshIdx = st.nextFresh by definition
          have hFreshEval : σ_ext (Var.Fresh st.nextFresh) = semVal := by
            simp only [σ_ext]
            have : st.nextFresh = freshIdx := rfl
            simp only [this, ↓reduceIte]
          rw [hFreshEval]
          rw [Bool.not_eq_true']
          -- Show semVal = false when idxs = []
          unfold semVal
          rw [decide_eq_false_iff_not]
          intro hSat
          simp only [Sat] at hSat
          -- Sat for predicate: ∃ H', histEq H' H ∧ pred ∈ M.predInterp w.p H'
          -- If pred is in M.predInterp, it must be in b.preds by FitsInBounds
          -- But idxs = [] means no k has b.preds.get k = pred
          obtain ⟨H', hHistEq, hPredMem⟩ := hSat
          -- Use FitsInBounds: pred must have an index
          have hPredInBounds : ∃ k : b.predIx, b.preds.get k = pred := by
            use ev.predIxOf pred
            exact ev.pred_spec pred
          -- But that contradicts idxs = []
          obtain ⟨k, hK⟩ := hPredInBounds
          have hKInIdxs : k ∈ idxs := by
            simp only [idxs, predIxList, List.mem_filter, List.mem_finRange, hK, decide_true,
              and_self]
          rw [hEmpty] at hKInIdxs
          cases hKInIdxs
      | inr hOld =>
          -- Base clause
          have hBase := (List.all_eq_true.mp hBaseClauses) clause hOld
          rw [SAT.Clause.eval_eq_any] at hBase ⊢
          rw [List.any_eq_true] at hBase ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hBase
          refine ⟨lit, hLitMem, ?_⟩
          cases lit with
          | pos v =>
              simp only [SAT.Lit.eval] at hLitTrue ⊢
              cases v with
              | Fresh n =>
                  simp only [σ_ext]
                  split
                  · next hEq =>
                      exfalso
                      have hNotIn := hWF.fresh_not_in_clauses hOld hLitMem
                      exact hNotIn (congrArg Var.Fresh hEq)
                  · exact hLitTrue
              | _ => exact hLitTrue
          | neg v =>
              simp only [SAT.Lit.eval] at hLitTrue ⊢
              cases v with
              | Fresh n =>
                  simp only [σ_ext]
                  split
                  · next hEq =>
                      exfalso
                      have hNotIn := hWF.fresh_not_in_clauses hOld hLitMem
                      exact hNotIn (congrArg Var.Fresh hEq)
                  · exact hLitTrue
              | _ => exact hLitTrue

  /- NON-EMPTY CASE: idxs ≠ [] -/
  · -- Non-empty case requires handling addPreEqFrom Fresh vars
    -- Unfold the encoding structure
    cases hMk : mkBigOrIff b literals st with
    | mk u st₁ =>
      let st₂ := addPreEqFrom b w.ti st₁
      let st₃ := addPreEqReflAll b st₂
      -- st₄ is the final state after adding bidirectional guards
      let st₄ := (Bounds.timesL b).foldl (fun stCur H' =>
        idxs.foldl (fun stAcc k =>
          let backward := [ SAT.Lit.neg (Var.PreEq w.ti H')
                          , SAT.Lit.neg (Var.Pred w.p H' k)
                          , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
          let forward := [ SAT.Lit.neg (Var.PreEq w.ti H')
                         , SAT.Lit.neg (Var.Pred w.p w.ti k)
                         , SAT.Lit.pos (Var.Pred w.p H' k) ]
          EncState.addClause b (EncState.addClause b stAcc backward) forward
        ) stCur
      ) st₃

      -- For non-empty case, we need an extended σ that handles addPreEqFrom Fresh vars
      -- Use addPreEqFrom_clauses_satisfiable to get a satisfying assignment for st₂

      -- First, show st₁ is well-formed and st.clauses ⊆ st₁.clauses
      have hMkSt1 : (mkBigOrIff b literals st).2 = st₁ := by simp only [hMk]
      have hWF1 : st₁.WellFormed := by
        rw [← hMkSt1]
        exact mkBigOrIff_wf b literals st hWF
          (by intro v hv n hEq; simp only [literals, List.mem_map] at hv
              obtain ⟨_, _, hvEq⟩ := hv; subst hvEq; exact Var.noConfusion hEq)

      -- Key semantic property: semVal = true ↔ ∃ k ∈ idxs, predHolds ev w.p w.ti k = true
      have hSemValIff : semVal = true ↔
          ∃ k ∈ idxs, predHolds ev w.p w.ti k = true := by
        unfold semVal
        simp only [decide_eq_true_eq]
        constructor
        · intro hSat
          simp only [Sat] at hSat
          obtain ⟨H', hHistEq, hPredMem⟩ := hSat
          use ev.predIxOf pred
          constructor
          · simp only [idxs, predIxList, List.mem_filter, List.mem_finRange,
              ev.pred_spec pred, decide_true, and_self]
          · unfold predHolds prehistoryOfTime
            simp only [decide_eq_true_eq]
            refine ⟨H', hHistEq, ?_⟩
            rwa [ev.pred_spec pred]
        · intro ⟨k, hKMem, hPredTrue⟩
          unfold predHolds prehistoryOfTime at hPredTrue
          simp only [decide_eq_true_eq] at hPredTrue
          obtain ⟨H', hHistEq, hPredMem⟩ := hPredTrue
          simp only [idxs, predIxList, List.mem_filter, List.mem_finRange, true_and] at hKMem
          simp only [decide_eq_true_eq] at hKMem
          simp only [pred] at hKMem
          unfold Sat
          exact ⟨H', hHistEq, hKMem ▸ hPredMem⟩

      -- Key insight: We use a custom freshExt that sets freshIdx = semVal
      -- and then apply the addPreEqPair fold to extend it for addPreEqFrom Fresh vars.
      --
      -- Define freshExt₀: freshIdx = semVal, other indices = false (like σ₀)
      let freshExt₀ : Nat → Bool := fun n => if n = freshIdx then semVal else false

      -- Show st₁.clauses are satisfied with freshExt₀
      -- Base clauses: satisfied by hBaseClauses (no Fresh vars by WF)
      -- mkBigOrIff clauses: satisfied by semVal definition (see below)
      let σ₁ : SAT.Assignment (Var b) := fun v =>
        match v with
        | Var.Fresh n => freshExt₀ n
        | _ => σ₀ v

      have hSt1Sat : st₁.clauses.all (SAT.Clause.eval σ₁) = true := by
        rw [List.all_eq_true]
        intro clause hClause1
        rw [← hMkSt1] at hClause1
        rcases (mkBigOrIff_clause_mem_iff b literals st clause).mp hClause1 with
          hBase | ⟨v, hv, hFwd⟩ | hBack
        -- Base clauses: for Fresh n with n < st.nextFresh, σ₁ = σ₀ (both give false)
        · have hEval := (List.all_eq_true.mp hBaseClauses) clause hBase
          rw [SAT.Clause.eval_eq_any] at hEval ⊢
          rw [List.any_eq_true] at hEval ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hEval
          refine ⟨lit, hLitMem, ?_⟩
          cases lit with
          | pos w =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases w with
            | Fresh n =>
              -- σ₀(Fresh _) = false always, so hLitTrue : false = true is a contradiction
              simp only [assignmentOf] at hLitTrue
              exact absurd hLitTrue Bool.false_ne_true
            | _ => exact hLitTrue
          | neg w =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases w with
            | Fresh n =>
              -- σ₀(Fresh _) = false always, so hLitTrue : !false = true holds
              -- But then we need σ₁(Fresh n) = false to make !σ₁(Fresh n) = true
              have hNLt := hWF.fresh_lt_nextFresh clause hBase (SAT.Lit.neg (Var.Fresh n)) hLitMem n rfl
              have hNe : n ≠ freshIdx := by omega
              simp only [σ₁, freshExt₀, hNe, ↓reduceIte, Bool.not_false]
            | _ => exact hLitTrue
        -- Forward clause [¬v, u] where v ∈ literals and u = Fresh freshIdx
        · rw [hFwd, SAT.Clause.eval_eq_any, List.any_eq_true]
          -- u = Fresh freshIdx, σ₁(u) = freshExt₀(freshIdx) = semVal
          have hUID : (mkBigOrIff b literals st).1.id = freshIdx := by
            simp only [mkBigOrIff, EncState.allocFresh]; rfl
          have hUVal : σ₁ (FVar.toVar b (mkBigOrIff b literals st).1) = semVal := by
            simp only [σ₁, FVar.toVar, hUID, freshExt₀, ↓reduceIte]
          by_cases hSem : semVal = true
          · -- semVal = true, so u = true, forward clause satisfied
            refine ⟨SAT.Lit.pos (FVar.toVar b (mkBigOrIff b literals st).1),
                    List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
            simp only [SAT.Lit.eval, hUVal, hSem]
          · -- semVal = false, so all Pred vars in literals are false
            -- ¬v = true for v ∈ literals
            simp only [Bool.not_eq_true] at hSem
            have hAllFalse : ∀ k ∈ idxs, σ₁ (Var.Pred w.p w.ti k) = false := by
              intro k hk
              simp only [σ₁, σ₀, assignmentOf_Pred]
              by_contra hContra
              simp only [Bool.eq_false_iff, not_not] at hContra
              have hSemTrue : semVal = true := by
                simp only [semVal, hSemValIff]
                exact ⟨k, hk, hContra⟩
              exact Bool.false_ne_true (hSem.symm.trans hSemTrue)
            -- v ∈ literals means v = Var.Pred w.p w.ti k for some k ∈ idxs
            simp only [literals, List.mem_map] at hv
            obtain ⟨k, hkMem, hvEq⟩ := hv
            subst hvEq
            refine ⟨SAT.Lit.neg (Var.Pred w.p w.ti k), List.Mem.head _, ?_⟩
            simp only [SAT.Lit.eval, hAllFalse k hkMem, Bool.not_false]
        -- Backward clause [¬u, v₁, ..., vₙ]
        · rw [hBack, SAT.Clause.eval_eq_any, List.any_eq_true]
          have hUID : (mkBigOrIff b literals st).1.id = freshIdx := by
            simp only [mkBigOrIff, EncState.allocFresh]; rfl
          have hUVal : σ₁ (FVar.toVar b (mkBigOrIff b literals st).1) = semVal := by
            simp only [σ₁, FVar.toVar, hUID, freshExt₀, ↓reduceIte]
          by_cases hSem : semVal = true
          · -- semVal = true means ∃ k ∈ idxs, predHolds
            have hExists := hSemValIff.mp hSem
            obtain ⟨k, hkMem, hkTrue⟩ := hExists
            have hPredLit : SAT.Lit.pos (Var.Pred w.p w.ti k) ∈
                (literals.map SAT.Lit.pos : List (SAT.Lit (Var b))) := by
              simp only [List.mem_map]
              exact ⟨Var.Pred w.p w.ti k, List.mem_map.mpr ⟨k, hkMem, rfl⟩, rfl⟩
            refine ⟨SAT.Lit.pos (Var.Pred w.p w.ti k),
                    List.mem_cons_of_mem _ hPredLit, ?_⟩
            simp only [SAT.Lit.eval, σ₁, σ₀, assignmentOf_Pred]
            exact hkTrue
          · -- semVal = false, so ¬u = true
            refine ⟨SAT.Lit.neg (FVar.toVar b (mkBigOrIff b literals st).1),
                    List.Mem.head _, ?_⟩
            simp only [SAT.Lit.eval, hUVal, hSem, Bool.not_false]

      -- Now apply the fold to extend freshExt₀ for addPreEqFrom Fresh vars
      -- We use a satProp similar to addPreEqFrom_clauses_satisfiable
      let satProp (stk : EncState b) : Prop :=
        st₁.nextFresh ≤ stk.nextFresh ∧
        stk.WellFormed ∧
        ∃ freshExt : Nat → Bool,
          (∀ n < st₁.nextFresh, freshExt n = freshExt₀ n) ∧
          stk.clauses.all (SAT.Clause.eval
            (fun v => match v with | Var.Fresh n => freshExt n | _ => σ₀ v)) = true

      have hBaseProp : satProp st₁ := by
        refine ⟨le_refl _, hWF1, freshExt₀, fun n _ => rfl, ?_⟩
        convert hSt1Sat using 2

      have hStep : ∀ H' stk, satProp stk → satProp (addPreEqPair b w.ti H' stk) := by
        intro H' stk ⟨hMono, hWFstk, freshExt, hBase', hSat⟩
        let stk' := addPreEqPair b w.ti H' stk
        have hMono' : st₁.nextFresh ≤ stk'.nextFresh :=
          le_trans hMono (addPreEqPair_nextFresh_mono b w.ti H' stk)
        have hWFstk' : stk'.WellFormed := addPreEqPair_wf b w.ti H' stk hWFstk
        have hExtExists := addPreEqPair_equisat b M hFits w.ti H' stk hWFstk freshExt hSat
        obtain ⟨freshExt', hAgree', hSat'⟩ := hExtExists
        refine ⟨hMono', hWFstk', freshExt', ?_, hSat'⟩
        intro n hn
        have hnStk : n < stk.nextFresh := Nat.lt_of_lt_of_le hn hMono
        rw [hAgree' n hnStk, hBase' n hn]

      have hFoldProp : ∀ (ts : List b.times) (stk : EncState b),
          satProp stk → satProp (ts.foldl (fun acc H' => addPreEqPair b w.ti H' acc) stk) := by
        intro ts
        induction ts with
        | nil => intro stk hSat; simp only [List.foldl_nil]; exact hSat
        | cons H' rest ih =>
            intro stk hSat
            simp only [List.foldl_cons]
            exact ih (addPreEqPair b w.ti H' stk) (hStep H' stk hSat)

      have hSt2Prop : satProp st₂ := by
        simp only [st₂, addPreEqFrom]
        exact hFoldProp (Bounds.timesL b) st₁ hBaseProp

      obtain ⟨_, _, freshExt, hFreshBase, hFreshSat⟩ := hSt2Prop

      -- Define σ_ext from freshExt
      let σ_ext : SAT.Assignment (Var b) := fun v =>
        match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v

      use σ_ext
      refine ⟨?nonFresh, ?clauses, ?iff⟩

      case nonFresh =>
        intro v hNotFresh
        cases v with
        | Fresh n =>
            exfalso
            apply hNotFresh
            simp only [isFreshVar, Var.isFresh]
        | _ => rfl

      case iff =>
        have hUId : (encodeFormula b (.predicate atom) w st).1.id = freshIdx := by
          simp only [encodeFormula, mkBigOrIff, EncState.allocFresh]
          split <;> rfl
        have hUVar : FVar.toVar b (encodeFormula b (.predicate atom) w st).1 = Var.Fresh freshIdx := by
          simp only [FVar.toVar, hUId]
        -- freshIdx < st₁.nextFresh since st₁ = mkBigOrIff output, which allocates freshIdx
        have hFreshIdxLt : freshIdx < st₁.nextFresh := by
          simp only [freshIdx]
          have hMkNext : st₁.nextFresh = st.nextFresh + 1 := by
            have : (mkBigOrIff b literals st).2.nextFresh = st.nextFresh + 1 :=
              mkBigOrIff_nextFresh b literals st
            rw [← hMkSt1]; exact this
          omega
        -- freshExt agrees with freshExt₀ on freshIdx
        have hFreshIdx : freshExt freshIdx = freshExt₀ freshIdx := hFreshBase freshIdx hFreshIdxLt
        have hFreshIdxVal : freshExt freshIdx = semVal := by
          rw [hFreshIdx]
          simp only [freshExt₀, ↓reduceIte]
        constructor
        · intro hSat
          rw [hUVar]
          simp only [σ_ext, hFreshIdxVal]
          simp only [semVal, decide_eq_true_eq]
          exact hSat
        · intro hU
          rw [hUVar] at hU
          simp only [σ_ext, hFreshIdxVal] at hU
          simp only [semVal, decide_eq_true_eq] at hU
          exact hU

      case clauses =>
        unfold encodeFormula
        simp only [pred, idxs, hEmpty, ↓reduceDIte]
        rw [List.all_eq_true]
        intro clause hClause

        -- Helper: σ_ext agrees with σ₀ on non-Fresh vars
        have hAgree : ∀ v, ¬Var.isFresh v → σ_ext v = σ₀ v := by
          intro v hNotFresh
          cases v with
          | Fresh n => exact absurd rfl hNotFresh
          | _ => rfl

        -- Case 1: Clause from st.clauses (base clauses)
        by_cases hBase : clause ∈ st.clauses
        · -- Base clause: use hBaseClauses, WF ensures Fresh st.nextFresh doesn't appear
          have hEval := (List.all_eq_true.mp hBaseClauses) clause hBase
          rw [SAT.Clause.eval_eq_any] at hEval ⊢
          rw [List.any_eq_true] at hEval ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hEval
          refine ⟨lit, hLitMem, ?_⟩
          cases lit with
          | pos v =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases v with
            | Fresh n =>
              -- For Fresh n in base clause, need to show σ_ext (Fresh n) = σ₀ (Fresh n)
              -- Since n < st.nextFresh (by WF) and freshIdx = st.nextFresh,
              -- we have n ≠ freshIdx, so σ_ext(Fresh n) = freshExt n = freshExt₀ n = false = σ₀(Fresh n)
              have hNLt := hWF.fresh_lt_nextFresh clause hBase (SAT.Lit.pos (Var.Fresh n)) hLitMem n rfl
              have hNe : n ≠ freshIdx := by omega
              -- freshExt agrees with freshExt₀ on n since n < st₁.nextFresh
              have hN_lt_st1 : n < st₁.nextFresh := by
                have hMkNext : st₁.nextFresh = st.nextFresh + 1 := by
                  have : (mkBigOrIff b literals st).2.nextFresh = st.nextFresh + 1 :=
                    mkBigOrIff_nextFresh b literals st
                  rw [← hMkSt1]; exact this
                omega
              have hAgree : freshExt n = freshExt₀ n := hFreshBase n hN_lt_st1
              simp only [σ_ext, hAgree, freshExt₀, hNe, ↓reduceIte]
              -- freshExt₀ n = false for n ≠ freshIdx
              exact hLitTrue
            | _ => exact hLitTrue
          | neg v =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases v with
            | Fresh n =>
              have hNLt := hWF.fresh_lt_nextFresh clause hBase (SAT.Lit.neg (Var.Fresh n)) hLitMem n rfl
              have hNe : n ≠ freshIdx := by omega
              have hN_lt_st1 : n < st₁.nextFresh := by
                have hMkNext : st₁.nextFresh = st.nextFresh + 1 := by
                  have : (mkBigOrIff b literals st).2.nextFresh = st.nextFresh + 1 :=
                    mkBigOrIff_nextFresh b literals st
                  rw [← hMkSt1]; exact this
                omega
              have hAgree : freshExt n = freshExt₀ n := hFreshBase n hN_lt_st1
              simp only [σ_ext, hAgree, freshExt₀, hNe, ↓reduceIte]
              exact hLitTrue
            | _ => exact hLitTrue

        -- The remaining clauses are from the encoding itself
        -- We analyze clause membership through the nested structure

        -- Helper: σ_ext on Fresh freshIdx = semVal
        -- freshIdx < st₁.nextFresh since st₁ = mkBigOrIff output, which allocates freshIdx
        have hFreshIdxLt' : freshIdx < st₁.nextFresh := by
          simp only [freshIdx]
          have hMkNext : st₁.nextFresh = st.nextFresh + 1 := by
            have : (mkBigOrIff b literals st).2.nextFresh = st.nextFresh + 1 :=
              mkBigOrIff_nextFresh b literals st
            rw [← hMkSt1]; exact this
          omega
        have hFreshEval : σ_ext (Var.Fresh freshIdx) = semVal := by
          simp only [σ_ext]
          have hAgree : freshExt freshIdx = freshExt₀ freshIdx := hFreshBase freshIdx hFreshIdxLt'
          rw [hAgree]
          simp only [freshExt₀, ↓reduceIte]

        -- Helper: σ_ext on non-Fresh equals σ₀
        have hNonFreshEval : ∀ v, ¬Var.isFresh v → σ_ext v = σ₀ v := by
          intro v hNotFresh
          cases v with
          | Fresh n => exact absurd rfl hNotFresh
          | _ => rfl

        -- Helper: For Pred vars, σ_ext = σ₀
        have hPredEval : ∀ (p' : Fin b.nParticipants) (ti' : b.times) (k' : b.predIx),
            σ_ext (Var.Pred p' ti' k') = σ₀ (Var.Pred p' ti' k') := fun _ _ _ => rfl

        -- Helper: For PreEq vars, σ_ext = σ₀
        have hPreEqEval : ∀ (ti1 ti2 : b.times),
            σ_ext (Var.PreEq ti1 ti2) = σ₀ (Var.PreEq ti1 ti2) := fun _ _ => rfl

        -- The encoding structure: mkBigOrIff → addPreEqFrom → addPreEqReflAll → guard folds
        -- Clause ∈ st₄.clauses and ∉ st.clauses
        -- We need to trace through where clause came from

        -- Key insight: All NEW clauses either:
        -- (a) Contain only non-Fresh vars (PreEq, Pred) - satisfied by σ₀ properties
        -- (b) Are mkBigOrIff clauses - satisfied by semVal definition

        -- For (a): PreEq reflexivity [PreEq(t,t)] is satisfied because preEqAt is reflexive
        -- Transfer guards [¬PreEq(ti,H'), ¬Pred(p,H',k), Pred(p,ti,k)] are satisfied because:
        --   If PreEq(ti,H') = true and Pred(p,H',k) = true, then by predHolds_invariant_of_histEq,
        --   Pred(p,ti,k) = true as well

        -- For (b): mkBigOrIff clauses are:
        --   Forward: [¬Pred_k, u] for each k ∈ idxs - satisfied if Pred_k false or u true
        --   Backward: [¬u, Pred_1, ..., Pred_n] - satisfied if u false or some Pred_k true
        -- When semVal = true, u = true so forward clauses satisfied
        -- When semVal = false, u = false so backward clause satisfied
        -- semVal = true iff some Pred_k true (via predHolds definition)

        -- The detailed clause membership analysis requires tracking through:
        -- 1. mkBigOrIff creates forward [¬v, u] and backward [¬u, v_1, ..., v_n] clauses
        -- 2. addPreEqFrom adds PreEq obligation clauses (Fresh vars only ≥ st₁.nextFresh)
        -- 3. addPreEqReflAll adds [PreEq(t,t)] unit clauses
        -- 4. Guard folds add transfer clauses (no Fresh vars)

        -- Helper: PreEq reflexivity under σ₀
        have hPreEqRefl : ∀ t : b.times, σ₀ (Var.PreEq t t) = true := by
          intro t
          simp only [σ₀]
          rw [assignmentOf_PreEq]
          unfold preEqAt prehistoryOfTime
          simp only [decide_eq_true_eq]
          exact PreHistory.histEq_refl _

        -- Helper: If PreEq(ti, ti') = true under σ₀, then predHolds is invariant
        have hPredInvariant : ∀ (ti ti' : b.times) (p' : Fin b.nParticipants) (k' : b.predIx),
            σ₀ (Var.PreEq ti ti') = true →
            σ₀ (Var.Pred p' ti' k') = true →
            σ₀ (Var.Pred p' ti k') = true := by
          intro ti ti' p' k' hPreEq hPred
          simp only [σ₀] at hPreEq hPred ⊢
          rw [assignmentOf_PreEq] at hPreEq
          unfold preEqAt at hPreEq
          simp only [decide_eq_true_eq] at hPreEq
          rw [assignmentOf_Pred] at hPred ⊢
          exact predHolds_invariant_of_histEq ev p' ti' ti k'
            (PreHistory.histEq_symm hPreEq) ▸ hPred

        -- Helper: Lit eval under σ_ext equals eval under σ₀ for non-Fresh vars
        have hNonFreshLit : ∀ (lit : SAT.Lit (Var b)),
            (∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n) →
            SAT.Lit.eval σ_ext lit = SAT.Lit.eval σ₀ lit := by
          intro lit hNoFresh
          cases lit with
          | pos v =>
            simp only [SAT.Lit.eval]
            cases v with
            | Fresh n =>
              exfalso
              exact hNoFresh n rfl
            | _ => rfl
          | neg v =>
            simp only [SAT.Lit.eval]
            cases v with
            | Fresh n =>
              exfalso
              exact hNoFresh n rfl
            | _ => rfl

        -- Now we prove clause satisfaction using the helper lemmas

        -- Key: σ_ext(u) = semVal where u = Fresh freshIdx
        have hUEval : σ_ext (FVar.toVar b u) = semVal := by
          have hUID : u.id = freshIdx := by
            have hEq : (mkBigOrIff b literals st).1 = u := by simp only [hMk]
            rw [← hEq]
            unfold mkBigOrIff EncState.allocFresh
            rfl
          unfold FVar.toVar
          simp only [hUID]
          exact hFreshEval

        -- Clause subset chain
        have hSt1 : st.clauses ⊆ st₁.clauses := by
          have : (mkBigOrIff b literals st).2 = st₁ := by simp only [hMk]
          rw [← this]
          exact mkBigOrIff_clauses_subset b literals st
        have hSt2 : st₁.clauses ⊆ st₂.clauses :=
          addPreEqFrom_clauses_subset b w.ti st₁
        have hSt3 : st₂.clauses ⊆ st₃.clauses :=
          addPreEqReflAll_clauses_subset b st₂

        -- The clause is not in st.clauses, so it's from encoding
        -- Case analysis on clause source

        -- First check if clause is in st₁.clauses (from mkBigOrIff)
        by_cases hSt1Mem : clause ∈ st₁.clauses
        · -- Clause from mkBigOrIff (but not base)
          -- mkBigOrIff clauses are either:
          -- - forward: [¬v, u] for v ∈ literals
          -- - backward: [¬u, v₁, ..., vₙ]
          -- All satisfied because σ_ext(u) = semVal and semVal ↔ ∃ k, Pred true

          -- Since clause ∈ st₁.clauses and clause ∉ st.clauses,
          -- it's a new clause from mkBigOrIff
          -- We need to show it's satisfied

          -- The key insight: mkBigOrIff clauses are satisfied when:
          -- - Forward [¬v, u]: u = true OR v = false
          -- - Backward [¬u, v₁, ..., vₙ]: u = false OR some v_k = true
          -- Our semVal definition ensures: semVal = true ↔ ∃ k, Pred(w.p,w.ti,k) = true

          -- Case split on semVal
          by_cases hSem : semVal = true
          · -- semVal = true, so u = true
            -- Forward clauses [¬v, u] satisfied because u = true
            -- Backward clause [¬u, ...] satisfied because ∃ k, v_k = true
            have hU : σ_ext (FVar.toVar b u) = true := by rw [hUEval, hSem]
            -- Need to show clause evaluates to true
            -- This requires knowing the exact form of the clause
            -- For forward clauses, use mkBigOrIff_forward_clause_sat
            -- For backward clause, use mkBigOrIff_backward_clause_sat_exists

            -- The semVal = true case implies ∃ k ∈ idxs, Pred(w.p, w.ti, k) = true
            have hExists := hSemValIff.mp hSem
            obtain ⟨k, hkMem, hkTrue⟩ := hExists
            -- The Pred var for k is in literals
            have hPredInLit : Var.Pred w.p w.ti k ∈ literals := by
              simp only [literals, List.mem_map]
              exact ⟨k, hkMem, rfl⟩
            -- Under σ_ext (= σ₀ on Pred vars), this Pred is true
            have hPredTrue : σ_ext (Var.Pred w.p w.ti k) = true := by
              have hkTrue' : σ₀ (Var.Pred w.p w.ti k) = true := by
                simp only [σ₀]
                rw [assignmentOf_Pred]
                exact hkTrue
              exact hkTrue'

            -- Now we need to show clause evaluates to true
            -- mkBigOrIff creates clauses: [¬v, u] for v ∈ vs, and [¬u, v₁⁺,...,vₙ⁺]
            -- Since u = true (hU), all forward clauses [¬v, u] are satisfied
            -- Since ∃ k, Pred(w.p,w.ti,k) = true, the backward clause is also satisfied

            -- Use the structural characterization of mkBigOrIff clauses
            -- Since clause ∈ st₁.clauses and clause ∉ st.clauses, it's a new clause
            -- from mkBigOrIff. By mkBigOrIff_newClause_vars, all lits have var = u or ∈ vs
            -- The forward clauses [¬v, u] have u positive, so satisfied by hU
            -- The backward clause [¬u, v₁⁺,...] has some v_k true, so satisfied
            have hMkU : (mkBigOrIff b literals st).1 = u := by simp only [hMk]
            have hMkSt : (mkBigOrIff b literals st).2 = st₁ := by simp only [hMk]

            -- For any new clause, either it's a forward clause (satisfied by u=true)
            -- or it's the backward clause (satisfied by ∃ Pred_k true)
            -- Use the backward clause sat lemma since we have a witness
            by_cases hBack : clause = SAT.Lit.neg (FVar.toVar b u) :: literals.map SAT.Lit.pos
            · -- It's the backward clause
              rw [hBack, ← hMkU]
              exact mkBigOrIff_backward_clause_sat_exists b literals st σ_ext
                (Var.Pred w.p w.ti k) hPredInLit hPredTrue
            · -- It's a forward clause [¬v, u] - satisfied since u = true
              -- Use mkBigOrIff_clause_mem_iff to characterize clause
              have hCharac := (mkBigOrIff_clause_mem_iff b literals st clause).mp
                (hMkSt ▸ hSt1Mem)
              -- hCharac : clause ∈ st.clauses ∨ forward ∨ backward
              cases hCharac with
              | inl hInBase => exact absurd hInBase hBase
              | inr hNew =>
                cases hNew with
                | inl hForward =>
                  obtain ⟨v, _, hClauseEq⟩ := hForward
                  rw [hClauseEq]
                  have hU' : σ_ext (FVar.toVar b (mkBigOrIff b literals st).1) = true := by
                    rw [hMkU]; exact hU
                  exact mkBigOrIff_forward_clause_sat b literals st σ_ext hU' v
                | inr hBackward =>
                  exfalso
                  apply hBack
                  rw [← hMkU, hBackward]

          · -- semVal = false, so u = false
            -- Backward clause [¬u, ...] satisfied because ¬u = true
            have hU : σ_ext (FVar.toVar b u) = false := by
              rw [hUEval]
              simp only [Bool.eq_false_iff]
              intro hContra
              exact hSem hContra
            -- The backward clause is satisfied because ¬u = true
            -- Forward clauses [¬v, u] might or might not be satisfied,
            -- but we need to check what type of clause this is
            have hMkU : (mkBigOrIff b literals st).1 = u := by simp only [hMk]
            have hMkSt : (mkBigOrIff b literals st).2 = st₁ := by simp only [hMk]

            by_cases hBack : clause = SAT.Lit.neg (FVar.toVar b u) :: literals.map SAT.Lit.pos
            · -- It's the backward clause - satisfied since u = false
              rw [hBack, ← hMkU]
              have hU' : σ_ext (FVar.toVar b (mkBigOrIff b literals st).1) = false := by
                rw [hMkU]; exact hU
              exact mkBigOrIff_backward_clause_sat_false b literals st σ_ext hU'
            · -- It's a forward clause [¬v, u]
              -- When semVal = false, all literals are false, so ¬v = true
              -- Use mkBigOrIff_clause_mem_iff to characterize clause
              have hCharac := (mkBigOrIff_clause_mem_iff b literals st clause).mp
                (hMkSt ▸ hSt1Mem)
              cases hCharac with
              | inl hInBase => exact absurd hInBase hBase
              | inr hNew =>
                cases hNew with
                | inl hForward =>
                  obtain ⟨v, hv, hClauseEq⟩ := hForward
                  rw [hClauseEq]
                  -- v ∈ literals means v = Var.Pred w.p w.ti k for some k ∈ idxs
                  simp only [literals, List.mem_map] at hv
                  obtain ⟨k, hkMem, hvEq⟩ := hv
                  subst hvEq
                  -- semVal = false means ¬∃ k, predHolds
                  -- So predHolds ev w.p w.ti k = false for all k ∈ idxs
                  have hPredFalse : σ_ext (Var.Pred w.p w.ti k) = false := by
                    simp only [σ_ext, σ₀, assignmentOf_Pred]
                    -- Need ¬ predHolds ev w.p w.ti k
                    by_contra hContra
                    simp only [Bool.eq_false_iff, not_not] at hContra
                    apply hSem
                    rw [hSemValIff]
                    exact ⟨k, hkMem, hContra⟩
                  -- Forward clause [¬v, u] is satisfied since v = false, so ¬v = true
                  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
                  refine ⟨SAT.Lit.neg (Var.Pred w.p w.ti k), List.Mem.head _, ?_⟩
                  simp only [SAT.Lit.eval, hPredFalse, Bool.not_false]
                | inr hBackward =>
                  exfalso
                  apply hBack
                  rw [← hMkU, hBackward]

        · -- Clause not from mkBigOrIff, check if from addPreEqFrom/addPreEqReflAll/guards
          by_cases hSt2Mem : clause ∈ st₂.clauses
          · -- From addPreEqFrom (in st₂ but not st₁)
            -- The key insight: we constructed freshExt via the fold on addPreEqPair,
            -- and hFreshSat guarantees st₂.clauses are satisfied by σ_ext.
            -- σ_ext agrees with the assignment used in hFreshSat (both use freshExt for
            -- Fresh vars and σ₀ for non-Fresh vars), so clause is satisfied.
            have hClauseSat := List.all_eq_true.mp hFreshSat clause hSt2Mem
            -- hFreshSat uses the assignment: fun v => match v with | Fresh n => freshExt n | _ => σ₀ v
            -- σ_ext is defined the same way, so they're definitionally equal
            exact hClauseSat
          · by_cases hSt3Mem : clause ∈ st₃.clauses
            · -- From addPreEqReflAll (but not st₂)
              -- These are [PreEq(t,t)] unit clauses for some t
              -- Use foldl_addClause_mem to characterize
              simp only [st₃, addPreEqReflAll] at hSt3Mem
              rcases foldl_addClause_mem b (Bounds.timesL b) st₂
                  (fun t => [SAT.Lit.pos (Var.PreEq t t)]) clause hSt3Mem with
                hSt2' | ⟨t, _, hEq⟩
              · -- clause ∈ st₂.clauses contradicts hSt2Mem
                exact absurd hSt2' hSt2Mem
              · -- clause = [pos (Var.PreEq t t)] for some t
                rw [hEq]
                rw [SAT.Clause.eval_eq_any, List.any_eq_true]
                refine ⟨SAT.Lit.pos (Var.PreEq t t), List.Mem.head _, ?_⟩
                simp only [SAT.Lit.eval]
                -- σ_ext (Var.PreEq t t) = σ₀ (Var.PreEq t t) = true
                exact hPreEqRefl t
            · -- From guard folds
              -- These are transfer clauses with only Pred and PreEq vars
              -- Clause is in st₄.clauses but not in st₃.clauses
              -- Use nested_foldl_addClause2_mem to characterize the clause
              -- Define the clause constructors
              let backward := fun (H' : b.times) (k : b.predIx) =>
                [ SAT.Lit.neg (Var.PreEq w.ti H')
                , SAT.Lit.neg (Var.Pred w.p H' k)
                , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
              let forward := fun (H' : b.times) (k : b.predIx) =>
                [ SAT.Lit.neg (Var.PreEq w.ti H')
                , SAT.Lit.neg (Var.Pred w.p w.ti k)
                , SAT.Lit.pos (Var.Pred w.p H' k) ]
              -- Convert hClause to match the expected type for nested_foldl_addClause2_mem
              have hClause' : clause ∈ st₄.clauses := by
                simp only [st₄, st₃, st₂, idxs, pred, ← hMkSt1]
                convert hClause using 2
              rcases nested_foldl_addClause2_mem b (Bounds.timesL b) idxs st₃
                  backward forward clause hClause' with
                hSt3' | ⟨H', hH', k, hk, hEq⟩
              · -- clause ∈ st₃.clauses contradicts hSt3Mem
                exact absurd hSt3' hSt3Mem
              · -- clause is backward or forward for some H', k
                cases hEq with
                | inl hBack =>
                  -- backward clause: [¬PreEq(w.ti, H'), ¬Pred(p, H', k), Pred(p, w.ti, k)]
                  simp only [backward] at hBack
                  rw [hBack]
                  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
                  -- Case on whether PreEq(w.ti, H') = true
                  -- Note: σ_ext = σ₀ on PreEq and Pred vars (non-Fresh)
                  by_cases hPreEq : σ_ext (Var.PreEq w.ti H') = true
                  · -- PreEq is true, so we need to show implication holds
                    by_cases hPredH' : σ_ext (Var.Pred w.p H' k) = true
                    · -- Both guards true, so Pred(p, w.ti, k) must be true
                      -- Use hPredInvariant (works on σ₀, but σ_ext = σ₀ on these vars)
                      have hPredTi := hPredInvariant w.ti H' w.p k hPreEq hPredH'
                      refine ⟨SAT.Lit.pos (Var.Pred w.p w.ti k), ?_, ?_⟩
                      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                          (List.mem_singleton.mpr rfl))
                      · simp only [SAT.Lit.eval]; exact hPredTi
                    · -- Pred(p, H', k) = false, so ¬Pred(p, H', k) = true
                      refine ⟨SAT.Lit.neg (Var.Pred w.p H' k), ?_, ?_⟩
                      · exact List.mem_cons_of_mem _ (List.Mem.head _)
                      · simp only [SAT.Lit.eval, hPredH', Bool.not_false]
                  · -- PreEq is false, so ¬PreEq = true
                    refine ⟨SAT.Lit.neg (Var.PreEq w.ti H'), ?_, ?_⟩
                    · exact List.Mem.head _
                    · simp only [SAT.Lit.eval, hPreEq, Bool.not_false]
                | inr hFwd =>
                  -- forward clause: [¬PreEq(w.ti, H'), ¬Pred(p, w.ti, k), Pred(p, H', k)]
                  simp only [forward] at hFwd
                  rw [hFwd]
                  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
                  -- Case on whether PreEq(w.ti, H') = true
                  by_cases hPreEq : σ_ext (Var.PreEq w.ti H') = true
                  · -- PreEq is true
                    by_cases hPredTi : σ_ext (Var.Pred w.p w.ti k) = true
                    · -- Both guards true, so Pred(p, H', k) must be true
                      -- PreEq(w.ti, H') = true means prehistory equality, symmetric
                      -- Use hPredInvariant with swapped times
                      have hPreEqSym : σ₀ (Var.PreEq H' w.ti) = true := by
                        rw [hPreEqEval] at hPreEq
                        simp only [σ₀] at hPreEq ⊢
                        rw [assignmentOf_PreEq] at hPreEq ⊢
                        unfold preEqAt at hPreEq ⊢
                        simp only [decide_eq_true_eq] at hPreEq ⊢
                        exact PreHistory.histEq_symm hPreEq
                      have hPredH' := hPredInvariant H' w.ti w.p k hPreEqSym hPredTi
                      refine ⟨SAT.Lit.pos (Var.Pred w.p H' k), ?_, ?_⟩
                      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                          (List.mem_singleton.mpr rfl))
                      · simp only [SAT.Lit.eval]; exact hPredH'
                    · -- Pred(p, w.ti, k) = false, so ¬Pred(p, w.ti, k) = true
                      refine ⟨SAT.Lit.neg (Var.Pred w.p w.ti k), ?_, ?_⟩
                      · exact List.mem_cons_of_mem _ (List.Mem.head _)
                      · simp only [SAT.Lit.eval, hPredTi, Bool.not_false]
                  · -- PreEq is false, so ¬PreEq = true
                    refine ⟨SAT.Lit.neg (Var.PreEq w.ti H'), ?_, ?_⟩
                    · exact List.Mem.head _
                    · simp only [SAT.Lit.eval, hPreEq, Bool.not_false]

end Encoding
