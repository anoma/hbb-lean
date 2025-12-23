import ModalDistribution.Core.Prehistory
import ModalDistribution.Logic.SATEncoding.PreEqEncoding
import ModalDistribution.Logic.SATEncoding.TseytinGadgets

/-!
# Formula Encoding

This file implements the main SAT encoding for modal logic formulas.
It provides the recursive `encodeFormula` function that converts a modal formula
into a CNF representation using Tseytin transformation techniques.

## Main Components

- `encodeFormula`: Main recursive encoder mapping formulas to boolean variables
- Clause subset lemmas: Prove monotonicity of encoding operations
- Correctness lemmas: Relate formula encoding to semantic truth conditions

## Dependencies

This module builds on:
- `PreEqEncoding`: Provides PreEq encoding machinery for prehistory equality
- `TseytinGadgets`: Provides reusable Tseytin transformation utilities
- `Decoder`: Provides decoding functions for extracting models from SAT assignments

## References

See CLAUDE.md and the user's specification for the overall encoding architecture.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-! ## Formula Encoding -/

/-- Create a tuple control variable from encoded witness variables.

    The encoding is intentionally lightweight: one clause forces that a true tuple
    with all guards satisfied witnesses at least one member, guard clauses force
    the tuple when any guard is false, and backward clauses force the tuple when
    a witness is true. -/
def encodeTupleControl (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars : List (Var b)) (st : EncState b) :
    FVar b × EncState b :=
  let guards := (learners.zip tuple).map fun (ℓ, Q) =>
    SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)

  let (uTuple, stAfterAlloc) := EncState.allocFresh b st

  -- Forward implication: if uTuple is true and all guards hold, some witness is true.
  let st1 :=
    EncState.addClause b stAfterAlloc
      ([SAT.Lit.neg (FVar.toVar b uTuple)] ++ guards ++
        witnessVars.map SAT.Lit.pos)

  -- If a guard is false, uTuple must be true.
  let st2 :=
    (learners.zip tuple).foldl (fun stAcc (ℓ, Q) =>
      EncState.addClause b stAcc
        [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
         SAT.Lit.pos (FVar.toVar b uTuple)]) st1

  -- If a witness is true, uTuple is true.
  let st3 :=
    witnessVars.foldl (fun stAcc v =>
      EncState.addClause b stAcc
        [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)]) st2

  (uTuple, st3)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The encodeTupleControl function preserves clause subsets. -/
lemma encodeTupleControl_clauses_subset (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars : List (Var b)) (st : EncState b) :
    st.clauses ⊆ (encodeTupleControl b learners tuple witnessVars st).2.clauses := by
  simp only [encodeTupleControl]

  have hAlloc : st.clauses ⊆ (EncState.allocFresh b st).2.clauses := by
    intro c h; simp [EncState.allocFresh_clauses_eq, h]

  set allocResult := EncState.allocFresh b st
  let guards := (learners.zip tuple).map fun (ℓ, Q) =>
    SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)
  set st1 := EncState.addClause b allocResult.2
    ([SAT.Lit.neg (FVar.toVar b allocResult.1)] ++ guards ++
      witnessVars.map SAT.Lit.pos)

  have hAdd1 : allocResult.2.clauses ⊆ st1.clauses :=
    EncState.addClause_subset_clauses b allocResult.2 _

  have hGuards : st1.clauses ⊆
      ((learners.zip tuple).foldl (fun stAcc (ℓ, Q) =>
        EncState.addClause b stAcc
          [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
           SAT.Lit.pos (FVar.toVar b allocResult.1)]) st1).clauses :=
    foldl_subset_state
      (f := fun stAcc (ℓ, Q) =>
        EncState.addClause b stAcc
          [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
           SAT.Lit.pos (FVar.toVar b allocResult.1)])
      (hStep := by intro stAcc pair; exact EncState.addClause_subset_clauses b stAcc _)
      (xs := learners.zip tuple)
      (init := st1)

  set st2 := (learners.zip tuple).foldl (fun stAcc (ℓ, Q) =>
    EncState.addClause b stAcc
      [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
       SAT.Lit.pos (FVar.toVar b allocResult.1)]) st1

  have hWitness : st2.clauses ⊆
      (witnessVars.foldl (fun stAcc v =>
        EncState.addClause b stAcc
          [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b allocResult.1)]) st2).clauses :=
    foldl_subset_state
      (f := fun stAcc v =>
        EncState.addClause b stAcc
          [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b allocResult.1)])
      (hStep := by intro stAcc v; exact EncState.addClause_subset_clauses b stAcc _)
      (xs := witnessVars)
      (init := st2)

  intro clause hClause
  exact hWitness (hGuards (hAdd1 (hAlloc hClause)))

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- encodeTupleControl preserves well-formedness if witness vars that are
    Fresh have id < st.nextFresh. -/
lemma encodeTupleControl_wf (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars : List (Var b)) (st : EncState b)
    (hWF : EncState.WellFormed st)
    (hWitness : ∀ v ∈ witnessVars, ∀ n, v = Var.Fresh n → n < st.nextFresh) :
    EncState.WellFormed (encodeTupleControl b learners tuple witnessVars st).2 := by
  simp only [encodeTupleControl]
  -- After allocFresh: uTuple.id = st.nextFresh, stAfterAlloc.nextFresh = st.nextFresh + 1
  have hAllocWF : (EncState.allocFresh b st).2.WellFormed := EncState.allocFresh_wf hWF
  have hAllocNext : (EncState.allocFresh b st).2.nextFresh = st.nextFresh + 1 :=
    EncState.allocFresh_nextFresh b st
  have hUId : (EncState.allocFresh b st).1.id = st.nextFresh := by simp only [EncState.allocFresh]
  set uTuple := (EncState.allocFresh b st).1
  set stAfterAlloc := (EncState.allocFresh b st).2
  -- Guards are MinQ vars (non-Fresh), so litFreshBelow is trivially true
  let guards := (learners.zip tuple).map fun (ℓ, Q) =>
    SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)
  -- Clause 1: forward clause [¬uTuple] ++ guards ++ witnessVars.map pos
  have hC1 : clauseFreshBelow ([SAT.Lit.neg (FVar.toVar b uTuple)] ++ guards ++
      witnessVars.map SAT.Lit.pos) stAfterAlloc.nextFresh := by
    intro lit hLit
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map] at hLit
    rcases hLit with (rfl | hGuard) | ⟨v, hv, rfl⟩
    · -- ¬uTuple
      simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hUId, hAllocNext]; omega
    · -- guard (MinQ var)
      simp only [guards, List.mem_map] at hGuard
      obtain ⟨⟨ℓ, Q⟩, _, rfl⟩ := hGuard
      simp only [litFreshBelow, SAT.Lit.getVar]
    · -- witness var (positive)
      unfold litFreshBelow
      cases hVar : SAT.Lit.getVar (SAT.Lit.pos v) with
      | Fresh n =>
        simp only [SAT.Lit.getVar] at hVar
        have := hWitness v hv n hVar
        rw [hAllocNext]; omega
      | _ => trivial
  let c1 := [SAT.Lit.neg (FVar.toVar b uTuple)] ++ guards ++ witnessVars.map SAT.Lit.pos
  have hWF1 := EncState.addClause_wf hAllocWF c1 hC1
  set st1 := EncState.addClause b stAfterAlloc c1
  have hSt1Next : st1.nextFresh = st.nextFresh + 1 := by
    simp only [st1, EncState.addClause_nextFresh, hAllocNext]
  -- Helper: uTuple.id < st.nextFresh + 1
  have hULt : uTuple.id < st.nextFresh + 1 := by rw [hUId]; omega
  -- Guard folds: use foldl_addClause_wf_pair
  have hGuardClauseFB : ∀ (ℓ : S.Value) (Q : Finset b.participants),
      clauseFreshBelow [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
        SAT.Lit.pos (FVar.toVar b uTuple)] st1.nextFresh := by
    intro ℓ Q lit hLit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h => subst h; simp only [litFreshBelow, SAT.Lit.getVar]
    | inr h => subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hSt1Next]; exact hULt
  have hGuardFold := foldl_addClause_wf_pair (learners.zip tuple) st1
    (fun ℓ Q => [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q), SAT.Lit.pos (FVar.toVar b uTuple)])
    hWF1 hGuardClauseFB
  set st2 := (learners.zip tuple).foldl (fun stAcc (ℓ, Q) =>
      EncState.addClause b stAcc [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
        SAT.Lit.pos (FVar.toVar b uTuple)]) st1
  have hGuardFoldWF : st2.WellFormed := hGuardFold.1
  have hSt2Next : st2.nextFresh = st1.nextFresh := hGuardFold.2
  -- Witness folds: use foldl_addClause_wf_mem since clause validity depends on v ∈ witnessVars
  have hWitnessClauseFB : ∀ v ∈ witnessVars,
      clauseFreshBelow [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)] st2.nextFresh := by
    intro v hv lit hLit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h =>
      subst h
      unfold litFreshBelow
      cases hVar : SAT.Lit.getVar (SAT.Lit.neg v) with
      | Fresh n =>
        simp only [SAT.Lit.getVar] at hVar
        have := hWitness v hv n hVar
        simp only [hSt2Next, hSt1Next]; omega
      | _ => trivial
    | inr h =>
      subst h
      simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hSt2Next, hSt1Next]; exact hULt
  exact (foldl_addClause_wf_mem witnessVars st2
    (fun v => [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)])
    hGuardFoldWF hWitnessClauseFB).1

/-- Witness pairs for event encoding: pairs of (PreEq, Mem) variables for matching worlds.

    For an event formula at world `w`, this collects all world-ids `w'` that could serve
    as witnesses, i.e., worlds with the same participant, same event, paired with their
    PreEq and Mem variables. -/
def eventWitnessPairs
  (b : Bounds S) (w : WId b) (evt : Signature.EventType S) : List (Var b × Var b) :=
  (WId.allWorlds b).filterMap (fun w' =>
    if w'.p == w.p then
      match b.decodeMaybeEvent w'.ei with
      | MaybeEvent.some e' => if decide (e' = evt) then
          some (Var.PreEq w.ti w'.ti, Var.Mem b.root w')
        else none
      | MaybeEvent.none => none
    else none)

/-- Step function for folding over event witness pairs.
    Creates a fresh variable z and adds Tseytin clauses: z ↔ (preEq ∧ mem). -/
def eventWitnessStep (b : Bounds S) (acc : List (Var b) × EncState b)
    (pair : Var b × Var b) : List (Var b) × EncState b :=
  let (vars, stAcc) := acc
  let (preEq, mem) := pair
  let (z, stAcc') := EncState.allocFresh b stAcc
  let stAcc'' := EncState.addClause b stAcc'
    [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos preEq]
  let stAcc''' := EncState.addClause b stAcc''
    [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos mem]
  let stAcc'''' := EncState.addClause b stAcc'''
    [SAT.Lit.neg preEq, SAT.Lit.neg mem, SAT.Lit.pos (FVar.toVar b z)]
  (vars ++ [FVar.toVar b z], stAcc'''')

/-- Helper function for encoding event formulas.

    This function handles the successful case where the world's event matches
    the expected event type. It creates witness variables for all worlds that
    could satisfy the event formula (same participant, same event, equivalent
    prehistory via PreEq).

    Extracted as a separate function to make the encoding provably correct
    by avoiding beta-expansion of inline lambdas. -/
def encodeFormulaEvent (b : Bounds S) (w : WId b) (evt : Signature.EventType S)
    (st : EncState b) : FVar b × EncState b :=
  let witnessPairs := eventWitnessPairs b w evt
  let (witnessVars, st1) := witnessPairs.foldl (eventWitnessStep b) ([], st)
  mkBigOrIff b witnessVars st1

/-- Encode a formula at a specific world into CNF using Tseytin transformation.
    Returns the control variable and updated state with accumulated clauses.

    Uses stateful encoding pattern: (FVar b × EncState b)
    - Allocates fresh FVar for this subformula
    - Recursively encodes subformulas
    - Adds Tseytin clauses to state

    Fully computable - uses list-based iteration instead of Finset.toList. -/
def encodeFormula (b : Bounds S) (φ : Formula S) (w : WId b) (st : EncState b) :
    FVar b × EncState b :=
  match φ with
  | Formula.bot =>
      -- u ↔ ⊥, encoded as ¬u
      let (u, st1) := EncState.allocFresh b st
      let st2 := EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u)]
      (u, st2)

  | Formula.eq v1 v2 =>
      -- u ↔ (v1 = v2)
      let (u, st1) := EncState.allocFresh b st
      let st2 := if v1 == v2 then
        -- Values equal: assert u
        EncState.addClause b st1 [SAT.Lit.pos (FVar.toVar b u)]
      else
        -- Values different: assert ¬u
        EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u)]
      (u, st2)

  | Formula.predicate atom =>
      let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
      let idxs := predIxList b pred
      let literals := idxs.map (fun k => Var.Pred w.p w.ti k)
      let (u, st1) := mkBigOrIff b literals st
      if hEmpty : idxs = [] then
        (u, st1)
      else
        -- PreEq pairs from w.ti to all other times
        let st2 := addPreEqFrom b w.ti st1
        -- Add reflexivity units for all time indices
        let st3 := addPreEqReflAll b st2
        -- Bidirectional guards: transfer predicates between PreEq-equivalent times
        let st4 :=
          (Bounds.timesL b).foldl (fun stCur H' =>
            idxs.foldl (fun stAcc k =>
              let backward :=
                [ SAT.Lit.neg (Var.PreEq w.ti H')
                , SAT.Lit.neg (Var.Pred w.p H' k)
                , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
              let forward :=
                [ SAT.Lit.neg (Var.PreEq w.ti H')
                , SAT.Lit.neg (Var.Pred w.p w.ti k)
                , SAT.Lit.pos (Var.Pred w.p H' k) ]
              let stAcc := EncState.addClause b stAcc backward
              EncState.addClause b stAcc forward
            ) stCur
          ) st3
        (u, st4)

  | Formula.event atom =>
      -- Event atom: guard on w.ei, then witness-based OR
      -- Semantics: evt = b.decodeMaybeEvent w.ei ∧ (w.p, evt, H) ∈ history
      let evt : Signature.EventType S := ⟨atom.sym, atom.args⟩

      -- Hard guard: check id-level event at THIS world w
      -- If w.ei doesn't decode to evt, semantic side is false → encode ¬u
      match b.decodeMaybeEvent w.ei with
      | MaybeEvent.some e =>
          if hEq : e = evt then
            -- Use helper function for the successful case
            encodeFormulaEvent b w evt st
          else
            -- Guard fails: force u = false
            let (u, st1) := EncState.allocFresh b st
            let st2 := EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u)]
            (u, st2)
      | MaybeEvent.none =>
          -- Guard fails: force u = false
          let (u, st1) := EncState.allocFresh b st
          let st2 := EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u)]
        (u, st2)

  | Formula.imp φ1 φ2 =>
      -- u ↔ (¬u1 ∨ u2) where u1 = encode(φ1), u2 = encode(φ2)
      let (u1, st1) := encodeFormula b φ1 w st
      let (u2, st2) := encodeFormula b φ2 w st1
      let (u, st3) := EncState.allocFresh b st2
      -- Add SAT.iff_imp clauses: [u1, u], [¬u2, u], [¬u, ¬u1, u2]
      let st4 := EncState.addClause b st3 [SAT.Lit.pos (FVar.toVar b u1)
                                          , SAT.Lit.pos (FVar.toVar b u)]
      let st5 := EncState.addClause b st4 [SAT.Lit.neg (FVar.toVar b u2)
                                          , SAT.Lit.pos (FVar.toVar b u)]
      let st6 := EncState.addClause b st5 [SAT.Lit.neg (FVar.toVar b u)
                                          , SAT.Lit.neg (FVar.toVar b u1)
                                          , SAT.Lit.pos (FVar.toVar b u2)]
      (u, st6)

  | Formula.atEnd φ1 =>
      -- u ↔ u' where u' encodes φ1 at end world (w.p, †, root)
      let wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩  -- 0 = †
      let (u', st1) := encodeFormula b φ1 wEnd st
      let (u, st2) := EncState.allocFresh b st1
      -- Add bi-conditional clauses: [¬u, u'], [¬u', u]
      let st3 := EncState.addClause b st2 [SAT.Lit.neg (FVar.toVar b u)
                                          , SAT.Lit.pos (FVar.toVar b u')]
      let st4 := EncState.addClause b st3 [SAT.Lit.neg (FVar.toVar b u')
                                          , SAT.Lit.pos (FVar.toVar b u)]
      (u, st4)

  | Formula.past φ1 =>
      -- u ↔ (∃ w' ∈ w.ti. w'.p = w.p ∧ φ@w')
      -- Encoded as: u ↔ (⋁_{w'} (Mem(w.ti, w') ∧ Place(w', w.p) ∧ u'))
      -- We'll use CNF: u → (⋁ ...) and each conjunction → u
      let (u, st1) := EncState.allocFresh b st

      -- Collect all possible witness worlds and their encoded formulas
      let witnesses := (WId.allWorlds b).filterMap fun w' =>
        if w'.p = w.p then some w' else none

      -- Encode φ at each witness world
      let encodeWitnesses (ws : List (WId b)) (stAcc : EncState b) :
          List (FVar b) × EncState b :=
        ws.foldl (fun (uvars, stCur) w' =>
          let (u', stNext) := encodeFormula b φ1 w' stCur
          (uvars ++ [u'], stNext)
        ) ([], stAcc)

      let (witnessVars, st2) := encodeWitnesses witnesses st1

      -- Correct existential Tseytin encoding for: u ↔ ∃ w'. (Mem(w.ti, w') ∧ u')
      --
      -- We use auxiliary variables aux_i ↔ (Mem_i ∧ u'_i) for each witness:
      -- - Type 1: (Mem ∧ u') → u      [¬Mem, ¬u', u]
      -- - Aux forward: (Mem ∧ u') → aux  [¬Mem, ¬u', aux]
      -- - Aux backward 1: aux → Mem    [¬aux, Mem]
      -- - Aux backward 2: aux → u'     [¬aux, u']
      -- - Type 2: u → (aux₁ ∨ ... ∨ auxₙ)  [¬u, aux₁, ..., auxₙ]
      --
      -- This ensures: if u is true, some aux_i is true, meaning both Mem_i AND u'_i
      -- are true for that specific witness (not all witnesses).
      let (auxVars, st3) := witnessVars.zip witnesses |>.foldl (fun (auxAcc, stCur) (u', w') =>
        let memVar := Var.Mem w.ti w'
        -- Allocate auxiliary variable for (Mem ∧ u')
        let (aux, stCur) := EncState.allocFresh b stCur
        -- Type 1: (Mem ∧ u') → u
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
            SAT.Lit.pos (FVar.toVar b u)]
        -- Aux forward: (Mem ∧ u') → aux
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
            SAT.Lit.pos (FVar.toVar b aux)]
        -- Aux backward 1: aux → Mem
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
        -- Aux backward 2: aux → u'
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
        (auxAcc ++ [aux], stCur)
      ) ([], st2)

      -- Type 2: u → (aux₁ ∨ ... ∨ auxₙ)
      let auxLits := auxVars.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))
      let st4 :=
        EncState.addClause b st3 ([SAT.Lit.neg (FVar.toVar b u)] ++ auxLits)
      (u, st4)

  | Formula.forall body =>
      -- u ↔ (⋀_{v ∈ values} body(v))
      -- Encode as conjunction over all enumerated values in b.values
      let (u, st1) := EncState.allocFresh b st

      -- Helper: encode body(v) for each value index and accumulate clauses
      -- We use a simple fold since we need to handle termination carefully
      let encodeConj : List b.valIx → EncState b → List (FVar b) × EncState b :=
        fun valIndices stAcc =>
          valIndices.foldl (fun (vars, stCur) vIdx =>
            let v := b.values.get vIdx
            -- Termination: need to show depth (body v) < depth (.forall body)
            -- Use depth_uniform: depth (body v) = depth (body (choice h)) for any value
            -- Then depth (body v) < 1 + depth (body v) = depth (.forall body)
            have hNonempty : Nonempty S.Value := ⟨v⟩
            have hDepth : depth (body v) < depth (.forall body) := by
              open Classical in
              simp only [depth]
              simp only [hNonempty, ↓reduceDIte]
              rw [depth_uniform body v (choice hNonempty)]
              omega
            let (uBody, stNext) := encodeFormula b (body v) w stCur
            (vars ++ [uBody], stNext)
          ) ([], stAcc)

      let (bodyVars, st2) := encodeConj (List.finRange b.nVals) st1

      -- Add clauses: u → each body(v): [¬u, uᵢ] for each i
      let st3 := bodyVars.foldl (fun stCur uBody =>
        EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]
      ) st2

      -- Add reverse implication: (all body(v)) → u: [¬u₁, ..., ¬uₙ, u]
      let clause := bodyVars.map (fun uBody => SAT.Lit.neg (FVar.toVar b uBody))
        ++ [SAT.Lit.pos (FVar.toVar b u)]
      let st4 := EncState.addClause b st3 clause

      (u, st4)

  | Formula.seq =>
      -- u ↔ Seq(w.ti, w.p)
      -- Sequentiality predicate: all worlds with participant w.p in prehistory w.ti
      -- are totally ordered by happens-before
      let (u, st1) := EncState.allocFresh b st
      let seqVar := Var.Seq w.ti w.p
      -- Add bi-conditional clauses: u ↔ Seq(w.ti, w.p)
      let st2 := EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos seqVar]
      let st3 := EncState.addClause b st2 [SAT.Lit.neg seqVar, SAT.Lit.pos (FVar.toVar b u)]
      (u, st3)

  | Formula.diamond learners φ1 =>
      -- Encode diamond with a control per quorum tuple, then conjoin them
      let getMinQs (ℓ : S.Value) : List (Finset b.participants) :=
        let vIdx := b.findValueIndex ℓ
        let allVars := Var.allMinQ b vIdx
        allVars.filterMap fun v =>
          match v with
          | Var.MinQ _ Q => some Q
          | _ => none

      let quorumSets : List (List (Finset b.participants)) :=
        learners.map getMinQs
      let tuples := cartesianProduct quorumSets

      let step :
          (List (FVar b) × EncState b) → List (Finset b.participants) →
          List (FVar b) × EncState b :=
        fun (accVars, stCur) tuple =>
          let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
          let witnessFold :=
            (Bounds.partsL b).foldl
              (fun (acc : List (FVar b × b.participants) × EncState b) p =>
                if hp : p ∈ intersection then
                  let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                  let (uWit, stNew) := encodeFormula b φ1 wEnd acc.2
                  (acc.1 ++ [(uWit, p)], stNew)
                else
                  acc)
              ([], stCur)
          let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
          let (uTuple, stFinal) := encodeTupleControl b learners tuple witnessVars witnessFold.2
          (accVars ++ [uTuple], stFinal)

      let (tupleVars, stTuples) := tuples.foldl step ([], st)

      -- Conjoin all tuple control variables into the returned control variable
      let (u, stFinal) :=
        match tupleVars with
        | [] =>
            let (u', st') := EncState.allocFresh b stTuples
            let st'' := EncState.addClause b st' [SAT.Lit.pos (FVar.toVar b u')]
            (u', st'')
        | u0 :: us =>
            let res := us.foldl (fun (acc : FVar b × EncState b) u' =>
              let (uAcc, stAcc) := acc
              mkAndIff b uAcc u' stAcc) (u0, stTuples)
            (res.1, res.2)

      (u, stFinal)
termination_by depth φ

/-- When the event guard fails (decoded event mismatches), the encoder allocates a
fresh variable and immediately forces it to `false` with a unit clause. -/
@[simp] lemma encodeFormula_event_guardMismatch
    (b : Bounds S) (atom : Logic.EventAtom S)
    (w : WId b) (st : EncState b)
    (e : Signature.EventType S)
    (hGuard : b.decodeMaybeEvent w.ei = MaybeEvent.some e)
    (hNe : e ≠ ⟨atom.sym, atom.args⟩) :
    encodeFormula b (.event atom) w st =
      (let (u, st1) := EncState.allocFresh b st
        let st2 := EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u)]
        (u, st2)) := by
  classical
  simp [encodeFormula, hGuard, dif_neg hNe]

/-- Helper used by `encodeFormula_clauses_subset` for the `forall` constructor. -/

lemma encodeFormula_clauses_subset_forall (b : Bounds S)
    (body : Signature.Value S → Formula S) (w : WId b) (st : EncState b)
    (ih : ∀ v (w' : WId b) (st' : EncState b),
      st'.clauses ⊆ (encodeFormula b (body v) w' st').2.clauses) :
    st.clauses ⊆ (encodeFormula b (.forall body) w st).2.clauses := by
  classical
  cases hAlloc : EncState.allocFresh b st with
  | mk u st₁ =>
      let encodeConj :
          List b.valIx → EncState b → List (FVar b) × EncState b :=
        fun valIndices stAcc =>
          valIndices.foldl
            (fun (vars, stCur) vIdx =>
              let v := b.values.get vIdx
              let res := encodeFormula b (body v) w stCur
              (vars ++ [res.1], res.2)) ([], stAcc)
      cases hEnc : encodeConj (List.finRange b.nVals) st₁ with
      | mk bodyVars st₂ =>
          let st₃ :=
            bodyVars.foldl (fun stCur uBody =>
              EncState.addClause b stCur
                [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]) st₂
          let clauseAll :=
            bodyVars.map (fun uBody => SAT.Lit.neg (FVar.toVar b uBody)) ++
              [SAT.Lit.pos (FVar.toVar b u)]
          let st₄ := EncState.addClause b st₃ clauseAll
          intro clause hClause
          have hAllocSub :
              st.clauses ⊆ st₁.clauses := by
            have eq : st₁ = (EncState.allocFresh b st).2 := by
              cases hAlloc
              rfl
            intro clause' h'
            rw [eq, EncState.allocFresh_clauses_eq]
            exact h'
          have hStep :
              ∀ (acc : List (FVar b) × EncState b) vIdx,
                acc.2.clauses ⊆
                  (let v := b.values.get vIdx
                   let res := encodeFormula b (body v) w acc.2
                   res.2).clauses := by
            intro acc vIdx
            have hSubset := ih (b.values.get vIdx) w acc.2
            exact hSubset
          have hEncodeSub :
              st₁.clauses ⊆ st₂.clauses := by
            simpa [encodeConj, hEnc] using
              (foldl_subset_snd
                (f := fun (acc : List (FVar b) × EncState b) vIdx =>
                  let v := b.values.get vIdx
                  let res := encodeFormula b (body v) w acc.2
                  (acc.1 ++ [res.1], res.2))
                (hStep := hStep)
                (xs := List.finRange b.nVals)
                (init := ([], st₁)))
          have hForwardSub :
              st₂.clauses ⊆ st₃.clauses := by
            simpa [st₃] using
              (foldl_subset_state
                (f := fun stCur uBody =>
                  EncState.addClause b stCur
                    [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
                (hStep := by
                  intro stCur uBody
                  exact EncState.addClause_subset_clauses (b := b) stCur
                    [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
                (xs := bodyVars)
                (init := st₂))
          have hBackwardSub :
              st₃.clauses ⊆ st₄.clauses :=
            EncState.addClause_subset_clauses (b := b) st₃ clauseAll
          have hChain :=
            List.Subset.trans hAllocSub
              (List.Subset.trans hEncodeSub
                (List.Subset.trans hForwardSub hBackwardSub))
          have hIn : clause ∈ st₄.clauses := hChain hClause
          simp only [encodeFormula, hAlloc, encodeConj, hEnc]
          exact hIn

lemma encodeFormula_clauses_subset_past (b : Bounds S)
    (φ : Formula S) (w : WId b) (st : EncState b)
    (ih : ∀ (w' : WId b) (st' : EncState b),
      st'.clauses ⊆ (encodeFormula b φ w' st').2.clauses) :
    st.clauses ⊆ (encodeFormula b (.past φ) w st).2.clauses := by
  classical
  cases hAlloc : EncState.allocFresh b st with
  | mk u st₁ =>
      let witnesses :=
        (WId.allWorlds b).filterMap fun w' =>
          if w'.p = w.p then some w' else none
      let encodeWitnesses (ws : List (WId b)) (stAcc : EncState b) :
          List (FVar b) × EncState b :=
        ws.foldl (fun (uvars, stCur) w' =>
          let res := encodeFormula b φ w' stCur
          (uvars ++ [res.1], res.2)) ([], stAcc)
      -- Match the encoding structure: st → st1 → st2 → st3 → st4
      cases hEnc : encodeWitnesses witnesses st₁ with
      | mk witnessVars st₂ =>
          -- Aux-variable fold over witnesses.zip witnessVars
          let auxStep :=
            fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
              let (u', w') := pair
              let memVar := Var.Mem w.ti w'
              let (aux, stCur) := EncState.allocFresh b acc.2
              let stCur := EncState.addClause b stCur
                [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                  SAT.Lit.pos (FVar.toVar b u)]
              let stCur := EncState.addClause b stCur
                [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                  SAT.Lit.pos (FVar.toVar b aux)]
              let stCur := EncState.addClause b stCur
                [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
              let stCur := EncState.addClause b stCur
                [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
              (acc.1 ++ [aux], stCur)
          cases hAux : (witnessVars.zip witnesses).foldl auxStep ([], st₂) with
          | mk auxVars st₃ =>
              let auxLits := auxVars.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))
              let st₄ := EncState.addClause b st₃ ([SAT.Lit.neg (FVar.toVar b u)] ++ auxLits)
              intro clause hClause
              -- Step 1: st.clauses ⊆ st₁.clauses via allocFresh
              have hAllocSub : st.clauses ⊆ st₁.clauses := by
                have eq : st₁ = (EncState.allocFresh b st).2 := by cases hAlloc; rfl
                intro c hc
                rw [eq, EncState.allocFresh_clauses_eq]
                exact hc
              -- Step 2: st₁.clauses ⊆ st₂.clauses via encodeWitnesses fold
              have hWitnessStep :
                  ∀ (acc : List (FVar b) × EncState b) w',
                    acc.2.clauses ⊆
                      (let res := encodeFormula b φ w' acc.2
                       (acc.1 ++ [res.1], res.2)).2.clauses := by
                intro acc w'
                exact ih w' acc.2
              have hEncodeSub : st₁.clauses ⊆ st₂.clauses := by
                simpa [encodeWitnesses, hEnc] using
                  (foldl_subset_snd
                    (f := fun (acc : List (FVar b) × EncState b) w' =>
                      let res := encodeFormula b φ w' acc.2
                      (acc.1 ++ [res.1], res.2))
                    (hStep := hWitnessStep)
                    (xs := witnesses)
                    (init := ([], st₁)))
              -- Step 3: st₂.clauses ⊆ st₃.clauses via aux fold
              have hAuxStep :
                  ∀ (acc : List (FVar b) × EncState b) pair,
                    acc.2.clauses ⊆ (auxStep acc pair).2.clauses := by
                intro acc ⟨u', w'⟩
                simp only [auxStep]
                let memVar := Var.Mem w.ti w'
                cases hAF : EncState.allocFresh b acc.2 with
                | mk aux stCur =>
                    have hAFS : acc.2.clauses ⊆ stCur.clauses := by
                      have eq : stCur = (EncState.allocFresh b acc.2).2 := by
                        cases hAF; rfl
                      intro c hc
                      rw [eq, EncState.allocFresh_clauses_eq]
                      exact hc
                    -- Chain through 4 addClause calls
                    let c1 := [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                                SAT.Lit.pos (FVar.toVar b u)]
                    let stCur1 := EncState.addClause b stCur c1
                    let c2 := [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                                SAT.Lit.pos (FVar.toVar b aux)]
                    let stCur2 := EncState.addClause b stCur1 c2
                    let c3 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
                    let stCur3 := EncState.addClause b stCur2 c3
                    let c4 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
                    have h1 : stCur.clauses ⊆ stCur1.clauses :=
                      EncState.addClause_subset_clauses (b := b) stCur c1
                    have h2 : stCur1.clauses ⊆ stCur2.clauses :=
                      EncState.addClause_subset_clauses (b := b) stCur1 c2
                    have h3 : stCur2.clauses ⊆ stCur3.clauses :=
                      EncState.addClause_subset_clauses (b := b) stCur2 c3
                    have h4 : stCur3.clauses ⊆ (EncState.addClause b stCur3 c4).clauses :=
                      EncState.addClause_subset_clauses (b := b) stCur3 c4
                    calc acc.2.clauses
                        ⊆ stCur.clauses := hAFS
                      _ ⊆ stCur1.clauses := h1
                      _ ⊆ stCur2.clauses := h2
                      _ ⊆ stCur3.clauses := h3
                      _ ⊆ (EncState.addClause b stCur3 c4).clauses := h4
              have hAuxSub : st₂.clauses ⊆ st₃.clauses := by
                simpa [hAux] using
                  (foldl_subset_snd
                    (f := auxStep)
                    (hStep := hAuxStep)
                    (xs := witnessVars.zip witnesses)
                    (init := ([], st₂)))
              -- Step 4: st₃.clauses ⊆ st₄.clauses via addClause
              have hFinalSub : st₃.clauses ⊆ st₄.clauses :=
                EncState.addClause_subset_clauses (b := b) st₃
                  ([SAT.Lit.neg (FVar.toVar b u)] ++ auxLits)
              -- Chain all subsets
              have hChain := List.Subset.trans hAllocSub
                (List.Subset.trans hEncodeSub
                  (List.Subset.trans hAuxSub hFinalSub))
              have hIn : clause ∈ st₄.clauses := hChain hClause
              -- The goal is clause ∈ (encodeFormula b (.past φ) w st).2.clauses
              -- Unfold encodeFormula for past
              simp only [encodeFormula, hAlloc]
              simp only [encodeWitnesses] at hEnc
              -- We need to show the encoding output matches st₄
              -- Key: prove that auxStep is definitionally equal to the encoding's fold step
              -- The encoding's step is: fun (auxAcc, stCur) (u', w') => ...
              -- which matches auxStep after eta-expansion
              have hAuxStepEq :
                  (fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
                    let (u', w') := pair
                    let memVar := Var.Mem w.ti w'
                    let (aux, stCur) := EncState.allocFresh b acc.2
                    let stCur := EncState.addClause b stCur
                      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                        SAT.Lit.pos (FVar.toVar b u)]
                    let stCur := EncState.addClause b stCur
                      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                        SAT.Lit.pos (FVar.toVar b aux)]
                    let stCur := EncState.addClause b stCur
                      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
                    let stCur := EncState.addClause b stCur
                      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
                    (acc.1 ++ [aux], stCur)) = auxStep := by rfl
              -- Rewrite using hEnc to replace first fold result
              have hEq1 : (witnesses.foldl
                (fun x w' => (x.1 ++ [(encodeFormula b φ w' x.2).1], (encodeFormula b φ w' x.2).2))
                ([], st₁)) = (witnessVars, st₂) := hEnc
              rw [hEq1]
              -- Rewrite the goal's fold to use auxStep
              rw [hAuxStepEq]
              -- Now can use hAux
              rw [hAux]
              exact hIn

/-- Helper used by `encodeFormula_clauses_subset` for the `diamond` constructor. -/

lemma encodeFormula_clauses_subset_diamond (b : Bounds S)
    (learners : List S.Value) (φ : Formula S) (w : WId b) (st : EncState b)
    (ih : ∀ (w' : WId b) (st' : EncState b),
      st'.clauses ⊆ (encodeFormula b φ w' st').2.clauses) :
    st.clauses ⊆ (encodeFormula b (.diamond learners φ) w st).2.clauses := by
  classical
  simp only [encodeFormula]
  -- Define step exactly as in encodeFormula
  let getMinQs (ℓ : S.Value) : List (Finset b.participants) :=
    let vIdx := b.findValueIndex ℓ
    let allVars := Var.allMinQ b vIdx
    allVars.filterMap fun v =>
      match v with
      | Var.MinQ _ Q => some Q
      | _ => none
  let quorumSets : List (List (Finset b.participants)) :=
    learners.map getMinQs
  let tuples := cartesianProduct quorumSets
  let step :
      (List (FVar b) × EncState b) → List (Finset b.participants) →
      List (FVar b) × EncState b :=
    fun (accVars, stCur) tuple =>
      let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
      let witnessFold :=
        (Bounds.partsL b).foldl
          (fun (acc : List (FVar b × b.participants) × EncState b) p =>
            if hp : p ∈ intersection then
              let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
              let (uWit, stNew) := encodeFormula b φ wEnd acc.2
              (acc.1 ++ [(uWit, p)], stNew)
            else
              acc)
          ([], stCur)
      let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
      let (uTuple, stFinal) := encodeTupleControl b learners tuple witnessVars witnessFold.2
      (accVars ++ [uTuple], stFinal)
  -- Case on the fold result to get proper equalities
  cases hFoldRes : tuples.foldl step ([], st) with
  | mk tupleVars stTuples =>
      -- Prove st.clauses ⊆ stTuples.clauses
      have hStepSubset :
          ∀ (acc : List (FVar b) × EncState b) tuple,
            acc.2.clauses ⊆ (step acc tuple).2.clauses := by
        intro acc tuple
        dsimp [step]
        let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
        -- Witness fold preserves clauses
        have hWitnessFold :
            acc.2.clauses ⊆
              ((Bounds.partsL b).foldl
                (fun (acc' : List (FVar b × b.participants) × EncState b) p =>
                  if hp : p ∈ intersection then
                    let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                    let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
                    (acc'.1 ++ [(uWit, p)], stNew)
                  else
                    acc')
                ([], acc.2)).2.clauses :=
          foldl_subset_snd
            (f := fun (acc' : List (FVar b × b.participants) × EncState b) p =>
              if hp : p ∈ intersection then
                let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
                (acc'.1 ++ [(uWit, p)], stNew)
              else
                acc')
            (hStep := by
              intro acc' p
              by_cases hp : p ∈ intersection
              · simp only [hp, ↓reduceDIte]
                exact ih ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc'.2
              · simp only [hp, ↓reduceDIte]
                exact List.Subset.refl _)
            (xs := Bounds.partsL b)
            (init := ([], acc.2))
        -- encodeTupleControl preserves clauses
        set witnessFold := (Bounds.partsL b).foldl
          (fun (acc' : List (FVar b × b.participants) × EncState b) p =>
            if hp : p ∈ intersection then
              let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
              let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
              (acc'.1 ++ [(uWit, p)], stNew)
            else
              acc')
          ([], acc.2)
        have hTupleControl :
            witnessFold.2.clauses ⊆
              (encodeTupleControl b learners tuple
                (witnessFold.1.map (fun u => FVar.toVar b u.1)) witnessFold.2).2.clauses :=
          encodeTupleControl_clauses_subset b learners tuple
            (witnessFold.1.map (fun u => FVar.toVar b u.1)) witnessFold.2
        exact List.Subset.trans hWitnessFold hTupleControl
      have hTuplesSubset :
          st.clauses ⊆ stTuples.clauses := by
        have h := foldl_subset_snd (f := step) (hStep := hStepSubset)
          (xs := tuples) (init := ([], st))
        simp only at h
        have heq : stTuples = (tuples.foldl step ([], st)).2 := by simp [hFoldRes]
        rw [heq]
        exact h
      -- Final step: handle the conjunction of tuple control variables
      match hMatch : tupleVars with
      | [] =>
          -- Empty case: allocate fresh and add positive clause
          cases hAlloc : EncState.allocFresh b stTuples with
          | mk u' st' =>
              have hAllocSub : stTuples.clauses ⊆ st'.clauses := by
                intro c hc
                have heq : st' = (EncState.allocFresh b stTuples).2 := by simp [hAlloc]
                rw [heq, EncState.allocFresh_clauses_eq]
                exact hc
              have hAddSub :=
                EncState.addClause_subset_clauses b st' [SAT.Lit.pos (FVar.toVar b u')]
              intro clause hClause
              exact hAddSub (hAllocSub (hTuplesSubset hClause))
      | u0 :: us =>
          -- Non-empty case: fold with mkAndIff
          have hAndFold :
              stTuples.clauses ⊆
                (us.foldl (fun (acc : FVar b × EncState b) u' =>
                  let (uAcc, stAcc) := acc
                  mkAndIff b uAcc u' stAcc) (u0, stTuples)).2.clauses := by
            refine foldl_subset_snd
              (f := fun (acc : FVar b × EncState b) u' =>
                let (uAcc, stAcc) := acc
                mkAndIff b uAcc u' stAcc)
              (hStep := by
                intro acc u'
                exact mkAndIff_clauses_subset b acc.1 u' acc.2)
              (xs := us)
              (init := (u0, stTuples))
          intro clause hClause
          exact hAndFold (hTuplesSubset hClause)

/-- Encoding a formula never removes clauses that were already present in the state. -/

lemma encodeFormula_clauses_subset (b : Bounds S) :
    ∀ (φ : Formula S) (w : WId b) (st : EncState b),
      st.clauses ⊆ (encodeFormula b φ w st).2.clauses := by
  classical
  intro φ
  induction φ with
  | bot =>
      intro w st clause hClause
      cases hAlloc : EncState.allocFresh b st with
      | mk u st₁ =>
          have hAllocSub : st.clauses ⊆ st₁.clauses := by
            have eq : st₁ = (EncState.allocFresh b st).2 := by
              cases hAlloc
              rfl
            intro clause' h'
            rw [eq, EncState.allocFresh_clauses_eq]
            exact h'
          have hAdd :=
            EncState.addClause_subset_clauses (b := b) st₁
              [SAT.Lit.neg (FVar.toVar b u)]
          have hChain := List.Subset.trans hAllocSub hAdd
          have hIn := hChain hClause
          simp only [encodeFormula]
          rw [hAlloc]
          simp only
          exact hIn
  | imp φ₁ φ₂ ih₁ ih₂ =>
      intro w st clause hClause
      set resLeft := encodeFormula b φ₁ w st with hLeft
      rcases resLeft with ⟨uLeft, st₁⟩
      set resRight := encodeFormula b φ₂ w st₁ with hRight
      rcases resRight with ⟨uRight, st₂⟩
      set alloc := EncState.allocFresh b st₂ with hAlloc
      rcases alloc with ⟨u, st₃⟩
      let st₄ :=
        EncState.addClause b st₃
          [SAT.Lit.pos (FVar.toVar b uLeft), SAT.Lit.pos (FVar.toVar b u)]
      let st₅ :=
        EncState.addClause b st₄
          [SAT.Lit.neg (FVar.toVar b uRight), SAT.Lit.pos (FVar.toVar b u)]
      let st₆ :=
        EncState.addClause b st₅
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b uLeft),
            SAT.Lit.pos (FVar.toVar b uRight)]
      have h₁ : st.clauses ⊆ st₁.clauses := by
        have : st₁ = (encodeFormula b φ₁ w st).2 := by
          rw [← hLeft]
        rw [this]
        exact ih₁ w st
      have h₂ : st₁.clauses ⊆ st₂.clauses := by
        have : st₂ = (encodeFormula b φ₂ w st₁).2 := by
          rw [← hRight]
        rw [this]
        exact ih₂ w st₁
      have h₃ : st₂.clauses ⊆ st₃.clauses := by
        have eq : st₃ = (EncState.allocFresh b st₂).2 := by
          rw [← hAlloc]
        intro clause' h'
        rw [eq, EncState.allocFresh_clauses_eq]
        exact h'
      have h₄ :=
        EncState.addClause_subset_clauses (b := b) st₃
          [SAT.Lit.pos (FVar.toVar b uLeft), SAT.Lit.pos (FVar.toVar b u)]
      have h₅ :=
        EncState.addClause_subset_clauses (b := b) st₄
          [SAT.Lit.neg (FVar.toVar b uRight), SAT.Lit.pos (FVar.toVar b u)]
      have h₆ :=
        EncState.addClause_subset_clauses (b := b) st₅
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b uLeft),
            SAT.Lit.pos (FVar.toVar b uRight)]
      have hChain :=
        List.Subset.trans h₁
          (List.Subset.trans h₂
            (List.Subset.trans h₃
              (List.Subset.trans h₄
                (List.Subset.trans h₅ h₆))))
      have hIn : clause ∈ st₆.clauses := hChain hClause
      simp only [encodeFormula]
      rw [← hLeft, ← hRight, ← hAlloc]
      simp
      exact hIn
  | eq v₁ v₂ =>
      intro w st clause hClause
      cases hAlloc : EncState.allocFresh b st with
      | mk u st₁ =>
          have hAllocSub : st.clauses ⊆ st₁.clauses := by
            have eq : st₁ = (EncState.allocFresh b st).2 := by
              cases hAlloc
              rfl
            intro clause' h'
            rw [eq, EncState.allocFresh_clauses_eq]
            exact h'
          by_cases hEq : v₁ == v₂
          · have hAdd :=
              EncState.addClause_subset_clauses (b := b) st₁
                [SAT.Lit.pos (FVar.toVar b u)]
            have hIn :
                clause ∈
                  (EncState.addClause b st₁ [SAT.Lit.pos (FVar.toVar b u)]).clauses :=
              hAdd (hAllocSub hClause)
            simp only [encodeFormula]
            rw [hAlloc]
            simp only [hEq, ↓reduceIte]
            exact hIn
          · have hAdd :=
              EncState.addClause_subset_clauses (b := b) st₁
                [SAT.Lit.neg (FVar.toVar b u)]
            have hIn :
                clause ∈
                  (EncState.addClause b st₁ [SAT.Lit.neg (FVar.toVar b u)]).clauses :=
              hAdd (hAllocSub hClause)
            simp only [encodeFormula]
            rw [hAlloc]
            simp only [hEq]
            exact hIn
  | «forall» body ih =>
      intro w st
      exact encodeFormula_clauses_subset_forall b body w st
          (fun v w' st' => ih v w' st')
  | predicate atom =>
      intro w st clause hClause
      classical
      let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
      let idxs := predIxList b pred
      let literals := idxs.map (fun k => Var.Pred w.p w.ti k)
      cases hMk : mkBigOrIff b literals st with
      | mk u st₁ =>
          have hBig : st.clauses ⊆ st₁.clauses := by
            simpa [literals, hMk] using
              mkBigOrIff_clauses_subset (b := b) (vs := literals) (st := st)
          by_cases hEmpty : idxs = []
          · have hIn : clause ∈ st₁.clauses := hBig hClause
            have heq :
                (encodeFormula b (.predicate atom) w st).2 = st₁ := by
              have hLitEmpty : literals = [] := by simp [literals, hEmpty]
              unfold encodeFormula
              have hPredEq : pred = ⟨atom.sym, atom.args⟩ := rfl
              simp only []
              have hIdxEq : predIxList b ⟨atom.sym, atom.args⟩ = idxs := rfl
              simp only [hIdxEq]
              have : idxs = [] := hEmpty
              simp only [this, List.map_nil]
              have : mkBigOrIff b [] st = (u, st₁) := by rw [← hLitEmpty]; exact hMk
              simp only [this, dite_true]
            simpa [heq] using hIn
          · let st₂ := addPreEqFrom b w.ti st₁
            have hFrom :
                st₁.clauses ⊆ st₂.clauses :=
              addPreEqFrom_clauses_subset (b := b) (H0 := w.ti) (st := st₁)
            let st₃ := addPreEqReflAll b st₂
            have hRefl :
                st₂.clauses ⊆ st₃.clauses :=
              addPreEqReflAll_clauses_subset (b := b) (st := st₂)
            -- Bidirectional guards: transfer predicates between PreEq-equivalent times
            let stepTimes :
                EncState b → b.times → EncState b :=
              fun stCur H' =>
                idxs.foldl (fun stAcc k =>
                  let backward :=
                    [ SAT.Lit.neg (Var.PreEq w.ti H')
                    , SAT.Lit.neg (Var.Pred w.p H' k)
                    , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
                  let forward :=
                    [ SAT.Lit.neg (Var.PreEq w.ti H')
                    , SAT.Lit.neg (Var.Pred w.p w.ti k)
                    , SAT.Lit.pos (Var.Pred w.p H' k) ]
                  let stAcc := EncState.addClause b stAcc backward
                  EncState.addClause b stAcc forward) stCur
            have hIdx :
                ∀ stCur H', stCur.clauses ⊆ (stepTimes stCur H').clauses := by
              intro stCur H'
              refine foldl_subset_state
                (b := b)
                (f := fun stAcc k =>
                  let backward :=
                    [ SAT.Lit.neg (Var.PreEq w.ti H')
                    , SAT.Lit.neg (Var.Pred w.p H' k)
                    , SAT.Lit.pos (Var.Pred w.p w.ti k) ]
                  let forward :=
                    [ SAT.Lit.neg (Var.PreEq w.ti H')
                    , SAT.Lit.neg (Var.Pred w.p w.ti k)
                    , SAT.Lit.pos (Var.Pred w.p H' k) ]
                  let stAcc :=
                    EncState.addClause b stAcc backward
                  EncState.addClause b stAcc forward)
                (hStep := by
                  intro stAcc k
                  dsimp
                  have hBack :
                      stAcc.clauses ⊆
                        (EncState.addClause b stAcc
                          [ SAT.Lit.neg (Var.PreEq w.ti H')
                          , SAT.Lit.neg (Var.Pred w.p H' k)
                          , SAT.Lit.pos (Var.Pred w.p w.ti k) ]).clauses :=
                    EncState.addClause_subset_clauses
                      (b := b)
                      (st := stAcc)
                      (clause :=
                        [ SAT.Lit.neg (Var.PreEq w.ti H')
                        , SAT.Lit.neg (Var.Pred w.p H' k)
                        , SAT.Lit.pos (Var.Pred w.p w.ti k) ])
                  have hForward :
                      (EncState.addClause b stAcc
                        [ SAT.Lit.neg (Var.PreEq w.ti H')
                        , SAT.Lit.neg (Var.Pred w.p H' k)
                        , SAT.Lit.pos (Var.Pred w.p w.ti k) ]).clauses ⊆
                        (EncState.addClause b
                          (EncState.addClause b stAcc
                            [ SAT.Lit.neg (Var.PreEq w.ti H')
                            , SAT.Lit.neg (Var.Pred w.p H' k)
                            , SAT.Lit.pos (Var.Pred w.p w.ti k) ])
                          [ SAT.Lit.neg (Var.PreEq w.ti H')
                          , SAT.Lit.neg (Var.Pred w.p w.ti k)
                          , SAT.Lit.pos (Var.Pred w.p H' k) ]).clauses :=
                    EncState.addClause_subset_clauses
                      (b := b)
                      (st := EncState.addClause b stAcc
                        [ SAT.Lit.neg (Var.PreEq w.ti H')
                        , SAT.Lit.neg (Var.Pred w.p H' k)
                        , SAT.Lit.pos (Var.Pred w.p w.ti k) ])
                      (clause :=
                        [ SAT.Lit.neg (Var.PreEq w.ti H')
                        , SAT.Lit.neg (Var.Pred w.p w.ti k)
                        , SAT.Lit.pos (Var.Pred w.p H' k) ])
                  exact List.Subset.trans hBack hForward)
                (xs := idxs)
                (init := stCur)
            have hTimes :
                st₃.clauses ⊆
                  ((Bounds.timesL b).foldl stepTimes st₃).clauses := by
              simpa [stepTimes] using
                (foldl_subset_state
                  (b := b)
                  (f := stepTimes)
                  (hStep := hIdx)
                  (xs := Bounds.timesL b)
                  (init := st₃))
            have hChain :=
              List.Subset.trans hBig
                (List.Subset.trans hFrom
                  (List.Subset.trans hRefl hTimes))
            have hIn :
                clause ∈
                  ((Bounds.timesL b).foldl stepTimes st₃).clauses :=
              hChain hClause
            have heq :
                (encodeFormula b (.predicate atom) w st).2 =
                  (Bounds.timesL b).foldl stepTimes st₃ := by
              unfold encodeFormula
              simp only [pred, idxs, literals, hMk, hEmpty
                        , dite_false, st₂, st₃, stepTimes]
            simpa [heq] using hIn
  | event atom =>
      intro w st clause hClause
      let evt : Signature.EventType S := ⟨atom.sym, atom.args⟩
      cases hDecode : b.decodeMaybeEvent w.ei with
      | some e =>
          by_cases hEq : e = evt
          · classical
            -- Reconstruct the auxiliary data used in the encoding.
            let witnessPairs := eventWitnessPairs b w evt
            let step := eventWitnessStep b
            have hStep :
                ∀ acc pair, acc.2.clauses ⊆ (step acc pair).2.clauses := by
              intro acc pair
              rcases acc with ⟨vars, stAcc⟩
              rcases pair with ⟨preEq, mem⟩
              dsimp [step, eventWitnessStep]
              cases hAllocStep : EncState.allocFresh b stAcc with
              | mk z stAcc' =>
                  have hAllocSub : stAcc.clauses ⊆ stAcc'.clauses := by
                    intro clause' h'
                    have eq : stAcc' = (EncState.allocFresh b stAcc).2 := by
                      simp [hAllocStep]
                    rw [eq, EncState.allocFresh_clauses_eq]
                    exact h'
                  have hAdd₁ :
                      stAcc'.clauses ⊆
                        (EncState.addClause b stAcc'
                          [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos preEq]).clauses :=
                    EncState.addClause_subset_clauses
                      (b := b)
                      (st := stAcc')
                      (clause :=
                        [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos preEq])
                  have hAdd₂ :
                      (EncState.addClause b stAcc'
                        [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos preEq]).clauses ⊆
                        (EncState.addClause b
                          (EncState.addClause b stAcc'
                            [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos preEq])
                          [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos mem]).clauses :=
                    EncState.addClause_subset_clauses
                      (b := b)
                      (st :=
                        EncState.addClause b stAcc'
                          [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos preEq])
                      (clause :=
                        [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos mem])
                  have hAdd₃ :
                      (EncState.addClause b
                        (EncState.addClause b stAcc'
                          [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos preEq])
                        [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos mem]).clauses ⊆
                        (EncState.addClause b
                          (EncState.addClause b
                            (EncState.addClause b stAcc'
                              [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos preEq])
                            [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos mem])
                          [ SAT.Lit.neg preEq
                          , SAT.Lit.neg mem
                          , SAT.Lit.pos (FVar.toVar b z) ]).clauses :=
                    EncState.addClause_subset_clauses
                      (b := b)
                      (st :=
                        EncState.addClause b
                          (EncState.addClause b stAcc'
                            [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos preEq])
                          [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos mem])
                      (clause :=
                        [ SAT.Lit.neg preEq
                        , SAT.Lit.neg mem
                        , SAT.Lit.pos (FVar.toVar b z) ])
                  exact List.Subset.trans hAllocSub
                    (List.Subset.trans hAdd₁
                      (List.Subset.trans hAdd₂ hAdd₃))
            cases hFoldRes : witnessPairs.foldl step ([], st) with
            | mk witnessVars st₁ =>
                cases hMk : mkBigOrIff b witnessVars st₁ with
                | mk u st₂ =>
                    have hWitness : st.clauses ⊆ st₁.clauses := by
                      have hSubset :=
                        foldl_subset_snd
                          (b := b)
                          (f := step)
                          (hStep := hStep)
                          (xs := witnessPairs)
                          (init := ([], st))
                      simpa [step, hFoldRes] using hSubset
                    have hBigOr : st₁.clauses ⊆ st₂.clauses := by
                      have hSubset :=
                        mkBigOrIff_clauses_subset
                          (b := b)
                          (vs := witnessVars)
                          (st := st₁)
                      simpa [hMk] using hSubset
                    have hChain :=
                      List.Subset.trans hWitness hBigOr
                    have hIn : clause ∈ st₂.clauses := hChain hClause
                    have heq :
                        (encodeFormula b (.event atom) w st).2 = st₂ := by
                      unfold encodeFormula encodeFormulaEvent
                      simp only [evt, hDecode, hEq, dite_true]
                      rw [hFoldRes, hMk]
                    simpa [heq] using hIn
          · cases hAlloc : EncState.allocFresh b st with
            | mk u st₁ =>
                have hAllocSub : st.clauses ⊆ st₁.clauses := by
                  have eq : st₁ = (EncState.allocFresh b st).2 := by
                    cases hAlloc
                    rfl
                  intro clause' h'
                  rw [eq, EncState.allocFresh_clauses_eq]
                  exact h'
                have hAdd :=
                  EncState.addClause_subset_clauses (b := b) st₁
                    [SAT.Lit.neg (FVar.toVar b u)]
                have hIn :
                    clause ∈
                      (EncState.addClause b st₁ [SAT.Lit.neg (FVar.toVar b u)]).clauses :=
                  hAdd (hAllocSub hClause)
                have heq :
                    (encodeFormula b (.event atom) w st).2 =
                      (EncState.addClause b st₁
                        [SAT.Lit.neg (FVar.toVar b u)]) := by
                  simp [evt, hDecode, hEq, hAlloc]
                simpa [heq] using hIn
      | none =>
          cases hAlloc : EncState.allocFresh b st with
          | mk u st₁ =>
              have hAllocSub : st.clauses ⊆ st₁.clauses := by
                have eq : st₁ = (EncState.allocFresh b st).2 := by
                  cases hAlloc
                  rfl
                intro clause' h'
                rw [eq, EncState.allocFresh_clauses_eq]
                exact h'
              have hAdd :=
                EncState.addClause_subset_clauses (b := b) st₁
                  [SAT.Lit.neg (FVar.toVar b u)]
              have hIn :
                  clause ∈
                    (EncState.addClause b st₁ [SAT.Lit.neg (FVar.toVar b u)]).clauses :=
                hAdd (hAllocSub hClause)
              have heq :
                  (encodeFormula b (.event atom) w st).2 =
                    (EncState.addClause b st₁
                      [SAT.Lit.neg (FVar.toVar b u)]) := by
                simp [encodeFormula, hDecode, hAlloc]
              simpa [heq] using hIn
  | past φ ih =>
      intro w st
      exact encodeFormula_clauses_subset_past b φ w st
          (fun w' st' => ih w' st')
  | atEnd φ ih =>
      intro w st clause hClause
      let wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
      set res := encodeFormula b φ wEnd st with hRes
      rcases res with ⟨u', st₁⟩
      set alloc := EncState.allocFresh b st₁ with hAlloc
      rcases alloc with ⟨u, st₂⟩
      let st₃ :=
        EncState.addClause b st₂
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b u')]
      let st₄ :=
        EncState.addClause b st₃
          [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b u)]
      have h₁ : st.clauses ⊆ st₁.clauses := by
        have : st₁ = (encodeFormula b φ wEnd st).2 := by
          rw [← hRes]
        rw [this]
        exact ih wEnd st
      have h₂ : st₁.clauses ⊆ st₂.clauses := by
        have eq : st₂ = (EncState.allocFresh b st₁).2 := by
          rw [← hAlloc]
        intro clause' h'
        rw [eq, EncState.allocFresh_clauses_eq]
        exact h'
      have h₃ :=
        EncState.addClause_subset_clauses (b := b) st₂
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b u')]
      have h₄ :=
        EncState.addClause_subset_clauses (b := b) st₃
          [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b u)]
      have hChain :=
        List.Subset.trans h₁
          (List.Subset.trans h₂ (List.Subset.trans h₃ h₄))
      have hIn : clause ∈ st₄.clauses := hChain hClause
      simp only [encodeFormula]
      rw [← hRes, ← hAlloc]
      simp
      exact hIn
  | diamond learners φ ih =>
      intro w st
      exact encodeFormula_clauses_subset_diamond b learners φ w st
          (fun w' st' => ih w' st')
  | seq =>
      intro w st clause hClause
      cases hAlloc : EncState.allocFresh b st with
      | mk u st₁ =>
          have hAllocSub : st.clauses ⊆ st₁.clauses := by
            have eq : st₁ = (EncState.allocFresh b st).2 := by
              cases hAlloc
              rfl
            intro clause' h'
            rw [eq, EncState.allocFresh_clauses_eq]
            exact h'
          have h₁ :=
            EncState.addClause_subset_clauses (b := b) st₁
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)]
          let st₂ := EncState.addClause b st₁
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)]
          have h₂ :=
            EncState.addClause_subset_clauses (b := b) st₂
              [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)]
          have hChain :=
            List.Subset.trans hAllocSub (List.Subset.trans h₁ h₂)
          have hIn : clause ∈ (EncState.addClause b st₂
              [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)]).clauses :=
            hChain hClause
          simp only [encodeFormula]
          rw [hAlloc]
          exact hIn

end Encoding
