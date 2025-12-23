import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Lemmas.Basic
import ModalDistribution.Logic.SATEncoding.Lemmas.StructuralDeterminism
import ModalDistribution.Logic.SATEncoding.Lemmas.NextFreshMono
import ModalDistribution.Logic.SATEncoding.Lemmas.NestedFoldWF
import ModalDistribution.Logic.SATEncoding.Lemmas.EventWitnessStep

/-!
# Well-Formedness Preservation Lemmas

This file contains lemmas about well-formedness preservation during formula encoding:

- `encodeFormula_nextFresh_mono`: nextFresh is monotonically non-decreasing
- `encodeFormula_preserves_wf`: Encoding preserves well-formedness invariant
- `encodeFormula_controlVar_*`: Control variable bounds
- `encodeFormula_new_clause_fresh_ge_nextFresh`: New clauses only use fresh vars >= nextFresh

These lemmas are critical for completeness proofs.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- The nextFresh counter is monotonically non-decreasing through encoding. -/
lemma encodeFormula_nextFresh_mono (b : Bounds S) (φ : Formula S) (w : WId b) (st : EncState b) :
    st.nextFresh ≤ (encodeFormula b φ w st).2.nextFresh := by
  induction φ generalizing w st with
  | bot =>
    simp only [encodeFormula]
    have h := EncState.allocFresh_nextFresh (b := b) st
    simp [EncState.addClause_nextFresh, h]
  | eq v1 v2 =>
    simp only [encodeFormula]
    have h := EncState.allocFresh_nextFresh (b := b) st
    split <;> simp [EncState.addClause_nextFresh, h]
  | predicate atom =>
    simp only [encodeFormula]
    let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
    let idxs := predIxList b pred
    let literals := idxs.map (fun k => Var.Pred w.p w.ti k)
    have hBigOr := mkBigOrIff_nextFresh b literals st
    split
    · rw [hBigOr]; omega
    · -- Non-empty case: mkBigOrIff → addPreEqFrom → addPreEqReflAll → foldl(foldl addClause)×2
      -- Define intermediate states
      let st1 := (mkBigOrIff b literals st).2
      let st2 := addPreEqFrom b w.ti st1
      let st3 := addPreEqReflAll b st2
      -- Step-by-step bounds
      have h1 : st.nextFresh ≤ st1.nextFresh := by rw [hBigOr]; omega
      have h2 : st1.nextFresh ≤ st2.nextFresh := addPreEqFrom_nextFresh_mono b w.ti st1
      have h3 : st2.nextFresh = st3.nextFresh := (addPreEqReflAll_nextFresh b st2).symm
      -- st3 → st4 (nested foldl for guard clauses): only addClause, preserves nextFresh
      -- Inner foldl preserves nextFresh (adds backward + forward per iteration)
      have hInner : ∀ stx H',
          (idxs.foldl (fun stAcc k =>
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
          ) stx).nextFresh = stx.nextFresh := by
        intro stx H'
        apply foldl_nextFresh_eq
        intro s' _; simp [EncState.addClause]
      have hFold : ∀ stx,
          stx.nextFresh = ((Bounds.timesL b).foldl (fun stCur H' =>
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
          ) stx).nextFresh := by
        intro stx
        exact (foldl_nextFresh_eq b _ stx _ (fun s H' => hInner s H')).symm
      -- Define st4 to match the encoding (the final state after guard foldl)
      let st4 := (Bounds.timesL b).foldl (fun stCur H' =>
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
        ) stCur) st3
      have h4 : st3.nextFresh = st4.nextFresh := hFold st3
      -- st4 is the final result
      change st.nextFresh ≤ st4.nextFresh
      omega
  | event atom =>
    simp only [encodeFormula]
    split
    · split
      · exact encodeFormulaEvent_nextFresh_mono b w _ st
      · simp [EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]
    · simp [EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]
  | imp φ1 φ2 ih1 ih2 =>
    simp only [encodeFormula]
    have h1 := ih1 w st
    have h2 := ih2 w (encodeFormula b φ1 w st).2
    -- imp: encodeFormula φ1, encodeFormula φ2, allocFresh, 3x addClause
    -- nextFresh increases through recursive calls and allocFresh
    calc st.nextFresh
      _ ≤ (encodeFormula b φ1 w st).2.nextFresh := h1
      _ ≤ (encodeFormula b φ2 w (encodeFormula b φ1 w st).2).2.nextFresh := h2
      _ ≤ (encodeFormula b φ2 w (encodeFormula b φ1 w st).2).2.nextFresh + 1 := by omega
      _ = (EncState.allocFresh b
          (encodeFormula b φ2 w (encodeFormula b φ1 w st).2).2).2.nextFresh := by
        rw [EncState.allocFresh_nextFresh]
      _ = _ := by simp [EncState.addClause]
  | atEnd φ ih =>
    simp only [encodeFormula]
    -- atEnd: encodeFormula φ at wEnd, allocFresh, 2x addClause
    have h1 := ih ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st
    -- final nextFresh = allocFresh(encodeFormula result).nextFresh = st1.nextFresh + 1
    -- st1.nextFresh ≥ st.nextFresh by IH
    calc st.nextFresh
      _ ≤ (encodeFormula b φ ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st).2.nextFresh := h1
      _ ≤ (encodeFormula b φ ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st).2.nextFresh + 1 := by omega
      _ = (EncState.allocFresh b
          (encodeFormula b φ ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st).2).2.nextFresh := by
        rw [EncState.allocFresh_nextFresh]
      _ = _ := by simp [EncState.addClause]
  | past φ ih =>
    simp only [encodeFormula]
    -- Structure: allocFresh, foldl encodeFormula, foldl (allocFresh + 4x addClause), addClause
    -- Step 1: allocFresh
    have hAlloc : st.nextFresh < (EncState.allocFresh b st).2.nextFresh := by
      simp [EncState.allocFresh_nextFresh]
    let st1 := (EncState.allocFresh b st).2
    -- Define witnesses
    let witnesses := (WId.allWorlds b).filterMap fun w' =>
      if w'.p = w.p then some w' else none
    -- Step 2: foldl with encodeFormula - monotonic by IH
    have hMono1 : ∀ (acc : List (FVar b) × EncState b) w',
        acc.2.nextFresh ≤ ((fun (uvars, stCur) w' =>
          let (u', stNext) := encodeFormula b φ w' stCur
          (uvars ++ [u'], stNext)) acc w').2.nextFresh := by
      intro (vars, stCur) w'
      simp only
      exact ih w' stCur
    have hFold1 : ∀ stx, stx.nextFresh ≤ (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) ([], stx)).2.nextFresh := by
      intro stx
      exact foldl_nextFresh_mono_pair witnesses (([] : List (FVar b)), stx) _ hMono1
    let st2 := (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) ([], st1)).2
    let witnessVars := (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) ([], st1)).1
    -- Step 3: foldl with allocFresh + 4x addClause - monotonic
    have hMono2 : ∀ (acc : List (FVar b) × EncState b) (pair : FVar b × WId b),
        acc.2.nextFresh ≤ ((fun (auxAcc, stCur) (u', w') =>
          let memVar := Var.Mem w.ti w'
          let (aux, stCur) := EncState.allocFresh b stCur
          let stCur := EncState.addClause b stCur [SAT.Lit.neg memVar,
            SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)]
          let stCur := EncState.addClause b stCur [SAT.Lit.neg memVar,
            SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b aux)]
          let stCur := EncState.addClause b stCur
            [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
          let stCur := EncState.addClause b stCur
            [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
          (auxAcc ++ [aux], stCur)) acc pair).2.nextFresh := by
      intro (auxAcc, stCur) (u', w')
      simp only [EncState.addClause, EncState.allocFresh_nextFresh]
      omega
    have hFold2 : ∀ stx, stx.nextFresh ≤
        ((witnessVars.zip witnesses).foldl (fun (auxAcc, stCur) (u', w') =>
          let memVar := Var.Mem w.ti w'
          let (aux, stCur) := EncState.allocFresh b stCur
          let stCur := EncState.addClause b stCur [SAT.Lit.neg memVar,
            SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)]
          let stCur := EncState.addClause b stCur [SAT.Lit.neg memVar,
            SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b aux)]
          let stCur := EncState.addClause b stCur
            [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
          let stCur := EncState.addClause b stCur
            [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
          (auxAcc ++ [aux], stCur)) (([] : List (FVar b)), stx)).2.nextFresh := by
      intro stx
      exact foldl_nextFresh_mono_pair
        (witnessVars.zip witnesses) (([] : List (FVar b)), stx) _ hMono2
    -- Step 4: addClause preserves
    have hAdd : ∀ stx c, (EncState.addClause b stx c).nextFresh = stx.nextFresh := by
      intro _ _; simp [EncState.addClause]
    -- Chain everything together
    have h1 : st.nextFresh < st1.nextFresh := hAlloc
    have h2 : st1.nextFresh ≤ st2.nextFresh := hFold1 st1
    change st.nextFresh ≤ _
    calc st.nextFresh
      _ ≤ st1.nextFresh := Nat.le_of_lt h1
      _ ≤ st2.nextFresh := h2
      _ ≤ _ := Nat.le_trans (hFold2 st2) (by rw [hAdd])
  | «forall» body ih =>
    simp only [encodeFormula]
    -- Structure: allocFresh, foldl encodeFormula, foldl addClause, addClause
    -- Step 1: allocFresh
    have hAlloc : st.nextFresh < (EncState.allocFresh b st).2.nextFresh := by
      simp [EncState.allocFresh_nextFresh]
    let st1 := (EncState.allocFresh b st).2
    -- Step 2: foldl with encodeFormula - monotonic by IH
    have hFold : ∀ (stx : EncState b),
        stx.nextFresh ≤ ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
          let v := b.values.get vIdx
          have hNonempty : Nonempty S.Value := ⟨v⟩
          have _hDepth : depth (body v) < depth (.forall body) := by
            open Classical in
            simp only [depth, hNonempty, ↓reduceDIte]
            rw [depth_uniform body v (choice hNonempty)]
            omega
          let (uBody, stNext) := encodeFormula b (body v) w stCur
          (vars ++ [uBody], stNext)
        ) ([], stx)).2.nextFresh := by
      intro stx
      have hMono : ∀ (acc : List (FVar b) × EncState b) vIdx,
          acc.2.nextFresh ≤ ((fun (vars, stCur) vIdx =>
            let v := b.values.get vIdx
            have hNonempty : Nonempty S.Value := ⟨v⟩
            have _hDepth : depth (body v) < depth (.forall body) := by
              open Classical in
              simp only [depth, hNonempty, ↓reduceDIte]
              rw [depth_uniform body v (choice hNonempty)]
              omega
            let (uBody, stNext) := encodeFormula b (body v) w stCur
            (vars ++ [uBody], stNext)) acc vIdx).2.nextFresh := by
        intro (vars, stCur) vIdx
        simp only
        exact ih (b.values.get vIdx) w stCur
      exact foldl_nextFresh_mono_pair (List.finRange b.nVals) (([] : List (FVar b)), stx)
        _ hMono
    let st2 := ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
      let v := b.values.get vIdx
      have hNonempty : Nonempty S.Value := ⟨v⟩
      have _hDepth : depth (body v) < depth (.forall body) := by
        open Classical in
        simp only [depth, hNonempty, ↓reduceDIte]
        rw [depth_uniform body v (choice hNonempty)]
        omega
      let (uBody, stNext) := encodeFormula b (body v) w stCur
      (vars ++ [uBody], stNext)
    ) ([], st1)).2
    -- Step 3: foldl addClause preserves nextFresh
    let bodyVars := ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
      let v := b.values.get vIdx
      have hNonempty : Nonempty S.Value := ⟨v⟩
      have _hDepth : depth (body v) < depth (.forall body) := by
        open Classical in
        simp only [depth, hNonempty, ↓reduceDIte]
        rw [depth_uniform body v (choice hNonempty)]
        omega
      let (uBody, stNext) := encodeFormula b (body v) w stCur
      (vars ++ [uBody], stNext)
    ) ([], st1)).1
    have hFold2 : ∀ stx, stx.nextFresh = (bodyVars.foldl (fun stCur uBody =>
        EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
           SAT.Lit.pos (FVar.toVar b uBody)]
      ) stx).nextFresh := by
      intro stx
      exact (foldl_nextFresh_eq b _ stx _ (fun s _ => by simp [EncState.addClause])).symm
    -- Step 4: final addClause preserves
    have hAdd : ∀ stx c, (EncState.addClause b stx c).nextFresh = stx.nextFresh := by
      intro _ _; simp [EncState.addClause]
    -- Combine: st → st1 → st2 → foldl → final
    have hChain1 : st.nextFresh < st1.nextFresh := hAlloc
    have hChain2 : st1.nextFresh ≤ st2.nextFresh := hFold st1
    change st.nextFresh ≤ _
    calc st.nextFresh
      _ ≤ st1.nextFresh := Nat.le_of_lt hChain1
      _ ≤ st2.nextFresh := hChain2
      _ = _ := by rw [hFold2 st2, hAdd]
  | seq =>
    simp only [encodeFormula]
    have h := EncState.allocFresh_nextFresh (b := b) st
    simp [EncState.addClause_nextFresh, h]
  | diamond learners φ ih =>
    simp only [encodeFormula]
    -- Structure: tuples.foldl step, then either allocFresh+addClause or foldl mkAndIff

    -- Helper definitions
    let getMinQs (ℓ : S.Value) : List (Finset b.participants) :=
      let vIdx := b.findValueIndex ℓ
      let allVars := Var.allMinQ b vIdx
      allVars.filterMap fun v =>
        match v with
        | Var.MinQ _ Q => some Q
        | _ => none
    let quorumSets : List (List (Finset b.participants)) := learners.map getMinQs
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

    -- Step monotonicity: each step does foldl encodeFormula then encodeTupleControl
    have hStepMono : ∀ (acc : List (FVar b) × EncState b) tuple,
        acc.2.nextFresh ≤ (step acc tuple).2.nextFresh := by
      intro (accVars, stCur) tuple
      simp only [step]
      let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
      -- The witness fold is monotonic (uses encodeFormula which is monotonic by IH)
      have hMono : ∀ (acc : List (FVar b × b.participants) × EncState b) p,
          acc.2.nextFresh ≤ ((fun acc p =>
            if hp : p ∈ intersection then
              let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
              let (uWit, stNew) := encodeFormula b φ wEnd acc.2
              (acc.1 ++ [(uWit, p)], stNew)
            else acc) acc p).2.nextFresh := by
        intro (accP, stP) p
        by_cases hp : p ∈ intersection
        · simp only [hp, dite_true]
          exact ih ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ stP
        · simp only [hp, dite_false]; exact Nat.le_refl _
      let witnessFold := (Bounds.partsL b).foldl
          (fun (acc : List (FVar b × b.participants) × EncState b) p =>
            if hp : p ∈ intersection then
              let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
              let (uWit, stNew) := encodeFormula b φ wEnd acc.2
              (acc.1 ++ [(uWit, p)], stNew)
            else
              acc)
          ([], stCur)
      have hWitFold : stCur.nextFresh ≤ witnessFold.2.nextFresh :=
        foldl_nextFresh_mono_pair (Bounds.partsL b)
          (([] : List (FVar b × b.participants)), stCur) _ hMono
      let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
      -- encodeTupleControl is monotonic
      have hEncode := encodeTupleControl_nextFresh_mono b learners tuple witnessVars witnessFold.2
      exact Nat.le_trans hWitFold hEncode

    -- Main foldl is monotonic
    have hFoldMain : st.nextFresh ≤ (tuples.foldl step ([], st)).2.nextFresh :=
      foldl_nextFresh_mono_pair tuples (([] : List (FVar b)), st) step hStepMono

    let stTuples := (tuples.foldl step ([], st)).2
    let tupleVars := (tuples.foldl step ([], st)).1

    -- Final step: either allocFresh+addClause or foldl mkAndIff
    -- Split on the match in the goal
    split
    next =>
      -- Empty case: allocFresh + addClause
      -- addClause preserves nextFresh, allocFresh increases by 1
      have hAllocMono : stTuples.nextFresh ≤ (EncState.allocFresh b stTuples).2.nextFresh := by
        simp [EncState.allocFresh_nextFresh]
      have hAddPres : (EncState.addClause b (EncState.allocFresh b stTuples).2
          [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b stTuples).1)]).nextFresh
          = (EncState.allocFresh b stTuples).2.nextFresh := by
        simp [EncState.addClause]
      calc st.nextFresh
        _ ≤ stTuples.nextFresh := hFoldMain
        _ ≤ (EncState.allocFresh b stTuples).2.nextFresh := hAllocMono
        _ = _ := hAddPres.symm
    next u0 us hEq =>
      -- Non-empty case: foldl mkAndIff
      have hMkAndMono : ∀ (acc : FVar b × EncState b) u',
          acc.2.nextFresh ≤ (mkAndIff b acc.1 u' acc.2).2.nextFresh := by
        intro (uAcc, stAcc) u'
        exact mkAndIff_nextFresh_mono b uAcc u' stAcc
      have hFoldMkAnd : stTuples.nextFresh ≤ (us.foldl (fun acc u' =>
          let (uAcc, stAcc) := acc
          mkAndIff b uAcc u' stAcc) (u0, stTuples)).2.nextFresh :=
        foldl_nextFresh_mono_pair us (u0, stTuples) _ hMkAndMono
      calc st.nextFresh
        _ ≤ stTuples.nextFresh := hFoldMain
        _ ≤ _ := hFoldMkAnd

/-- The witness fold is monotonic w.r.t. nextFresh. -/
lemma diamondWitnessFold_nextFresh_mono (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (st : EncState b) :
    st.nextFresh ≤ (diamondWitnessFold b φ w intersection st).2.nextFresh := by
  simp only [diamondWitnessFold]
  have hMono : ∀ (acc : List (FVar b × b.participants) × EncState b) p,
      acc.2.nextFresh ≤ ((fun acc p =>
        if hp : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc.2
          (acc.1 ++ [(uWit, p)], stNew)
        else acc) acc p).2.nextFresh := by
    intro acc p
    by_cases hp : p ∈ intersection
    · simp only [hp, dite_true]
      exact encodeFormula_nextFresh_mono b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2
    · simp only [hp, dite_false]; exact Nat.le_refl _
  exact foldl_nextFresh_mono_pair (Bounds.partsL b)
    (([] : List (FVar b × b.participants)), st) _ hMono

/-- diamondStep is monotonic w.r.t. nextFresh. -/
lemma diamondStep_nextFresh_mono (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b) (acc : List (FVar b) × EncState b)
    (tuple : List (Finset b.participants)) :
    acc.2.nextFresh ≤ (diamondStep b learners φ w acc tuple).2.nextFresh := by
  simp only [diamondStep]
  have hWitMono := diamondWitnessFold_nextFresh_mono b φ w
    (tuple.foldl (· ∩ ·) Finset.univ) acc.2
  exact Nat.le_trans hWitMono (encodeTupleControl_nextFresh_mono b learners tuple _ _)

/-- Each element in the diamondStep fold has id ≥ st.nextFresh. -/
lemma diamondStep_foldl_all_id_ge (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b)
    (tuples : List (List (Finset b.participants))) (st : EncState b) :
    ∀ u ∈ (tuples.foldl (diamondStep b learners φ w) ([], st)).1, u.id ≥ st.nextFresh := by
  have hElem : ∀ (acc : List (FVar b) × EncState b) tuple,
      (diamondStep b learners φ w acc tuple).1 =
      acc.1 ++ [(encodeTupleControl b learners tuple
        ((diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) acc.2).1.map
          fun u => FVar.toVar b u.1)
        (diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) acc.2).2).1] := by
    intro acc tuple
    simp only [diamondStep]
  have hFoldAcc : ∀ (ts : List (List (Finset b.participants)))
      (acc : List (FVar b) × EncState b),
      ∀ u ∈ (ts.foldl (diamondStep b learners φ w) acc).1,
      u ∈ acc.1 ∨ u.id ≥ acc.2.nextFresh := by
    intro ts
    induction ts with
    | nil => intro acc u hu; left; exact hu
    | cons t ts' ih =>
      intro acc u hu
      simp only [List.foldl_cons] at hu
      have hStep := ih (diamondStep b learners φ w acc t) u hu
      rcases hStep with hInStep | hGeStep
      · rw [hElem] at hInStep
        simp only [List.mem_append, List.mem_singleton] at hInStep
        rcases hInStep with hOld | hNew
        · left; exact hOld
        · right
          rw [hNew]
          have := diamondStep_element_id_eq_nextFresh b learners φ w t acc.2
          rw [this]
          exact diamondWitnessFold_nextFresh_mono b φ w (t.foldl (· ∩ ·) Finset.univ) acc.2
      · right
        have hStepMono := diamondStep_nextFresh_mono b learners φ w acc t
        exact Nat.le_trans hStepMono hGeStep
  intro u hu
  have := hFoldAcc tuples ([], st) u hu
  rcases this with hEmpty | hGe
  · simp only [List.not_mem_nil] at hEmpty
  · exact hGe

/-- The control variable returned by encodeFormula has id ≥ input state's nextFresh.

    This follows because the control variable is allocated via allocFresh, and
    allocFresh uses the current nextFresh as the new variable's id. -/
lemma encodeFormula_controlVar_ge_nextFresh (b : Bounds S) (φ : Formula S) (w : WId b)
    (st : EncState b) :
    (encodeFormula b φ w st).1.id ≥ st.nextFresh := by
  -- The control variable comes from allocFresh at some point during encoding.
  -- Since allocFresh uses st.nextFresh (possibly of a later state), and
  -- nextFresh is monotonically non-decreasing, the result is ≥ st.nextFresh.
  induction φ generalizing w st with
  | bot => simp only [encodeFormula, EncState.allocFresh]; rfl
  | eq _ _ => simp only [encodeFormula, EncState.allocFresh]; rfl
  | seq => simp only [encodeFormula, EncState.allocFresh]; rfl
  | predicate atom =>
      simp only [encodeFormula]
      -- In both branches, the control var comes from mkBigOrIff which allocates at st.nextFresh
      split <;> simp only [mkBigOrIff_fst] <;> rfl
  | event _ =>
      simp only [encodeFormula]
      split
      · split
        · -- encodeFormulaEvent: control var comes from mkBigOrIff at state after fold
          simp only [encodeFormulaEvent, mkBigOrIff_fst]
          -- The state going into mkBigOrIff has nextFresh ≥ st.nextFresh by foldl monotonicity
          exact foldl_eventWitnessStep_nextFresh_mono b _ ([], st)
        · exact le_refl _
      · exact le_refl _
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [encodeFormula, EncState.allocFresh]
      -- u.id = (encodeFormula φ₂ ...).2.nextFresh
      -- Need: (encodeFormula φ₂ ...).2.nextFresh ≥ st.nextFresh
      exact encodeFormula_nextFresh_mono b φ₂ w (encodeFormula b φ₁ w st).2
        |> Nat.le_trans (encodeFormula_nextFresh_mono b φ₁ w st)
  | atEnd φ ih =>
      simp only [encodeFormula, EncState.allocFresh]
      exact encodeFormula_nextFresh_mono b φ ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st
  | past φ ih => simp only [encodeFormula, EncState.allocFresh]; rfl
  | «forall» body ih => simp only [encodeFormula, EncState.allocFresh]; rfl
  | diamond learners φ ih =>
      simp only [encodeFormula]
      -- The control var comes from either allocFresh (empty) or mkAndIff fold (non-empty)
      -- In all cases, the id equals some intermediate or final nextFresh ≥ st.nextFresh
      let getMinQs (ℓ : S.Value) : List (Finset b.participants) :=
        let vIdx := b.findValueIndex ℓ
        (Var.allMinQ b vIdx).filterMap fun v =>
          match v with | Var.MinQ _ Q => some Q | _ => none
      let quorumSets := learners.map getMinQs
      let tuples := cartesianProduct quorumSets
      -- Define inline step and show it's monotonic (same as encodeFormula_nextFresh_mono)
      let step : (List (FVar b) × EncState b) → List (Finset b.participants) →
          List (FVar b) × EncState b :=
        fun (accVars, stCur) tuple =>
          let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
          let witnessFold := (Bounds.partsL b).foldl
              (fun (acc : List (FVar b × b.participants) × EncState b) p =>
                if hp : p ∈ intersection then
                  let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                  let (uWit, stNew) := encodeFormula b φ wEnd acc.2
                  (acc.1 ++ [(uWit, p)], stNew)
                else acc)
              ([], stCur)
          let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
          let (uTuple, stFinal) := encodeTupleControl b learners tuple witnessVars witnessFold.2
          (accVars ++ [uTuple], stFinal)
      -- Step monotonicity
      have hStepMono : ∀ (acc : List (FVar b) × EncState b) tuple,
          acc.2.nextFresh ≤ (step acc tuple).2.nextFresh := by
        intro (accVars, stCur) tuple
        simp only [step]
        let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
        have hMono : ∀ (acc : List (FVar b × b.participants) × EncState b) p,
            acc.2.nextFresh ≤ ((fun acc p =>
              if hp : p ∈ intersection then
                let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd acc.2
                (acc.1 ++ [(uWit, p)], stNew)
              else acc) acc p).2.nextFresh := by
          intro acc p
          by_cases hp : p ∈ intersection
          · simp only [hp, dite_true]
            exact encodeFormula_nextFresh_mono b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2
          · simp only [hp, dite_false]; exact Nat.le_refl _
        have hWitFold := foldl_nextFresh_mono_pair (Bounds.partsL b)
            (([] : List (FVar b × b.participants)), stCur) _ hMono
        exact Nat.le_trans hWitFold (encodeTupleControl_nextFresh_mono b learners tuple _ _)
      have hFoldMain : st.nextFresh ≤ (tuples.foldl step ([], st)).2.nextFresh :=
        foldl_nextFresh_mono_pair tuples (([] : List (FVar b)), st) step hStepMono
      -- All elements in fold have id ≥ st.nextFresh
      have hAllGe : ∀ u ∈ (tuples.foldl step ([], st)).1, u.id ≥ st.nextFresh := by
        have hFoldAcc : ∀ (ts : List (List (Finset b.participants)))
            (acc : List (FVar b) × EncState b),
            ∀ u ∈ (ts.foldl step acc).1, u ∈ acc.1 ∨ u.id ≥ acc.2.nextFresh := by
          intro ts
          induction ts with
          | nil => intro acc u hu; left; exact hu
          | cons t ts' ihts =>
            intro acc u hu
            simp only [List.foldl_cons] at hu
            have hIh := ihts (step acc t) u hu
            rcases hIh with hIn | hGe
            · simp only [step, List.mem_append, List.mem_singleton] at hIn
              rcases hIn with hOld | hNew
              · left; exact hOld
              · right; rw [hNew, encodeTupleControl_fst_id]
                let intersection := t.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
                have hMono' : ∀ (acc' : List (FVar b × b.participants) × EncState b) p,
                    acc'.2.nextFresh ≤ ((fun acc' p =>
                      if hp : p ∈ intersection then
                        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                        let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
                        (acc'.1 ++ [(uWit, p)], stNew)
                      else acc') acc' p).2.nextFresh := by
                  intro acc' p
                  by_cases hp : p ∈ intersection
                  · simp only [hp, dite_true]
                    exact encodeFormula_nextFresh_mono b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc'.2
                  · simp only [hp, dite_false]; exact Nat.le_refl _
                exact foldl_nextFresh_mono_pair (Bounds.partsL b)
                  (([] : List (FVar b × b.participants)), acc.2) _ hMono'
            · right; exact Nat.le_trans (hStepMono acc t) hGe
        intro u hu
        have := hFoldAcc tuples ([], st) u hu
        rcases this with hEmpty | hGe
        · simp only [List.not_mem_nil] at hEmpty
        · exact hGe
      -- The control var id ≥ st.nextFresh because:
      -- - Empty case: allocFresh at stTuples gives id = stTuples.nextFresh ≥ st.nextFresh
      -- - Non-empty case: mkAndIff fold allocates at monotonically increasing nextFresh values
      -- The proof requires matching the inline step function form, which is complex.
      -- TODO: Complete this proof by showing inline step equals `step` definitionally
      split
      · -- Empty case: allocFresh at stTuples
        simp only [EncState.allocFresh]; exact hFoldMain
      · -- Non-empty case: mkAndIff fold
        -- The returned control var comes from mkAndIff which allocates at a state
        -- with nextFresh ≥ st.nextFresh (by monotonicity of all intermediate operations)
        rename_i u0 us hNonEmpty
        -- The fold result is definitionally equal to our step/tuples version
        have hFoldEq1 : (tuples.foldl step ([], st)).1 = u0 :: us := hNonEmpty
        -- u0 is in fold.1, so u0.id ≥ st.nextFresh
        have hu0Mem : u0 ∈ (tuples.foldl step ([], st)).1 := by
          rw [hFoldEq1]; simp
        have hu0Ge := hAllGe u0 hu0Mem
        -- Case split on us
        cases hus : us with
        | nil =>
          -- Singleton case: control is u0
          simp only [List.foldl_nil]
          exact hu0Ge
        | cons v vs =>
          -- Multiple case: control is from mkAndIff fold
          simp only []
          -- The result's id = fold.2.nextFresh + vs.length by mkAndIff_fold_fst_id_pos
          have hPos : 0 < (v :: vs).length := by simp
          have hResultId :=
            mkAndIff_fold_fst_id_pos b u0 (v :: vs) (tuples.foldl step ([], st)).2 hPos
          -- Show the goal equals the pattern from hResultId
          calc ((v :: vs).foldl (fun acc u' => mkAndIff b acc.1 u' acc.2)
                (u0, (tuples.foldl step ([], st)).2)).1.id
            _ = (tuples.foldl step ([], st)).2.nextFresh + (v :: vs).length - 1 := hResultId
            _ ≥ st.nextFresh := by omega

/-- The control variable returned by encodeFormula has id < output state's nextFresh.

    This is needed to show that the returned FVar can be used in subsequent encoding
    steps without appearing in the output state's clauses. -/
lemma encodeFormula_controlVar_lt_nextFresh (b : Bounds S) (φ : Formula S) (w : WId b)
    (st : EncState b) :
    (encodeFormula b φ w st).1.id < (encodeFormula b φ w st).2.nextFresh := by
  induction φ generalizing w st with
  | bot =>
    -- bot: allocFresh then addClause
    -- u.id = st.nextFresh, output.nextFresh = st.nextFresh + 1
    simp only [encodeFormula]
    exact Nat.lt_succ_self _
  | eq v1 v2 =>
    -- eq: allocFresh then addClause
    simp only [encodeFormula]
    split <;> exact Nat.lt_succ_self _
  | seq =>
    -- seq: allocFresh then two addClauses
    simp only [encodeFormula]
    exact Nat.lt_succ_self _
  | imp φ₁ φ₂ ih₁ ih₂ =>
    -- imp: encode φ₁, encode φ₂, allocFresh, three addClauses
    -- The returned u is from the final allocFresh
    simp only [encodeFormula]
    exact Nat.lt_succ_self _
  | atEnd φ ih =>
    -- atEnd: encode φ at wEnd, allocFresh, two addClauses
    simp only [encodeFormula]
    exact Nat.lt_succ_self _
  | predicate atom =>
    -- mkBigOrIff returns a control var that is < output nextFresh
    simp only [encodeFormula]
    split
    · exact mkBigOrIff_controlVar_lt_nextFresh b _ st
    · -- Complex fold case: control var from mkBigOrIff has id = st.nextFresh
      -- mkBigOrIff_nextFresh gives +1, subsequent ops are monotonic
      -- So final nextFresh ≥ st.nextFresh + 1 > control.id
      let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
      let idxs := predIxList b pred
      let literals := idxs.map (fun k => Var.Pred w.p w.ti k)
      -- Control var id = st.nextFresh (from mkBigOrIff)
      have hControlId : (mkBigOrIff b literals st).1.id = st.nextFresh := by
        simp only [mkBigOrIff_fst]
      -- mkBigOrIff output nextFresh = st.nextFresh + 1
      have hBigOrNext : (mkBigOrIff b literals st).2.nextFresh = st.nextFresh + 1 :=
        mkBigOrIff_nextFresh b literals st
      -- All subsequent operations preserve or increase nextFresh
      let st1 := (mkBigOrIff b literals st).2
      let st2 := addPreEqFrom b w.ti st1
      let st3 := addPreEqReflAll b st2
      have h1 : st1.nextFresh ≤ st2.nextFresh := addPreEqFrom_nextFresh_mono b w.ti st1
      have h2 : st2.nextFresh = st3.nextFresh := (addPreEqReflAll_nextFresh b st2).symm
      -- The nested fold only uses addClause which preserves nextFresh
      have hInner : ∀ stx H',
          (idxs.foldl (fun stAcc k =>
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
          ) stx).nextFresh = stx.nextFresh := by
        intro stx H'
        apply foldl_nextFresh_eq
        intro s' _; simp [EncState.addClause]
      have hFold : ∀ stx,
          stx.nextFresh = ((Bounds.timesL b).foldl (fun stCur H' =>
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
          ) stx).nextFresh := by
        intro stx
        exact (foldl_nextFresh_eq b _ stx _ (fun s H' => hInner s H')).symm
      -- Define st4 to match the encoding (final state after guard fold)
      let st4 := (Bounds.timesL b).foldl (fun stCur H' =>
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
        ) stCur) st3
      have h3 : st3.nextFresh = st4.nextFresh := hFold st3
      -- Chain: u.id = st.nextFresh < st.nextFresh + 1 = st1.nextFresh ≤ st4.nextFresh
      calc (mkBigOrIff b literals st).1.id
        _ = st.nextFresh := hControlId
        _ < st.nextFresh + 1 := Nat.lt_succ_self _
        _ = st1.nextFresh := hBigOrNext.symm
        _ ≤ st2.nextFresh := h1
        _ = st3.nextFresh := h2
        _ = st4.nextFresh := h3
  | event atom =>
    simp only [encodeFormula]
    split
    next e =>
      split
      · -- encodeFormulaEvent case
        simp only [encodeFormulaEvent]
        exact mkBigOrIff_controlVar_lt_nextFresh b _ _
      · -- Guard fails: simple allocFresh + addClause
        exact Nat.lt_succ_self _
    · -- MaybeEvent.none case
      exact Nat.lt_succ_self _
  | past φ ih =>
    -- Past: allocFresh for u FIRST, then folds increase nextFresh
    -- The returned u.id = st.nextFresh, output.nextFresh > st.nextFresh
    -- The control var id = st.nextFresh (from the first allocFresh)
    have hControlEq : (encodeFormula b (Formula.past φ) w st).1.id = st.nextFresh := by
      simp only [encodeFormula]; rfl
    -- After allocFresh, nextFresh = st.nextFresh + 1
    have hAfterAlloc : (EncState.allocFresh b st).2.nextFresh = st.nextFresh + 1 :=
      EncState.allocFresh_nextFresh b st
    -- All subsequent operations are monotonic
    have hMono := encodeFormula_nextFresh_mono b (Formula.past φ) w st
    -- The key: output.nextFresh ≥ st.nextFresh + 1
    -- This follows because: output.nextFresh ≥ allocFresh_result.nextFresh = st.nextFresh + 1
    -- Proof: after simp [encodeFormula], the result is a nested foldl starting from allocFresh
    -- and all folds preserve monotonicity (≥)
    have hStrict : st.nextFresh + 1 ≤ (encodeFormula b (Formula.past φ) w st).2.nextFresh := by
      simp only [encodeFormula]
      -- Need: st1.nextFresh ≤ output.nextFresh where st1 = allocFresh result
      -- The monotonicity proof (above in this file, case | past) shows exactly this
      -- We reproduce the structure here
      let st1 := (EncState.allocFresh b st).2
      let witnesses := (WId.allWorlds b).filterMap fun w' =>
        if w'.p = w.p then some w' else none
      have hFold1 : ∀ stx, stx.nextFresh ≤ (witnesses.foldl (fun (uvars, stCur) w' =>
          let (u', stNext) := encodeFormula b φ w' stCur
          (uvars ++ [u'], stNext)) ([], stx)).2.nextFresh := by
        intro stx
        exact foldl_nextFresh_mono_pair witnesses (([] : List (FVar b)), stx) _
          (fun acc w' => encodeFormula_nextFresh_mono b φ w' acc.2)
      let witnessVars := (witnesses.foldl (fun (uvars, stCur) w' =>
          let (u', stNext) := encodeFormula b φ w' stCur
          (uvars ++ [u'], stNext)) ([], st1)).1
      let st2 := (witnesses.foldl (fun (uvars, stCur) w' =>
          let (u', stNext) := encodeFormula b φ w' stCur
          (uvars ++ [u'], stNext)) ([], st1)).2
      have hMono2 : ∀ (acc : List (FVar b) × EncState b) (pair : FVar b × WId b),
          acc.2.nextFresh ≤ ((fun (auxAcc, stCur) (u', w') =>
            let memVar := Var.Mem w.ti w'
            let (aux, stCur) := EncState.allocFresh b stCur
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)]
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b aux)]
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
            (auxAcc ++ [aux], stCur)) acc pair).2.nextFresh := by
        intro (auxAcc, stCur) (u', w')
        simp only [EncState.addClause, EncState.allocFresh_nextFresh]
        omega
      have hFold2 : ∀ stx, stx.nextFresh ≤
          ((witnessVars.zip witnesses).foldl (fun (auxAcc, stCur) (u', w') =>
            let memVar := Var.Mem w.ti w'
            let (aux, stCur) := EncState.allocFresh b stCur
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)]
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b aux)]
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
            let stCur := EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
            (auxAcc ++ [aux], stCur)) (([] : List (FVar b)), stx)).2.nextFresh := by
        intro stx
        exact foldl_nextFresh_mono_pair
          (witnessVars.zip witnesses) (([] : List (FVar b)), stx) _ hMono2
      -- Chain: st1.nextFresh ≤ st2.nextFresh ≤ st3.nextFresh ≤ final (addClause preserves)
      have hAdd : ∀ stx c, (EncState.addClause b stx c).nextFresh = stx.nextFresh := by
        intro _ _; simp [EncState.addClause]
      calc st.nextFresh + 1
        _ = st1.nextFresh := hAfterAlloc.symm
        _ ≤ st2.nextFresh := hFold1 st1
        _ ≤ _ := Nat.le_trans (hFold2 st2) (by rw [hAdd])
    omega
  | «forall» body ih =>
    -- Forall: allocFresh for u FIRST, then folds increase nextFresh
    have hControlEq : (encodeFormula b (Formula.forall body) w st).1.id = st.nextFresh := by
      simp only [encodeFormula]; rfl
    -- After allocFresh, nextFresh = st.nextFresh + 1
    have hAfterAlloc : (EncState.allocFresh b st).2.nextFresh = st.nextFresh + 1 :=
      EncState.allocFresh_nextFresh b st
    have hStrict : st.nextFresh + 1 ≤ (encodeFormula b (Formula.forall body) w st).2.nextFresh := by
      simp only [encodeFormula]
      let st1 := (EncState.allocFresh b st).2
      -- Step 2: foldl with encodeFormula - monotonic by IH
      have hFold : ∀ (stx : EncState b),
          stx.nextFresh ≤ ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
            let v := b.values.get vIdx
            have hNonempty : Nonempty S.Value := ⟨v⟩
            have _hDepth : depth (body v) < depth (.forall body) := by
              open Classical in
              simp only [depth, hNonempty, ↓reduceDIte]
              rw [depth_uniform body v (choice hNonempty)]
              omega
            let (uBody, stNext) := encodeFormula b (body v) w stCur
            (vars ++ [uBody], stNext)
          ) ([], stx)).2.nextFresh := by
        intro stx
        have hMono : ∀ (acc : List (FVar b) × EncState b) vIdx,
            acc.2.nextFresh ≤ ((fun (vars, stCur) vIdx =>
              let v := b.values.get vIdx
              have hNonempty : Nonempty S.Value := ⟨v⟩
              have _hDepth : depth (body v) < depth (.forall body) := by
                open Classical in
                simp only [depth, hNonempty, ↓reduceDIte]
                rw [depth_uniform body v (choice hNonempty)]
                omega
              let (uBody, stNext) := encodeFormula b (body v) w stCur
              (vars ++ [uBody], stNext)) acc vIdx).2.nextFresh := by
          intro (vars, stCur) vIdx
          simp only
          exact encodeFormula_nextFresh_mono b (body (b.values.get vIdx)) w stCur
        exact foldl_nextFresh_mono_pair (List.finRange b.nVals) (([] : List (FVar b)), stx) _ hMono
      let st2 := ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        have hNonempty : Nonempty S.Value := ⟨v⟩
        have _hDepth : depth (body v) < depth (.forall body) := by
          open Classical in
          simp only [depth, hNonempty, ↓reduceDIte]
          rw [depth_uniform body v (choice hNonempty)]
          omega
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)
      ) ([], st1)).2
      let bodyVars := ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        have hNonempty : Nonempty S.Value := ⟨v⟩
        have _hDepth : depth (body v) < depth (.forall body) := by
          open Classical in
          simp only [depth, hNonempty, ↓reduceDIte]
          rw [depth_uniform body v (choice hNonempty)]
          omega
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)
      ) ([], st1)).1
      -- Step 3: foldl addClause preserves nextFresh
      have hFold2 : ∀ stx, stx.nextFresh = (bodyVars.foldl (fun stCur uBody =>
          EncState.addClause b stCur
            [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
             SAT.Lit.pos (FVar.toVar b uBody)]
        ) stx).nextFresh := by
        intro stx
        exact (foldl_nextFresh_eq b _ stx _ (fun s _ => by simp [EncState.addClause])).symm
      -- Step 4: final addClause preserves
      have hAdd : ∀ stx c, (EncState.addClause b stx c).nextFresh = stx.nextFresh := by
        intro _ _; simp [EncState.addClause]
      calc st.nextFresh + 1
        _ = st1.nextFresh := hAfterAlloc.symm
        _ ≤ st2.nextFresh := hFold st1
        _ = _ := by rw [hFold2 st2, hAdd]
    omega
  | diamond learners φ ih =>
    -- Diamond encoding has structure:
    -- 1. Fold over tuples with step function → (tupleVars, stTuples)
    -- 2. Match on tupleVars:
    --    - Empty: allocFresh, addClause → id = stTuples.nextFresh < stTuples.nextFresh + 1
    --    - Singleton [u0]: return u0 → u0.id < stTuples.nextFresh
    --    - Multiple u0::us: mkAndIff fold → id = stTuples.nextFresh + |us| - 1 <
    --      stTuples.nextFresh + |us|
    simp only [encodeFormula]
    -- Define the inline step function and fold result
    let tuples := cartesianProduct (learners.map (diamondGetMinQs (b := b)))
    let step := fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      (x.1 ++
        [(encodeTupleControl b learners tuple
            (List.map (fun u => FVar.toVar b u.1)
              (List.foldl
                (fun acc p =>
                  if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ
                        { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                      (encodeFormula b φ
                        { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                  else acc)
                ([], x.2) b.partsL).1)
            (List.foldl
              (fun acc p =>
                if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ
                      { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ
                      { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).2).1],
      (encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ
                      { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ
                      { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).2)
    let fold := tuples.foldl step ([], st)
    -- The inline step is definitionally equal to diamondStep
    have hStepEq : step = diamondStep b learners φ w :=
      encodeFormula_diamond_step_unfolded_eq b learners φ w
    have hFoldEq : fold = tuples.foldl (diamondStep b learners φ w) ([], st) := by
      simp only [fold, hStepEq]
    -- Get the length equality
    have hLen : fold.1.length = tuples.length := by
      rw [hFoldEq]
      exact diamondStep_foldl_length b learners φ w tuples st
    -- Case split on fold.1 structure
    -- Prove the result in terms of fold, then apply definitional equality
    suffices h : (match fold.1 with
        | [] => let (u', st') := EncState.allocFresh b fold.2
                let st'' := EncState.addClause b st' [SAT.Lit.pos (FVar.toVar b u')]
                (u', st'')
        | u0 :: us => let res := us.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0, fold.2)
                (res.1, res.2)).1.id <
       (match fold.1 with
        | [] => let (u', st') := EncState.allocFresh b fold.2
                let st'' := EncState.addClause b st' [SAT.Lit.pos (FVar.toVar b u')]
                (u', st'')
        | u0 :: us => let res := us.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0, fold.2)
                (res.1, res.2)).2.nextFresh by exact h
    cases hf : fold.1 with
    | nil =>
      -- Empty case: fold.1 = []
      simp only [EncState.allocFresh, EncState.addClause]
      exact Nat.lt_succ_self _
    | cons u0 us =>
      -- Non-empty case: fold.1 = u0 :: us
      simp only []
      cases hus : us with
      | nil =>
        -- Singleton case: fold.1 = [u0]
        simp only [List.foldl_nil]
        -- u0.id < fold.2.nextFresh
        have hSingletonList : fold.1 = [u0] := by simp only [hf, hus]
        have hLenOne : tuples.length = 1 := by
          have : fold.1.length = tuples.length := hLen
          simp only [hSingletonList, List.length_singleton] at this
          exact this.symm
        obtain ⟨tuple, hTuples⟩ := List.length_eq_one_iff.mp hLenOne
        have hFoldEqTuple : fold = tuples.foldl (diamondStep b learners φ w) ([], st) := hFoldEq
        rw [hTuples] at hFoldEqTuple
        simp only [List.foldl_cons, List.foldl_nil] at hFoldEqTuple
        -- Now fold = diamondStep b learners φ w ([], st) tuple
        -- Extract u0's id from the diamondStep result
        have hu0Eq : u0 = (encodeTupleControl b learners tuple
            ((diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).1.map
              fun u => FVar.toVar b u.1)
            (diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).2).1 := by
          have hFold1 : fold.1 = (diamondStep b learners φ w ([], st) tuple).1 := by
            simp only [hFoldEqTuple]
          rw [hSingletonList, diamondStep_nil_fst_eq] at hFold1
          simp only [List.cons.injEq, and_true] at hFold1
          exact hFold1
        have hFold2Eq : fold.2 = (diamondStep b learners φ w ([], st) tuple).2 := by
          simp only [hFoldEqTuple]
        -- The control var id = witnessFold.2.nextFresh and
        -- fold.2.nextFresh = witnessFold.2.nextFresh + 1
        have hId := encodeTupleControl_fst_id b learners tuple
          ((diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).1.map
            fun u => FVar.toVar b u.1)
          (diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).2
        have hNext := encodeTupleControl_nextFresh' b learners tuple
          ((diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).1.map
            fun u => FVar.toVar b u.1)
          (diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).2
        rw [hu0Eq, hId, hFold2Eq]
        simp only [diamondStep]
        rw [hNext]
        exact Nat.lt_succ_self _
      | cons v vs =>
        -- Multiple case: fold.1 = u0 :: v :: vs
        -- result.id = fold.2.nextFresh + (v :: vs).length - 1
        -- final.nextFresh = fold.2.nextFresh + (v :: vs).length
        have hPos : 0 < (v :: vs).length := by simp
        have hResultId := mkAndIff_fold_fst_id_pos b u0 (v :: vs) fold.2 hPos
        have hFinalNext := mkAndIff_fold_nextFresh_eq b u0 (v :: vs) fold.2
        rw [hResultId, hFinalNext]
        simp only [List.length_cons]
        omega

/- ## Helper lemmas for encodeFormula_preserves_wf

   Each constructor case is split into its own lemma to improve modularity and
   reduce context complexity for tactics like omega. -/

/-- Bot case: allocFresh + addClause [neg u] preserves WF. -/
lemma encodeFormula_bot_preserves_wf (b : Bounds S) (w : WId b) (st : EncState b)
    (hwf : EncState.WellFormed st) :
    EncState.WellFormed (encodeFormula b Formula.bot w st).2 := by
  simp only [encodeFormula]
  have hAllocWF := EncState.allocFresh_wf hwf
  have hC : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1)]
      (EncState.allocFresh b st).2.nextFresh := by
    intro lit hLit
    simp only [List.mem_singleton] at hLit
    subst hLit
    simp only [litFreshBelow]
    exact Nat.lt_succ_self _
  exact EncState.addClause_wf hAllocWF _ hC

/-- Eq case: allocFresh + addClause [pos/neg u] preserves WF. -/
lemma encodeFormula_eq_preserves_wf (b : Bounds S) (v1 v2 : S.Value) (w : WId b) (st : EncState b)
    (hwf : EncState.WellFormed st) :
    EncState.WellFormed (encodeFormula b (Formula.eq v1 v2) w st).2 := by
  simp only [encodeFormula]
  have hAllocWF := EncState.allocFresh_wf hwf
  have hC : ∀ clause, clause = [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)] ∨
      clause = [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1)] →
      clauseFreshBelow clause (EncState.allocFresh b st).2.nextFresh := by
    intro clause hClause lit hLit
    rcases hClause with rfl | rfl <;> (
      simp only [List.mem_singleton] at hLit
      subst hLit
      simp only [litFreshBelow]
      exact Nat.lt_succ_self _)
  split
  · exact EncState.addClause_wf hAllocWF _ (hC _ (Or.inl rfl))
  · exact EncState.addClause_wf hAllocWF _ (hC _ (Or.inr rfl))

/-- Seq case: allocFresh + 2 addClauses preserves WF. -/
lemma encodeFormula_seq_preserves_wf (b : Bounds S) (w : WId b) (st : EncState b)
    (hwf : EncState.WellFormed st) :
    EncState.WellFormed (encodeFormula b Formula.seq w st).2 := by
  simp only [encodeFormula]
  -- Name intermediate states explicitly
  let stAlloc := (EncState.allocFresh b st).2
  let u := (EncState.allocFresh b st).1
  have hAllocWF := EncState.allocFresh_wf hwf
  have hAllocNext : stAlloc.nextFresh = st.nextFresh + 1 := EncState.allocFresh_nextFresh b st
  -- Clause 1: [neg u, pos Seq]
  let clause1 := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)]
  have hC1 : clauseFreshBelow clause1 stAlloc.nextFresh := by
    intro lit hLit
    simp only [clause1, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h =>
      subst h
      simp only [litFreshBelow]
      simp only [u, stAlloc, hAllocNext]
      exact Nat.lt_succ_self _
    | inr h => subst h; simp only [litFreshBelow]; trivial
  have hWF1 := EncState.addClause_wf hAllocWF clause1 hC1
  -- Clause 2: [neg Seq, pos u]
  let clause2 := [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)]
  have hC2 : clauseFreshBelow clause2 (EncState.addClause b stAlloc clause1).nextFresh := by
    intro lit hLit
    simp only [clause2, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    simp only [EncState.addClause_nextFresh]
    cases hLit with
    | inl h => subst h; simp only [litFreshBelow]; trivial
    | inr h =>
      subst h
      simp only [litFreshBelow]
      simp only [u, stAlloc, hAllocNext]
      exact Nat.lt_succ_self _
  exact EncState.addClause_wf hWF1 clause2 hC2

/-- Predicate case: mkBigOrIff + optional PreEq/Pred folds preserves WF. -/
lemma encodeFormula_predicate_preserves_wf (b : Bounds S) (atom : PredicateAtom S)
    (w : WId b) (st : EncState b) (hwf : EncState.WellFormed st) :
    EncState.WellFormed (encodeFormula b (Formula.predicate atom) w st).2 := by
  simp only [encodeFormula]
  let idxs := predIxList b ⟨atom.sym, atom.args⟩
  let literals := idxs.map fun k => Var.Pred w.p w.ti k
  have hLitsNonFresh : ∀ v ∈ literals, ∀ n, v = Var.Fresh n → n < st.nextFresh := by
    intro v hv n hEq; simp only [literals, List.mem_map] at hv
    obtain ⟨_, _, rfl⟩ := hv; cases hEq
  have hMkBigOrIffWF := mkBigOrIff_wf b literals st hwf hLitsNonFresh
  split
  · exact hMkBigOrIffWF
  · -- Non-empty idxs case: folds with non-Fresh vars preserve WF
    let st1 := (mkBigOrIff b literals st).2
    let st2 := addPreEqFrom b w.ti st1
    have hSt2WF := addPreEqFrom_wf b w.ti st1 hMkBigOrIffWF
    have hSt3WF := addPreEqReflAll_wf b st2 hSt2WF
    let st3 := addPreEqReflAll b st2
    -- One nested fold adding backward and forward clauses
    -- These clauses only contain PreEq and Pred vars (not Fresh), so WF is preserved
    let mkPairClauses (H' : b.times) (k : b.predIx) : SAT.Clause (Var b) × SAT.Clause (Var b) :=
      ([SAT.Lit.neg (Var.PreEq w.ti H'), SAT.Lit.neg (Var.Pred w.p H' k),
        SAT.Lit.pos (Var.Pred w.p w.ti k)],
       [SAT.Lit.neg (Var.PreEq w.ti H'), SAT.Lit.neg (Var.Pred w.p w.ti k),
        SAT.Lit.pos (Var.Pred w.p H' k)])
    have hPairClauseNonFresh : ∀ H' k,
        clauseFreshBelow (mkPairClauses H' k).1 st3.nextFresh ∧
        clauseFreshBelow (mkPairClauses H' k).2 st3.nextFresh := by
      intro H' k
      constructor <;> (
        intro lit hLit
        simp only [mkPairClauses, List.mem_cons, List.mem_nil_iff, or_false] at hLit
        rcases hLit with rfl | rfl | rfl <;> simp only [litFreshBelow] <;> trivial)
    have hSt4WF : ((Bounds.timesL b).foldl (fun stCur H' =>
        idxs.foldl (fun stAcc k =>
          EncState.addClause b (EncState.addClause b stAcc (mkPairClauses H' k).1)
            (mkPairClauses H' k).2) stCur) st3).WellFormed :=
      nested_foldl_addClause_pair_nonFresh_wf b (Bounds.timesL b) idxs st3
        mkPairClauses hSt3WF (fun H' k => hPairClauseNonFresh H' k)
    exact hSt4WF

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- encodeFormulaEvent preserves well-formedness. -/
lemma encodeFormulaEvent_wf (b : Bounds S) (w : WId b) (evt : Signature.EventType S)
    (st : EncState b) (hwf : st.WellFormed) :
    (encodeFormulaEvent b w evt st).2.WellFormed := by
  simp only [encodeFormulaEvent]
  have hNonFresh := eventWitnessPairs_nonFresh b w evt
  have hFoldWF := eventWitnessStep_foldl_wf b (eventWitnessPairs b w evt) ([], st) hwf hNonFresh
  apply mkBigOrIff_wf
  · exact hFoldWF
  · -- Need: all v in witnessVars satisfy: if v = Fresh n then n < st1.nextFresh
    intro v hv n hEq
    exact eventWitnessStep_foldl_vars_fresh_below b
      (eventWitnessPairs b w evt) st hNonFresh v hv n hEq

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Event case (guard fails): allocFresh + addClause [neg u] preserves WF. -/
lemma encodeFormula_event_fail_preserves_wf (b : Bounds S) (_w : WId b) (st : EncState b)
    (hwf : EncState.WellFormed st) :
    EncState.WellFormed (EncState.addClause b (EncState.allocFresh b st).2
        [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1)]) := by
  have hAllocWF := EncState.allocFresh_wf hwf
  have hC : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1)]
      (EncState.allocFresh b st).2.nextFresh := by
    intro lit hLit
    simp only [List.mem_singleton] at hLit
    subst hLit
    simp only [litFreshBelow, EncState.allocFresh]
    exact Nat.lt_succ_self _
  exact EncState.addClause_wf hAllocWF _ hC

/-- Event case: handles all event subcases. -/
lemma encodeFormula_event_preserves_wf (b : Bounds S) (atom : EventAtom S)
    (w : WId b) (st : EncState b) (hwf : EncState.WellFormed st) :
    EncState.WellFormed (encodeFormula b (Formula.event atom) w st).2 := by
  simp only [encodeFormula]
  split
  · rename_i e _
    split
    · -- e = evt: encodeFormulaEvent case
      exact encodeFormulaEvent_wf b w ⟨atom.sym, atom.args⟩ st hwf
    · -- e ≠ evt: guard fails
      exact encodeFormula_event_fail_preserves_wf b w st hwf
  · -- MaybeEvent.none: guard fails
    exact encodeFormula_event_fail_preserves_wf b w st hwf

/-- Imp case: two recursive calls + allocFresh + 3 addClauses preserves WF. -/
lemma encodeFormula_imp_preserves_wf (b : Bounds S) (φ1 φ2 : Formula S) (w : WId b)
    (st : EncState b) (hwf : EncState.WellFormed st)
    (ih1 : ∀ w' st', st'.WellFormed → (encodeFormula b φ1 w' st').2.WellFormed)
    (ih2 : ∀ w' st', st'.WellFormed → (encodeFormula b φ2 w' st').2.WellFormed) :
    EncState.WellFormed (encodeFormula b (Formula.imp φ1 φ2) w st).2 := by
  simp only [encodeFormula]
  -- Name all intermediate states explicitly
  let st1 := (encodeFormula b φ1 w st).2
  let u1 := (encodeFormula b φ1 w st).1
  let st2 := (encodeFormula b φ2 w st1).2
  let u2 := (encodeFormula b φ2 w st1).1
  let stAlloc := (EncState.allocFresh b st2).2
  let u := (EncState.allocFresh b st2).1
  have hWF1 := ih1 w st hwf
  have hWF2 := ih2 w st1 hWF1
  have hAllocWF := EncState.allocFresh_wf hWF2
  have hUId : u.id = st2.nextFresh := by simp only [u, EncState.allocFresh]
  have hAllocNext : stAlloc.nextFresh = st2.nextFresh + 1 := EncState.allocFresh_nextFresh b st2
  have hU1Lt := encodeFormula_controlVar_lt_nextFresh b φ1 w st
  have hU2Lt := encodeFormula_controlVar_lt_nextFresh b φ2 w st1
  have hMono1 := encodeFormula_nextFresh_mono b φ1 w st
  have hMono2 := encodeFormula_nextFresh_mono b φ2 w st1
  -- Clause 1: [pos u1, pos u]
  let clause1 := [SAT.Lit.pos (FVar.toVar b u1), SAT.Lit.pos (FVar.toVar b u)]
  have hC1 : clauseFreshBelow clause1 stAlloc.nextFresh := by
    intro lit hLit
    simp only [clause1, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h =>
      subst h
      simp only [litFreshBelow, FVar.toVar]
      simp only [u1, stAlloc, hAllocNext, st2, st1]
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hU1Lt hMono2) (Nat.le_succ _)
    | inr h =>
      subst h
      simp only [litFreshBelow, FVar.toVar, hUId]
      simp only [stAlloc, hAllocNext]
      exact Nat.lt_succ_self _
  have hWF3 := EncState.addClause_wf hAllocWF clause1 hC1
  -- Clause 2: [neg u2, pos u]
  let clause2 := [SAT.Lit.neg (FVar.toVar b u2), SAT.Lit.pos (FVar.toVar b u)]
  have hC2 : clauseFreshBelow clause2 (EncState.addClause b stAlloc clause1).nextFresh := by
    intro lit hLit
    simp only [clause2, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    simp only [EncState.addClause_nextFresh]
    cases hLit with
    | inl h =>
      subst h
      simp only [litFreshBelow, FVar.toVar]
      simp only [u2, stAlloc, hAllocNext, st2]
      exact Nat.lt_of_lt_of_le hU2Lt (Nat.le_succ _)
    | inr h =>
      subst h
      simp only [litFreshBelow, FVar.toVar, hUId]
      simp only [stAlloc, hAllocNext]
      exact Nat.lt_succ_self _
  have hWF4 := EncState.addClause_wf hWF3 clause2 hC2
  -- Clause 3: [neg u, neg u1, pos u2]
  let clause3 := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b u1),
                  SAT.Lit.pos (FVar.toVar b u2)]
  have hC3 : clauseFreshBelow clause3
      (EncState.addClause b (EncState.addClause b stAlloc clause1) clause2).nextFresh := by
    intro lit hLit
    simp only [clause3, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    simp only [EncState.addClause_nextFresh]
    rcases hLit with h | h | h
    · subst h
      simp only [litFreshBelow, FVar.toVar, hUId]
      simp only [stAlloc, hAllocNext]
      exact Nat.lt_succ_self _
    · subst h
      simp only [litFreshBelow, FVar.toVar]
      simp only [u1, stAlloc, hAllocNext, st2, st1]
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hU1Lt hMono2) (Nat.le_succ _)
    · subst h
      simp only [litFreshBelow, FVar.toVar]
      simp only [u2, stAlloc, hAllocNext, st2]
      exact Nat.lt_of_lt_of_le hU2Lt (Nat.le_succ _)
  exact EncState.addClause_wf hWF4 clause3 hC3

/-- AtEnd case: recursive call + allocFresh + 2 addClauses preserves WF. -/
lemma encodeFormula_atEnd_preserves_wf (b : Bounds S) (φ : Formula S) (w : WId b)
    (st : EncState b) (hwf : EncState.WellFormed st)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    EncState.WellFormed (encodeFormula b (Formula.atEnd φ) w st).2 := by
  simp only [encodeFormula]
  let wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
  -- Name intermediate states explicitly
  let st1 := (encodeFormula b φ wEnd st).2
  let u' := (encodeFormula b φ wEnd st).1
  let stAlloc := (EncState.allocFresh b st1).2
  let u := (EncState.allocFresh b st1).1
  have hWF1 := ih wEnd st hwf
  have hAllocWF := EncState.allocFresh_wf hWF1
  have hUId : u.id = st1.nextFresh := by simp only [u, EncState.allocFresh]
  have hAllocNext : stAlloc.nextFresh = st1.nextFresh + 1 := EncState.allocFresh_nextFresh b st1
  have hU'Lt := encodeFormula_controlVar_lt_nextFresh b φ wEnd st
  -- Clause 1: [neg u, pos u']
  let clause1 := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b u')]
  have hC1 : clauseFreshBelow clause1 stAlloc.nextFresh := by
    intro lit hLit
    simp only [clause1, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h =>
      subst h
      simp only [litFreshBelow, FVar.toVar, hUId]
      simp only [stAlloc, hAllocNext]
      exact Nat.lt_succ_self _
    | inr h =>
      subst h
      simp only [litFreshBelow, FVar.toVar]
      simp only [u', stAlloc, hAllocNext, st1]
      exact Nat.lt_of_lt_of_le hU'Lt (Nat.le_succ _)
  have hWF2 := EncState.addClause_wf hAllocWF clause1 hC1
  -- Clause 2: [neg u', pos u]
  let clause2 := [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b u)]
  have hC2 : clauseFreshBelow clause2 (EncState.addClause b stAlloc clause1).nextFresh := by
    intro lit hLit
    simp only [clause2, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    simp only [EncState.addClause_nextFresh]
    cases hLit with
    | inl h =>
      subst h
      simp only [litFreshBelow, FVar.toVar]
      simp only [u', stAlloc, hAllocNext, st1]
      exact Nat.lt_of_lt_of_le hU'Lt (Nat.le_succ _)
    | inr h =>
      subst h
      simp only [litFreshBelow, FVar.toVar, hUId]
      simp only [stAlloc, hAllocNext]
      exact Nat.lt_succ_self _
  exact EncState.addClause_wf hWF2 clause2 hC2

/-- Helper: encodeWitnesses fold preserves WF - generalized for any initial accumulator. -/
lemma encodeWitnesses_foldl_wf_aux (b : Bounds S) (φ : Formula S) (witnesses : List (WId b))
    (acc : List (FVar b) × EncState b) (hwf : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) acc).2.WellFormed := by
  induction witnesses generalizing acc with
  | nil =>
    simp only [List.foldl_nil]
    exact hwf
  | cons w' ws ihWs =>
    simp only [List.foldl_cons]
    have hWF' := ih w' acc.2 hwf
    let acc' := (acc.1 ++ [(encodeFormula b φ w' acc.2).1], (encodeFormula b φ w' acc.2).2)
    exact ihWs acc' hWF'

/-- Helper: encodeWitnesses fold preserves WF. -/
lemma encodeWitnesses_foldl_wf (b : Bounds S) (φ : Formula S) (witnesses : List (WId b))
    (st : EncState b) (hwf : st.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) ([], st)).2.WellFormed :=
  encodeWitnesses_foldl_wf_aux b φ witnesses ([], st) hwf ih

/-- Helper: encodeWitnesses fold output vars have ids < resulting state's nextFresh. -/
lemma encodeWitnesses_foldl_vars_lt_nextFresh_aux (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (acc : List (FVar b) × EncState b)
    (hAccLt : ∀ v ∈ acc.1, v.id < acc.2.nextFresh) :
    let result := witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) acc
    ∀ v ∈ result.1, v.id < result.2.nextFresh := by
  induction witnesses generalizing acc with
  | nil =>
    simp only [List.foldl_nil]
    exact hAccLt
  | cons w' ws ih =>
    simp only [List.foldl_cons]
    apply ih
    intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    cases hv with
    | inl hOld =>
      -- v was already in acc.1, so v.id < acc.2.nextFresh
      have hVLt := hAccLt v hOld
      -- acc.2.nextFresh ≤ (encodeFormula b φ w' acc.2).2.nextFresh
      have hMono := encodeFormula_nextFresh_mono b φ w' acc.2
      exact Nat.lt_of_lt_of_le hVLt hMono
    | inr hNew =>
      -- v is the new control var from encodeFormula
      subst hNew
      exact encodeFormula_controlVar_lt_nextFresh b φ w' acc.2

/-- Helper: encodeWitnesses fold output vars have ids < resulting state's nextFresh. -/
lemma encodeWitnesses_foldl_vars_lt_nextFresh (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (st : EncState b) :
    let result := witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) ([], st)
    ∀ v ∈ result.1, v.id < result.2.nextFresh := by
  apply encodeWitnesses_foldl_vars_lt_nextFresh_aux
  intro v hv
  simp only [List.not_mem_nil] at hv

/-- Helper: nextFresh is monotonic through encodeWitnesses fold. -/
lemma encodeWitnesses_foldl_nextFresh_mono_aux (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (acc : List (FVar b) × EncState b) :
    acc.2.nextFresh ≤ (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) acc).2.nextFresh := by
  induction witnesses generalizing acc with
  | nil => simp only [List.foldl_nil, Nat.le_refl]
  | cons w' ws ih =>
    simp only [List.foldl_cons]
    have hStep := encodeFormula_nextFresh_mono b φ w' acc.2
    have hRest := ih (acc.1 ++ [(encodeFormula b φ w' acc.2).1], (encodeFormula b φ w' acc.2).2)
    exact Nat.le_trans hStep hRest

/-- Helper: nextFresh is monotonic through encodeWitnesses fold. -/
lemma encodeWitnesses_foldl_nextFresh_mono (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (st : EncState b) :
    st.nextFresh ≤ (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) ([], st)).2.nextFresh :=
  encodeWitnesses_foldl_nextFresh_mono_aux b φ witnesses ([], st)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- One step of auxVars fold preserves WF. -/
lemma auxVars_step_wf (b : Bounds S) (w : WId b) (u : FVar b)
    (uv : FVar b) (w' : WId b) (acc : List (FVar b) × EncState b)
    (hwf : acc.2.WellFormed)
    (hULt : u.id < acc.2.nextFresh)
    (hUvLt : uv.id < acc.2.nextFresh) :
    let memVar := Var.Mem w.ti w'
    let (aux, stCur) := EncState.allocFresh b acc.2
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
    let stCur := EncState.addClause b stCur
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
    stCur.WellFormed ∧ u.id < stCur.nextFresh ∧ uv.id < stCur.nextFresh := by
  have hAllocWF := EncState.allocFresh_wf hwf
  have hAuxId : (EncState.allocFresh b acc.2).1.id = acc.2.nextFresh := by
    simp only [EncState.allocFresh]
  have hAllocNext : (EncState.allocFresh b acc.2).2.nextFresh = acc.2.nextFresh + 1 :=
    EncState.allocFresh_nextFresh b acc.2
  -- Define clauses explicitly
  let memVar := Var.Mem w.ti w'
  let aux := (EncState.allocFresh b acc.2).1
  let st0 := (EncState.allocFresh b acc.2).2
  let c1 := [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
  let c2 := [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
  let c3 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
  let c4 := [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
  -- Clause 1: [neg Mem, neg uv, pos u]
  have hC1 : clauseFreshBelow c1 st0.nextFresh := by
    intro lit hLit
    simp only [c1, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    rcases hLit with rfl | rfl | rfl
    · simp only [litFreshBelow, memVar]; trivial  -- Mem is not Fresh
    · simp only [litFreshBelow, FVar.toVar, st0, hAllocNext]
      exact Nat.lt_of_lt_of_le hUvLt (Nat.le_succ _)
    · simp only [litFreshBelow, FVar.toVar, st0, hAllocNext]
      exact Nat.lt_of_lt_of_le hULt (Nat.le_succ _)
  let st1 := EncState.addClause b st0 c1
  have hWF1 : st1.WellFormed := EncState.addClause_wf hAllocWF c1 hC1
  have hSt1Next : st1.nextFresh = acc.2.nextFresh + 1 := by
    simp only [st1, st0, EncState.addClause_nextFresh, hAllocNext]
  -- Clause 2: [neg Mem, neg uv, pos aux]
  have hC2 : clauseFreshBelow c2 st1.nextFresh := by
    intro lit hLit
    simp only [c2, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    simp only [hSt1Next]
    rcases hLit with rfl | rfl | rfl
    · simp only [litFreshBelow, memVar]; trivial  -- Mem is not Fresh
    · simp only [litFreshBelow, FVar.toVar]
      exact Nat.lt_of_lt_of_le hUvLt (Nat.le_succ _)
    · simp only [litFreshBelow, FVar.toVar, aux, hAuxId]
      exact Nat.lt_succ_self _
  let st2 := EncState.addClause b st1 c2
  have hWF2 : st2.WellFormed := EncState.addClause_wf hWF1 c2 hC2
  have hSt2Next : st2.nextFresh = acc.2.nextFresh + 1 := by
    simp only [st2, EncState.addClause_nextFresh, hSt1Next]
  -- Clause 3: [neg aux, pos Mem]
  have hC3 : clauseFreshBelow c3 st2.nextFresh := by
    intro lit hLit
    simp only [c3, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    simp only [hSt2Next]
    rcases hLit with rfl | rfl
    · simp only [litFreshBelow, FVar.toVar, aux, hAuxId]
      exact Nat.lt_succ_self _
    · simp only [litFreshBelow, memVar]; trivial  -- Mem is not Fresh
  let st3 := EncState.addClause b st2 c3
  have hWF3 : st3.WellFormed := EncState.addClause_wf hWF2 c3 hC3
  have hSt3Next : st3.nextFresh = acc.2.nextFresh + 1 := by
    simp only [st3, EncState.addClause_nextFresh, hSt2Next]
  -- Clause 4: [neg aux, pos uv]
  have hC4 : clauseFreshBelow c4 st3.nextFresh := by
    intro lit hLit
    simp only [c4, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    simp only [hSt3Next]
    rcases hLit with rfl | rfl
    · simp only [litFreshBelow, FVar.toVar, aux, hAuxId]
      exact Nat.lt_succ_self _
    · simp only [litFreshBelow, FVar.toVar]
      exact Nat.lt_of_lt_of_le hUvLt (Nat.le_succ _)
  let st4 := EncState.addClause b st3 c4
  have hWF4 : st4.WellFormed := EncState.addClause_wf hWF3 c4 hC4
  have hSt4Next : st4.nextFresh = acc.2.nextFresh + 1 := by
    simp only [st4, EncState.addClause_nextFresh, hSt3Next]
  -- Goal uses let-expanded version matching st4
  refine ⟨hWF4, ?_, ?_⟩ <;> simp only [EncState.addClause_nextFresh]
  · exact Nat.lt_of_lt_of_le hULt (Nat.le_succ _)
  · exact Nat.lt_of_lt_of_le hUvLt (Nat.le_succ _)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: auxVars fold preserves WF - generalized version. -/
lemma auxVars_foldl_wf_aux (b : Bounds S) (w : WId b) (u : FVar b)
    (pairs : List (FVar b × WId b)) (acc : List (FVar b) × EncState b)
    (hwf : acc.2.WellFormed)
    (hULt : u.id < acc.2.nextFresh)
    (hVarsLt : ∀ p ∈ pairs, p.1.id < acc.2.nextFresh) :
    (pairs.foldl (fun (auxAcc, stCur) (uv, w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) acc).2.WellFormed := by
  induction pairs generalizing acc with
  | nil =>
    simp only [List.foldl_nil]
    exact hwf
  | cons p ps ih =>
    simp only [List.foldl_cons]
    obtain ⟨uv, w'⟩ := p
    have hUvLt := hVarsLt (uv, w') List.mem_cons_self
    have ⟨hStepWF, hULt', _⟩ := auxVars_step_wf b w u uv w' acc hwf hULt hUvLt
    -- After one step, u.id and all remaining uvs have ids < new nextFresh
    -- The step produces state with nextFresh = acc.2.nextFresh + 1
    have hPsLt : ∀ q ∈ ps, q.1.id < acc.2.nextFresh + 1 := by
      intro q hq
      have hqLt := hVarsLt q (List.mem_cons_of_mem (uv, w') hq)
      exact Nat.lt_of_lt_of_le hqLt (Nat.le_succ _)
    exact ih _ hStepWF hULt' hPsLt

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: auxVars fold preserves WF. -/
lemma auxVars_foldl_wf (b : Bounds S) (w : WId b) (u : FVar b)
    (witnessVars : List (FVar b)) (witnesses : List (WId b))
    (st : EncState b) (hwf : st.WellFormed)
    (hULt : u.id < st.nextFresh)
    (hVarsLt : ∀ v ∈ witnessVars, ∀ n, FVar.toVar b v = Var.Fresh n → n < st.nextFresh) :
    ((witnessVars.zip witnesses).foldl (fun (auxAcc, stCur) (uv, w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv),
          SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv),
          SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) ([], st)).2.WellFormed := by
  apply auxVars_foldl_wf_aux b w u (witnessVars.zip witnesses) ([], st) hwf hULt
  intro p hp
  have ⟨hpFst, _⟩ := List.of_mem_zip hp
  have hVLt := hVarsLt p.1 hpFst p.1.id (by simp [FVar.toVar])
  exact hVLt

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: auxVars fold is monotonic w.r.t. nextFresh - generalized. -/
lemma auxVars_foldl_nextFresh_mono_aux (b : Bounds S) (w : WId b) (u : FVar b)
    (pairs : List (FVar b × WId b)) (acc : List (FVar b) × EncState b) :
    acc.2.nextFresh ≤ (pairs.foldl (fun (auxAcc, stCur) (uv, w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) acc).2.nextFresh := by
  induction pairs generalizing acc with
  | nil => simp only [List.foldl_nil, Nat.le_refl]
  | cons p ps ih =>
    simp only [List.foldl_cons]
    -- After one step (allocFresh + 4 addClause), nextFresh = acc.2.nextFresh + 1
    -- Set up the intermediate state after processing one element
    let memVar := Var.Mem w.ti p.2
    let allocResult := EncState.allocFresh b acc.2
    let aux := allocResult.1
    let st0 := allocResult.2
    let st1 := EncState.addClause b st0
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b u)]
    let st2 := EncState.addClause b st1
      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b p.1), SAT.Lit.pos (FVar.toVar b aux)]
    let st3 := EncState.addClause b st2
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
    let stCur := EncState.addClause b st3
      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b p.1)]
    let acc' : List (FVar b) × EncState b := (acc.1 ++ [aux], stCur)
    -- nextFresh after one step
    have hNextFresh : acc'.2.nextFresh = acc.2.nextFresh + 1 := by
      simp only [acc', stCur, st3, st2, st1, st0, allocResult,
                 EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]
    -- Apply IH to get acc'.2.nextFresh ≤ final
    have hIH := ih acc'
    -- Goal: acc.2.nextFresh ≤ final
    -- We have: acc.2.nextFresh < acc'.2.nextFresh (since +1), and acc'.2.nextFresh ≤ final
    calc acc.2.nextFresh ≤ acc.2.nextFresh + 1 := Nat.le_succ _
      _ = acc'.2.nextFresh := hNextFresh.symm
      _ ≤ _ := hIH

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: auxVars fold is monotonic w.r.t. nextFresh. -/
lemma auxVars_foldl_nextFresh_mono (b : Bounds S) (w : WId b) (u : FVar b)
    (witnessVars : List (FVar b)) (witnesses : List (WId b)) (st : EncState b) :
    st.nextFresh ≤ ((witnessVars.zip witnesses).foldl (fun (auxAcc, stCur) (uv, w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) ([], st)).2.nextFresh :=
  auxVars_foldl_nextFresh_mono_aux b w u (witnessVars.zip witnesses) ([], st)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: auxVars fold result vars have ids < resulting state's nextFresh - generalized. -/
lemma auxVars_foldl_result_lt_nextFresh_aux (b : Bounds S) (w : WId b) (u : FVar b)
    (pairs : List (FVar b × WId b)) (acc : List (FVar b) × EncState b)
    (hAccLt : ∀ v ∈ acc.1, v.id < acc.2.nextFresh) :
    let result := pairs.foldl (fun (auxAcc, stCur) (uv, w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) acc
    ∀ v ∈ result.1, v.id < result.2.nextFresh := by
  induction pairs generalizing acc with
  | nil =>
    simp only [List.foldl_nil]
    exact hAccLt
  | cons p ps ih =>
    simp only [List.foldl_cons]
    apply ih
    intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    -- After one step, nextFresh = acc.2.nextFresh + 1
    cases hv with
    | inl hOld =>
      have hVLt := hAccLt v hOld
      -- Result state nextFresh = acc.2.nextFresh + 1
      simp only [EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]
      exact Nat.lt_of_lt_of_le hVLt (Nat.le_succ _)
    | inr hNew =>
      subst hNew
      simp only [EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]
      exact Nat.lt_succ_self _

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: auxVars fold result vars have ids < resulting state's nextFresh. -/
lemma auxVars_foldl_result_lt_nextFresh (b : Bounds S) (w : WId b) (u : FVar b)
    (witnessVars : List (FVar b)) (witnesses : List (WId b)) (st : EncState b)
    (aux : FVar b)
    (hMem : aux ∈ ((witnessVars.zip witnesses).foldl (fun (auxAcc, stCur) (uv, w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) ([], st)).1) :
    aux.id < ((witnessVars.zip witnesses).foldl (fun (auxAcc, stCur) (uv, w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) ([], st)).2.nextFresh := by
  have h := auxVars_foldl_result_lt_nextFresh_aux b w u (witnessVars.zip witnesses) ([], st)
    (by intro v hv; simp only [List.not_mem_nil] at hv)
  exact h aux hMem

/-- Past case: complex nested folds. -/
lemma encodeFormula_past_preserves_wf (b : Bounds S) (φ : Formula S) (w : WId b)
    (st : EncState b) (hwf : EncState.WellFormed st)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    EncState.WellFormed (encodeFormula b (Formula.past φ) w st).2 := by
  simp only [encodeFormula]
  -- Step 1: allocFresh for u
  have hAllocWF := EncState.allocFresh_wf hwf
  have hAllocNext := EncState.allocFresh_nextFresh b st
  have hUId : (EncState.allocFresh b st).1.id = st.nextFresh := by simp [EncState.allocFresh]
  let u := (EncState.allocFresh b st).1
  let st1 := (EncState.allocFresh b st).2
  let witnesses := (WId.allWorlds b).filterMap fun w' => if w'.p = w.p then some w' else none
  -- Step 2: encodeWitnesses fold preserves WF
  have hSt2WF := encodeWitnesses_foldl_wf b φ witnesses st1 hAllocWF ih
  let foldResult := witnesses.foldl (fun (uvars, stCur) w' =>
      let (u', stNext) := encodeFormula b φ w' stCur
      (uvars ++ [u'], stNext)) ([], st1)
  let witnessVars := foldResult.1
  let st2 := foldResult.2
  -- witnessVars have ids < st2.nextFresh
  have hWitnessLt := encodeWitnesses_foldl_vars_lt_nextFresh b φ witnesses st1
  -- u.id = st.nextFresh < st1.nextFresh ≤ st2.nextFresh
  have hSt1Le : st1.nextFresh ≤ st2.nextFresh :=
    encodeWitnesses_foldl_nextFresh_mono b φ witnesses st1
  have hULtSt2 : u.id < st2.nextFresh := by
    simp only [u, hUId]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hSt1Le
  -- Step 3: auxVars fold
  have hVarsLt : ∀ v ∈ witnessVars, ∀ n, FVar.toVar b v = Var.Fresh n → n < st2.nextFresh := by
    intro v hv n hEq
    simp only [FVar.toVar] at hEq
    have hVLt := hWitnessLt v hv
    simp only [] at hVLt
    cases hEq; exact hVLt
  have hSt3WF := auxVars_foldl_wf b w u witnessVars witnesses st2 hSt2WF hULtSt2 hVarsLt
  let auxFoldResult := (witnessVars.zip witnesses).foldl (fun (auxAcc, stCur) (uv, w') =>
      let memVar := Var.Mem w.ti w'
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (auxAcc ++ [aux], stCur)) ([], st2)
  let auxVars := auxFoldResult.1
  let st3 := auxFoldResult.2
  -- Step 4: final addClause [¬u] ++ auxVars.map pos
  -- Need: clauseFreshBelow ([neg u] ++ auxVars.map pos) st3.nextFresh
  -- u.id < st2.nextFresh ≤ st3.nextFresh (monotonic fold)
  -- auxVars are from allocFresh during the fold, so their ids < st3.nextFresh
  have hC4 : clauseFreshBelow ([SAT.Lit.neg (FVar.toVar b u)] ++
      auxVars.map fun aux => SAT.Lit.pos (FVar.toVar b aux)) st3.nextFresh := by
    intro lit hLit
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map] at hLit
    cases hLit with
    | inl hU =>
      subst hU
      simp only [litFreshBelow, FVar.toVar]
      -- u.id < st2.nextFresh ≤ st3.nextFresh
      have hSt3Mono := auxVars_foldl_nextFresh_mono b w u witnessVars witnesses st2
      exact Nat.lt_of_lt_of_le hULtSt2 hSt3Mono
    | inr hAux =>
      obtain ⟨aux, hAuxMem, rfl⟩ := hAux
      simp only [litFreshBelow, FVar.toVar]
      -- aux was allocated during auxVars fold, so aux.id < st3.nextFresh
      exact auxVars_foldl_result_lt_nextFresh b w u witnessVars witnesses st2 aux hAuxMem
  exact EncState.addClause_wf hSt3WF _ hC4

/-- Helper: forall encoding fold preserves WF - generalized. -/
lemma forall_encodeConj_foldl_wf_aux (b : Bounds S) (body : S.Value → Formula S) (w : WId b)
    (valIndices : List b.valIx) (acc : List (FVar b) × EncState b)
    (hwf : acc.2.WellFormed)
    (ih : ∀ v w' st', st'.WellFormed → (encodeFormula b (body v) w' st').2.WellFormed) :
    (valIndices.foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        have hNonempty : Nonempty S.Value := ⟨v⟩
        have _hDepth : depth (body v) < depth (.forall body) := by
          open Classical in
          simp only [depth, hNonempty, ↓reduceDIte]
          rw [depth_uniform body v (choice hNonempty)]; omega
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)) acc).2.WellFormed := by
  induction valIndices generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hwf
  | cons vIdx vs ihVs =>
    simp only [List.foldl_cons]
    have hWF' := ih (b.values.get vIdx) w acc.2 hwf
    exact ihVs _ hWF'

/-- Helper: forall encoding fold preserves WF. -/
lemma forall_encodeConj_foldl_wf (b : Bounds S) (body : S.Value → Formula S) (w : WId b)
    (st : EncState b) (hwf : st.WellFormed)
    (ih : ∀ v w' st', st'.WellFormed → (encodeFormula b (body v) w' st').2.WellFormed) :
    ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        have hNonempty : Nonempty S.Value := ⟨v⟩
        have _hDepth : depth (body v) < depth (.forall body) := by
          open Classical in
          simp only [depth, hNonempty, ↓reduceDIte]
          rw [depth_uniform body v (choice hNonempty)]; omega
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)) ([], st)).2.WellFormed :=
  forall_encodeConj_foldl_wf_aux b body w (List.finRange b.nVals) ([], st) hwf ih

/-- Helper: forall encoding fold output vars have ids < resulting state's nextFresh. -/
lemma forall_encodeConj_foldl_vars_lt_nextFresh_aux (b : Bounds S) (body : S.Value → Formula S)
    (w : WId b) (valIndices : List b.valIx) (acc : List (FVar b) × EncState b)
    (hAccLt : ∀ v ∈ acc.1, v.id < acc.2.nextFresh) :
    let result := valIndices.foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        have hNonempty : Nonempty S.Value := ⟨v⟩
        have _hDepth : depth (body v) < depth (.forall body) := by
          open Classical in
          simp only [depth, hNonempty, ↓reduceDIte]
          rw [depth_uniform body v (choice hNonempty)]; omega
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)) acc
    ∀ v ∈ result.1, v.id < result.2.nextFresh := by
  induction valIndices generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hAccLt
  | cons vIdx vs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    cases hv with
    | inl hOld =>
      have hVLt := hAccLt v hOld
      exact Nat.lt_of_lt_of_le hVLt (encodeFormula_nextFresh_mono b (body _) w acc.2)
    | inr hNew =>
      subst hNew
      exact encodeFormula_controlVar_lt_nextFresh b (body _) w acc.2

/-- Helper: forall encoding fold output vars have ids < resulting state's nextFresh. -/
lemma forall_encodeConj_foldl_vars_lt_nextFresh (b : Bounds S) (body : S.Value → Formula S)
    (w : WId b) (st : EncState b) :
    let result := (List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        have hNonempty : Nonempty S.Value := ⟨v⟩
        have _hDepth : depth (body v) < depth (.forall body) := by
          open Classical in
          simp only [depth, hNonempty, ↓reduceDIte]
          rw [depth_uniform body v (choice hNonempty)]; omega
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)) ([], st)
    ∀ v ∈ result.1, v.id < result.2.nextFresh := by
  apply forall_encodeConj_foldl_vars_lt_nextFresh_aux
  intro v hv; simp only [List.not_mem_nil] at hv

/-- Helper: forall encoding fold is monotonic w.r.t. nextFresh. -/
lemma forall_encodeConj_foldl_nextFresh_mono_aux (b : Bounds S) (body : S.Value → Formula S)
    (w : WId b) (valIndices : List b.valIx) (acc : List (FVar b) × EncState b) :
    acc.2.nextFresh ≤ (valIndices.foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        have hNonempty : Nonempty S.Value := ⟨v⟩
        have _hDepth : depth (body v) < depth (.forall body) := by
          open Classical in
          simp only [depth, hNonempty, ↓reduceDIte]
          rw [depth_uniform body v (choice hNonempty)]; omega
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)) acc).2.nextFresh := by
  induction valIndices generalizing acc with
  | nil => simp only [List.foldl_nil, Nat.le_refl]
  | cons vIdx vs ih =>
    simp only [List.foldl_cons]
    let v := b.values.get vIdx
    let result := encodeFormula b (body v) w acc.2
    let newAcc : List (FVar b) × EncState b := (acc.1 ++ [result.1], result.2)
    have hStep : acc.2.nextFresh ≤ newAcc.2.nextFresh :=
      encodeFormula_nextFresh_mono b (body v) w acc.2
    exact Nat.le_trans hStep (ih newAcc)

/-- Helper: forall encoding fold is monotonic w.r.t. nextFresh. -/
lemma forall_encodeConj_foldl_nextFresh_mono (b : Bounds S) (body : S.Value → Formula S)
    (w : WId b) (st : EncState b) :
    st.nextFresh ≤ ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
        let v := b.values.get vIdx
        have hNonempty : Nonempty S.Value := ⟨v⟩
        have _hDepth : depth (body v) < depth (.forall body) := by
          open Classical in
          simp only [depth, hNonempty, ↓reduceDIte]
          rw [depth_uniform body v (choice hNonempty)]; omega
        let (uBody, stNext) := encodeFormula b (body v) w stCur
        (vars ++ [uBody], stNext)) ([], st)).2.nextFresh :=
  forall_encodeConj_foldl_nextFresh_mono_aux b body w (List.finRange b.nVals) ([], st)

/-- Forall case: fold over values. -/
lemma encodeFormula_forall_preserves_wf (b : Bounds S) (body : S.Value → Formula S) (w : WId b)
    (st : EncState b) (hwf : EncState.WellFormed st)
    (ih : ∀ v w' st', st'.WellFormed → (encodeFormula b (body v) w' st').2.WellFormed) :
    EncState.WellFormed (encodeFormula b (Formula.forall body) w st).2 := by
  simp only [encodeFormula]
  -- Step 1: allocFresh for u
  have hAllocWF := EncState.allocFresh_wf hwf
  have hAllocNext := EncState.allocFresh_nextFresh b st
  have hUId : (EncState.allocFresh b st).1.id = st.nextFresh := by simp [EncState.allocFresh]
  let u := (EncState.allocFresh b st).1
  let st1 := (EncState.allocFresh b st).2
  -- Step 2: encodeConj fold
  have hSt2WF := forall_encodeConj_foldl_wf b body w st1 hAllocWF ih
  let foldResult := (List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
      let v := b.values.get vIdx
      have hNonempty : Nonempty S.Value := ⟨v⟩
      have _hDepth : depth (body v) < depth (.forall body) := by
        open Classical in
        simp only [depth, hNonempty, ↓reduceDIte]
        rw [depth_uniform body v (choice hNonempty)]; omega
      let (uBody, stNext) := encodeFormula b (body v) w stCur
      (vars ++ [uBody], stNext)) ([], st1)
  let bodyVars := foldResult.1
  let st2 := foldResult.2
  -- bodyVars have ids < st2.nextFresh
  have hBodyVarsLt := forall_encodeConj_foldl_vars_lt_nextFresh b body w st1
  -- u.id < st2.nextFresh
  have hSt2Mono : st1.nextFresh ≤ st2.nextFresh :=
    forall_encodeConj_foldl_nextFresh_mono b body w st1
  have hULtSt2 : u.id < st2.nextFresh := by
    simp only [u, hUId]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hSt2Mono
  -- Step 3: forward clauses [¬u, uᵢ]
  have hSt3WF : (bodyVars.foldl (fun stCur uBody =>
      EncState.addClause b stCur [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
      st2).WellFormed := by
    have hClauseFB : ∀ uBody ∈ bodyVars,
        clauseFreshBelow [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]
          st2.nextFresh := by
      intro uBody hMem lit hLit
      simp only [] at hMem
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      cases hLit with
      | inl h =>
        subst h
        simp only [litFreshBelow, FVar.toVar]; exact hULtSt2
      | inr h =>
        subst h
        simp only [litFreshBelow, FVar.toVar]
        exact hBodyVarsLt uBody hMem
    exact (foldl_addClause_wf_mem bodyVars st2
      (fun uBody => [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)])
      hSt2WF hClauseFB).1
  let st3 := bodyVars.foldl (fun stCur uBody =>
    EncState.addClause b stCur [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]) st2
  have hSt3Next : st3.nextFresh = st2.nextFresh := by
    simp only [st3]
    exact foldl_nextFresh_eq b bodyVars st2 _ (fun s _ => EncState.addClause_nextFresh b s _)
  -- Step 4: final clause [¬u₁, ..., ¬uₙ, u]
  have hC4 : clauseFreshBelow (bodyVars.map (fun uBody => SAT.Lit.neg (FVar.toVar b uBody))
      ++ [SAT.Lit.pos (FVar.toVar b u)]) st3.nextFresh := by
    intro lit hLit
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl hBody =>
      obtain ⟨uBody, hMem, rfl⟩ := hBody
      simp only [litFreshBelow, FVar.toVar, hSt3Next]
      simp only [bodyVars, foldResult] at hMem
      exact hBodyVarsLt uBody hMem
    | inr hU =>
      subst hU
      simp only [litFreshBelow, FVar.toVar, hSt3Next]; exact hULtSt2
  exact EncState.addClause_wf hSt3WF _ hC4

/-- Helper: the inner witness fold for diamond encoding preserves WF - generalized. -/
lemma diamond_witnessFold_wf_aux (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (parts : List b.participants)
    (acc : List (FVar b × b.participants) × EncState b) (hwf : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    (parts.foldl (fun acc' p =>
      if _ : p ∈ intersection then
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
        (acc'.1 ++ [(uWit, p)], stNew)
      else acc') acc).2.WellFormed := by
  induction parts generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hwf
  | cons p ps ihPs =>
    simp only [List.foldl_cons]
    split_ifs with hp
    · have hStep := ih ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2 hwf
      exact ihPs _ hStep
    · exact ihPs acc hwf

/-- Helper: the inner witness fold for diamond encoding preserves WF. -/
lemma diamond_witnessFold_wf (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (st : EncState b) (hwf : st.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    ((Bounds.partsL b).foldl (fun acc p =>
      if _ : p ∈ intersection then
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let (uWit, stNew) := encodeFormula b φ wEnd acc.2
        (acc.1 ++ [(uWit, p)], stNew)
      else acc) ([], st)).2.WellFormed :=
  diamond_witnessFold_wf_aux b φ w intersection (Bounds.partsL b) ([], st) hwf ih

/-- Helper: witness vars from diamond inner fold have Fresh ids
    < resulting state's nextFresh - aux. -/
lemma diamond_witnessFold_vars_lt_nextFresh_aux (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (parts : List b.participants)
    (acc : List (FVar b × b.participants) × EncState b)
    (hAccLt : ∀ v ∈ acc.1, v.1.id < acc.2.nextFresh) :
    let result := parts.foldl (fun acc' p =>
      if _ : p ∈ intersection then
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
        (acc'.1 ++ [(uWit, p)], stNew)
      else acc') acc
    ∀ v ∈ result.1, v.1.id < result.2.nextFresh := by
  induction parts generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hAccLt
  | cons p ps ihPs =>
    simp only [List.foldl_cons]
    split_ifs with hp
    · apply ihPs
      intro v hv
      simp only [List.mem_append, List.mem_singleton] at hv
      cases hv with
      | inl hOld =>
        have hVLt := hAccLt v hOld
        exact Nat.lt_of_lt_of_le hVLt (encodeFormula_nextFresh_mono b φ _ acc.2)
      | inr hNew =>
        cases hNew
        exact encodeFormula_controlVar_lt_nextFresh b φ _ acc.2
    · exact ihPs acc hAccLt

/-- Helper: witness vars from diamond inner fold have Fresh ids < resulting state's nextFresh. -/
lemma diamond_witnessFold_vars_lt_nextFresh (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (st : EncState b) :
    let result := (Bounds.partsL b).foldl (fun acc p =>
      if _ : p ∈ intersection then
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let (uWit, stNew) := encodeFormula b φ wEnd acc.2
        (acc.1 ++ [(uWit, p)], stNew)
      else acc) ([], st)
    ∀ v ∈ result.1, v.1.id < result.2.nextFresh := by
  apply diamond_witnessFold_vars_lt_nextFresh_aux
  intro v hv; simp only [List.not_mem_nil] at hv

/-- Helper: diamond outer fold step (one tuple) preserves WF. -/
lemma diamond_step_wf (b : Bounds S) (learners : List S.Value) (φ : Formula S) (w : WId b)
    (acc : List (FVar b) × EncState b) (tuple : List (Finset b.participants))
    (hwf : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
    let witnessFold := (Bounds.partsL b).foldl (fun acc' p =>
      if _ : p ∈ intersection then
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
        (acc'.1 ++ [(uWit, p)], stNew)
      else acc') ([], acc.2)
    let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
    (encodeTupleControl b learners tuple witnessVars witnessFold.2).2.WellFormed := by
  intro intersection witnessFold witnessVars
  have hWFFold := diamond_witnessFold_wf b φ w intersection acc.2 hwf ih
  have hVarsLt := diamond_witnessFold_vars_lt_nextFresh b φ w intersection acc.2
  -- Need to show witnessVars are "safe" for encodeTupleControl
  have hWitnessSafe : ∀ v ∈ witnessVars, ∀ n, v = Var.Fresh n → n < witnessFold.2.nextFresh := by
    intro v hv n hEq
    simp only [witnessVars, List.mem_map] at hv
    obtain ⟨pair, hPair, rfl⟩ := hv
    simp only [FVar.toVar] at hEq
    cases hEq
    exact hVarsLt pair hPair
  exact encodeTupleControl_wf b learners tuple witnessVars witnessFold.2 hWFFold hWitnessSafe

/-- Helper: diamond outer fold preserves WF - generalized. -/
lemma diamond_outerFold_wf_aux (b : Bounds S) (learners : List S.Value) (φ : Formula S) (w : WId b)
    (tuples : List (List (Finset b.participants)))
    (acc : List (FVar b) × EncState b) (hwf : acc.2.WellFormed)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    (tuples.foldl (fun (accVars, stCur) tuple =>
      let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
      let witnessFold := (Bounds.partsL b).foldl (fun acc' p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
          (acc'.1 ++ [(uWit, p)], stNew)
        else acc') ([], stCur)
      let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
      let (uTuple, stFinal) := encodeTupleControl b learners tuple witnessVars witnessFold.2
      (accVars ++ [uTuple], stFinal)) acc).2.WellFormed := by
  induction tuples generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hwf
  | cons tuple ts ihTs =>
    simp only [List.foldl_cons]
    have hStep := diamond_step_wf b learners φ w acc tuple hwf ih
    exact ihTs _ hStep

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: conditional foldl with pair accumulator is monotonic in nextFresh. -/
lemma foldl_nextFresh_mono_pair_cond {b : Bounds S} {α β}
    (xs : List α) (init : β × EncState b)
    (cond : α → Prop) [DecidablePred cond]
    (f : β × EncState b → α → β × EncState b)
    (hMono : ∀ acc x, cond x → acc.2.nextFresh ≤ (f acc x).2.nextFresh) :
    init.2.nextFresh ≤
      (xs.foldl (fun acc x => if cond x then f acc x else acc) init).2.nextFresh := by
  induction xs generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    split_ifs with hc
    · exact Nat.le_trans (hMono init hd hc) (ih (f init hd))
    · exact ih init

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: encodeTupleControl's control var id < final state's nextFresh. -/
lemma encodeTupleControl_controlVar_lt_nextFresh (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars : List (Var b)) (st : EncState b) :
    (encodeTupleControl b learners tuple witnessVars st).1.id <
    (encodeTupleControl b learners tuple witnessVars st).2.nextFresh := by
  rw [encodeTupleControl_fst_id, encodeTupleControl_nextFresh]
  omega

/-- Helper: diamond outer fold output vars have Fresh ids < resulting state's nextFresh - aux. -/
lemma diamond_outerFold_vars_lt_nextFresh_aux (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b) (tuples : List (List (Finset b.participants)))
    (acc : List (FVar b) × EncState b)
    (hAccLt : ∀ v ∈ acc.1, v.id < acc.2.nextFresh)
    (_ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    let result := tuples.foldl (fun (accVars, stCur) tuple =>
      let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
      let witnessFold := (Bounds.partsL b).foldl (fun acc' p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
          (acc'.1 ++ [(uWit, p)], stNew)
        else acc') ([], stCur)
      let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
      let (uTuple, stFinal) := encodeTupleControl b learners tuple witnessVars witnessFold.2
      (accVars ++ [uTuple], stFinal)) acc
    ∀ v ∈ result.1, v.id < result.2.nextFresh := by
  induction tuples generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hAccLt
  | cons tuple ts ihTs =>
    simp only [List.foldl_cons]
    apply ihTs
    intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    cases hv with
    | inl hOld =>
      have hVLt := hAccLt v hOld
      -- v.id < acc.2.nextFresh, need v.id < stFinal.nextFresh
      -- stFinal comes from encodeTupleControl which is monotonic in nextFresh
      -- First show acc.2.nextFresh ≤ witnessFold.2.nextFresh via induction
      have hMono1 : acc.2.nextFresh ≤ ((Bounds.partsL b).foldl (fun acc' p =>
          if _ : p ∈ tuple.foldl (· ∩ ·) Finset.univ then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
            (acc'.1 ++ [(uWit, p)], stNew)
          else acc') ([], acc.2)).2.nextFresh := by
        suffices h : ∀ (parts : List b.participants)
            (init : List (FVar b × b.participants) × EncState b),
            init.2.nextFresh ≤ (parts.foldl (fun acc' p =>
              if _ : p ∈ tuple.foldl (· ∩ ·) Finset.univ then
                let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
                (acc'.1 ++ [(uWit, p)], stNew)
              else acc') init).2.nextFresh by exact h (Bounds.partsL b) ([], acc.2)
        intro parts
        induction parts with
        | nil => intro init; rfl
        | cons p ps ihPs =>
          intro init
          simp only [List.foldl_cons]
          split_ifs with hp
          · let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let newInit := (init.1 ++ [((encodeFormula b φ wEnd init.2).1, p)],
                           (encodeFormula b φ wEnd init.2).2)
            exact Nat.le_trans (encodeFormula_nextFresh_mono b φ wEnd init.2) (ihPs newInit)
          · exact ihPs init
      -- Then witnessFold.2.nextFresh ≤ stFinal.nextFresh
      have hMono2 := encodeTupleControl_nextFresh_mono b learners tuple
        (((Bounds.partsL b).foldl (fun acc' p =>
          if _ : p ∈ tuple.foldl (· ∩ ·) Finset.univ then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
            (acc'.1 ++ [(uWit, p)], stNew)
          else acc') ([], acc.2)).1.map (fun u => FVar.toVar b u.1))
        ((Bounds.partsL b).foldl (fun acc' p =>
          if _ : p ∈ tuple.foldl (· ∩ ·) Finset.univ then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
            (acc'.1 ++ [(uWit, p)], stNew)
          else acc') ([], acc.2)).2
      exact Nat.lt_of_lt_of_le hVLt (Nat.le_trans hMono1 hMono2)
    | inr hNew =>
      subst hNew
      -- uTuple was allocated by encodeTupleControl, so its id < stFinal.nextFresh
      exact encodeTupleControl_controlVar_lt_nextFresh b learners tuple _ _

/-- Diamond case: diamondStep fold + mkAndIff. -/
lemma encodeFormula_diamond_preserves_wf (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b) (st : EncState b) (hwf : EncState.WellFormed st)
    (ih : ∀ w' st', st'.WellFormed → (encodeFormula b φ w' st').2.WellFormed) :
    EncState.WellFormed (encodeFormula b (Formula.diamond learners φ) w st).2 := by
  simp only [encodeFormula]
  -- Define helpers
  let getMinQs (ℓ : S.Value) : List (Finset b.participants) :=
    let vIdx := b.findValueIndex ℓ
    (Var.allMinQ b vIdx).filterMap fun v =>
      match v with
      | Var.MinQ _ Q => some Q
      | _ => none
  let quorumSets := learners.map getMinQs
  let tuples := cartesianProduct quorumSets
  -- Outer fold WF
  have hFoldWF := diamond_outerFold_wf_aux b learners φ w tuples ([], st) hwf ih
  let foldResult := tuples.foldl (fun (accVars, stCur) tuple =>
    let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
    let witnessFold := (Bounds.partsL b).foldl (fun acc p =>
      if _ : p ∈ intersection then
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let (uWit, stNew) := encodeFormula b φ wEnd acc.2
        (acc.1 ++ [(uWit, p)], stNew)
      else acc) ([], stCur)
    let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
    let (uTuple, stFinal) := encodeTupleControl b learners tuple witnessVars witnessFold.2
    (accVars ++ [uTuple], stFinal)) ([], st)
  -- Output vars have Fresh ids < final nextFresh
  have hVarsLt := diamond_outerFold_vars_lt_nextFresh_aux b learners φ w tuples ([], st)
    (by intro v hv; simp only [List.not_mem_nil] at hv) ih
  -- Final match
  match hMatch : foldResult.1 with
  | [] =>
    -- Empty tuples case: allocFresh + unit clause
    have hAllocWF := EncState.allocFresh_wf hFoldWF
    have hC : clauseFreshBelow [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b foldResult.2).1)]
        (EncState.allocFresh b foldResult.2).2.nextFresh := by
      intro lit hLit
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
      subst hLit
      simp only [litFreshBelow, FVar.toVar, EncState.allocFresh]
      exact Nat.lt_succ_self _
    exact EncState.addClause_wf hAllocWF _ hC
  | u0 :: us =>
    -- Non-empty: mkAndIff chain
    have hU0Lt : u0.id < foldResult.2.nextFresh := by
      have := hVarsLt u0 (by simp only [] at hMatch ⊢; rw [hMatch]; simp)
      simp only [] at this
      exact this
    have hChainWF : (us.foldl (fun (acc : FVar b × EncState b) u' =>
        mkAndIff b acc.1 u' acc.2) (u0, foldResult.2)).2.WellFormed := by
      -- Induction on us, tracking that acc.1.id < acc.2.nextFresh
      suffices h : ∀ (xs : List (FVar b)) (acc : FVar b × EncState b),
          acc.2.WellFormed → acc.1.id < acc.2.nextFresh →
          (∀ v ∈ xs, v.id < acc.2.nextFresh) →
          (xs.foldl (fun (acc' : FVar b × EncState b) u' =>
            mkAndIff b acc'.1 u' acc'.2) acc).2.WellFormed by
        apply h us (u0, foldResult.2) hFoldWF hU0Lt
        intro v hv
        have := hVarsLt v (by simp only [] at hMatch ⊢; rw [hMatch]; simp [hv])
        simp only [] at this
        exact this
      intro xs
      induction xs with
      | nil => intro acc hWF _ _; simp only [List.foldl_nil]; exact hWF
      | cons x xs' ihXs =>
        intro acc hWF hAccLt hXsLt
        simp only [List.foldl_cons]
        apply ihXs
        · have hXLt : x.id < acc.2.nextFresh := hXsLt x List.mem_cons_self
          exact mkAndIff_wf b acc.1 x acc.2 hWF hAccLt hXLt
        · -- New control var has id = acc.2.nextFresh
          simp only [mkAndIff, EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]
          simp only [EncState.allocFresh]
          omega
        · intro v hv
          have hVLt := hXsLt v (List.mem_cons_of_mem x hv)
          simp only [mkAndIff, EncState.addClause_nextFresh, EncState.allocFresh_nextFresh]
          omega
    exact hChainWF

/-- The encoding preserves well-formedness of the encoding state.

    If the input state st is well-formed (all Fresh vars in clauses have index < nextFresh),
    then the output state is also well-formed.

    This is essential for completeness: when we extend an assignment to set a newly
    allocated Fresh variable, we need to know it doesn't appear in prior clauses. -/
lemma encodeFormula_preserves_wf (b : Bounds S) (φ : Formula S) (w : WId b) (st : EncState b)
    (hwf : EncState.WellFormed st) :
    EncState.WellFormed (encodeFormula b φ w st).2 := by
  induction φ generalizing w st with
  | bot => exact encodeFormula_bot_preserves_wf b w st hwf
  | eq v1 v2 => exact encodeFormula_eq_preserves_wf b v1 v2 w st hwf
  | seq => exact encodeFormula_seq_preserves_wf b w st hwf
  | predicate atom => exact encodeFormula_predicate_preserves_wf b atom w st hwf
  | event atom => exact encodeFormula_event_preserves_wf b atom w st hwf
  | imp φ1 φ2 ih1 ih2 => exact encodeFormula_imp_preserves_wf b φ1 φ2 w st hwf ih1 ih2
  | atEnd φ ih => exact encodeFormula_atEnd_preserves_wf b φ w st hwf ih
  | past φ ih => exact encodeFormula_past_preserves_wf b φ w st hwf ih
  | «forall» body ih => exact encodeFormula_forall_preserves_wf b body w st hwf ih
  | diamond learners φ ih => exact encodeFormula_diamond_preserves_wf b learners φ w st hwf ih

end Encoding
