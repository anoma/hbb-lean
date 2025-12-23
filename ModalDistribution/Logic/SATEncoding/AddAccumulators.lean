import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.TseytinGadgets

/-!
# Accumulator Reasoning Lemmas

Reusable facts about the conjunction accumulator built from `addAccStep`
and the `mkMemEq`-powered variant used in the PreEq encoding.  These lemmas
are shared by multiple adequacy proofs.
-/

open ModalDistribution Encoding

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]
variable [DecidableEq S.Value]

/-! ## addAccStep Lemmas -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The AND-accumulator: if `next` is true, then both `cur` and `eqb` are true. -/
lemma addAccStep_forward
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (cur next eqb : FVar b) (st : EncState b)
    (hClauses : (addAccStep b cur next eqb st).clauses.all (SAT.Clause.eval σ) = true)
    (hNext : σ (FVar.toVar b next) = true) :
    σ (FVar.toVar b cur) = true ∧ σ (FVar.toVar b eqb) = true := by
  unfold addAccStep at hClauses
  let clause₁ :=
    [ SAT.Lit.neg (FVar.toVar b next)
    , SAT.Lit.pos (FVar.toVar b cur) ]
  let clause₂ :=
    [ SAT.Lit.neg (FVar.toVar b next)
    , SAT.Lit.pos (FVar.toVar b eqb) ]
  let clause₃ :=
    [ SAT.Lit.neg (FVar.toVar b cur)
    , SAT.Lit.neg (FVar.toVar b eqb)
    , SAT.Lit.pos (FVar.toVar b next) ]
  have hAll :
      ∀ clause ∈
          (EncState.addClause b
            (EncState.addClause b
              (EncState.addClause b st clause₁) clause₂) clause₃).clauses,
            SAT.Clause.eval σ clause = true :=
    List.all_eq_true.mp
      (by
        simpa [clause₁, clause₂, clause₃, EncState.addClause] using hClauses)
  have hClause₁ :
      SAT.Clause.eval σ clause₁ = true :=
    hAll clause₁ (by simp [EncState.addClause, clause₁, clause₂, clause₃])
  have hClause₂ :
      SAT.Clause.eval σ clause₂ = true :=
    hAll clause₂ (by simp [EncState.addClause, clause₁, clause₂, clause₃])
  have hCur : σ (FVar.toVar b cur) = true := by
    simpa [clause₁, SAT.Clause.eval, SAT.Lit.eval, List.foldl,
           hNext, Bool.not_true, Bool.false_or, Bool.or_false]
      using hClause₁
  have hEqb : σ (FVar.toVar b eqb) = true := by
    simpa [clause₂, SAT.Clause.eval, SAT.Lit.eval, List.foldl,
           hNext, Bool.not_true, Bool.false_or, Bool.or_false]
      using hClause₂
  exact ⟨hCur, hEqb⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Backward direction: if `cur` and `eqb` are true, then `next` is true. -/
lemma addAccStep_backward
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (cur next eqb : FVar b) (st : EncState b)
    (hClauses : (addAccStep b cur next eqb st).clauses.all (SAT.Clause.eval σ) = true)
    (hCur : σ (FVar.toVar b cur) = true)
    (hEqb : σ (FVar.toVar b eqb) = true) :
    σ (FVar.toVar b next) = true := by
  unfold addAccStep at hClauses
  let clause₁ :=
    [ SAT.Lit.neg (FVar.toVar b next)
    , SAT.Lit.pos (FVar.toVar b cur) ]
  let clause₂ :=
    [ SAT.Lit.neg (FVar.toVar b next)
    , SAT.Lit.pos (FVar.toVar b eqb) ]
  let clause₃ :=
    [ SAT.Lit.neg (FVar.toVar b cur)
    , SAT.Lit.neg (FVar.toVar b eqb)
    , SAT.Lit.pos (FVar.toVar b next) ]
  have hAll :
      ∀ clause ∈
          (EncState.addClause b
            (EncState.addClause b
              (EncState.addClause b st clause₁) clause₂) clause₃).clauses,
            SAT.Clause.eval σ clause = true :=
    List.all_eq_true.mp
      (by
        simpa [clause₁, clause₂, clause₃, EncState.addClause] using hClauses)
  have hClause₃ :
      SAT.Clause.eval σ clause₃ = true :=
    hAll clause₃ (by simp [EncState.addClause, clause₁, clause₂, clause₃])
  simpa [clause₃, SAT.Clause.eval, SAT.Lit.eval, List.foldl,
         hCur, hEqb, Bool.not_true, Bool.false_or, Bool.or_false,
         Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
    using hClause₃

/-! ## General AND-Accumulator Lemmas -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If the final value of an AND-accumulator is true, then all input bits were true. -/
lemma and_accumulator_all_true
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    {α : Type} (xs : List α)
    (inputBit : α → FVar b)
    (base : FVar b) (st_init : EncState b)
    (result : FVar b × EncState b)
    (hResult : result = xs.foldl
      (fun (acc : FVar b × EncState b) x =>
        let (cur, stAcc) := acc
        let eqb := inputBit x
        let (next, stAcc') := EncState.allocFresh b stAcc
        let stFinal := addAccStep b cur next eqb stAcc'
        (next, stFinal))
      (base, st_init))
    (hClauses : result.2.clauses.all (SAT.Clause.eval σ) = true)
    (hFinal : σ (FVar.toVar b result.1) = true) :
    ∀ x ∈ xs, σ (FVar.toVar b (inputBit x)) = true := by
  classical
  let step :=
    fun (acc : FVar b × EncState b) x =>
      let (cur, stAcc) := acc
      let eqb := inputBit x
      let (next, stAcc') := EncState.allocFresh b stAcc
      let stFinal := addAccStep b cur next eqb stAcc'
      (next, stFinal)
  have hResult' : result = xs.foldl step (base, st_init) := by
    simpa [step] using hResult
  clear hResult
  have aux :
      ∀ rev (xs : List α),
        xs.reverse = rev →
        ∀ (result : FVar b × EncState b),
          result = xs.foldl step (base, st_init) →
          result.2.clauses.all (SAT.Clause.eval σ) = true →
          σ (FVar.toVar b result.1) = true →
          ∀ x ∈ xs, σ (FVar.toVar b (inputBit x)) = true := by
    refine fun rev => List.recOn rev ?baseCase ?stepCase
    · intro xs hRev result hResultEq hClauses hFinal w hMem
      have hXs : xs = [] := by
        have hRev' := congrArg List.reverse hRev
        simpa [List.reverse_reverse] using hRev'
      subst hXs
      cases hMem
    · intro xLast revTail IH xs hRev result hResultEq hClauses hFinal w hw
      have hXs : xs = revTail.reverse ++ [xLast] := by
        have := congrArg List.reverse hRev
        simpa [List.reverse_reverse, List.reverse_cons] using this
      let xsInit := revTail.reverse
      have hSplit : xs = xsInit ++ [xLast] := by
        simpa [xsInit] using hXs
      have hFoldSplit :
          result = step (xsInit.foldl step (base, st_init)) xLast := by
        simpa [hSplit, List.foldl_append, step] using hResultEq
      cases hMid : xsInit.foldl step (base, st_init) with
      | mk curMid stMid =>
          have hFoldSplit' :
              result = step (curMid, stMid) xLast := by
            simpa [hMid] using hFoldSplit
          let eqbLast := inputBit xLast
          cases hAlloc : EncState.allocFresh b stMid with
          | mk nextFresh stAlloc =>
              let stFinal := addAccStep b curMid nextFresh eqbLast stAlloc
              have hResultPair : result = (nextFresh, stFinal) := by
                simpa [step, hMid, eqbLast, hAlloc, stFinal] using hFoldSplit'
              have hNextTrue :
                  σ (FVar.toVar b nextFresh) = true := by
                simpa [hResultPair] using hFinal
              have hClausesFinal :
                  (addAccStep b curMid nextFresh eqbLast stAlloc).clauses.all
                    (SAT.Clause.eval σ) = true := by
                simpa [hResultPair, stFinal] using hClauses
              obtain ⟨hCurTrue, hEqbLastTrue⟩ :=
                addAccStep_forward (b := b) (σ := σ)
                  (cur := curMid) (next := nextFresh)
                  (eqb := eqbLast) (st := stAlloc)
                  hClausesFinal hNextTrue
              have hAllocClauses :
                  stAlloc.clauses = stMid.clauses := by
                simpa [hAlloc] using
                  EncState.allocFresh_clauses_eq (b := b) (st := stMid)
              have hSubsetMid :
                  stMid.clauses ⊆ stFinal.clauses := by
                intro clause hClause
                have hClauseAlloc :
                    clause ∈ stAlloc.clauses := by
                  simpa [hAllocClauses] using hClause
                exact
                  addAccStep_clauses_subset (b := b)
                    (cur := curMid) (next := nextFresh) (eqb := eqbLast)
                    (st := stAlloc) hClauseAlloc
              have hClausesMid :
                  stMid.clauses.all (SAT.Clause.eval σ) = true := by
                have hAllFinal :
                    ∀ clause ∈ stFinal.clauses,
                      SAT.Clause.eval σ clause = true :=
                  List.all_eq_true.mp (by
                    simpa [hResultPair, stFinal] using hClauses)
                refine List.all_eq_true.mpr ?_
                intro clause hClause
                exact hAllFinal clause (hSubsetMid hClause)
              have hRevInit : xsInit.reverse = revTail := by
                simp [xsInit]
              have hIH :=
                IH xsInit hRevInit (curMid, stMid)
                  (by simpa using hMid.symm) hClausesMid hCurTrue
              have hMemSplit :
                  w ∈ xsInit ++ [xLast] := by
                simpa [hSplit] using hw
              have hCases := List.mem_append.mp hMemSplit
              cases hCases with
              | inl hPrefix =>
                  exact hIH w hPrefix
              | inr hLast =>
                  have hEq : w = xLast := by
                    simpa [List.mem_singleton] using hLast
                  subst hEq
                  simpa [eqbLast] using hEqbLastTrue
  exact
    aux xs.reverse xs
      (by simp)
      result hResult' hClauses hFinal

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Backward propagation: if the final accumulator variable is true, the initial base is true. -/
lemma and_accumulator_base_true
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    {α : Type} (xs : List α)
    (inputBit : α → FVar b)
    (base : FVar b) (st_init : EncState b)
    (result : FVar b × EncState b)
    (hResult : result = xs.foldl
      (fun (acc : FVar b × EncState b) x =>
        let (cur, stAcc) := acc
        let eqb := inputBit x
        let (next, stAcc') := EncState.allocFresh b stAcc
        let stFinal := addAccStep b cur next eqb stAcc'
        (next, stFinal))
      (base, st_init))
    (hClauses : result.2.clauses.all (SAT.Clause.eval σ) = true)
    (hFinal : σ (FVar.toVar b result.1) = true) :
    σ (FVar.toVar b base) = true := by
  classical
  let step :=
    fun (acc : FVar b × EncState b) x =>
      let (cur, stAcc) := acc
      let eqb := inputBit x
      let (next, stAcc') := EncState.allocFresh b stAcc
      let stFinal := addAccStep b cur next eqb stAcc'
      (next, stFinal)
  have hResult' : result = xs.foldl step (base, st_init) := by
    simpa [step] using hResult
  clear hResult
  have aux :
      ∀ rev (xs : List α),
        xs.reverse = rev →
        ∀ (result : FVar b × EncState b),
          result = xs.foldl step (base, st_init) →
          result.2.clauses.all (SAT.Clause.eval σ) = true →
          σ (FVar.toVar b result.1) = true →
          σ (FVar.toVar b base) = true := by
    refine fun rev => List.recOn rev ?baseCase ?stepCase
    · intro xs hRev result hResultEq _ hFinal'
      have hXs : xs = [] := by
        have hRev' := congrArg List.reverse hRev
        simpa [List.reverse_reverse] using hRev'
      subst hXs
      have hResultBase :
          result = (base, st_init) := by
        simpa [List.foldl, step] using hResultEq
      simpa [hResultBase] using hFinal'
    · intro xLast revTail IH xs hRev result hResultEq hClauses' hFinal'
      have hXs : xs = revTail.reverse ++ [xLast] := by
        have := congrArg List.reverse hRev
        simpa [List.reverse_reverse, List.reverse_cons] using this
      let xsInit := revTail.reverse
      have hSplit : xs = xsInit ++ [xLast] := by
        simpa [xsInit] using hXs
      have hFoldSplit :
          result = step (xsInit.foldl step (base, st_init)) xLast := by
        simpa [hSplit, List.foldl_append, step] using hResultEq
      cases hMid : xsInit.foldl step (base, st_init) with
      | mk curMid stMid =>
          have hFoldSplit' :
              result = step (curMid, stMid) xLast := by
            simpa [hMid] using hFoldSplit
          let eqbLast := inputBit xLast
          cases hAlloc : EncState.allocFresh b stMid with
          | mk nextFresh stAlloc =>
              let stFinal := addAccStep b curMid nextFresh eqbLast stAlloc
              have hResultPair : result = (nextFresh, stFinal) := by
                simpa [step, hMid, eqbLast, hAlloc, stFinal] using hFoldSplit'
              have hClausesFinal :
                  (addAccStep b curMid nextFresh eqbLast stAlloc).clauses.all
                    (SAT.Clause.eval σ) = true := by
                simpa [hResultPair, stFinal] using hClauses'
              obtain ⟨hCurTrue, _⟩ :=
                addAccStep_forward (b := b) (σ := σ)
                  (cur := curMid) (next := nextFresh)
                  (eqb := eqbLast) (st := stAlloc)
                  hClausesFinal (by simpa [hResultPair] using hFinal')
              have hAllocClauses :
                  stAlloc.clauses = stMid.clauses := by
                simpa [hAlloc] using
                  EncState.allocFresh_clauses_eq (b := b) (st := stMid)
              have hSubsetMid :
                  stMid.clauses ⊆ stFinal.clauses := by
                intro clause hClause
                have hClauseAlloc :
                    clause ∈ stAlloc.clauses := by
                  simpa [hAllocClauses] using hClause
                exact
                  addAccStep_clauses_subset (b := b)
                    (cur := curMid) (next := nextFresh) (eqb := eqbLast)
                    (st := stAlloc) hClauseAlloc
              have hClausesMid :
                  stMid.clauses.all (SAT.Clause.eval σ) = true := by
                have hAllFinal :
                    ∀ clause ∈ stFinal.clauses,
                      SAT.Clause.eval σ clause = true :=
                  List.all_eq_true.mp (by
                    simpa [hResultPair, stFinal] using hClauses')
                refine List.all_eq_true.mpr ?_
                intro clause hClause
                exact hAllFinal clause (hSubsetMid hClause)
              exact
                IH xsInit
                  (by
                    have := congrArg List.reverse hRev
                    simp [xsInit])
                  (curMid, stMid)
                  (by simpa [step] using hMid.symm)
                  hClausesMid hCurTrue
  exact
    aux xs.reverse xs
      (by simp)
      result hResult' hClauses hFinal


/-! ## mkMemEq-Specific Accumulator Lemma -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- For the mkMemEq-based AND accumulator, a true final accumulator implies
    every witness generated along the fold is also true. -/
lemma and_accumulator_final_implies_all
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (ti ti' : b.times)
    (ws : List (WId b)) (base : FVar b) (st_init : EncState b)
    (result : FVar b × EncState b)
    (hResult : result = ws.foldl
      (fun (acc : FVar b × EncState b) w =>
        let (cur, stAcc) := acc
        let (eqb, stAcc') := mkMemEq b ti ti' w stAcc
        let (next, stAcc'') := EncState.allocFresh b stAcc'
        let stFinal := addAccStep b cur next eqb stAcc''
        (next, stFinal))
      (base, st_init))
    (hClauses : result.2.clauses.all (SAT.Clause.eval σ) = true)
    (hFinal : σ (FVar.toVar b result.1) = true) :
    ∀ w ∈ ws,
      ∃ (pre suf : List (WId b)) (eqb : FVar b) (stEqb : EncState b),
        ws = pre ++ w :: suf ∧
        (eqb, stEqb) =
          mkMemEq b ti ti' w
            ((pre.foldl
              (fun (acc : FVar b × EncState b) w =>
                let (cur, stAcc) := acc
                let (eqb, stAcc') := mkMemEq b ti ti' w stAcc
                let (next, stAcc'') := EncState.allocFresh b stAcc'
                let stFinal := addAccStep b cur next eqb stAcc''
                (next, stFinal))
              (base, st_init)).2) ∧
        σ (FVar.toVar b eqb) = true := by
  classical
  let step :=
    fun (acc : FVar b × EncState b) w =>
      let (cur, stAcc) := acc
      let (eqb, stAcc') := mkMemEq b ti ti' w stAcc
      let (next, stAcc'') := EncState.allocFresh b stAcc'
      let stFinal := addAccStep b cur next eqb stAcc''
      (next, stFinal)
  have hResult' : result = ws.foldl step (base, st_init) := by
    simpa [step] using hResult
  have aux :
      ∀ rev (xs : List (WId b)),
        xs.reverse = rev →
        ∀ (result : FVar b × EncState b),
          result = xs.foldl step (base, st_init) →
          result.2.clauses.all (SAT.Clause.eval σ) = true →
          σ (FVar.toVar b result.1) = true →
          ∀ w ∈ xs,
            ∃ (pre suf : List (WId b)) (eqb : FVar b) (stEqb : EncState b),
              xs = pre ++ w :: suf ∧
              (eqb, stEqb) =
                  mkMemEq b ti ti' w
                    ((pre.foldl
                      (fun (acc : FVar b × EncState b) w =>
                        let (cur, stAcc) := acc
                        let (eqb, stAcc') := mkMemEq b ti ti' w stAcc
                        let (next, stAcc'') := EncState.allocFresh b stAcc'
                        let stFinal := addAccStep b cur next eqb stAcc''
                        (next, stFinal))
                      (base, st_init)).2) ∧
                σ (FVar.toVar b eqb) = true := by
    refine fun rev => List.recOn rev ?baseCase ?stepCase
    · intro xs hRev result hResultEq hClauses hFinal w hw
      have hXs : xs = [] := by
        have hRev' := congrArg List.reverse hRev
        simpa [List.reverse_reverse] using hRev'
      subst hXs
      cases hw
    · intro wLast revTail IH xs hRev result hResultEq hClauses hFinal w hw
      have hXs : xs = revTail.reverse ++ [wLast] := by
        have := congrArg List.reverse hRev
        simpa [List.reverse_reverse, List.reverse_cons] using this
      let xsInit := revTail.reverse
      have hSplit : xs = xsInit ++ [wLast] := by
        simpa [xsInit] using hXs
      have hFoldSplit :
          result = step (xsInit.foldl step (base, st_init)) wLast := by
        simpa [hSplit, List.foldl_append, step] using hResultEq
      cases hMid : xsInit.foldl step (base, st_init) with
      | mk curMid stMid =>
          have hFoldSplit' :
              result = step (curMid, stMid) wLast := by
            simpa [hMid] using hFoldSplit
          cases hMk : mkMemEq b ti ti' wLast stMid with
          | mk eqbLast stEqbLast =>
              cases hAlloc : EncState.allocFresh b stEqbLast with
              | mk nextFresh stAlloc =>
                  let stFinal := addAccStep b curMid nextFresh eqbLast stAlloc
                  have hResultPair : result = (nextFresh, stFinal) := by
                    simpa [step, hMid, hMk, hAlloc, stFinal] using hFoldSplit'
                  have hNextTrue :
                      σ (FVar.toVar b nextFresh) = true := by
                    simpa [hResultPair] using hFinal
                  have hClausesFinal :
                      (addAccStep b curMid nextFresh eqbLast stAlloc).clauses.all
                        (SAT.Clause.eval σ) = true := by
                    simpa [hResultPair, stFinal] using hClauses
                  obtain ⟨hCurTrue, hEqbLastTrue⟩ :=
                    addAccStep_forward (b := b) (σ := σ)
                      (cur := curMid) (next := nextFresh)
                      (eqb := eqbLast) (st := stAlloc)
                      hClausesFinal hNextTrue
                  have hSubsetMid :
                      stMid.clauses ⊆ stFinal.clauses := by
                    have hSubsetMk :
                        stMid.clauses ⊆ stEqbLast.clauses := by
                      simpa [hMk] using
                        mkMemEq_clauses_subset (b := b) (H := ti) (H' := ti')
                          (w := wLast) (st := stMid)
                    have hAllocClauses :
                        stAlloc.clauses = stEqbLast.clauses := by
                      simpa [hAlloc] using
                        EncState.allocFresh_clauses_eq
                          (b := b) (st := stEqbLast)
                    have hSubsetAlloc :
                        stEqbLast.clauses ⊆ stAlloc.clauses := by
                      intro clause hClause
                      simpa [hAllocClauses] using hClause
                    have hSubsetAdd :=
                      addAccStep_clauses_subset (b := b) (cur := curMid)
                        (next := nextFresh) (eqb := eqbLast) (st := stAlloc)
                    exact hSubsetMk.trans (hSubsetAlloc.trans hSubsetAdd)
                  have hClausesMid :
                      stMid.clauses.all (SAT.Clause.eval σ) = true := by
                    have hAllResult :
                        ∀ clause ∈ stFinal.clauses,
                          SAT.Clause.eval σ clause = true :=
                      List.all_eq_true.mp (by
                        simpa [hResultPair, stFinal] using hClauses)
                    refine List.all_eq_true.mpr ?_
                    intro clause hClause
                    exact hAllResult clause (hSubsetMid hClause)
                  have hRevInit : xsInit.reverse = revTail := by
                    simp [xsInit]
                  have hIH :
                      ∀ w ∈ xsInit,
                        ∃ (pre suf : List (WId b)) (eqb : FVar b)
                            (stEqb : EncState b),
                          xsInit = pre ++ w :: suf ∧
                            (eqb, stEqb) =
                              mkMemEq b ti ti' w
                                ((pre.foldl
                                  (fun (acc : FVar b × EncState b) w =>
                                    let (cur, stAcc) := acc
                                    let (eqb, stAcc') := mkMemEq b ti ti' w stAcc
                                    let (next, stAcc'') := EncState.allocFresh b stAcc'
                                    let stFinal :=
                                      addAccStep b cur next eqb stAcc''
                                    (next, stFinal))
                                  (base, st_init)).2) ∧
                            σ (FVar.toVar b eqb) = true :=
                    IH xsInit hRevInit (curMid, stMid)
                      (by simpa [step] using hMid.symm)
                      hClausesMid hCurTrue
                  have hMemSplit :
                      w ∈ xsInit ++ [wLast] := by
                    simpa [hSplit] using hw
                  have hCases := List.mem_append.mp hMemSplit
                  cases hCases with
                  | inl hPrefix =>
                      obtain ⟨pre, suf, eqb, stEqb, hSplitPre, hMkPre, hTruePre⟩ :=
                        hIH w hPrefix
                      refine ⟨pre, suf ++ [wLast], eqb, stEqb, ?_, hMkPre, hTruePre⟩
                      simp [hSplit, hSplitPre, List.append_assoc]
                  | inr hLast =>
                      have hEq : w = wLast := by
                        simpa [List.mem_singleton] using hLast
                      subst hEq
                      refine ⟨xsInit, [], eqbLast, stEqbLast, ?_, ?_, hEqbLastTrue⟩
                      · simp [hSplit]
                      · simpa [step, hMid] using hMk.symm
  exact
    aux ws.reverse ws
      (by simp)
      result hResult' hClauses hFinal

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
lemma addAccStep_clauses_length_le
    (b : Bounds S) (cur next eqb : FVar b) (st : EncState b) :
    st.clauses.length ≤ (addAccStep b cur next eqb st).clauses.length := by
  unfold addAccStep
  simp only
  set_option linter.style.longLine false in
  have h1 := EncState.addClause_length_le b st
    [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)]
  set_option linter.style.longLine false in
  have h2 := EncState.addClause_length_le b
    (EncState.addClause b st
      [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)])
    [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)]
  set_option linter.style.longLine false in
  have h3 := EncState.addClause_length_le b
    (EncState.addClause b
      (EncState.addClause b st
        [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)])
      [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)])
    [SAT.Lit.neg (FVar.toVar b cur), SAT.Lit.neg (FVar.toVar b eqb),
     SAT.Lit.pos (FVar.toVar b next)]
  apply Nat.le_trans h1
  apply Nat.le_trans h2
  exact h3

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
def addAccStep_clauses (b : Bounds S) (cur next eqb : FVar b) : List (SAT.Clause (Var b)) :=
  [ [SAT.Lit.neg (FVar.toVar b cur), SAT.Lit.neg (FVar.toVar b eqb),
      SAT.Lit.pos (FVar.toVar b next)]
  , [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)]
  , [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)] ]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma addAccStep_clauses_eq_append (b : Bounds S)
    (cur next eqb : FVar b) (st : EncState b) :
    (addAccStep b cur next eqb st).clauses =
      addAccStep_clauses b cur next eqb ++ st.clauses := by
  classical
  unfold addAccStep addAccStep_clauses
  simp [EncState.addClause, List.cons_append]

end Encoding
