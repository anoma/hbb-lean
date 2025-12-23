import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.WFViews
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.Adequacy.HereditaryTransitivity

/-!
# WF Extraction

Extract well-formedness proof from CNF evaluation.
-/

open ModalDistribution Encoding

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Extract well-formedness proof from CNF evaluation.
    If the combined CNF is satisfied, then WF holds. -/
lemma wf_from_eval (b : Bounds S) (σ : SAT.Assignment (Var b))
    (h : (cnfWellFormed b).eval σ = true) :
    WF b σ :=
  h  -- WF is defined as cnfWellFormed.eval σ = true

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Extract that cnfReach is satisfied from WF. -/
lemma cnfReach_from_wf (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) :
    (cnfReach b).eval σ = true := by
  -- Extract cnfReach using the extraction lemma
  have ⟨_, hReach, _, _, _, _, _, _, _, _, _⟩ := (cnfWellFormed_eval_iff b σ).mp hWF
  exact hReach

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The base clause of cnfReach: ReachT(root) is always true. -/
lemma reachT_root (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) :
    σ (Var.ReachT b.root) = true := by
  -- From hWF, extract that cnfReach is satisfied
  have hReach := cnfReach_from_wf b σ hWF
  -- cnfReach includes base clause [ReachT(root)]
  unfold cnfReach at hReach
  -- Extract that the unit clause [Lit.pos (Var.ReachT b.root)] is satisfied
  set baseClause := [SAT.Lit.pos (Var.ReachT b.root)]
  set hornClauses :=
    (Bounds.timesL b).flatMap fun H =>
      (WId.allWorlds b).map fun w =>
        [SAT.Lit.neg (Var.ReachT H),
         SAT.Lit.neg (Var.Mem H w),
         SAT.Lit.pos (Var.ReachT w.ti)]
  have hClauses :
      ∀ clause ∈ (baseClause :: hornClauses),
        SAT.Clause.eval σ clause = true := by
    have hAll :
        (baseClause :: hornClauses).all (SAT.Clause.eval σ) = true := by
      simpa [SAT.CNF.eval, baseClause, hornClauses] using hReach
    exact List.all_eq_true.mp hAll
  have hBase :
      SAT.Clause.eval σ baseClause = true :=
    hClauses baseClause (by
      simp [baseClause])
  have : σ (Var.ReachT b.root) = true := by
    simpa [baseClause, SAT.Clause.eval, SAT.Lit.eval] using hBase
  exact this

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Horn clauses propagate reachability: if ReachT(H) and Mem(H,w),
    then ReachT(w.ti) follows from the Horn clause. -/
lemma reachT_propagate (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (w : WId b)
    (hReachH : σ (Var.ReachT H) = true)
    (hMem : σ (Var.Mem H w) = true) :
    σ (Var.ReachT w.ti) = true := by
  -- Get cnfReach satisfaction
  have hReach := cnfReach_from_wf b σ hWF
  unfold cnfReach at hReach
  -- The Horn clause: ¬ReachT(H) ∨ ¬Mem(H,w) ∨ ReachT(w.ti)
  -- must be satisfied. Since the first two literals are false
  -- (their variables are true), the third must be true.
  classical
  set baseClause := [SAT.Lit.pos (Var.ReachT b.root)]
  set hornClauses :=
    (Bounds.timesL b).flatMap fun H =>
      (WId.allWorlds b).map fun w =>
        [SAT.Lit.neg (Var.ReachT H),
         SAT.Lit.neg (Var.Mem H w),
         SAT.Lit.pos (Var.ReachT w.ti)]
  have hClauses :
      ∀ clause ∈ (baseClause :: hornClauses),
        SAT.Clause.eval σ clause = true := by
    have hAll :
        (baseClause :: hornClauses).all (SAT.Clause.eval σ) = true := by
      simpa [SAT.CNF.eval, baseClause, hornClauses] using hReach
    exact List.all_eq_true.mp hAll
  have hH : H ∈ Bounds.timesL b := by
    simp [Bounds.timesL]
  have hW : w ∈ WId.allWorlds b := WId.mem_allWorlds b w
  have hClauseMem :
      [SAT.Lit.neg (Var.ReachT H),
        SAT.Lit.neg (Var.Mem H w),
        SAT.Lit.pos (Var.ReachT w.ti)] ∈ hornClauses := by
    unfold hornClauses
    refine List.mem_flatMap.2 ?_
    refine ⟨H, hH, ?_⟩
    refine List.mem_map.2 ?_
    exact ⟨w, hW, rfl⟩
  have hHornClause :
      SAT.Clause.eval σ
          [SAT.Lit.neg (Var.ReachT H),
           SAT.Lit.neg (Var.Mem H w),
           SAT.Lit.pos (Var.ReachT w.ti)] = true :=
    hClauses _
      (List.mem_cons_of_mem baseClause hClauseMem)
  have hReachTi :
      σ (Var.ReachT w.ti) = true := by
    simpa [SAT.Clause.eval, SAT.Lit.eval, hReachH, hMem] using hHornClause
  exact hReachTi

/-! ## ReachT Correspondence Lemmas

These lemmas establish the correspondence between decoded prehistories and the ReachT
variables in the SAT encoding. They are essential for adequacy proofs.
-/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: If a world with a given time prehistory appears in decodePre H,
    then there exists a world w with Mem(H, w) = true whose structural time
    field w.ti decodes to that prehistory. -/
lemma decodePre_member_witness (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ)
    (H : b.times) (p : Fin b.nParticipants)
    (e : MaybeEvent (Signature.EventType S))
    (pre : PreHistory (Fin b.nParticipants) (Signature.EventType S))
    (hMem : (p, e, pre) ∈ decodePre b σ hWF H) :
    ∃ (w : WId b),
      σ (Var.Mem H w) = true ∧
      decodePre b σ hWF w.ti = pre := by
  classical
  -- Unfold decodePre to access members
  unfold decodePre at hMem
  split at hMem
  · rename_i hFuel
    -- H has positive fuel, so world came from some w with Mem(H, w)
    simp only [PreHistory.mem_mk, List.mem_map, List.mem_attach, true_and,
      Subtype.exists, List.mem_filter] at hMem
    obtain ⟨w, ⟨_, hMemHw⟩, hDecoded⟩ := hMem
    -- The decoded world is (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti)
    have hPre : pre = decodePre b σ hWF w.ti := by
      have : (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti) = (p, e, pre) := hDecoded
      injection this with _ h_rest
      injection h_rest with _ h_third
      exact h_third.symm
    exact ⟨w, hMemHw, hPre.symm⟩
  · -- H has zero fuel, contradiction
    simp at hMem

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Worlds that appear in the decoded root prehistory have their time indices
    marked with ReachT = true.

    This is the key property for adequacy: we encoded constraints at all
    worlds that exist in the decoded model. -/
lemma reachT_for_decoded_worlds (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (w : WId b)
    (hMem : σ (Var.Mem b.root w) = true) :
    σ (Var.ReachT w.ti) = true := by
  -- Base: ReachT(root) = true
  have hReachRoot := reachT_root b σ hWF
  -- Apply the Horn clause: ReachT(root) ∧ Mem(root, w) → ReachT(w.ti)
  exact reachT_propagate b σ hWF b.root w hReachRoot hMem

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- General version: if ReachT(H) and there's a world w with Mem(H,w),
    then ReachT(w.ti).

    This handles transitive reachability through the prehistory structure. -/
lemma reachT_transitive (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (w : WId b)
    (hReachH : σ (Var.ReachT H) = true)
    (hMem : σ (Var.Mem H w) = true) :
    σ (Var.ReachT w.ti) = true := by
  exact reachT_propagate b σ hWF H w hReachH hMem

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- **World Correspondence (Recursive)**: Any prehistory reachable from a time H
    with ReachT(H) = true will have all its component time indices marked with ReachT.

    This is proven by induction on the prehistory structure, using the Horn clauses
    to propagate ReachT through membership edges. -/
lemma reachT_for_prehistory (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times)
    (hReachH : σ (Var.ReachT H) = true)
    (pre : PreHistory (Fin b.nParticipants) (Signature.EventType S))
    (hPre : pre ⪯ decodePre b σ hWF H) :
    ∀ (p : Fin b.nParticipants) (e : Signature.EventType S)
      (subpre : PreHistory (Fin b.nParticipants) (Signature.EventType S)),
      (p, MaybeEvent.some e, subpre) ∈ pre →
      (∃ (w : WId b),
        σ (Var.Mem H w) = true ∧
        decodePre b σ hWF w.ti = subpre ∧
        σ (Var.ReachT w.ti) = true) := by
  classical
  -- Extract that `cnfEdge` is satisfied under the WF assignment.
  have ⟨_, _, hEdgeEval, _, _, _, _, _, _, _, _⟩ := (cnfWellFormed_eval_iff b σ).mp hWF

  -- Helper: lift Mem facts along an Edge clause.
  have mem_of_edge_mem :
      ∀ {H H' : b.times} {w : WId b},
        σ (Var.Edge H H') = true →
        σ (Var.Mem H' w) = true →
        σ (Var.Mem H w) = true := by
    intro H₀ H₁ w hEdge hMem
    classical
    let clause :=
      [ SAT.Lit.neg (Var.Edge H₀ H₁)
      , SAT.Lit.neg (Var.Mem H₁ w)
      , SAT.Lit.pos (Var.Mem H₀ w) ]
    -- The clause above lives in the transitivity component of cnfEdge.
    have hClauseIn : clause ∈ (cnfEdge b).clauses := by
      classical
      let transitiveClauses :=
        (Bounds.timesL b).flatMap fun H =>
          (Bounds.timesL b).flatMap fun H' =>
            (WId.allWorlds b).map fun w' =>
              [ SAT.Lit.neg (Var.Edge H H')
              , SAT.Lit.neg (Var.Mem H' w')
              , SAT.Lit.pos (Var.Mem H w') ]
      have hClauseInTrans :
          clause ∈ transitiveClauses := by
        refine List.mem_flatMap.mpr ?_
        refine ⟨H₀, ?_, ?_⟩
        · simp [Bounds.timesL, List.mem_finRange]
        · refine List.mem_flatMap.mpr ?_
          refine ⟨H₁, ?_, ?_⟩
          · simp [Bounds.timesL, List.mem_finRange]
          · refine List.mem_map.mpr ?_
            exact ⟨w, WId.mem_allWorlds b w, rfl⟩
      unfold cnfEdge
      simp only []
      exact List.mem_append.mpr (Or.inr hClauseInTrans)
    -- Apply the three-literal propagation lemma to obtain Mem(H₀, w).
    have :=
      SAT.clause_three_unit (σ := σ) (cnf := cnfEdge b)
        (v1 := Var.Edge H₀ H₁) (v2 := Var.Mem H₁ w) (v3 := Var.Mem H₀ w)
        hClauseIn hEdgeEval hEdge hMem
    simpa [clause] using this

  -- Proof strategy:
  -- 1. Use decodePre_member_witness to get the world w
  -- 2. Apply reachT_transitive with H and w.ti
  -- 3. Recursively apply to subpre if needed
  intro p e subpre hMem
  -- Split on whether `pre` is exactly `decodePre H` or a strict predecessor.
  rcases hPre with hStrict | hEq
  · -- Strict case: pre ≺− decodePre H. Obtain an enclosing world at H.
    rcases hStrict with ⟨p0, e0, hParentMem⟩
    -- Decode the parent world witnessing `pre`.
    obtain ⟨w0, hMemH_w0, hDecodePre⟩ :=
      decodePre_member_witness b σ hWF H p0 e0 pre hParentMem
    -- Reachability propagates from H down to w0.ti via w0.
    have hReachTi0 :
        σ (Var.ReachT w0.ti) = true :=
      reachT_transitive b σ hWF H w0 hReachH hMemH_w0
    -- Rewrite membership in `pre` as membership in `decodePre w0.ti`.
    have hMemTi0 :
        (p, MaybeEvent.some e, subpre) ∈ decodePre b σ hWF w0.ti := by
      simpa [hDecodePre] using hMem
    -- Decode the child world witnessing `subpre`.
    obtain ⟨w1, hMemTi0_w1, hDecodeSubpre⟩ :=
      decodePre_member_witness b σ hWF w0.ti p (MaybeEvent.some e) subpre hMemTi0
    -- Reachability propagates further from w0.ti to w1.ti.
    have hReachTi1 :
        σ (Var.ReachT w1.ti) = true :=
      reachT_transitive b σ hWF w0.ti w1 hReachTi0 hMemTi0_w1
    -- Lift Mem facts along the edge from H to w0.ti.
    -- We need to show Edge(H, w0.ti) from Mem(H, w0)
    have hEdge :
        σ (Var.Edge H w0.ti) = true := by
      -- This follows from the backward clause: Mem(H, w0) → Edge(H, w0.ti)
      classical
      -- The backward clause: [¬Mem(H, w0), Edge(H, w0.ti)]
      let clause := [SAT.Lit.neg (Var.Mem H w0), SAT.Lit.pos (Var.Edge H w0.ti)]
      have hClauseIn : clause ∈ (cnfEdge b).clauses := by
        unfold cnfEdge
        -- The backward clauses are in the bwd component of cnfEdge
        let edgeClauses :=
          (Bounds.timesL b).flatMap fun H₀ =>
            (Bounds.timesL b).flatMap fun H₁ =>
              let witnesses := (WId.allWorlds b).filter (fun w' => w'.ti == H₁)
                               |>.map (Var.Mem H₀ ·)
              let fwd := SAT.Lit.neg (Var.Edge H₀ H₁) :: witnesses.map SAT.Lit.pos
              let bwd := witnesses.map fun m => [SAT.Lit.neg m, SAT.Lit.pos (Var.Edge H₀ H₁)]
              [fwd] ++ bwd
        have hInBwd : clause ∈ edgeClauses := by
          refine List.mem_flatMap.mpr ⟨H, by simp [Bounds.timesL], ?_⟩
          refine List.mem_flatMap.mpr ⟨w0.ti, by simp [Bounds.timesL], ?_⟩
          let witnesses := (WId.allWorlds b).filter (fun w' => w'.ti == w0.ti)
                           |>.map (Var.Mem H ·)
          have hW0InWitnesses : Var.Mem H w0 ∈ witnesses := by
            simp [witnesses]
            exact WId.mem_allWorlds b w0
          let bwd := witnesses.map fun m => [SAT.Lit.neg m, SAT.Lit.pos (Var.Edge H w0.ti)]
          have hInBwdList : clause ∈ bwd := by
            refine List.mem_map.mpr ?_
            exact ⟨Var.Mem H w0, hW0InWitnesses, rfl⟩
          simp only [List.mem_append]
          exact Or.inr hInBwdList
        simp only []
        exact List.mem_append.mpr (Or.inl hInBwd)
      have hClauseTrue := SAT.clause_unit_propagation σ (cnfEdge b) clause hClauseIn hEdgeEval
      unfold SAT.Clause.eval at hClauseTrue
      simp only [clause, List.foldl_cons, List.foldl_nil, SAT.Lit.eval,
        hMemH_w0, Bool.false_or] at hClauseTrue
      exact hClauseTrue
    have hMemH_w1 :
        σ (Var.Mem H w1) = true :=
      mem_of_edge_mem hEdge hMemTi0_w1
    exact ⟨w1, hMemH_w1, hDecodeSubpre, hReachTi1⟩
  · -- Equality case: pre = decodePre H
    subst hEq
    -- Decode the witnessing world directly from membership.
    obtain ⟨w, hMemH_w, hDecodeSub⟩ :=
      decodePre_member_witness b σ hWF H p (MaybeEvent.some e) subpre hMem
    -- Reachability propagates along the direct Mem edge.
    have hReachTi :
        σ (Var.ReachT w.ti) = true :=
      reachT_transitive b σ hWF H w hReachH hMemH_w
    exact ⟨w, hMemH_w, hDecodeSub, hReachTi⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Edge enforces time ordering: Edge(H, H') → H'.val < H.val.

    This follows from the acyclic constraint and Edge definition:
    - Edge(H, H') means ∃w. w.ti = H' ∧ Mem(H, w)
    - By acyclic: Mem(H, w) → w.ti.val < H.val
    - Therefore: H'.val < H.val -/
lemma edge_time_lt (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H H' : b.times)
    (hEdge : σ (Var.Edge H H') = true) :
    H'.val < H.val := by
  classical
  -- Extract the acyclicity view and cnfEdge satisfaction.
  have views := WF.views b σ hWF
  obtain ⟨_, _, hEdgeEval, _, _, _, _, _, _, _, _⟩ :=
    (cnfWellFormed_eval_iff b σ).mp hWF

  -- Edge clause witnesses a world with matching time index.
  have hWitness :
      ∃ w : WId b, w.ti = H' ∧ σ (Var.Mem H w) = true := by
    -- Forward clause: Edge(H, H') → ⋁_{w.ti = H'} Mem(H, w)
    let witnesses :=
      (WId.allWorlds b).filter (fun w => w.ti == H')
        |>.map (Var.Mem H ·)
    let clause :=
      SAT.Lit.neg (Var.Edge H H') :: witnesses.map SAT.Lit.pos
    have hClauseIn : clause ∈ (cnfEdge b).clauses := by
      unfold cnfEdge
      -- Separate edge aggregation and transitivity pieces.
      let edgeClauses :=
        (Bounds.timesL b).flatMap fun H₀ =>
          (Bounds.timesL b).flatMap fun H₁ =>
            let witnesses := (WId.allWorlds b).filter (fun w => w.ti == H₁)
                             |>.map (Var.Mem H₀ ·)
            let fwd := SAT.Lit.neg (Var.Edge H₀ H₁) :: witnesses.map SAT.Lit.pos
            let bwd := witnesses.map fun m => [SAT.Lit.neg m, SAT.Lit.pos (Var.Edge H₀ H₁)]
            [fwd] ++ bwd
      let transitiveClauses :=
        (Bounds.timesL b).flatMap fun H₀ =>
          (Bounds.timesL b).flatMap fun H₁ =>
            (WId.allWorlds b).map fun w =>
              [ SAT.Lit.neg (Var.Edge H₀ H₁),
                SAT.Lit.neg (Var.Mem H₁ w),
                SAT.Lit.pos (Var.Mem H₀ w) ]
      -- Show clause lies in the forward component of edgeClauses.
      have hInEdge : clause ∈ edgeClauses := by
        dsimp [edgeClauses]
        refine List.mem_flatMap.mpr ?_
        refine ⟨H, by simp [Bounds.timesL], ?_⟩
        refine List.mem_flatMap.mpr ?_
        refine ⟨H', by simp [Bounds.timesL], ?_⟩
        -- The clause is exactly the forward clause for (H, H').
        simp [witnesses, clause]
      have hEdgeMem :
          clause ∈ edgeClauses ++ transitiveClauses :=
        List.mem_append.mpr (Or.inl hInEdge)
      simpa [edgeClauses, transitiveClauses] using hEdgeMem

    -- The clause is satisfied, hence some witness literal must be true.
    have hClauseEval :
        SAT.Clause.eval σ clause = true :=
      SAT.clause_unit_propagation σ (cnfEdge b) clause hClauseIn hEdgeEval
    have hAny :
        clause.any (fun lit => SAT.Lit.eval σ lit) = true := by
      exact (SAT.Clause.eval_eq_any (σ := σ) (C := clause) ▸ hClauseEval)
    obtain ⟨lit, hMem, hEval⟩ := List.any_eq_true.mp hAny
    have hNe : lit ≠ SAT.Lit.neg (Var.Edge H H') := by
      intro hEq
      subst hEq
      simp [SAT.Lit.eval, hEdge] at hEval
    -- Therefore lit comes from the witness list.
    have hTail : lit ∈ witnesses.map SAT.Lit.pos := by
      have := List.mem_cons.mp hMem
      cases this with
      | inl hEq =>
          have : False := hNe hEq
          exact this.elim
      | inr hTail => exact hTail
    obtain ⟨m, hmWitness, rfl⟩ := List.mem_map.mp hTail
    have hmTrue : σ m = true := by
      simpa [SAT.Lit.eval] using hEval
    -- Unpack the witness world and its time equality.
    have : ∃ w, w ∈ (WId.allWorlds b).filter (fun w => w.ti == H') ∧
        Var.Mem H w = m := by
      simpa [witnesses] using hmWitness
    obtain ⟨w, hwFilter, rfl⟩ := this
    have hwPredicate := List.mem_filter.mp hwFilter
    have hwTi : w.ti = H' := by
      have : decide (w.ti = H') = true := by
        simpa using hwPredicate.2
      exact of_decide_eq_true this
    exact ⟨w, hwTi, hmTrue⟩
  -- Apply acyclicity to the witness world.
  obtain ⟨w, hwTi, hMem⟩ := hWitness
  have hLt := views.acyclic H w hMem
  simpa [hwTi] using hLt

end Encoding
