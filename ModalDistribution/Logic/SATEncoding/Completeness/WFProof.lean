import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf
import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction

/-!
# Well-Formedness Proof for Completeness

This file proves that `assignmentOf b M hFits` satisfies `cnfWellFormed b`.

## Main Results

- `assignmentOf_satisfies_cnfAcyclic`
- `assignmentOf_satisfies_cnfReach`
- `assignmentOf_satisfies_cnfLevel_*`
- `assignmentOf_satisfies_cnfSeq`
- etc.
- `assignmentOf_satisfies_wf`: The combined well-formedness proof

## Strategy

For each CNF component, we show that the semantic definitions used in `assignmentOf`
satisfy the corresponding constraints. The key insight is that the semantic model M
already has the required properties (hereditary transitivity, sequentiality, etc.)
and `FitsInBounds` guarantees additional bounds-related properties.

## References

- AssignmentOf.lean for the encoder construction
- Structure.lean for CNF constraint definitions
- FitsInBounds.lean for FitsInBounds structure
-/

open ModalDistribution Encoding
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Lemmas about prehistoryOfTime

These lemmas connect the semantic prehistory lookups with the encoding view. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- prehistoryOfTime at root gives the model's history. -/
lemma prehistoryOfTime_root
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    prehistoryOfTime hFits.view b.root = M.history.val := by
  unfold prehistoryOfTime
  exact prehistoryAt_root hFits.view

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- For reachable H, prehistoryOfTime gives back H. -/
lemma prehistoryOfTime_of_reachable
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    {H : PreHistory (Fin b.nParticipants) (Signature.EventType S)}
    (hReach : H ∈ reachablePreHistories M.history.val) :
    prehistoryOfTime ev (ev.timeIndexOf H) = H := by
  unfold prehistoryOfTime
  exact prehistoryAt_of_reachable ev hReach

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If prehistoryAt returns a non-empty prehistory, then the time index corresponds to
    a reachable prehistory and prehistoryAt returns exactly that prehistory. -/
lemma prehistoryAt_nonempty_implies_reachable
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (ti : b.times)
    (hNonempty : ∃ w, w ∈ prehistoryAt ev ti) :
    ∃ H ∈ reachablePreHistories M.history.val,
      ev.timeIndexOf H = ti ∧ prehistoryAt ev ti = H := by
  classical
  unfold prehistoryAt at hNonempty ⊢
  by_cases h : ∃ H ∈ reachablePreHistories M.history.val, ev.timeIndexOf H = ti
  · simp only [h, ↓reduceDIte]
    have hSpec := Classical.choose_spec h
    exact ⟨Classical.choose h, hSpec.1, hSpec.2, rfl⟩
  · simp only [h, ↓reduceDIte] at hNonempty
    obtain ⟨w, hwMem⟩ := hNonempty
    exact absurd hwMem PreHistory.not_mem_empty

/-! ## cnfAcyclic Satisfaction

The acyclic constraint: Mem(H, w) → w.ti.val < H.val

This follows from the encoding view's timeIndex_hb property which ensures
happens-before corresponds to strict ordering on time indices. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If a world is in a prehistory, its time index is strictly less.
    This follows from the encoding view's timeIndex_hb property. -/
lemma worldInPrehistory_implies_ti_lt
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (w : WId b)
    (hMem : worldInPrehistory hFits.view H w = true) :
    w.ti.val < H.val := by
  classical
  -- Extract the semantic world from worldInPrehistory
  unfold worldInPrehistory at hMem
  simp only [decide_eq_true_eq] at hMem
  obtain ⟨sem, hSemMem, _, _, hTi⟩ := hMem

  -- The prehistory at H is non-empty (contains sem)
  have hNonempty : ∃ sem', sem' ∈ prehistoryAt hFits.view H :=
    ⟨sem, hSemMem⟩

  -- Get the reachable prehistory corresponding to H
  obtain ⟨pH, hReach, hIdx, hEq⟩ := prehistoryAt_nonempty_implies_reachable hFits.view H hNonempty

  -- sem ∈ pH
  have hSemInpH : sem ∈ pH := by
    rw [← hEq]
    exact hSemMem

  -- sem.time ≺− pH (by membership in prehistory)
  have hSemTimeBefore : sem.time ≺− pH := History.happensBefore_of_mem hSemInpH

  -- sem.time is reachable (since pH is reachable and sem ∈ pH)
  have hSemTimeReach : sem.time ∈ reachablePreHistories M.history.val :=
    time_mem_reachablePreHistories_of_mem_history hReach hSemInpH

  -- Apply timeIndex_hb: happens-before gives strict ordering
  have hLt := hFits.view.timeIndex_hb hSemTimeBefore hSemTimeReach hReach

  -- w.ti = timeIndexOf sem.time and H = timeIndexOf pH
  rw [← hTi, ← hIdx]
  exact hLt

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfAcyclic.
    The acyclic constraint: Mem(H, w) → w.ti.val < H.val
    This follows from worldInPrehistory_implies_ti_lt. -/
theorem assignmentOf_satisfies_cnfAcyclic
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfAcyclic b).eval (assignmentOf b M hFits) = true := by
  -- cnfAcyclic has clauses [¬Mem(H, w)] for pairs where ¬(w.ti.val < H.val)
  -- For such pairs, we need to show Mem(H, w) evaluates to false
  -- By contrapositive of worldInPrehistory_implies_ti_lt:
  --   if ¬(w.ti.val < H.val), then worldInPrehistory = false
  unfold cnfAcyclic SAT.CNF.eval
  simp only [List.all_eq_true]
  intro clause hClause
  simp only [List.mem_flatMap, List.mem_filterMap] at hClause
  obtain ⟨H, _, w, hFM⟩ := hClause
  -- hFM : ... Option result from filterMap
  -- We need to case split on the condition w.ti.val < H.val
  split_ifs at hFM with hCond
  · -- Case: w.ti.val < H.val, clause was filtered out (none)
    simp at hFM
  · -- Case: ¬(w.ti.val < H.val), clause is [¬Mem(H, w)]
    simp only [Option.some.injEq] at hFM
    obtain ⟨_, hClauseEq⟩ := hFM
    rw [← hClauseEq]
    -- Now we need to show that the clause [¬Mem(H, w)] evaluates to true
    simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or,
               SAT.Lit.eval, Bool.not_eq_true']
    -- Need: assignmentOf b M hFits (Var.Mem H w) = false
    rw [assignmentOf_Mem]
    -- Need: worldInPrehistory hFits.view H w = false
    by_contra hWIP
    push_neg at hWIP
    simp only [Bool.not_eq_false] at hWIP
    -- hWIP : worldInPrehistory hFits.view H w = true
    have hLt := worldInPrehistory_implies_ti_lt hFits H w hWIP
    -- hLt : w.ti.val < H.val
    -- hCond : ¬(w.ti.val < H.val)
    exact hCond hLt

/-! ## cnfReach Satisfaction

Reachability constraints:
- Base: ReachT(root) = true
- Horn: ReachT(H) ∧ Mem(H, w) → ReachT(w.ti) -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The root time is reachable. -/
lemma isReachableTime_root
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    isReachableTime hFits.view b.root = true := by
  classical
  unfold isReachableTime
  simp only [decide_eq_true_eq]
  use M.history.val
  constructor
  · exact self_mem_reachablePreHistories M.history.val
  · exact hFits.view.timeIndex_root

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If Mem(H, w) = true, then the child time w.ti is reachable if H is. -/
lemma worldInPrehistory_preserves_reach
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (w : WId b)
    (_ : isReachableTime ev H = true)
    (hMem : worldInPrehistory ev H w = true) :
    isReachableTime ev w.ti = true := by
  classical
  unfold worldInPrehistory at hMem
  simp only [decide_eq_true_eq] at hMem
  obtain ⟨sem, hSemMem, _, _, hTi⟩ := hMem
  have hNonempty : ∃ sem', sem' ∈ prehistoryAt ev H := ⟨sem, hSemMem⟩
  obtain ⟨pH, hReach, _, hEq⟩ := prehistoryAt_nonempty_implies_reachable ev H hNonempty
  have hSemInpH : sem ∈ pH := by rw [← hEq]; exact hSemMem
  -- sem.time is reachable since pH is reachable
  have hSemTimeReach : sem.time ∈ reachablePreHistories M.history.val :=
    time_mem_reachablePreHistories_of_mem_history hReach hSemInpH
  simp only [isReachableTime, decide_eq_true_eq]
  exact ⟨sem.time, hSemTimeReach, hTi⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfReach. -/
theorem assignmentOf_satisfies_cnfReach
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfReach b).eval (assignmentOf b M hFits) = true := by
  -- cnfReach has base clause [ReachT(root)] and Horn clauses
  unfold cnfReach SAT.CNF.eval
  simp only [List.all_eq_true, List.mem_cons, List.mem_flatMap, List.mem_map]
  intro clause hClause
  rcases hClause with hBase | ⟨H, _, w, _, hClauseEq⟩
  · -- Base clause: [ReachT(root)]
    rw [hBase]
    simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
    rw [assignmentOf_ReachT]
    exact isReachableTime_root hFits
  · -- Horn clause: [¬ReachT(H), ¬Mem(H, w), ReachT(w.ti)]
    rw [← hClauseEq]
    simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
    rw [assignmentOf_ReachT, assignmentOf_Mem, assignmentOf_ReachT]
    by_cases hReachH : isReachableTime hFits.view H = true
    · by_cases hMem : worldInPrehistory hFits.view H w = true
      · -- Both ReachT(H) and Mem(H, w) are true, need ReachT(w.ti)
        simp only [hReachH, hMem, Bool.not_true, Bool.false_or]
        exact worldInPrehistory_preserves_reach hFits.view H w hReachH hMem
      · simp only [Bool.not_eq_true] at hMem
        simp only [hReachH, hMem, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or]
    · simp only [Bool.not_eq_true] at hReachH
      simp only [hReachH, Bool.not_false, Bool.true_or]

/-! ## cnfLevel Satisfaction

Level constraints encode fuel levels as monotone prefixes:
- cnfLevel_monotone: Level(ti, j+1) → Level(ti, j)
- cnfLevel_decrease: Mem(H, w) ∧ Level(w.ti, j) → Level(H, j+1)
- cnfLevel_max_bound: ¬Level(ti, b.nTimes)
- cnfMemRequiresFuel: Mem(H, w) → Level(H, 1) -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Level is monotone (prefix-closed). -/
lemma levelAt_monotone
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (ti : b.times) (j : Fin b.nTimes) (hj : j.succ < b.nTimes.succ) :
    levelAt ev ti ⟨j.succ, hj⟩ = true → levelAt ev ti ⟨j, Nat.lt_succ_of_lt j.isLt⟩ = true := by
  unfold levelAt
  simp only [decide_eq_true_eq]
  intro h
  -- j.succ ≤ fuelOfTime ev ti implies j ≤ fuelOfTime ev ti
  exact Nat.le_of_succ_le h

/-- Helper: height of any prehistory reachable from root is ≤ height of root. -/
lemma reachable_height_le
    {P Event : Type*}
    (root : PreHistory P Event)
    (pH : PreHistory P Event)
    (hReach : pH ∈ reachablePreHistories root) :
    PreHistory.height pH ≤ PreHistory.height root := by
  induction root using
      (PreHistory.happensBefore_wellFounded (P := P) (Event := Event)).induction
      generalizing pH with
  | _ rootVal ih =>
    unfold reachablePreHistories at hReach
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion] at hReach
    cases hReach with
    | inl hBeforeEq =>
      exact PreHistory.happensBeforeEq_height_le hBeforeEq
    | inr hInUnion =>
      obtain ⟨w', hw'Mem, hReach'⟩ := hInUnion
      have hHB : w'.time ≺− rootVal := History.happensBefore_of_mem hw'Mem
      have hFromW' := ih w'.time hHB pH hReach'
      have hW'Lt := PreHistory.height_lt_of_happensBefore hHB
      exact Nat.le_trans hFromW' (Nat.le_of_lt hW'Lt)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The height of prehistoryAt is always less than nTimes.
    This is because either:
    1. ti corresponds to a reachable prehistory, whose height ≤ root height < nTimes
    2. ti doesn't correspond to any reachable prehistory, so prehistoryAt
       returns empty (height 1) -/
lemma prehistoryAt_height_lt_nTimes
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (ti : b.times) :
    PreHistory.height (prehistoryAt hFits.view ti) < b.nTimes := by
  classical
  unfold prehistoryAt
  by_cases h : ∃ H ∈ reachablePreHistories M.history.val, hFits.view.timeIndexOf H = ti
  · -- Case: ti corresponds to a reachable prehistory
    simp only [h, ↓reduceDIte]
    have hSpec := Classical.choose_spec h
    obtain ⟨hReach, _⟩ := hSpec
    have hHeightLe := reachable_height_le M.history.val (Classical.choose h) hReach
    exact Nat.lt_of_le_of_lt hHeightLe hFits.height_bound
  · -- Case: ti doesn't correspond to any reachable prehistory
    simp only [h, ↓reduceDIte]
    -- prehistoryAt returns empty, which has height 1
    rw [PreHistory.height_empty]
    -- Need 1 < b.nTimes
    -- From height_bound: height M.history.val < nTimes
    -- Since height ≥ 1 always, we have 1 ≤ height < nTimes, so 1 < nTimes
    have hHeightGe1 : 1 ≤ PreHistory.height M.history.val := PreHistory.height_pos M.history.val
    exact Nat.lt_of_le_of_lt hHeightGe1 hFits.height_bound

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Level is bounded below nTimes. -/
lemma levelAt_max_false
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (ti : b.times) :
    levelAt hFits.view ti ⟨b.nTimes, Nat.lt_succ_self _⟩ = false := by
  unfold levelAt fuelOfTime rankPre prehistoryOfTime
  simp only [decide_eq_false_iff_not, not_le]
  -- Need: b.nTimes > height (prehistoryAt ...)
  exact prehistoryAt_height_lt_nTimes hFits ti

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfLevel_monotone. -/
theorem assignmentOf_satisfies_cnfLevel_monotone
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfLevel_monotone b).eval (assignmentOf b M hFits) = true := by
  -- cnfLevel_monotone has:
  -- 1. Base clauses [Level(ti, 0)] - satisfied since 0 ≤ any height
  -- 2. Monotone clauses [¬Level(ti, j+1), Level(ti, j)] - satisfied by levelAt_monotone
  unfold cnfLevel_monotone SAT.CNF.eval
  simp only [List.all_eq_true]
  intro clause hClause
  simp only [List.mem_flatMap, List.mem_cons, List.mem_filterMap] at hClause
  obtain ⟨ti, _, hClauseType⟩ := hClause
  rcases hClauseType with hBase | ⟨j, _, hFilterMap⟩
  · -- Base clause: [Level(ti, 0)]
    rw [hBase]
    simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
    rw [assignmentOf_Level]
    unfold levelAt
    simp only [decide_eq_true_eq]
    exact Nat.zero_le _
  · -- Monotone clause: [¬Level(ti, j+1), Level(ti, j)]
    -- hFilterMap : (if h : j < nTimes ∧ j.succ < nTimes.succ then
    --   some [...] else none) = some clause
    -- j is already bound from the rcases
    split_ifs at hFilterMap with hCond
    simp only [Option.some.injEq] at hFilterMap
    subst hFilterMap
    simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or,
               SAT.Lit.eval, Bool.or_eq_true, Bool.not_eq_true']
    rw [assignmentOf_Level, assignmentOf_Level]
    -- Either Level(ti, j+1) = false, or Level(ti, j) = true
    by_cases hLevel : levelAt hFits.view ti ⟨j.succ, hCond.2⟩ = true
    · right
      exact levelAt_monotone hFits.view ti ⟨j, hCond.1⟩ hCond.2 hLevel
    · left; simp only [Bool.not_eq_true] at hLevel ⊢; exact hLevel

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] [DecidableEq S.EventType] in
/-- If w is in prehistory H, then height(H) > height(w.ti). -/
lemma worldInPrehistory_height_lt
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (w : WId b)
    (hMem : worldInPrehistory ev H w = true) :
    fuelOfTime ev w.ti < fuelOfTime ev H := by
  classical
  unfold worldInPrehistory at hMem
  simp only [decide_eq_true_eq] at hMem
  obtain ⟨sem, hSemMem, _, _, hTi⟩ := hMem
  have hNonempty : ∃ sem', sem' ∈ prehistoryAt ev H := ⟨sem, hSemMem⟩
  obtain ⟨pH, hReach, _, hEq⟩ := prehistoryAt_nonempty_implies_reachable ev H hNonempty
  unfold fuelOfTime rankPre prehistoryOfTime
  -- pH contains sem, so height(pH) > height(sem.time)
  -- And prehistoryAt w.ti = prehistoryAt (ev.timeIndexOf sem.time) = sem.time (by reachability)
  have hSemInpH : sem ∈ pH := by rw [← hEq]; exact hSemMem
  have hSemHB : sem.time ≺− pH := History.happensBefore_of_mem hSemInpH
  have hHeightLt : PreHistory.height sem.time < PreHistory.height pH :=
    PreHistory.height_lt_of_happensBefore hSemHB
  rw [hEq]
  -- Need to show height(prehistoryAt w.ti) ≤ height(sem.time)
  -- By hTi, w.ti = timeIndexOf sem.time, so prehistoryAt w.ti = sem.time
  rw [← hTi]
  -- prehistoryAt at (timeIndexOf sem.time) = sem.time if sem.time is reachable
  -- sem.time is reachable since it's in pH which is reachable
  have hSemTimeReach : sem.time ∈ reachablePreHistories M.history.val :=
    time_mem_reachablePreHistories_of_mem_history hReach hSemInpH
  rw [prehistoryAt_of_reachable ev hSemTimeReach]
  exact hHeightLt

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] [DecidableEq S.EventType] in
/-- Fuel implication for level decrease: if fuel(w.ti) ≥ j, then fuel(H) ≥ j+1. -/
lemma worldInPrehistory_level_decrease
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (w : WId b) (j : ℕ)
    (hMem : worldInPrehistory ev H w = true)
    (hLevel : j ≤ fuelOfTime ev w.ti) :
    j.succ ≤ fuelOfTime ev H := by
  have hLt := worldInPrehistory_height_lt ev H w hMem
  omega

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- assignmentOf satisfies cnfLevel_decrease. -/
theorem assignmentOf_satisfies_cnfLevel_decrease
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfLevel_decrease b).eval (assignmentOf b M hFits) = true := by
  -- cnfLevel_decrease: [¬Mem(H, w), ¬Level(w.ti, j), Level(H, j+1)]
  unfold cnfLevel_decrease SAT.CNF.eval
  simp only [List.all_eq_true]
  intro clause hClause
  simp only [List.mem_flatMap, List.mem_filterMap] at hClause
  obtain ⟨H, _, w, _, j, _, hFM⟩ := hClause
  split_ifs at hFM with hCond
  simp only [Option.some.injEq] at hFM
  subst hFM
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or,
             SAT.Lit.eval]
  rw [assignmentOf_Mem, assignmentOf_Level, assignmentOf_Level]
  -- Either Mem = false, Level(w.ti, j) = false, or Level(H, j+1) = true
  by_cases hMem : worldInPrehistory hFits.view H w = true
  · by_cases hLevelW : levelAt hFits.view w.ti ⟨j, Nat.lt_succ_of_lt hCond.1⟩ = true
    · -- Both Mem and Level(w) are true, need Level(H, j+1) = true
      simp only [hMem, hLevelW, Bool.not_true, Bool.false_or]
      unfold levelAt at hLevelW ⊢
      simp only [decide_eq_true_eq] at hLevelW ⊢
      exact worldInPrehistory_level_decrease hFits.view H w j hMem hLevelW
    · -- Level(w.ti, j) = false
      simp only [Bool.not_eq_true] at hLevelW
      simp only [hMem, hLevelW, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or]
  · -- Mem = false
    simp only [Bool.not_eq_true] at hMem
    simp only [hMem, Bool.not_false, Bool.true_or]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfLevel_max_bound. -/
theorem assignmentOf_satisfies_cnfLevel_max_bound
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfLevel_max_bound b).eval (assignmentOf b M hFits) = true := by
  -- cnfLevel_max_bound: [¬Level(ti, b.nTimes)] for each ti
  unfold cnfLevel_max_bound SAT.CNF.eval
  simp only [List.all_eq_true, List.mem_map]
  intro clause ⟨ti, _, hClauseEq⟩
  rw [← hClauseEq]
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or,
             SAT.Lit.eval, Bool.not_eq_true']
  rw [assignmentOf_Level]
  exact levelAt_max_false hFits ti

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Level(H, 1) is always true since height ≥ 1 for any prehistory. -/
lemma levelAt_one_always_true
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) :
    levelAt ev H ⟨1, Nat.succ_lt_succ b.posTimes⟩ = true := by
  unfold levelAt fuelOfTime rankPre prehistoryOfTime
  simp only [decide_eq_true_eq]
  exact PreHistory.height_pos _

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfMemRequiresFuel. -/
theorem assignmentOf_satisfies_cnfMemRequiresFuel
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfMemRequiresFuel b).eval (assignmentOf b M hFits) = true := by
  -- cnfMemRequiresFuel: [¬Mem(H, w), Level(H, 1)] for each H, w
  unfold cnfMemRequiresFuel SAT.CNF.eval
  simp only [List.all_eq_true]
  intro clause hClause
  simp only [List.mem_flatMap, List.mem_map] at hClause
  obtain ⟨H, _, w, _, hClauseEq⟩ := hClause
  rw [← hClauseEq]
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or,
             SAT.Lit.eval, Bool.or_eq_true, Bool.not_eq_true']
  rw [assignmentOf_Level]
  -- Level(H, 1) is always true since height ≥ 1
  right
  exact levelAt_one_always_true hFits.view H

/-! ## cnfEdge Satisfaction

Edge encoding for hereditary transitivity optimization. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If a world is in a prehistory at H, then Edge(H, w.ti) is true. -/
lemma worldInPrehistory_implies_edge
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (w : WId b)
    (hMem : worldInPrehistory ev H w = true) :
    hasEdge ev H w.ti = true := by
  classical
  unfold worldInPrehistory at hMem
  simp only [decide_eq_true_eq] at hMem
  obtain ⟨sem, hSemMem, _, _, hTi⟩ := hMem
  unfold hasEdge prehistoryOfTime
  simp only [decide_eq_true_eq]
  exact ⟨sem, hSemMem, hTi⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If hasEdge ev H H' = true, there exists a WId w with w.ti = H' and
    worldInPrehistory ev H w = true. -/
lemma hasEdge_implies_exists_world
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H H' : b.times)
    (hEdge : hasEdge hFits.view H H' = true) :
    ∃ w : WId b, w.ti = H' ∧ worldInPrehistory hFits.view H w = true := by
  classical
  unfold hasEdge prehistoryOfTime at hEdge
  simp only [decide_eq_true_eq] at hEdge
  obtain ⟨sem, hSemMem, hTi⟩ := hEdge
  -- Build a WId from sem
  -- We need: p = sem.place, ei encodes sem.event, ti = H'
  let w : WId b :=
    { p := sem.place
      ei := hFits.view.evSelOf sem.event
      ti := H' }
  refine ⟨w, rfl, ?_⟩
  unfold worldInPrehistory prehistoryOfTime
  simp only [decide_eq_true_eq]
  refine ⟨sem, hSemMem, rfl, ?_, ?_⟩
  · -- b.decodeMaybeEvent w.ei = sem.event
    exact hFits.view.evSel_spec sem.event
  · -- ev.timeIndexOf sem.time = w.ti = H'
    exact hTi

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Hereditary transitivity for worldInPrehistory: if Edge(H, H') and world w is in H',
    then w is also in H. -/
lemma hereditary_worldInPrehistory
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H H' : b.times) (w : WId b)
    (hEdge : hasEdge hFits.view H H' = true)
    (hMemH' : worldInPrehistory hFits.view H' w = true) :
    worldInPrehistory hFits.view H w = true := by
  classical
  -- Extract edge: there's a world in prehistoryAt H with time index H'
  unfold hasEdge prehistoryOfTime at hEdge
  simp only [decide_eq_true_eq] at hEdge
  obtain ⟨edgeSem, hEdgeMem, hEdgeTi⟩ := hEdge

  -- Extract membership: there's a semantic world in prehistoryAt H' matching w
  unfold worldInPrehistory prehistoryOfTime at hMemH' ⊢
  simp only [decide_eq_true_eq] at hMemH' ⊢
  obtain ⟨sem, hSemMem, hPlace, hEvent, hTi⟩ := hMemH'

  -- Get the prehistory at H and H' as actual reachable prehistories
  have hNonemptyH : ∃ x, x ∈ prehistoryAt hFits.view H := ⟨edgeSem, hEdgeMem⟩
  have hNonemptyH' : ∃ x, x ∈ prehistoryAt hFits.view H' := ⟨sem, hSemMem⟩
  obtain ⟨pH, hReachH, hIdxH, hEqH⟩ :=
    prehistoryAt_nonempty_implies_reachable hFits.view H hNonemptyH
  obtain ⟨pH', hReachH', hIdxH', hEqH'⟩ :=
    prehistoryAt_nonempty_implies_reachable hFits.view H' hNonemptyH'

  -- edgeSem ∈ pH and sem ∈ pH'
  have hEdgeInpH : edgeSem ∈ pH := by rw [← hEqH]; exact hEdgeMem
  have hSemInpH' : sem ∈ pH' := by rw [← hEqH']; exact hSemMem

  -- edgeSem.time ∈ reachablePreHistories (happens-before pH)
  have hEdgeTimeReach : edgeSem.time ∈ reachablePreHistories M.history.val :=
    time_mem_reachablePreHistories_of_mem_history hReachH hEdgeInpH

  -- Key: edgeSem.time has index H' and pH' has index H'
  -- So edgeSem.time = pH' (by injectivity of timeIndexOf on reachable)
  have hEdgeTimeIdx : hFits.view.timeIndexOf edgeSem.time = H' := hEdgeTi
  have hSameIdx : hFits.view.timeIndexOf edgeSem.time = hFits.view.timeIndexOf pH' := by
    rw [hEdgeTimeIdx, hIdxH']
  have hEdgeTimeEq : edgeSem.time = pH' :=
    hFits.view.timeIndex_inj hEdgeTimeReach hReachH' hSameIdx

  -- Now sem ∈ pH' = edgeSem.time ≺− pH
  -- By hereditary transitivity: sem ∈ pH
  have hHB : edgeSem.time ≺− pH := History.happensBefore_of_mem hEdgeInpH
  rw [hEdgeTimeEq] at hHB

  -- pH is reachable from M.history.val, so it's hereditarily transitive (a History)
  let pHHist : History (Fin b.nParticipants) (Signature.EventType S) :=
    historyOfReachable hReachH

  -- Use pHHist as the ambient history to get pH' ⊆ pH
  have hSubset : pH' ⊆ pH := History.subset_of_happensBefore (H := pHHist) hHB

  -- Therefore sem ∈ pH
  have hSemInpH : sem ∈ pH := hSubset sem hSemInpH'

  -- Put sem back into prehistoryAt H
  rw [hEqH]
  exact ⟨sem, hSemInpH, hPlace, hEvent, hTi⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfEdge. -/
theorem assignmentOf_satisfies_cnfEdge
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfEdge b).eval (assignmentOf b M hFits) = true := by
  -- cnfEdge has three types of clauses:
  -- 1. Forward: Edge(H, H') → ⋁_{w | w.ti = H'} Mem(H, w)
  -- 2. Backward: Mem(H, w) → Edge(H, w.ti)
  -- 3. Transitivity: Edge(H, H') ∧ Mem(H', w) → Mem(H, w)
  unfold cnfEdge SAT.CNF.eval
  simp only [List.all_eq_true]
  intro clause hClause
  -- cnfEdge = SAT.CNF.mk (edgeClauses ++ transitiveClauses)
  -- edgeClauses: timesL.flatMap(H => timesL.flatMap(H' => [fwd] ++ bwd))
  -- transitiveClauses: timesL.flatMap(H => timesL.flatMap(H' => allWorlds.map(w => clause)))
  simp only [List.mem_append, List.mem_flatMap] at hClause
  rcases hClause with ⟨H, _, ⟨H', _, hClauseIn⟩⟩ | ⟨H, _, ⟨H', _, hClauseIn2⟩⟩
  · -- Edge clauses (forward and backward)
    simp only [List.mem_singleton, List.mem_map] at hClauseIn
    rcases hClauseIn with hFwd | ⟨m, hWitness, hBwd⟩
    · -- Forward clause: Edge(H, H') → ⋁_{w | w.ti = H'} Mem(H, w)
      -- clause = [¬Edge(H, H'), Mem(H, w₁), Mem(H, w₂), ...]
      rw [hFwd]
      -- If Edge(H, H') = false, we're done (first lit is true)
      -- If Edge(H, H') = true, need to show some Mem is true
      rw [SAT.Clause.eval_eq_any]
      rw [List.any_eq_true]
      by_cases hEdge : assignmentOf b M hFits (Var.Edge H H') = true
      · -- Edge is true, need to find a witness Mem that's true
        rw [assignmentOf_Edge] at hEdge
        obtain ⟨w, hWTi, hWMem⟩ := hasEdge_implies_exists_world hFits H H' hEdge
        -- w has w.ti = H' and worldInPrehistory H w = true
        -- So Var.Mem H w is in the witness list and evaluates to true
        have hMemTrue : assignmentOf b M hFits (Var.Mem H w) = true := by
          rw [assignmentOf_Mem]; exact hWMem
        -- Show there's a true literal in the clause
        -- Clause structure: [¬Edge, pos(Mem H w₁), pos(Mem H w₂), ...]
        -- witnesses = (allWorlds.filter (ti == H')).map (Var.Mem H)
        -- We have w with w.ti = H', so Var.Mem H w ∈ witnesses
        refine ⟨SAT.Lit.pos (Var.Mem H w), ?_, ?_⟩
        · -- Show SAT.Lit.pos (Var.Mem H w) ∈ clause
          simp only [List.mem_cons, List.mem_map, List.mem_filter, beq_iff_eq]
          right
          -- Need to show it's in witnesses.map SAT.Lit.pos
          -- witnesses = (allWorlds.filter (ti == H')).map (Var.Mem H)
          refine ⟨Var.Mem H w, ?_, rfl⟩
          -- Need to show Var.Mem H w ∈ witnesses
          refine ⟨w, ?_, rfl⟩
          exact ⟨WId.mem_allWorlds b w, hWTi⟩
        · simp only [SAT.Lit.eval]
          exact hMemTrue
      · -- Edge is false, clause is satisfied by first literal
        simp only [Bool.not_eq_true] at hEdge
        refine ⟨SAT.Lit.neg (Var.Edge H H'), List.mem_cons.mpr (Or.inl rfl), ?_⟩
        simp only [SAT.Lit.eval, hEdge, Bool.not_false]
    · -- Backward clause: Mem(H, w) → Edge(H, w.ti)
      -- clause = [¬Mem(H, w), Edge(H, w.ti)]
      rw [← hBwd]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl_cons, List.foldl_nil, Bool.false_or]
      -- m is Var.Mem H (some w with w.ti = H')
      -- hWitness : m ∈ (allWorlds.filter (w.ti == H')).map (Var.Mem H)
      simp only [List.mem_filter, beq_iff_eq] at hWitness
      -- hWitness : ∃ w, (w ∈ allWorlds ∧ w.ti = H') ∧ Var.Mem H w = m
      obtain ⟨w, ⟨hWWorld, hWTi⟩, hMEq⟩ := hWitness
      rw [← hMEq]
      -- Show: ¬assignmentOf(Var.Mem H w) ∨ assignmentOf(Var.Edge H H')
      by_cases hMem : assignmentOf b M hFits (Var.Mem H w) = true
      · -- Mem is true, need Edge to be true
        simp only [hMem, Bool.not_true, Bool.false_or]
        rw [assignmentOf_Mem] at hMem
        have hEdge := worldInPrehistory_implies_edge hFits.view H w hMem
        rw [assignmentOf_Edge, ← hWTi]
        exact hEdge
      · -- Mem is false, clause is satisfied
        simp only [hMem, Bool.not_false, Bool.true_or]
  · -- Transitivity clause: Edge(H, H') ∧ Mem(H', w) → Mem(H, w)
    -- clause = [¬Edge(H, H'), ¬Mem(H', w), Mem(H, w)]
    simp only [List.mem_map] at hClauseIn2
    obtain ⟨w, _, hClauseEq⟩ := hClauseIn2
    rw [← hClauseEq]
    simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl_cons, List.foldl_nil,
               Bool.false_or]
    -- Show: ¬Edge(H, H') ∨ ¬Mem(H', w) ∨ Mem(H, w)
    by_cases hEdge : assignmentOf b M hFits (Var.Edge H H') = true
    · -- Edge is true
      simp only [hEdge, Bool.not_true, Bool.false_or]
      by_cases hMem' : assignmentOf b M hFits (Var.Mem H' w) = true
      · -- Mem(H', w) is true, need to show Mem(H, w) is true
        simp only [hMem', Bool.not_true, Bool.false_or]
        rw [assignmentOf_Mem] at hMem' ⊢
        rw [assignmentOf_Edge] at hEdge
        exact hereditary_worldInPrehistory hFits H H' w hEdge hMem'
      · -- Mem(H', w) is false, clause satisfied
        simp only [hMem', Bool.not_false, Bool.true_or]
    · -- Edge is false, clause satisfied
      simp only [hEdge, Bool.not_false, Bool.true_or]

/-! ## cnfExists Satisfaction

Exists aggregator constraints. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If Mem(H, w) = true, then Exists(H, w.p, w.ti) = true. -/
lemma worldInPrehistory_implies_exists
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (w : WId b)
    (hMem : worldInPrehistory ev H w = true) :
    hasExists ev H w.p w.ti = true := by
  classical
  unfold worldInPrehistory at hMem
  simp only [decide_eq_true_eq] at hMem
  obtain ⟨sem, hSemMem, hPlace, _, hTi⟩ := hMem
  unfold hasExists prehistoryOfTime
  simp only [decide_eq_true_eq]
  exact ⟨sem, hSemMem, hPlace, hTi⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfExists. -/
theorem assignmentOf_satisfies_cnfExists
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfExists b).eval (assignmentOf b M hFits) = true := by
  -- cnfExists: [¬Mem(H, w), Exists(H, w.p, w.ti)]
  unfold cnfExists SAT.CNF.eval
  simp only [List.all_eq_true, List.mem_flatMap, List.mem_map]
  intro clause ⟨H, _, w, _, hClauseEq⟩
  rw [← hClauseEq]
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Mem]
  by_cases hMem : worldInPrehistory hFits.view H w = true
  · simp only [hMem, Bool.not_true, Bool.false_or]
    -- Need: assignmentOf ... (Var.Exists H w.p w.ti) = true
    change hasExists hFits.view H w.p w.ti = true
    exact worldInPrehistory_implies_exists hFits.view H w hMem
  · simp only [Bool.not_eq_true] at hMem
    simp only [hMem, Bool.not_false, Bool.true_or]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfExists_back.
    Clause structure: For each (H, p, t):
    - If no worlds match: [¬Exists(H,p,t)]
    - If worlds match: [¬Exists(H,p,t), Mem(H,w₁), Mem(H,w₂), ...]
    Completeness: If Exists(H,p,t) is true, some Mem(H,w) must be true. -/
theorem assignmentOf_satisfies_cnfExists_back
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfExists_back b).eval (assignmentOf b M hFits) = true := by
  unfold cnfExists_back SAT.CNF.eval
  simp only [List.all_eq_true, List.mem_flatMap, List.mem_map]
  intro clause ⟨H, _, p, _, t, _, hClauseEq⟩
  rw [← hClauseEq]
  -- The clause depends on whether there are worlds with (p, t)
  -- The clause is either [¬Exists(H,p,t)] or [¬Exists(H,p,t), Mem(H,w₁), ...]
  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
  by_cases hExists : hasExists hFits.view H p t = true
  · -- Exists is true, need to find some satisfied literal in the clause
    -- Since Exists is true, there's a world in H with (p, t)
    -- hasExists_implies_worldInPrehistory gives us that world
    obtain ⟨wWit, hWitP, hWitT, hWitMem, hWitWorld⟩ :=
      hasExists_implies_worldInPrehistory hFits.view H p t hExists
    -- wWit is in the filtered list (since w.p = p and w.ti = t)
    have hWitInFilter : wWit ∈ (WId.allWorlds b).filter (fun w => decide (w.p = p ∧ w.ti = t)) := by
      rw [List.mem_filter]
      constructor
      · exact hWitMem
      · simp only [decide_eq_true_eq]
        exact ⟨hWitP, hWitT⟩
    -- The clause contains the Mem literal for this witness
    -- Need to show Mem(H, wWit) is in the clause and evaluates to true
    -- First show ws is non-empty, so the clause has the Mem literals
    cases hWs : (WId.allWorlds b).filter (fun w => decide (w.p = p ∧ w.ti = t)) with
    | nil =>
        -- Contradiction: wWit ∈ ws but ws = []
        rw [hWs] at hWitInFilter
        cases hWitInFilter
    | cons w ws' =>
        -- ws is non-empty, clause is [¬Exists(H,p,t), Mem(H,w), Mem(H,w'), ...]
        refine ⟨SAT.Lit.pos (Var.Mem H wWit), ?_, ?_⟩
        · -- Show literal is in clause
          simp only [List.mem_cons, List.mem_map]
          right
          -- Need to show wWit ∈ w :: ws' and it maps to the literal
          have hWitInList : wWit ∈ w :: ws' := by
            rw [← hWs]
            exact hWitInFilter
          refine ⟨wWit, List.mem_cons.mp hWitInList, rfl⟩
        · -- Show literal evaluates to true
          simp only [SAT.Lit.eval]
          rw [assignmentOf_Mem]
          exact hWitWorld
  · -- Exists is false, first literal ¬Exists is true
    simp only [Bool.not_eq_true] at hExists
    -- The clause always has ¬Exists(H,p,t) as first literal regardless of ws
    cases hWs : (WId.allWorlds b).filter (fun w => decide (w.p = p ∧ w.ti = t)) with
    | nil =>
        -- clause is [¬Exists(H,p,t)]
        refine ⟨SAT.Lit.neg (Var.Exists H p t), List.mem_cons.mpr (Or.inl rfl), ?_⟩
        simp only [SAT.Lit.eval, Bool.not_eq_true']
        unfold assignmentOf
        exact hExists
    | cons _ _ =>
        -- clause is [¬Exists(H,p,t), ...]
        refine ⟨SAT.Lit.neg (Var.Exists H p t), List.mem_cons.mpr (Or.inl rfl), ?_⟩
        simp only [SAT.Lit.eval, Bool.not_eq_true']
        unfold assignmentOf
        exact hExists

/-! ## cnfSeq Satisfaction

Sequentiality encoding uses Acc/Incomp/Seq variables with bidirectional implications.
The encoding has 5 clause groups: accDef, incompFwd, incompBwd, seqToNoIncomp, noIncompToSeq.

Key semantic properties used:
- Acc(w₁,w₂,w₃) is true iff w₃ witnesses w₁ accessible from w₂
- Incomp(H,p,w₁,w₂) is true iff w₁,w₂ are incomparable p-worlds in H
- Seq(H,p) is true iff participant p is sequential at prehistory H

Completeness relies on:
- If Seq(H,p)=true semantically, then no Incomp can be true (worlds are comparable)
- The Acc/Incomp definitions match the semantic accessibility relation -/

/-! ### Helper: accWitnesses membership -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- A WId is in accWitnesses w₁ iff it has the same place and event as w₁. -/
lemma mem_accWitnesses
    {b : Bounds S}
    (w₁ w₃ : WId b) :
    w₃ ∈ (WId.allWorlds b).filter (fun w => w.p = w₁.p && w.ei = w₁.ei) ↔
    (w₃ ∈ WId.allWorlds b ∧ w₃.p = w₁.p ∧ w₃.ei = w₁.ei) := by
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]

/-! ### accDef Clauses

The accDef clauses define: Acc(w₁,w₂,w₃) ↔ Mem(w₂.ti,w₃) ∧ PreEq(w₃.ti,w₁.ti)
(for witnesses w₃ with w₃.p = w₁.p ∧ w₃.ei = w₁.ei)

assignmentOf sets Acc to:
  worldInPrehistory w₂.ti w₃ && preEqAt w₃.ti w₁.ti && (w₃.p = w₁.p) && (w₃.ei = w₁.ei)

Since accWitnesses only includes w₃ with matching p and ei, the clauses hold:
- Forward: Acc → Mem and Acc → PreEq (when w₃ is a valid witness)
- Backward: Mem ∧ PreEq → Acc (the extra conditions are ensured by witness selection) -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- accDef forward clause 1: Acc(w₁,w₂,w₃) → Mem(w₂.ti, w₃) -/
lemma accDef_fwd1_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (w₁ w₂ w₃ : WId b) :
    SAT.Clause.eval (assignmentOf b M hFits)
      [SAT.Lit.neg (Var.Acc w₁ w₂ w₃), SAT.Lit.pos (Var.Mem w₂.ti w₃)] = true := by
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Acc, assignmentOf_Mem]
  -- Either Acc is false (¬Acc is true) or Mem is true
  -- Acc = Mem && PreEq && (p eq) && (ei eq), so Acc → Mem
  by_cases hAcc : (worldInPrehistory hFits.view w₂.ti w₃ &&
                   preEqAt hFits.view w₃.ti w₁.ti &&
                   decide (w₃.p = w₁.p) &&
                   decide (w₃.ei = w₁.ei)) = true
  · -- Acc is true, extract Mem from conjunction
    -- Structure: (((a && b) && c) && d), so h.1.1.1 = a (worldInPrehistory)
    have hMem : worldInPrehistory hFits.view w₂.ti w₃ = true := by
      simp only [Bool.and_eq_true] at hAcc
      exact hAcc.1.1.1
    -- Goal: (!Acc || Mem) = true. Since Mem = true, the right side is true
    simp only [hMem, Bool.or_true]
  · -- Acc is false, ¬Acc is true
    simp only [Bool.not_eq_true] at hAcc
    simp only [hAcc, Bool.not_false, Bool.true_or]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- accDef forward clause 2: Acc(w₁,w₂,w₃) → PreEq(w₃.ti, w₁.ti) -/
lemma accDef_fwd2_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (w₁ w₂ w₃ : WId b) :
    SAT.Clause.eval (assignmentOf b M hFits)
      [SAT.Lit.neg (Var.Acc w₁ w₂ w₃), SAT.Lit.pos (Var.PreEq w₃.ti w₁.ti)] = true := by
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Acc, assignmentOf_PreEq]
  by_cases hAcc : (worldInPrehistory hFits.view w₂.ti w₃ &&
                   preEqAt hFits.view w₃.ti w₁.ti &&
                   decide (w₃.p = w₁.p) &&
                   decide (w₃.ei = w₁.ei)) = true
  · -- Structure: (((a && b) && c) && d), so h.1.1.2 = b (preEqAt)
    have hPreEq : preEqAt hFits.view w₃.ti w₁.ti = true := by
      simp only [Bool.and_eq_true] at hAcc
      exact hAcc.1.1.2
    -- Goal: (!Acc || PreEq) = true. Since PreEq = true, right side is true
    simp only [hPreEq, Bool.or_true]
  · simp only [Bool.not_eq_true] at hAcc
    simp only [hAcc, Bool.not_false, Bool.true_or]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- accDef backward clause: Mem(w₂.ti, w₃) ∧ PreEq(w₃.ti, w₁.ti) → Acc(w₁,w₂,w₃)
    This requires w₃ to be a valid witness (w₃.p = w₁.p ∧ w₃.ei = w₁.ei). -/
lemma accDef_bwd_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (w₁ w₂ w₃ : WId b)
    (hWit : w₃.p = w₁.p ∧ w₃.ei = w₁.ei) :
    SAT.Clause.eval (assignmentOf b M hFits)
      [SAT.Lit.neg (Var.Mem w₂.ti w₃), SAT.Lit.neg (Var.PreEq w₃.ti w₁.ti),
       SAT.Lit.pos (Var.Acc w₁ w₂ w₃)] = true := by
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Mem, assignmentOf_PreEq, assignmentOf_Acc]
  by_cases hMem : worldInPrehistory hFits.view w₂.ti w₃ = true
  · by_cases hPreEq : preEqAt hFits.view w₃.ti w₁.ti = true
    · -- Both Mem and PreEq are true, so Acc must be true
      simp only [hMem, hPreEq, hWit.1, hWit.2, Bool.not_true, Bool.false_or,
                 Bool.true_and, decide_true]
    · simp only [Bool.not_eq_true] at hPreEq
      simp only [hMem, hPreEq, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or]
  · simp only [Bool.not_eq_true] at hMem
    simp only [hMem, Bool.not_false, Bool.true_or]

/-! ### Linking Lemma: Acc implies anyAccTrue

The key semantic insight: if Acc(w₁,w₂,w₃)=true with the proper witness constraints,
then anyAccTrue w₁ w₂ = true (there exists a valid Acc witness).

This is straightforward by definition since anyAccTrue existentially quantifies
over exactly the Acc witnesses with matching p/ei. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If Acc(w₁,w₂,w₃)=true where w₃ has matching p and ei, then anyAccTrue w₁ w₂ = true. -/
lemma acc_implies_anyAccTrue
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (w₁ w₂ w₃ : WId b)
    (hPEi : w₃.p = w₁.p ∧ w₃.ei = w₁.ei)
    (hAcc : assignmentOf b M hFits (Var.Acc w₁ w₂ w₃) = true) :
    anyAccTrue hFits.view w₁ w₂ = true := by
  classical
  rw [assignmentOf_Acc] at hAcc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hAcc
  unfold anyAccTrue
  simp only [decide_eq_true_eq]
  exact ⟨w₃, hPEi.1, hPEi.2, hAcc.1.1.1, hAcc.1.1.2⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If anyAccTrue w₁ w₂ = true, then there exists w₃ with Acc(w₁,w₂,w₃)=true. -/
lemma anyAccTrue_implies_acc
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (w₁ w₂ : WId b)
    (hAny : anyAccTrue hFits.view w₁ w₂ = true) :
    ∃ w₃ : WId b, w₃.p = w₁.p ∧ w₃.ei = w₁.ei ∧
      assignmentOf b M hFits (Var.Acc w₁ w₂ w₃) = true := by
  classical
  unfold anyAccTrue at hAny
  simp only [decide_eq_true_eq] at hAny
  obtain ⟨w₃, hP, hEi, hMem, hPreEq⟩ := hAny
  refine ⟨w₃, hP, hEi, ?_⟩
  rw [assignmentOf_Acc]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hMem, hPreEq⟩, hP⟩, hEi⟩

/-! ### incompFwd Clauses -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- incompFwd: Incomp(H,p,w₁,w₂) → Mem(H,w₁) -/
lemma incompFwd_mem1_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants) (w₁ w₂ : WId b) :
    SAT.Clause.eval (assignmentOf b M hFits)
      [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.pos (Var.Mem H w₁)] = true := by
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Incomp, assignmentOf_Mem]
  -- Incomp = Mem(H,w₁) && Mem(H,w₂) && !anyAccTrue12 && !anyAccTrue21 && (ei_cond)
  by_cases hIncomp : (worldInPrehistory hFits.view H w₁ &&
                      worldInPrehistory hFits.view H w₂ &&
                      !anyAccTrue hFits.view w₁ w₂ &&
                      !anyAccTrue hFits.view w₂ w₁ &&
                      (if w₁.ei = w₂.ei then !preEqAt hFits.view w₁.ti w₂.ti else true)) = true
  · -- Incomp is true, extract first conjunct (Mem w₁)
    have hMem1 : worldInPrehistory hFits.view H w₁ = true := by
      simp only [Bool.and_eq_true] at hIncomp
      exact hIncomp.1.1.1.1
    simp only [hMem1, Bool.or_true]
  · simp only [Bool.not_eq_true] at hIncomp
    simp only [hIncomp, Bool.not_false, Bool.true_or]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- incompFwd: Incomp(H,p,w₁,w₂) → Mem(H,w₂) -/
lemma incompFwd_mem2_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants) (w₁ w₂ : WId b) :
    SAT.Clause.eval (assignmentOf b M hFits)
      [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.pos (Var.Mem H w₂)] = true := by
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Incomp, assignmentOf_Mem]
  by_cases hIncomp : (worldInPrehistory hFits.view H w₁ &&
                      worldInPrehistory hFits.view H w₂ &&
                      !anyAccTrue hFits.view w₁ w₂ &&
                      !anyAccTrue hFits.view w₂ w₁ &&
                      (if w₁.ei = w₂.ei then !preEqAt hFits.view w₁.ti w₂.ti else true)) = true
  · -- Incomp is true, extract second conjunct (Mem w₂)
    have hMem2 : worldInPrehistory hFits.view H w₂ = true := by
      simp only [Bool.and_eq_true] at hIncomp
      exact hIncomp.1.1.1.2
    simp only [hMem2, Bool.or_true]
  · simp only [Bool.not_eq_true] at hIncomp
    simp only [hIncomp, Bool.not_false, Bool.true_or]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- incompFwd: Incomp(H,p,w₁,w₂) → ¬Acc(w₁,w₂,w₃)

    Incomp includes !anyAccTrue w₁ w₂, so if Incomp=true then no Acc(w₁,w₂,w₃) can be true. -/
lemma incompFwd_acc12_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants) (w₁ w₂ w₃ : WId b) :
    SAT.Clause.eval (assignmentOf b M hFits)
      [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.neg (Var.Acc w₁ w₂ w₃)] = true := by
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Incomp, assignmentOf_Acc]
  by_cases hIncomp : (worldInPrehistory hFits.view H w₁ &&
                      worldInPrehistory hFits.view H w₂ &&
                      !anyAccTrue hFits.view w₁ w₂ &&
                      !anyAccTrue hFits.view w₂ w₁ &&
                      (if w₁.ei = w₂.ei then !preEqAt hFits.view w₁.ti w₂.ti else true)) = true
  · -- Incomp is true, need to show Acc is false
    -- Extract !anyAccTrue w₁ w₂ = true, i.e., anyAccTrue w₁ w₂ = false
    have hNotAny12 : anyAccTrue hFits.view w₁ w₂ = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hIncomp
      exact hIncomp.1.1.2
    simp only [hIncomp, Bool.not_true, Bool.false_or]
    -- Goal: !(Mem && PreEq && p_eq && ei_eq) = true
    -- If Acc(w₁,w₂,w₃) were true with w₃.p=w₁.p and w₃.ei=w₁.ei, anyAccTrue would be true
    cases hAccVal : (worldInPrehistory hFits.view w₂.ti w₃ &&
                     preEqAt hFits.view w₃.ti w₁.ti &&
                     decide (w₃.p = w₁.p) &&
                     decide (w₃.ei = w₁.ei))
    · rfl  -- Acc = false
    · -- Acc = true, contradiction: anyAccTrue would be true
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hAccVal
      have hAny := acc_implies_anyAccTrue hFits w₁ w₂ w₃ ⟨hAccVal.1.2, hAccVal.2⟩
        (by rw [assignmentOf_Acc]; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hAccVal)
      rw [hAny] at hNotAny12
      simp at hNotAny12
  · simp only [Bool.not_eq_true] at hIncomp
    simp only [hIncomp, Bool.not_false, Bool.true_or]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- incompFwd: Incomp(H,p,w₁,w₂) → ¬Acc(w₂,w₁,w₃)

    Incomp includes !anyAccTrue w₂ w₁, so if Incomp=true then no Acc(w₂,w₁,w₃) can be true. -/
lemma incompFwd_acc21_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants) (w₁ w₂ w₃ : WId b) :
    SAT.Clause.eval (assignmentOf b M hFits)
      [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.neg (Var.Acc w₂ w₁ w₃)] = true := by
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Incomp, assignmentOf_Acc]
  by_cases hIncomp : (worldInPrehistory hFits.view H w₁ &&
                      worldInPrehistory hFits.view H w₂ &&
                      !anyAccTrue hFits.view w₁ w₂ &&
                      !anyAccTrue hFits.view w₂ w₁ &&
                      (if w₁.ei = w₂.ei then !preEqAt hFits.view w₁.ti w₂.ti else true)) = true
  · -- Incomp is true, need to show Acc(w₂,w₁,w₃) is false
    -- Extract !anyAccTrue w₂ w₁ = true, i.e., anyAccTrue w₂ w₁ = false
    have hNotAny21 : anyAccTrue hFits.view w₂ w₁ = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hIncomp
      exact hIncomp.1.2
    simp only [hIncomp, Bool.not_true, Bool.false_or]
    -- Goal: !(Mem && PreEq && p_eq && ei_eq) = true
    cases hAccVal : (worldInPrehistory hFits.view w₁.ti w₃ &&
                     preEqAt hFits.view w₃.ti w₂.ti &&
                     decide (w₃.p = w₂.p) &&
                     decide (w₃.ei = w₂.ei))
    · rfl  -- Acc = false
    · -- Acc = true, contradiction: anyAccTrue would be true
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hAccVal
      have hAny := acc_implies_anyAccTrue hFits w₂ w₁ w₃ ⟨hAccVal.1.2, hAccVal.2⟩
        (by rw [assignmentOf_Acc]; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hAccVal)
      rw [hAny] at hNotAny21
      simp at hNotAny21
  · simp only [Bool.not_eq_true] at hIncomp
    simp only [hIncomp, Bool.not_false, Bool.true_or]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- incompFwd: Incomp(H,p,w₁,w₂) → ¬PreEq(w₁.ti,w₂.ti) (only used when w₁.ei = w₂.ei)

    Note: This clause is only generated when events match. When Incomp is true and events match,
    the definition includes !preEqAt, so preEqAt must be false. -/
lemma incompFwd_worldEq_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants) (w₁ w₂ : WId b)
    (hEi : w₁.ei = w₂.ei) :
    SAT.Clause.eval (assignmentOf b M hFits)
      [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.neg (Var.PreEq w₁.ti w₂.ti)] = true := by
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Incomp, assignmentOf_PreEq]
  by_cases hIncomp : (worldInPrehistory hFits.view H w₁ &&
                      worldInPrehistory hFits.view H w₂ &&
                      !anyAccTrue hFits.view w₁ w₂ &&
                      !anyAccTrue hFits.view w₂ w₁ &&
                      (if w₁.ei = w₂.ei then !preEqAt hFits.view w₁.ti w₂.ti else true)) = true
  · -- Incomp is true, events match: preEqAt must be false from the definition
    have hPreEqFalse : preEqAt hFits.view w₁.ti w₂.ti = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', hEi, ↓reduceIte] at hIncomp
      exact hIncomp.2
    simp only [hPreEqFalse, Bool.not_false, Bool.or_true]
  · simp only [Bool.not_eq_true] at hIncomp
    simp only [hIncomp, Bool.not_false, Bool.true_or]

/-! ### incompBwd Clauses -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- incompBwd: Mem ∧ Mem ∧ (¬∃w₃. Acc12) ∧ (¬∃w₃. Acc21) ∧ ¬PreEq → Incomp

    This is the backward direction: if all conditions for incomparability hold,
    then Incomp is true. Since assignmentOf sets Incomp = (Mem w₁ && Mem w₂ &&
    !isComparable12 && !isComparable21 && !preEqAt), this holds by definition.

    The clause is: ¬Mem H w₁ ∨ ¬Mem H w₂ ∨ (⋁ Acc12) ∨ (⋁ Acc21) ∨ PreEq ∨ Incomp

    Case analysis:
    - If Mem w₁ = false or Mem w₂ = false: clause satisfied by ¬Mem
    - If some Acc(w₁,w₂,w₃) = true: clause satisfied by that Acc
    - If some Acc(w₂,w₁,w₃) = true: clause satisfied by that Acc
    - If PreEq = true: clause satisfied by PreEq
    - Otherwise: Incomp = true (all conditions met), clause satisfied
-/
lemma incompBwd_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants) (w₁ w₂ : WId b)
    (clause : SAT.Clause (Var b))
    (hClause : clause =
      ([SAT.Lit.neg (Var.Mem H w₁), SAT.Lit.neg (Var.Mem H w₂),
        SAT.Lit.pos (Var.Incomp H p w₁ w₂)] ++
      ((WId.allWorlds b).filter (fun w₃ => w₃.p = w₁.p && w₃.ei = w₁.ei)).map
        (fun w₃ => SAT.Lit.pos (Var.Acc w₁ w₂ w₃)) ++
      ((WId.allWorlds b).filter (fun w₃ => w₃.p = w₂.p && w₃.ei = w₂.ei)).map
        (fun w₃ => SAT.Lit.pos (Var.Acc w₂ w₁ w₃)) ++
      (if w₁.ei = w₂.ei then [SAT.Lit.pos (Var.PreEq w₁.ti w₂.ti)] else []))) :
    SAT.Clause.eval (assignmentOf b M hFits) clause = true := by
  -- Key insight: assignmentOf sets Incomp = Mem ∧ Mem ∧ ¬anyAccTrue12 ∧ ¬anyAccTrue21 ∧ ¬preEq
  -- If Incomp=true, the Incomp literal makes the clause true
  -- If Incomp=false, one of: Mem=false, anyAccTrue12=true, anyAccTrue21=true, or preEq=true
  -- Each of these has a corresponding literal in the clause
  rw [hClause]
  by_cases hIncomp : assignmentOf b M hFits (Var.Incomp H p w₁ w₂) = true
  · -- Incomp = true, clause satisfied by the Incomp literal
    apply SAT.Clause.eval_true_of_pos_mem
    · -- Show Incomp literal is in clause: [¬Mem₁, ¬Mem₂, Incomp] ++ Accs12 ++ Accs21 ++ PreEq
      -- Structure is ((([a,b,c] ++ l₁) ++ l₂) ++ l₃)
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      -- Goal: x = a ∨ x = b ∨ x = c (right-assoc)
      right; right; rfl
    · exact hIncomp
  · -- Incomp = false, one of the escape conditions must hold
    simp only [Bool.not_eq_true] at hIncomp
    rw [assignmentOf_Incomp] at hIncomp
    -- Incomp = Mem w₁ && Mem w₂ && !anyAccTrue12 && !anyAccTrue21 && !preEq
    by_cases hM1 : worldInPrehistory hFits.view H w₁ = false
    · -- Mem w₁ = false: ¬Mem w₁ makes clause true
      apply SAT.Clause.eval_true_of_neg_mem
      · apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        left; rfl
      · rw [assignmentOf_Mem]; exact hM1
    · by_cases hM2 : worldInPrehistory hFits.view H w₂ = false
      · -- Mem w₂ = false: ¬Mem w₂ makes clause true
        apply SAT.Clause.eval_true_of_neg_mem
        · apply List.mem_append_left
          apply List.mem_append_left
          apply List.mem_append_left
          simp only [List.mem_cons, List.mem_nil_iff, or_false]
          right; left; rfl
        · rw [assignmentOf_Mem]; exact hM2
      · by_cases hAcc12 : anyAccTrue hFits.view w₁ w₂ = true
        · -- anyAccTrue w₁ w₂ = true: some Acc(w₁,w₂,w₃) is true
          obtain ⟨w₃, hP, hEi, hAccTrue⟩ := anyAccTrue_implies_acc hFits w₁ w₂ hAcc12
          apply SAT.Clause.eval_true_of_pos_mem (v := Var.Acc w₁ w₂ w₃)
          · -- Acc(w₁,w₂,w₃) is in Accs12 part
            apply List.mem_append_left
            apply List.mem_append_left
            apply List.mem_append_right
            simp only [List.mem_map, List.mem_filter]
            refine ⟨w₃, ⟨w₃.mem_allWorlds, ?_⟩, rfl⟩
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨hP, hEi⟩
          · exact hAccTrue
        · simp only [Bool.not_eq_true] at hAcc12
          by_cases hAcc21 : anyAccTrue hFits.view w₂ w₁ = true
          · -- anyAccTrue w₂ w₁ = true: some Acc(w₂,w₁,w₃) is true
            obtain ⟨w₃, hP, hEi, hAccTrue⟩ := anyAccTrue_implies_acc hFits w₂ w₁ hAcc21
            apply SAT.Clause.eval_true_of_pos_mem (v := Var.Acc w₂ w₁ w₃)
            · -- Acc(w₂,w₁,w₃) is in Accs21 part
              apply List.mem_append_left
              apply List.mem_append_right
              simp only [List.mem_map, List.mem_filter]
              refine ⟨w₃, ⟨w₃.mem_allWorlds, ?_⟩, rfl⟩
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨hP, hEi⟩
            · exact hAccTrue
          · simp only [Bool.not_eq_true] at hAcc21
            -- All escape conditions false. Case split on event equality.
            -- With the new encoding:
            --   Incomp = Mem₁ && Mem₂ && !anyAcc12 && !anyAcc21 && (ei_match → !preEq)
            -- When ei don't match, the last term is `true`, so Incomp = Mem₁ && ... && true
            -- which would be true given our hypotheses, contradicting Incomp = false
            by_cases hEi : w₁.ei = w₂.ei
            · -- Events match: derive preEqAt = true from Incomp = false
              have hPreEq : preEqAt hFits.view w₁.ti w₂.ti = true := by
                by_contra hNotPreEq
                simp only [Bool.not_eq_true] at hNotPreEq
                -- With events matching, Incomp's last term is !preEqAt
                have hM1' : worldInPrehistory hFits.view H w₁ = true :=
                  Bool.eq_true_of_not_eq_false hM1
                have hM2' : worldInPrehistory hFits.view H w₂ = true :=
                  Bool.eq_true_of_not_eq_false hM2
                have hIncompTrue :
                    (worldInPrehistory hFits.view H w₁ &&
                     worldInPrehistory hFits.view H w₂ &&
                     !anyAccTrue hFits.view w₁ w₂ &&
                     !anyAccTrue hFits.view w₂ w₁ &&
                     (if w₁.ei = w₂.ei then !preEqAt hFits.view w₁.ti w₂.ti
                      else true)) = true := by
                  simp only [Bool.and_eq_true, Bool.not_eq_true', hEi, ↓reduceIte]
                  exact ⟨⟨⟨⟨hM1', hM2'⟩, hAcc12⟩, hAcc21⟩, hNotPreEq⟩
                rw [hIncompTrue] at hIncomp
                simp at hIncomp
              -- preEqAt = true: PreEq literal makes clause true
              apply SAT.Clause.eval_true_of_pos_mem (v := Var.PreEq w₁.ti w₂.ti)
              · apply List.mem_append_right
                simp only [hEi, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false]
              · rw [assignmentOf_PreEq]; exact hPreEq
            · -- Events don't match: Incomp should be true, contradicting hIncomp
              -- With ei ≠ ei', the conditional is `true`, so
              --   Incomp = Mem₁ && Mem₂ && !anyAcc12 && !anyAcc21 && true = true
              have hM1' : worldInPrehistory hFits.view H w₁ = true :=
                Bool.eq_true_of_not_eq_false hM1
              have hM2' : worldInPrehistory hFits.view H w₂ = true :=
                Bool.eq_true_of_not_eq_false hM2
              have hIncompTrue :
                  (worldInPrehistory hFits.view H w₁ &&
                   worldInPrehistory hFits.view H w₂ &&
                   !anyAccTrue hFits.view w₁ w₂ &&
                   !anyAccTrue hFits.view w₂ w₁ &&
                   (if w₁.ei = w₂.ei then !preEqAt hFits.view w₁.ti w₂.ti
                    else true)) = true := by
                simp only [Bool.and_eq_true, Bool.not_eq_true', hEi, ↓reduceIte, and_true]
                exact ⟨⟨⟨hM1', hM2'⟩, hAcc12⟩, hAcc21⟩
              rw [hIncompTrue] at hIncomp
              simp at hIncomp

/-! ### seqToNoIncomp Clauses -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- seqToNoIncomp: Seq(H,p) → ¬Incomp(H,p,w₁,w₂)

    The clause is: ¬Seq(H,p) ∨ ¬Incomp(H,p,w₁,w₂)

    Semantic meaning: If H is sequential for p, no two p-worlds in H can be incomparable.

    Proof: By contrapositive. If both Seq and Incomp are true, contradiction:
    - Seq(H,p) = true means isSequential p (prehistoryOfTime H)
    - Incomp(H,p,w₁,w₂) = true means w₁,w₂ in prehistory AND not comparable AND not worldEq
    - But isSequential says all p-worlds in prehistory are comparable or worldEq, contradiction

    Note: This lemma requires w₁.p = p and w₂.p = p because the clauses in the CNF
    are only generated for pairs with matching places. The semantic bridge relies on
    sequentiality for p applying to both worlds. -/
lemma seqToNoIncomp_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants) (w₁ w₂ : WId b)
    (hW1p : w₁.p = p) (hW2p : w₂.p = p) :
    SAT.Clause.eval (assignmentOf b M hFits)
      [SAT.Lit.neg (Var.Seq H p), SAT.Lit.neg (Var.Incomp H p w₁ w₂)] = true := by
  simp only [SAT.Clause.eval, List.foldl_cons, List.foldl_nil, Bool.false_or, SAT.Lit.eval]
  rw [assignmentOf_Seq, assignmentOf_Incomp]
  -- Goal: (!Seq || !Incomp) = true
  -- If Seq = false: !Seq = true, done
  -- If Incomp = false: !Incomp = true, done
  -- If both true: contradiction from semantics
  by_cases hSeq : isSeqAt hFits.view H p = true
  · by_cases hIncomp : (worldInPrehistory hFits.view H w₁ &&
                        worldInPrehistory hFits.view H w₂ &&
                        !anyAccTrue hFits.view w₁ w₂ &&
                        !anyAccTrue hFits.view w₂ w₁ &&
                        (if w₁.ei = w₂.ei then !preEqAt hFits.view w₁.ti w₂.ti else true)) = true
    · -- Both Seq and Incomp are true: derive contradiction from semantics
      -- isSeqAt H p means isSequential p (prehistoryOfTime H)
      -- Incomp conditions mean w₁,w₂ in H, no accessibility witness, and not worldEq
      -- isSequential says all p-worlds are comparable via accessibility or equal
      -- This contradicts the Incomp conditions
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hIncomp
      have hW1mem : worldInPrehistory hFits.view H w₁ = true := hIncomp.1.1.1.1
      have hW2mem : worldInPrehistory hFits.view H w₂ = true := hIncomp.1.1.1.2
      have hNoAcc12 : anyAccTrue hFits.view w₁ w₂ = false := hIncomp.1.1.2
      have hNoAcc21 : anyAccTrue hFits.view w₂ w₁ = false := hIncomp.1.2
      -- Extract semantic worlds from worldInPrehistory
      obtain ⟨sem₁, hSem1Mem, hSem1Place, hSem1Event, hSem1Ti⟩ :=
        extract_of_worldInPrehistory hFits.view H w₁ hW1mem
      obtain ⟨sem₂, hSem2Mem, hSem2Place, hSem2Event, hSem2Ti⟩ :=
        extract_of_worldInPrehistory hFits.view H w₂ hW2mem

      -- Get reachable prehistory (prehistoryAt H is nonempty since sem₁ is in it)
      have hNonempty : ∃ w, w ∈ prehistoryAt hFits.view H := ⟨sem₁, hSem1Mem⟩
      obtain ⟨pH, hReach, hIdx, hEq⟩ :=
        prehistoryAt_nonempty_implies_reachable hFits.view H hNonempty

      -- sem₁, sem₂ are in pH (rewrite using hEq)
      have hSem1InpH : sem₁ ∈ pH := hEq ▸ hSem1Mem
      have hSem2InpH : sem₂ ∈ pH := hEq ▸ hSem2Mem

      -- Get reachability of times
      have hReach1 : sem₁.time ∈ reachablePreHistories M.history.val :=
        time_mem_reachablePreHistories_of_mem_history hReach hSem1InpH
      have hReach2 : sem₂.time ∈ reachablePreHistories M.history.val :=
        time_mem_reachablePreHistories_of_mem_history hReach hSem2InpH

      -- Show widOfWorld ev sem₁ = w₁ (by injectivity of decodeMaybeEvent)
      have hWid1Eq : widOfWorld hFits.view sem₁ = w₁ := by
        unfold widOfWorld
        -- .ei: use injectivity
        have hEi1 : hFits.view.evSelOf sem₁.event = w₁.ei := by
          have h1 : b.decodeMaybeEvent w₁.ei = sem₁.event := hSem1Event
          have h2 : b.decodeMaybeEvent (hFits.view.evSelOf sem₁.event) = sem₁.event :=
            hFits.view.evSel_spec sem₁.event
          exact b.decodeMaybeEvent_injective _ _ (h2.trans h1.symm)
        simp only [hSem1Place, hEi1, hSem1Ti]

      have hWid2Eq : widOfWorld hFits.view sem₂ = w₂ := by
        unfold widOfWorld
        have hEi2 : hFits.view.evSelOf sem₂.event = w₂.ei := by
          have h1 : b.decodeMaybeEvent w₂.ei = sem₂.event := hSem2Event
          have h2 : b.decodeMaybeEvent (hFits.view.evSelOf sem₂.event) = sem₂.event :=
            hFits.view.evSel_spec sem₂.event
          exact b.decodeMaybeEvent_injective _ _ (h2.trans h1.symm)
        simp only [hSem2Place, hEi2, hSem2Ti]

      -- Convert anyAccTrue=false to ¬accessible
      have hNotAcc12 : ¬(sem₁ ≪ sem₂) := by
        rw [← hWid1Eq, ← hWid2Eq] at hNoAcc12
        exact not_accessible_of_anyAccTrue_false hFits.view hReach1 hReach2 hNoAcc12
      have hNotAcc21 : ¬(sem₂ ≪ sem₁) := by
        rw [← hWid2Eq, ← hWid1Eq] at hNoAcc21
        exact not_accessible_of_anyAccTrue_false hFits.view hReach2 hReach1 hNoAcc21

      -- Get ¬worldEq from the conditional
      have hNotWorldEq : ¬PreHistory.worldEq sem₁ sem₂ := by
        intro hWEq
        -- If worldEq sem₁ sem₂, then same place, same event, histEq times
        have hPlaceEq := PreHistory.worldEq_place hWEq
        have hEventEq := PreHistory.worldEq_event hWEq
        have hTimeEq := PreHistory.worldEq_time hWEq
        -- w₁.ei = evSelOf sem₁.event and w₂.ei = evSelOf sem₂.event
        -- If sem₁.event = sem₂.event, then w₁.ei = w₂.ei
        have hEiEq : w₁.ei = w₂.ei := by
          have h1 : b.decodeMaybeEvent w₁.ei = sem₁.event := hSem1Event
          have h2 : b.decodeMaybeEvent w₂.ei = sem₂.event := hSem2Event
          have hDecEq : b.decodeMaybeEvent w₁.ei = b.decodeMaybeEvent w₂.ei := by
            rw [h1, h2, hEventEq]
          exact b.decodeMaybeEvent_injective _ _ hDecEq
        -- In this case, the condition becomes !preEqAt w₁.ti w₂.ti = true
        simp only [hEiEq, ↓reduceIte] at hIncomp
        have hPreEqFalse : preEqAt hFits.view w₁.ti w₂.ti = false := by
          simp only [Bool.not_eq_true'] at hIncomp
          exact hIncomp.2
        -- But histEq times means preEqAt should be true
        have hPreEqTrue : preEqAt hFits.view w₁.ti w₂.ti = true := by
          have h := preEqAt_of_histEq_reachable hFits.view hReach1 hReach2 hTimeEq
          rw [hSem1Ti, hSem2Ti] at h
          exact h
        rw [hPreEqTrue] at hPreEqFalse
        simp at hPreEqFalse

      -- Get sequentiality from isSeqAt
      unfold isSeqAt at hSeq
      simp only [decide_eq_true_eq] at hSeq

      -- Apply sequentiality_contradiction to get False, then use False.elim
      exact False.elim (sequentiality_contradiction hFits.view H p sem₁ sem₂
        hSem1Mem hSem2Mem
        (hSem1Place.trans hW1p) (hSem2Place.trans hW2p)
        hSeq hNotAcc12 hNotAcc21 hNotWorldEq)
    · -- Incomp = false: one of the escape conditions holds
      simp only [Bool.not_eq_true] at hIncomp
      -- Goal is: !Seq || !Incomp = true. Since Incomp=false, !Incomp=true.
      simp only [hIncomp, Bool.not_false, Bool.or_true]
  · simp only [Bool.not_eq_true] at hSeq
    simp only [hSeq, Bool.not_false, Bool.true_or]

/-! ### noIncompToSeq Clauses -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- noIncompToSeq: (∧_{w₁,w₂} ¬Incomp(H,p,w₁,w₂)) → Seq(H,p)

    The clause is: Seq(H,p) ∨ (⋁ Incomp(H,p,w₁,w₂))

    Semantic meaning: If all pairs of p-worlds are comparable, then H is sequential for p.

    Proof: Contrapositive. If Seq = false, some Incomp must be true.
    - Seq(H,p) = false means ¬isSequential p (prehistoryOfTime H)
    - So ∃ w₁,w₂ in prehistory with place p that are not comparable and not worldEq
    - This exactly matches Incomp conditions, so that Incomp = true -/
lemma noIncompToSeq_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants)
    (clause : SAT.Clause (Var b))
    (hClause : clause = SAT.Lit.pos (Var.Seq H p) ::
      ((WId.allWorlds b).filter (fun w => w.p = p)).flatMap (fun w₁ =>
        ((WId.allWorlds b).filter (fun w => w.p = p)).map (fun w₂ =>
          SAT.Lit.pos (Var.Incomp H p w₁ w₂)))) :
    SAT.Clause.eval (assignmentOf b M hFits) clause = true := by
  rw [hClause]
  -- If Seq(H,p) = true: first literal satisfies clause
  by_cases hSeq : assignmentOf b M hFits (Var.Seq H p) = true
  · apply SAT.Clause.eval_true_of_pos_mem (v := Var.Seq H p)
    · simp only [List.mem_cons, true_or]
    · exact hSeq
  · -- Seq(H,p) = false: need to find a true Incomp
    simp only [Bool.not_eq_true] at hSeq
    rw [assignmentOf_Seq] at hSeq
    -- isSeqAt H p = false means ¬isSequential p (prehistoryOfTime H)
    -- So ∃ worlds that witness non-sequentiality
    unfold isSeqAt at hSeq
    simp only [decide_eq_false_iff_not] at hSeq
    -- hSeq : ¬isSequential p (prehistoryOfTime ev H)
    -- Push negation to get witnesses
    unfold isSequential at hSeq
    push_neg at hSeq
    -- hSeq : ∃ t₁ t₂, t₁ ∈ pH ∧ t₂ ∈ pH ∧ place=p ∧ place=p ∧ ¬(t₁≪t₂) ∧ ¬(t₂≪t₁) ∧ ¬worldEq
    obtain ⟨t₁, t₂, hT1mem, hT2mem, hP1, hP2, hNoAcc12, hNoAcc21, hNotEq⟩ := hSeq
    -- hNoAcc12 : ¬(t₁ ≪ t₂), hNoAcc21 : ¬(t₂ ≪ t₁), hNotEq : ¬worldEq t₁ t₂
    -- Let w₁ = widOfWorld t₁, w₂ = widOfWorld t₂
    let w₁ := widOfWorld hFits.view t₁
    let w₂ := widOfWorld hFits.view t₂
    -- Show the Incomp literal at (w₁, w₂) is in the clause and is true
    -- The clause is: Seq H p :: flatMap(...Incomp literals...)
    -- We need to find our Incomp literal in the list
    apply SAT.Clause.eval_true_of_pos_mem (v := Var.Incomp H p w₁ w₂)
    · -- Show Incomp H p w₁ w₂ is in the clause
      simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, List.mem_map]
      right
      -- Need to show w₁ ∈ filter (place=p) allWorlds and w₂ ∈ filter (place=p) allWorlds
      use w₁
      refine ⟨⟨WId.mem_allWorlds b w₁, ?_⟩, w₂, ⟨WId.mem_allWorlds b w₂, ?_⟩, rfl⟩
      · -- decide (w₁.p = p) = true
        simp only [decide_eq_true_eq, w₁, widOfWorld, hP1]
      · -- decide (w₂.p = p) = true
        simp only [decide_eq_true_eq, w₂, widOfWorld, hP2]
    · -- Show assignmentOf (Incomp H p w₁ w₂) = true
      -- Incomp = worldInPrehistory H w₁ && worldInPrehistory H w₂ &&
      --          !anyAccTrue w₁ w₂ && !anyAccTrue w₂ w₁ &&
      --          (if w₁.ei = w₂.ei then !preEqAt w₁.ti w₂.ti else true)
      simp only [assignmentOf]
      -- Need all conjuncts to be true
      -- First get reachability
      have hNonempty : ∃ w, w ∈ prehistoryAt hFits.view H := ⟨t₁, hT1mem⟩
      obtain ⟨pH, hReach, hIdx, hEq⟩ :=
        prehistoryAt_nonempty_implies_reachable hFits.view H hNonempty
      have hT1InpH : t₁ ∈ pH := hEq ▸ hT1mem
      have hT2InpH : t₂ ∈ pH := hEq ▸ hT2mem
      have hReach1 : t₁.time ∈ reachablePreHistories M.history.val :=
        time_mem_reachablePreHistories_of_mem_history hReach hT1InpH
      have hReach2 : t₂.time ∈ reachablePreHistories M.history.val :=
        time_mem_reachablePreHistories_of_mem_history hReach hT2InpH
      -- worldInPrehistory for both
      have hWip1 : worldInPrehistory hFits.view H w₁ = true :=
        worldInPrehistory_of_mem hFits.view H t₁ hT1mem
      have hWip2 : worldInPrehistory hFits.view H w₂ = true :=
        worldInPrehistory_of_mem hFits.view H t₂ hT2mem
      -- anyAccTrue is false for both directions
      have hNoAnyAcc12 : anyAccTrue hFits.view w₁ w₂ = false :=
        anyAccTrue_false_of_not_accessible hFits.view hReach1 hReach2 hNoAcc12
      have hNoAnyAcc21 : anyAccTrue hFits.view w₂ w₁ = false :=
        anyAccTrue_false_of_not_accessible hFits.view hReach2 hReach1 hNoAcc21
      -- Handle the preEqAt conditional
      simp only [hWip1, hWip2, hNoAnyAcc12, hNoAnyAcc21, Bool.and_true,
                 Bool.true_and, Bool.not_false]
      -- Goal: if w₁.ei = w₂.ei then !preEqAt w₁.ti w₂.ti else true
      by_cases hEiEq : w₁.ei = w₂.ei
      · -- Events match: need !preEqAt = true, i.e., preEqAt = false
        simp only [hEiEq, ↓reduceIte, Bool.not_eq_true']
        -- From hNotEq : ¬worldEq t₁ t₂
        -- Events match means t₁.event = t₂.event (decoded from same ei)
        -- Places match: hP1 = hP2
        -- So by preEqAt_false_of_not_worldEq_same_event, preEqAt = false
        have hSamePlace : t₁.place = t₂.place := hP1.trans hP2.symm
        have hSameEvent : t₁.event = t₂.event := by
          -- w₁.ei = evSelOf t₁.event, w₂.ei = evSelOf t₂.event
          -- hEiEq : evSelOf t₁.event = evSelOf t₂.event
          -- By evSel_spec: decodeMaybeEvent (evSelOf e) = e
          -- So t₁.event = t₂.event
          simp only [w₁, w₂, widOfWorld] at hEiEq
          have h1 := hFits.view.evSel_spec t₁.event
          have h2 := hFits.view.evSel_spec t₂.event
          rw [hEiEq] at h1
          exact h1.symm.trans h2
        exact preEqAt_false_of_not_worldEq_same_event hFits.view hReach1 hReach2
               hSamePlace hSameEvent hNotEq
      · -- Events don't match: result is true
        simp only [hEiEq, ↓reduceIte]

/-! ### Main cnfSeq Theorem -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfSeq.

    The encoding has multiple clause types:
    1. accDef: Tseytin definition of Acc(w₁,w₂,w₃) ↔ Mem(w₂.ti,w₃) ∧ PreEq(w₃.ti,w₁.ti)
    2. incompFwd: Incomp implies its conjuncts
    3. incompBwd: Conjuncts imply Incomp
    4. seqToNoIncomp: Seq(H,p) → ¬Incomp(H,p,w₁,w₂)
    5. noIncompToSeq: (∧ ¬Incomp) → Seq(H,p)

    For completeness, the key insight is that assignmentOf sets each variable according
    to its semantic definition, so the bidirectional implications hold. -/
theorem assignmentOf_satisfies_cnfSeq
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfSeq b).eval (assignmentOf b M hFits) = true := by
  -- cnfSeq = SAT.CNF.mk (accDef ++ incompFwd ++ incompBwd ++ seqToNoIncomp ++ noIncompToSeq)
  unfold cnfSeq SAT.CNF.eval
  simp only [List.all_eq_true]
  intro clause hClause
  simp only [List.mem_append] at hClause
  -- Structure: ((((accDef ++ incompFwd) ++ incompBwd) ++ seqToNoIncomp) ++ noIncompToSeq)
  -- Each ++ gives an Or after List.mem_append
  obtain ((((hAccDef | hIncompFwd) | hIncompBwd) | hSeqToNoIncomp) | hNoIncompToSeq) := hClause

  -- Case 1: accDef clauses - from allPairs.flatMap (fun ⟨_,_,w₁,w₂⟩ => accWitnesses.flatMap ...)
  case inl.inl.inl.inl =>
    -- accDef: allPairs.flatMap (fun ⟨_,_,w₁,w₂⟩ => accWitnesses.flatMap ...)
    -- allPairs: timesL.flatMap (partsL.flatMap (ws.flatMap (ws.map)))
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map] at hAccDef
    obtain ⟨⟨_, _, w₁, w₂⟩, hPair, w₃, ⟨_, hW3filter⟩, hClauseIn⟩ := hAccDef
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hW3filter
    obtain ⟨hW3p, hW3ei⟩ := hW3filter
    -- hClauseIn : clause ∈ [fwd1, fwd2, bwd]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hClauseIn
    rcases hClauseIn with hFwd1 | hFwd2 | hBwd
    · subst hFwd1; exact accDef_fwd1_satisfied hFits w₁ w₂ w₃
    · subst hFwd2; exact accDef_fwd2_satisfied hFits w₁ w₂ w₃
    · subst hBwd; exact accDef_bwd_satisfied hFits w₁ w₂ w₃ ⟨hW3p, hW3ei⟩

  -- Case 2: incompFwd clauses
  case inl.inl.inl.inr =>
    -- incompFwd = allPairs.flatMap fun ⟨H, p, w₁, w₂⟩ => (memClauses ++ acc12 ++ acc21 ++ worldEq)
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_append] at hIncompFwd
    obtain ⟨⟨H, p, w₁, w₂⟩, hPair, hSubClause⟩ := hIncompFwd
    -- hSubClause : clause ∈ memClauses ++ acc12Clauses ++ acc21Clauses ++ worldEqClauses
    obtain (((hMem | hAcc12) | hAcc21) | hWorldEq) := hSubClause
    · -- memClauses: [mem1, mem2]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
      rcases hMem with hMem1 | hMem2
      · subst hMem1; exact incompFwd_mem1_satisfied hFits H p w₁ w₂
      · subst hMem2; exact incompFwd_mem2_satisfied hFits H p w₁ w₂
    · -- acc12Clauses
      obtain ⟨w₃, ⟨_, hW3filter⟩, hClauseEq⟩ := hAcc12
      subst hClauseEq; exact incompFwd_acc12_satisfied hFits H p w₁ w₂ w₃
    · -- acc21Clauses
      obtain ⟨w₃, ⟨_, hW3filter⟩, hClauseEq⟩ := hAcc21
      subst hClauseEq; exact incompFwd_acc21_satisfied hFits H p w₁ w₂ w₃
    · -- worldEqClauses
      split at hWorldEq
      case isTrue hEiEq =>
        simp only [List.mem_singleton] at hWorldEq
        subst hWorldEq; exact incompFwd_worldEq_satisfied hFits H p w₁ w₂ hEiEq
      case isFalse => simp only [List.not_mem_nil] at hWorldEq

  -- Case 3: incompBwd clauses
  case inl.inl.inr =>
    -- incompBwd = allPairs.map fun ⟨H, p, w₁, w₂⟩ => clause
    simp only [List.mem_map, List.mem_flatMap, List.mem_filter] at hIncompBwd
    obtain ⟨⟨H, p, w₁, w₂⟩, hPair, hClauseEq⟩ := hIncompBwd
    subst hClauseEq; exact incompBwd_satisfied hFits H p w₁ w₂ _ rfl

  -- Case 4: seqToNoIncomp clauses
  case inl.inr =>
    -- seqToNoIncomp = allPairs.map fun ⟨H, p, w₁, w₂⟩ => [¬Seq, ¬Incomp]
    simp only [List.mem_map, List.mem_flatMap, List.mem_filter] at hSeqToNoIncomp
    obtain ⟨⟨H, p, w₁, w₂⟩, hPair, hClauseEq⟩ := hSeqToNoIncomp
    -- hPair : (H, p, w₁, w₂) ∈ allPairs
    -- allPairs = timesL.flatMap (partsL.flatMap (ws.flatMap (ws.map)))
    -- Membership gives existential structure that after simp becomes conjunctions
    simp only [decide_eq_true_eq] at hPair
    -- hPair now has structure: ∃ H' p' w₁' w₂', ... ∧ w₁'.p = p' ∧ w₂'.p = p' ∧ (H,p,w₁,w₂) = ...
    obtain ⟨_, _, p', _, w₁', ⟨_, hw1p⟩, w₂', ⟨_, hw2p⟩, hEq⟩ := hPair
    -- hEq is the equality of the tuples : (H', p', w₁', w₂') = (H, p, w₁, w₂)
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨hHeq, hpeq, hw1eq, hw2eq⟩ := hEq
    -- Substitute all equalities: w₁' = w₁, w₂' = w₂, p' = p
    -- After subst, the primed names survive and unprimed are eliminated
    subst hw1eq hw2eq hpeq
    -- Now hw1p : w₁'.p = p', hw2p : w₂'.p = p'
    subst hClauseEq; exact seqToNoIncomp_satisfied hFits H p' w₁' w₂' hw1p hw2p

  -- Case 5: noIncompToSeq clauses
  case inr =>
    -- noIncompToSeq = timesL.flatMap (fun H => partsL.map (fun p => clause))
    simp only [List.mem_flatMap, List.mem_map] at hNoIncompToSeq
    obtain ⟨H, _, p, _, hClauseEq⟩ := hNoIncompToSeq
    subst hClauseEq; exact noIncompToSeq_satisfied hFits H p _ rfl

/-! ## cnfLearners Satisfaction

Semifilter constraints for learners. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: repUnitClauses are satisfied by assignmentOf. -/
lemma repUnit_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (clause : SAT.Clause (Var b))
    (hMem : clause ∈ repUnitClauses b) :
    SAT.Clause.eval (assignmentOf b M hFits) clause = true := by
  -- repUnitClauses = (classValues b).map (fun v => [Lit.pos (Var.Rep (b.findValueIndex v))])
  simp only [repUnitClauses, List.mem_map] at hMem
  obtain ⟨v, hVmem, hClause⟩ := hMem
  subst hClause
  simp only [SAT.Clause.eval]
  simp only [SAT.Lit.eval, assignmentOf]
  -- Need to show isRepresentative (b.findValueIndex v) = true
  -- Use the findValueIndex_spec: findValueIndex v is minimal for value v
  have hEx : ∃ i : b.valIx, b.values.get i = v := by
    -- v ∈ classValues b means v = b.values.get i for some i
    simp only [classValues, List.mem_dedup, List.mem_map, List.mem_finRange, true_and] at hVmem
    exact hVmem
  exact isRepresentative_findValueIndex v hEx

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: repExoClauses are satisfied by assignmentOf. -/
lemma repExo_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (clause : SAT.Clause (Var b))
    (hMem : clause ∈ repExoClauses b) :
    SAT.Clause.eval (assignmentOf b M hFits) clause = true := by
  -- repExoClauses = (classValues b).flatMap
  --   (fun v => (SAT.exo (valueIndices b v).map Var.Rep).clauses)
  -- exo = alo.and amo, so clauses are from either alo or amo
  simp only [repExoClauses, List.mem_flatMap] at hMem
  obtain ⟨v, hVmem, hClauseInExo⟩ := hMem
  -- v ∈ classValues b means v appears in b.values
  have hEx : ∃ i : b.valIx, b.values.get i = v := by
    simp only [classValues, List.mem_dedup, List.mem_map, List.mem_finRange, true_and] at hVmem
    exact hVmem
  let indices := valueIndices b v
  -- The exo constraint is: (alo (indices.map Var.Rep)).and (amo (indices.map Var.Rep))
  -- Its clauses are the concatenation of alo clauses and amo clauses
  simp only [SAT.exo, SAT.CNF.and, List.mem_append] at hClauseInExo
  obtain hAlo | hAmo := hClauseInExo
  · -- ALO case: clause ∈ (alo (indices.map Var.Rep)).clauses = [[Rep i₁⁺, Rep i₂⁺, ...]]
    simp only [SAT.alo] at hAlo
    simp only [List.mem_singleton] at hAlo
    subst hAlo
    -- clause = (indices.map Var.Rep).map SAT.Lit.pos = [Rep(i₁)⁺, Rep(i₂)⁺, ...]
    -- Need to show at least one Rep(i) is true
    -- findValueIndex v is in indices and isRepresentative (findValueIndex v) = true
    have hFindMem : b.findValueIndex v ∈ indices := findValueIndex_mem_valueIndices v hEx
    have hRepTrue : isRepresentative (b.findValueIndex v) = true :=
      isRepresentative_findValueIndex v hEx
    -- Var.Rep (findValueIndex v) is in the list
    have hRepInList : Var.Rep (b.findValueIndex v) ∈ indices.map Var.Rep :=
      List.mem_map.mpr ⟨b.findValueIndex v, hFindMem, rfl⟩
    -- Its assignment is true
    have hAssignTrue : assignmentOf b M hFits (Var.Rep (b.findValueIndex v)) = true := by
      simp only [assignmentOf, hRepTrue]
    -- The clause evaluates to true because it contains a true positive literal
    have hPosInClause : SAT.Lit.pos (Var.Rep (b.findValueIndex v)) ∈
        (indices.map Var.Rep).map SAT.Lit.pos :=
      List.mem_map.mpr ⟨Var.Rep (b.findValueIndex v), hRepInList, rfl⟩
    exact SAT.Clause.eval_true_of_pos_mem (assignmentOf b M hFits) _
      (Var.Rep (b.findValueIndex v)) hPosInClause hAssignTrue
  · -- AMO case: clause ∈ (amo (indices.map Var.Rep)).clauses = [[¬Rep(x), ¬Rep(y)] | x ≠ y]
    -- The amo clauses are: for each pair (x, y) with x ≠ y in the list, clause = [¬x, ¬y]
    simp only [SAT.amo] at hAmo
    -- hAmo : clause ∈ (pairs.filter (fun p => p.1 ≠ p.2)).map (fun p => [Lit.neg p.1, Lit.neg p.2])
    rw [List.mem_map] at hAmo
    obtain ⟨⟨x, y⟩, hPairMem, hClauseEq⟩ := hAmo
    rw [List.mem_filter] at hPairMem
    obtain ⟨hPairInPairs, hNeq⟩ := hPairMem
    -- hPairInPairs : (x, y) ∈ (indices.map Var.Rep).flatMap
    --   (fun x => (indices.map Var.Rep).map ...)
    rw [List.mem_flatMap] at hPairInPairs
    obtain ⟨x', hx'Mem, hPairInMap⟩ := hPairInPairs
    rw [List.mem_map] at hPairInMap
    obtain ⟨y', hy'Mem, hPairEq⟩ := hPairInMap
    simp only [Prod.mk.injEq] at hPairEq
    obtain ⟨hxEq, hyEq⟩ := hPairEq
    subst hxEq hyEq hClauseEq
    -- Now we have clause = [¬x', ¬y'] where x', y' ∈ indices.map Var.Rep and x' ≠ y'
    -- x' = Var.Rep i₁, y' = Var.Rep i₂ for some i₁, i₂ in indices
    rw [List.mem_map] at hx'Mem hy'Mem
    obtain ⟨i₁, hi₁Mem, hx'⟩ := hx'Mem
    obtain ⟨i₂, hi₂Mem, hy'⟩ := hy'Mem
    subst hx' hy'
    -- i₁ ≠ i₂ (because Var.Rep i₁ ≠ Var.Rep i₂ and Var.Rep is injective)
    have hNeqIdx : i₁ ≠ i₂ := by
      intro h
      subst h
      simp at hNeq
    -- Both i₁ and i₂ have value v (since they're in valueIndices b v)
    have hi₁Val : b.values.get i₁ = v := by
      simp only [valueIndices, List.mem_filterMap, List.mem_finRange, true_and] at hi₁Mem
      obtain ⟨_, h⟩ := hi₁Mem
      split at h <;> simp_all
    have hi₂Val : b.values.get i₂ = v := by
      simp only [valueIndices, List.mem_filterMap, List.mem_finRange, true_and] at hi₂Mem
      obtain ⟨_, h⟩ := hi₂Mem
      split at h <;> simp_all
    -- At most one of them is the findValueIndex v
    -- So at least one of isRepresentative i₁ or isRepresentative i₂ is false
    by_cases hCase : i₁ = b.findValueIndex v
    · -- i₁ is the representative, so i₂ is not
      have hi₂NotRep : isRepresentative i₂ = false := by
        have hNe₂ : i₂ ≠ b.findValueIndex v := fun h => hNeqIdx (hCase.trans h.symm)
        exact isRepresentative_false_of_ne_findValueIndex i₂ v hEx hi₂Val hNe₂
      have hAssignFalse : assignmentOf b M hFits (Var.Rep i₂) = false := by
        simp only [assignmentOf, hi₂NotRep]
      -- The clause [¬Rep i₁, ¬Rep i₂] is satisfied because Rep i₂ = false
      exact SAT.Clause.eval_true_of_neg_mem (assignmentOf b M hFits) _
        (Var.Rep i₂) (List.mem_cons.mpr (Or.inr List.mem_cons_self)) hAssignFalse
    · -- i₁ is not the representative
      have hi₁NotRep : isRepresentative i₁ = false :=
        isRepresentative_false_of_ne_findValueIndex i₁ v hEx hi₁Val hCase
      have hAssignFalse : assignmentOf b M hFits (Var.Rep i₁) = false := by
        simp only [assignmentOf, hi₁NotRep]
      -- The clause [¬Rep i₁, ¬Rep i₂] is satisfied because Rep i₁ = false
      exact SAT.Clause.eval_true_of_neg_mem (assignmentOf b M hFits) _
        (Var.Rep i₁) List.mem_cons_self hAssignFalse

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If MinQ is true, then Rep is true (by definition of isMinimalQuorum). -/
private lemma minQ_implies_rep
    {b : Bounds S}
    (M : Model S (Fin b.nParticipants))
    (i : b.valIx) (Q : Finset (Fin b.nParticipants))
    (hMinQ : isMinimalQuorum M i Q = true) :
    isRepresentative i = true := by
  unfold isMinimalQuorum at hMinQ
  simp only [decide_eq_true_eq] at hMinQ
  -- hMinQ : isRepresentative i = true ∧ _ ∧ _
  exact hMinQ.1

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: gatingClauses are satisfied by assignmentOf. -/
lemma gating_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (clause : SAT.Clause (Var b))
    (hMem : clause ∈ gatingClauses b) :
    SAT.Clause.eval (assignmentOf b M hFits) clause = true := by
  -- gatingClauses: [¬MinQ(i,Q), Rep(i)]
  -- The clause is satisfied if MinQ(i,Q) = false OR Rep(i) = true
  -- By definition, isMinimalQuorum includes isRepresentative as a conjunct,
  -- so if MinQ = true then Rep = true.
  simp only [gatingClauses, List.mem_flatMap, List.mem_map] at hMem
  obtain ⟨i, _, v, hvMem, hClause⟩ := hMem
  -- v ∈ allMinQ b i, so v = MinQ i Q for some Q
  simp only [Var.allMinQ, List.mem_map, List.mem_finRange, true_and] at hvMem
  obtain ⟨mask, hV⟩ := hvMem
  subst hV hClause
  -- Now clause = [Lit.neg (MinQ i Q), Lit.pos (Rep i)]
  -- The clause is a disjunction: ¬MinQ(i,Q) ∨ Rep(i)
  -- Satisfied if MinQ is false OR Rep is true
  -- By design, isMinimalQuorum includes isRepresentative as part of its definition
  by_cases hMinQ : isMinimalQuorum M i (bitmaskToFinset b.nParticipants mask) = true
  · -- MinQ is true, so Rep must also be true
    have hRep := minQ_implies_rep M i _ hMinQ
    -- The clause [¬MinQ, Rep] evaluates to true when Rep = true
    apply SAT.Clause.eval_true_of_pos_mem
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))
    · simp only [assignmentOf, hRep]
  · -- MinQ is false, so ¬MinQ is true and the clause is satisfied
    have h := Bool.eq_false_iff.mpr hMinQ
    have hFalse :
        assignmentOf b M hFits (Var.MinQ i (bitmaskToFinset b.nParticipants mask))
        = false := by
      simp only [assignmentOf, h]
    exact SAT.Clause.eval_true_of_neg_mem (assignmentOf b M hFits) _
      (Var.MinQ i (bitmaskToFinset b.nParticipants mask)) List.mem_cons_self hFalse

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: condAloClauses are satisfied by assignmentOf. -/
lemma condAlo_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (clause : SAT.Clause (Var b))
    (hMem : clause ∈ condAloClauses b) :
    SAT.Clause.eval (assignmentOf b M hFits) clause = true := by
  -- condAloClauses: [¬Rep(i)] ++ MinQ vars
  -- If Rep(i) = false, clause is satisfied (first literal true)
  -- If Rep(i) = true, need some MinQ(i,Q) = true for some Q
  simp only [condAloClauses, List.mem_map] at hMem
  obtain ⟨i, _, hClause⟩ := hMem
  subst hClause
  -- Now clause = SAT.Lit.neg (Var.Rep i) :: (Var.allMinQ b i).map SAT.Lit.pos
  by_cases hRep : isRepresentative i = true
  · -- Rep(i) = true, need to find a MinQ(i,Q) that is true
    obtain ⟨Q, hMinQ⟩ := exists_minQ_for_representative M i hRep
    obtain ⟨mask, hMask⟩ := minQ_has_bitmask M i Q hMinQ
    -- Q = bitmaskToFinset mask, so Var.MinQ i Q is in allMinQ
    apply SAT.Clause.eval_true_of_pos_mem
    · · apply List.mem_cons.mpr
        · right
          simp only [List.mem_map]
          use Var.MinQ i Q
          constructor
          · simp only [Var.allMinQ, List.mem_map, List.mem_finRange, true_and]
            exact ⟨mask, hMask.symm ▸ rfl⟩
          · rfl
    · · simp only [assignmentOf, hMinQ]
  · -- Rep(i) = false, first literal ¬Rep(i) is true
    have h := Bool.eq_false_iff.mpr hRep
    have hFalse : assignmentOf b M hFits (Var.Rep i) = false := by
      simp only [assignmentOf, h]
    exact SAT.Clause.eval_true_of_neg_mem (assignmentOf b M hFits) _
      (Var.Rep i) List.mem_cons_self hFalse

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: withinIndexClauses are satisfied by assignmentOf. -/
lemma withinIndex_satisfied
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (clause : SAT.Clause (Var b))
    (hMem : clause ∈ withinIndexClauses b) :
    SAT.Clause.eval (assignmentOf b M hFits) clause = true := by
  -- withinIndexClauses has three types of clauses per index:
  -- 1. Minimality: [¬MinQ(i,Q1), ¬MinQ(i,Q2)] when Q2 ⊂ Q1
  -- 2. Intersection: [¬MinQ(i,Q1), ¬MinQ(i,Q2)] when Q1 ∩ Q2 = ∅
  -- 3. No-empty: [¬MinQ(i,∅)]
  simp only [withinIndexClauses, List.mem_flatMap] at hMem
  obtain ⟨i, _, hClauseInner⟩ := hMem
  -- The clause is in minimalityClauses ++ intersectionClauses ++ noEmptyClauses for index i
  simp only [List.mem_append] at hClauseInner
  obtain ((hMin | hInter) | hEmpty) := hClauseInner
  · -- Minimality clause: [¬MinQ(i,Q1), ¬MinQ(i,Q2)] where Q2 ⊂ Q1
    -- If both MinQ(i,Q1) and MinQ(i,Q2) are true, Q1 and Q2 are both minimal quorums
    -- But Q2 ⊂ Q1 means Q2 is a strict subset of Q1, contradicting Q1's minimality
    simp only [List.mem_flatMap, List.mem_filterMap] at hMin
    obtain ⟨q1, hQ1mem, q2, hQ2mem, hMatch⟩ := hMin
    -- q1, q2 are MinQ variables from allMinQ
    simp only [Var.allMinQ, List.mem_map, List.mem_finRange, true_and] at hQ1mem hQ2mem
    obtain ⟨mask1, hQ1eq⟩ := hQ1mem
    obtain ⟨mask2, hQ2eq⟩ := hQ2mem
    subst hQ1eq hQ2eq
    -- Now q1 = MinQ i Q1, q2 = MinQ i Q2 where Q1, Q2 are bitmask-derived sets
    set Q1 := bitmaskToFinset b.nParticipants mask1.val with hQ1def
    set Q2 := bitmaskToFinset b.nParticipants mask2.val with hQ2def
    -- The match is: (match q1, q2 with ...) = some clause
    -- After substituting q1 = MinQ i Q1, q2 = MinQ i Q2, it becomes:
    -- (if Q2 ⊂ Q1 ∧ Q2 ≠ Q1 then some [...] else none) = some clause
    -- Use by_cases on the condition
    by_cases hCond : Q2 ⊂ Q1 ∧ Q2 ≠ Q1
    · -- Condition holds: clause = [¬MinQ(i,Q1), ¬MinQ(i,Q2)]
      simp only [if_pos hCond, Option.some.injEq] at hMatch
      -- hMatch : [...] = clause, rewrite to work with the clause
      rw [← hMatch]
      -- hCond : Q2 ⊂ Q1 ∧ Q2 ≠ Q1
      -- clause = [¬MinQ(i,Q1), ¬MinQ(i,Q2)]
      -- Clause is satisfied if at least one of MinQ(i,Q1) or MinQ(i,Q2) is false
      by_cases hMinQ1 : isMinimalQuorum M i Q1 = true
      · -- MinQ(i,Q1) = true, so Q1 is a minimal quorum
        unfold isMinimalQuorum at hMinQ1
        simp only [decide_eq_true_eq] at hMinQ1
        obtain ⟨_, hQ1Quorum, hQ1Min⟩ := hMinQ1
        -- Q2 ⊂ Q1 means Q2 ⊆ Q1 and Q2 ≠ Q1
        -- By Q1's minimality, if Q2 is a quorum and Q2 ⊆ Q1, then Q2 = Q1
        -- So Q2 cannot be a minimal quorum
        have hQ2NotMin : isMinimalQuorum M i Q2 = false := by
          unfold isMinimalQuorum
          simp only [decide_eq_false_iff_not, not_and]
          intro _ hQ2Quorum
          have hQ2Sub : Q2 ⊆ Q1 := hCond.1.1
          have hQ2Ne : Q2 ≠ Q1 := hCond.2
          have := hQ1Min Q2 hQ2Quorum hQ2Sub
          exact absurd this hQ2Ne
        have hFalse : assignmentOf b M hFits (Var.MinQ i Q2) = false := by
          simp only [assignmentOf, hQ2NotMin]
        exact SAT.Clause.eval_true_of_neg_mem (assignmentOf b M hFits) _
          (Var.MinQ i Q2) (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))) hFalse
      · -- MinQ(i,Q1) = false, first literal is true
        have hFalse : assignmentOf b M hFits (Var.MinQ i Q1) = false := by
          simp only [assignmentOf, Bool.eq_false_iff.mpr hMinQ1]
        exact SAT.Clause.eval_true_of_neg_mem (assignmentOf b M hFits) _
          (Var.MinQ i Q1) List.mem_cons_self hFalse
    · -- Condition doesn't hold: none = some clause, contradiction
      simp only [if_neg hCond] at hMatch
      exact Option.noConfusion hMatch
  · -- Intersection clause: [¬MinQ(i,Q1), ¬MinQ(i,Q2)] where Q1 ∩ Q2 = ∅
    -- If both are true, Q1 and Q2 are minimal quorums with empty intersection
    -- But semifilters have pairwise intersection property: all quorums intersect
    simp only [List.mem_flatMap, List.mem_filterMap] at hInter
    obtain ⟨q1, hQ1mem, q2, hQ2mem, hMatch⟩ := hInter
    -- q1, q2 are MinQ variables from allMinQ
    simp only [Var.allMinQ, List.mem_map, List.mem_finRange, true_and] at hQ1mem hQ2mem
    obtain ⟨mask1, hQ1eq⟩ := hQ1mem
    obtain ⟨mask2, hQ2eq⟩ := hQ2mem
    subst hQ1eq hQ2eq
    -- Now q1 = MinQ i Q1, q2 = MinQ i Q2 where Q1, Q2 are bitmask-derived sets
    set Q1 := bitmaskToFinset b.nParticipants mask1.val with hQ1def
    set Q2 := bitmaskToFinset b.nParticipants mask2.val with hQ2def
    -- Use by_cases on the condition
    by_cases hCond : (Q1 ∩ Q2).card = 0 ∧ Q1 ≠ Q2
    · -- Condition holds: clause = [¬MinQ(i,Q1), ¬MinQ(i,Q2)]
      simp only [if_pos hCond, Option.some.injEq] at hMatch
      rw [← hMatch]
      -- hCond : (Q1 ∩ Q2).card = 0 ∧ Q1 ≠ Q2
      by_cases hMinQ1 : isMinimalQuorum M i Q1 = true
      · -- Q1 is a minimal quorum
        by_cases hMinQ2 : isMinimalQuorum M i Q2 = true
        · -- Both are minimal quorums - derive contradiction from semifilter intersection
          unfold isMinimalQuorum at hMinQ1 hMinQ2
          simp only [decide_eq_true_eq] at hMinQ1 hMinQ2
          obtain ⟨_, hQ1Quorum, _⟩ := hMinQ1
          obtain ⟨_, hQ2Quorum, _⟩ := hMinQ2
          -- Q1, Q2 are quorums with (Q1 ∩ Q2).card = 0
          let L := M.learner (b.values.get i)
          have hIntersect := L.pairwiseInter hQ1Quorum hQ2Quorum
          -- pairwiseIntersecting means (Q1 ∩ Q2).Nonempty
          simp only at hIntersect
          obtain ⟨p, hpQ1, hpQ2⟩ := hIntersect
          -- But (Q1 ∩ Q2).card = 0 means the intersection is empty
          have hCardZero : (Q1 ∩ Q2).card = 0 := hCond.1
          rw [Finset.card_eq_zero] at hCardZero
          have hpIn : p ∈ (Q1 ∩ Q2 : Finset _) := Finset.mem_inter.mpr ⟨hpQ1, hpQ2⟩
          rw [hCardZero] at hpIn
          simp at hpIn
        · -- Q2 not minimal, second literal true
          have hFalse : assignmentOf b M hFits (Var.MinQ i Q2) = false := by
            simp only [assignmentOf, Bool.eq_false_iff.mpr hMinQ2]
          exact SAT.Clause.eval_true_of_neg_mem (assignmentOf b M hFits) _
            (Var.MinQ i Q2) (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))) hFalse
      · -- Q1 not minimal, first literal true
        have hFalse : assignmentOf b M hFits (Var.MinQ i Q1) = false := by
          simp only [assignmentOf, Bool.eq_false_iff.mpr hMinQ1]
        exact SAT.Clause.eval_true_of_neg_mem (assignmentOf b M hFits) _
          (Var.MinQ i Q1) List.mem_cons_self hFalse
    · -- Condition doesn't hold: none = some clause, contradiction
      simp only [if_neg hCond] at hMatch
      exact Option.noConfusion hMatch
  · -- No-empty clause: [¬MinQ(i,∅)]
    -- isMinimalQuorum M i ∅ = false because empty set is not a quorum
    simp only [List.mem_filterMap] at hEmpty
    obtain ⟨q, hQmem, hMatch⟩ := hEmpty
    -- q is a MinQ variable from allMinQ
    simp only [Var.allMinQ, List.mem_map, List.mem_finRange, true_and] at hQmem
    obtain ⟨mask, hQeq⟩ := hQmem
    subst hQeq
    set Q := bitmaskToFinset b.nParticipants mask.val with hQdef
    -- Use by_cases on the condition
    by_cases hCard : Q.card = 0
    · -- Condition holds: clause = [¬MinQ(i,Q)] where Q is empty
      simp only [if_pos hCard, Option.some.injEq] at hMatch
      rw [← hMatch]
      -- Q.card = 0 means Q = ∅
      rw [Finset.card_eq_zero] at hCard
      -- Q (= ∅) is not a quorum in any semifilter (quorums are nonempty by intersection property)
      have hNotMin : isMinimalQuorum M i Q = false := by
        unfold isMinimalQuorum
        simp only [decide_eq_false_iff_not]
        -- Goal: ¬(isRepresentative i ∧ ↑Q ∈ L.quorums ∧ ...)
        -- We'll show ↑Q ∈ L.quorums is impossible because Q = ∅
        intro ⟨_, hQQuorum, _⟩
        -- Q (= ∅) in quorums contradicts that quorums are nonempty
        let L := M.learner (b.values.get i)
        -- Get any quorum from L.nonempty
        obtain ⟨O, hO⟩ := L.nonempty
        -- O and Q (= ∅) must intersect by pairwiseIntersecting
        have hInter := L.pairwiseInter hQQuorum hO
        -- But ∅ ≬ O is False
        simp only [hCard, Finset.coe_empty, Semifilter.intersects_empty_left] at hInter
      have hFalse : assignmentOf b M hFits (Var.MinQ i Q) = false := by
        simp only [assignmentOf, hNotMin]
      exact SAT.Clause.eval_true_of_neg_mem (assignmentOf b M hFits) _
        (Var.MinQ i Q) List.mem_cons_self hFalse
    · -- Condition doesn't hold: none = some clause, contradiction
      simp only [if_neg hCard] at hMatch
      exact Option.noConfusion hMatch

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- assignmentOf satisfies cnfLearners. -/
theorem assignmentOf_satisfies_cnfLearners
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M) :
    (cnfLearners b).eval (assignmentOf b M hFits) = true := by
  -- cnfLearners = repUnit ++ repExo ++ gating ++ condAlo ++ withinIndex
  -- All clauses are in one of the five lists
  unfold cnfLearners
  simp only [SAT.CNF.eval, List.all_eq_true]
  intro clause hMem
  simp only [List.mem_append] at hMem
  obtain ((((h1|h2)|h3)|h4)|h5) := hMem
  · exact repUnit_satisfied hFits clause h1
  · exact repExo_satisfied hFits clause h2
  · exact gating_satisfied hFits clause h3
  · exact condAlo_satisfied hFits clause h4
  · exact withinIndex_satisfied hFits clause h5

/-! ## Main WF Theorem -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The assignment constructed from M satisfies cnfWellFormed. -/
theorem assignmentOf_satisfies_wf
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M) :
    (cnfWellFormed b).eval (assignmentOf b M hFits) = true := by
  rw [cnfWellFormed_eval_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact assignmentOf_satisfies_cnfAcyclic hFits
  · exact assignmentOf_satisfies_cnfReach hFits
  · exact assignmentOf_satisfies_cnfEdge hFits
  · exact assignmentOf_satisfies_cnfLearners hFits
  · exact assignmentOf_satisfies_cnfLevel_monotone hFits
  · exact assignmentOf_satisfies_cnfLevel_decrease hFits
  · exact assignmentOf_satisfies_cnfLevel_max_bound hFits
  · exact assignmentOf_satisfies_cnfMemRequiresFuel hFits
  · exact assignmentOf_satisfies_cnfExists hFits
  · exact assignmentOf_satisfies_cnfExists_back hFits
  · exact assignmentOf_satisfies_cnfSeq hFits

/-- Extract WF proof from the evaluation. -/
noncomputable def wfOf
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M) :
    WF b (assignmentOf b M hFits) :=
  assignmentOf_satisfies_wf b M hFits

end Encoding
