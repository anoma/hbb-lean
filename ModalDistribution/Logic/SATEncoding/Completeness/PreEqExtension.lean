import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.PreEqEncoding
import ModalDistribution.Logic.SATEncoding.PreEqGadgets
import ModalDistribution.Logic.SATEncoding.TseytinGadgets
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf
import ModalDistribution.Logic.SATEncoding.Completeness.WFProof

/-!
# PreEq Extension for Completeness

This file provides the machinery to extend `assignmentOf` to satisfy `addPreEqFrom` clauses.

## Approach

We define an extension `extendForPreEq` that sets Fresh variables according to their
semantic meaning in the Tseytin encoding. The extension is defined by simulating the
encoding process: for each Fresh variable allocated, we compute what value it should
have based on the semantic values of its inputs.

## Fresh Variable Structure in addPreEqFrom

For a single pair (H0, H'), `addPreEqPair_core` allocates Fresh vars in this order:
1. For each w in allWorlds: mkDw allocates Fresh vars (mkY vars + mkBigOrIff var)
2. For each w in allWorlds: mkOw allocates one Fresh var
3. For each w in allWorlds (reverse dir): mkDw + mkOw again
4. One base Fresh var (set to true)
5. For each obligation: preEqAccStep allocates one Fresh var
6. addPreEqExpose uses the final accumulated var (no new allocation)

The key insight: each Fresh var's semantic value is determined by the semantic values
of Mem and PreEq variables, which are correctly set by assignmentOf.
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Semantic Value Definitions

These compute what each internal Fresh variable should be set to. -/

/-- Semantic value for mkY gadget: y ↔ (Mem(t', w') ∧ PreEq(w.ti, w'.ti)). -/
noncomputable def semY
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (t' : b.times) (w w' : WId b) : Bool :=
  worldInPrehistory ev t' w' && preEqAt ev w.ti w'.ti

/-- Semantic value for mkDw gadget: d ↔ ∃ matching w', y_{w,w'}. -/
noncomputable def semDw
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (t' : b.times) (w : WId b) : Bool :=
  (WId.allWorlds b).any fun w' =>
    if sameSig b w w' then semY ev t' w w' else false

/-- Semantic value for mkOw gadget: o ↔ (¬Mem(t, w) ∨ d). -/
noncomputable def semOw
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (t t' : b.times) (w : WId b) : Bool :=
  !(worldInPrehistory ev t w) || semDw ev t' w

/-- Semantic value for obligation chain: all worlds in t have matches in t'. -/
noncomputable def semObligationChain
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (t t' : b.times) : Bool :=
  (WId.allWorlds b).all fun w => semOw ev t t' w

/-- Semantic value for full PreEq check: both directions. -/
noncomputable def semPreEqFull
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (t t' : b.times) : Bool :=
  semObligationChain ev t t' && semObligationChain ev t' t

/-! ## Semantic Correspondence

Key lemmas connecting the σ₀ = assignmentOf values to the semantic definitions.
These are definitionally equal but need explicit Bool annotations to avoid Prop coercion. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- semY expressed using σ₀ values equals semY definition. -/
lemma semY_eq_sigma
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (t' : b.times) (w w' : WId b) :
    let σ₀ := assignmentOf b M hFits
    let ev := hFits.view
    (σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti) : Bool) = (semY ev t' w w' : Bool) := rfl

omit [DecidableEq S.AtomicPredType] in
/-- semDw expressed using σ₀ values equals semDw definition. -/
lemma semDw_eq_sigma
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (t' : b.times) (w : WId b) :
    let σ₀ := assignmentOf b M hFits
    let ev := hFits.view
    ((WId.allWorlds b).any (fun w' =>
      if sameSig b w w' then σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti) else false) : Bool) =
    (semDw ev t' w : Bool) := by
  simp only [semDw]
  congr 1

omit [DecidableEq S.AtomicPredType] in
/-- semOw expressed using σ₀ and dVal equals semOw definition. -/
lemma semOw_eq_sigma
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (t t' : b.times) (w : WId b)
    (dVal : Bool)
    (hDVal : dVal = semDw hFits.view t' w) :
    let σ₀ := assignmentOf b M hFits
    let ev := hFits.view
    (!(σ₀ (Var.Mem t w)) || dVal : Bool) = (semOw ev t t' w : Bool) := by
  simp only [semOw, assignmentOf, hDVal]

/-! ## Key Lemma: Semantic PreEq equals preEqAt

This is the central lemma connecting the semantic computation (semPreEqFull) to
the definitional equality check (preEqAt). Both compute histEq via different paths. -/

omit [DecidableEq (Signature.Value S)] [DecidableEq S.AtomicPredType] in
/-- Forward direction: semObligationChain implies the histEq forward condition. -/
lemma semObligationChain_implies_histEq_fwd
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (t t' : b.times)
    (hReach : prehistoryOfTime hFits.view t ∈ reachablePreHistories M.history.val)
    (hReach' : prehistoryOfTime hFits.view t' ∈ reachablePreHistories M.history.val)
    (hChain : semObligationChain hFits.view t t' = true) :
    ∀ sem ∈ prehistoryOfTime hFits.view t,
      ∃ sem' ∈ prehistoryOfTime hFits.view t', PreHistory.worldEq sem sem' := by
  classical
  let ev := hFits.view
  intro sem hSemMem
  have hSemReach : sem.time ∈ reachablePreHistories M.history.val :=
    time_mem_reachablePreHistories_of_mem_history hReach hSemMem
  let w : WId b := ⟨sem.place, b.encodeMaybeEvent sem.event, ev.timeIndexOf sem.time⟩
  have hInPre : worldInPrehistory ev t w = true := by
    simp only [worldInPrehistory, decide_eq_true_eq]
    exact ⟨sem, hSemMem, rfl, b.decodeMaybeEvent_encodeMaybeEvent sem.event, rfl⟩
  have hOw := List.all_eq_true.mp hChain w (WId.mem_allWorlds b w)
  simp only [semOw] at hOw
  rw [hInPre] at hOw
  simp only [Bool.not_true, Bool.false_or] at hOw
  simp only [semDw, List.any_eq_true] at hOw
  obtain ⟨w', _, hSameSigY⟩ := hOw
  by_cases hSameSig : sameSig b w w' = true
  · simp only [hSameSig, ↓reduceIte, semY, Bool.and_eq_true] at hSameSigY
    obtain ⟨hInPre', hPreEq⟩ := hSameSigY
    simp only [worldInPrehistory, decide_eq_true_eq] at hInPre'
    obtain ⟨sem', hSem'Mem, hPlace', hEvent', hTime'⟩ := hInPre'
    use sem', hSem'Mem
    -- Use sameSig_true_iff to get w'.p = w.p and decodeMaybeEvent w'.ei = decodeMaybeEvent w.ei
    obtain ⟨hPEq, hEvEq⟩ := sameSig_true_iff hSameSig
    rw [PreHistory.worldEq_spec]
    refine ⟨?_, ?_, ?_⟩
    · -- place equality: sem.place = sem'.place
      -- w.p = sem.place (by def), w'.p = sem'.place (from hPlace'), w'.p = w.p (from hPEq)
      calc sem.place = w.p := rfl
        _ = w'.p := hPEq.symm
        _ = sem'.place := hPlace'.symm
    · -- event equality: sem.event = sem'.event
      -- w.ei = encodeMaybeEvent sem.event (by def), hEvent' : decodeMaybeEvent w'.ei = sem'.event
      -- hEvEq : decodeMaybeEvent w'.ei = decodeMaybeEvent w.ei
      rw [← hEvent', hEvEq, b.decodeMaybeEvent_encodeMaybeEvent]
    · -- histEq on times
      simp only [preEqAt, decide_eq_true_eq] at hPreEq
      have hSem'Reach : sem'.time ∈ reachablePreHistories M.history.val :=
        time_mem_reachablePreHistories_of_mem_history hReach' hSem'Mem
      have hEq1 : prehistoryOfTime ev (ev.timeIndexOf sem.time) = sem.time :=
        prehistoryOfTime_of_reachable ev hSemReach
      have hEq2 : prehistoryOfTime ev (ev.timeIndexOf sem'.time) = sem'.time :=
        prehistoryOfTime_of_reachable ev hSem'Reach
      simp only [w] at hPreEq
      rw [hEq1, ← hTime', hEq2] at hPreEq
      exact hPreEq
  · -- hSameSig : ¬sameSig b w w' = true, so the `if` in hSameSigY reduces to `false = true`
    simp only [if_neg hSameSig] at hSameSigY
    exact absurd hSameSigY Bool.false_ne_true

omit [DecidableEq (Signature.Value S)] [DecidableEq S.AtomicPredType] in
/-- Backward direction: histEq condition implies semObligationChain. -/
lemma histEq_fwd_implies_semObligationChain
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (t t' : b.times)
    (hReach : prehistoryOfTime hFits.view t ∈ reachablePreHistories M.history.val)
    (hReach' : prehistoryOfTime hFits.view t' ∈ reachablePreHistories M.history.val)
    (hFwd : ∀ sem ∈ prehistoryOfTime hFits.view t,
      ∃ sem' ∈ prehistoryOfTime hFits.view t', PreHistory.worldEq sem sem') :
    semObligationChain hFits.view t t' = true := by
  classical
  let ev := hFits.view
  simp only [semObligationChain, List.all_eq_true]
  intro w _
  simp only [semOw]
  by_cases hInPre : worldInPrehistory ev t w = true
  · rw [hInPre]
    simp only [Bool.not_true, Bool.false_or]
    simp only [worldInPrehistory, decide_eq_true_eq] at hInPre
    obtain ⟨sem, hSemMem, hPlace, hEvent, hTime⟩ := hInPre
    obtain ⟨sem', hSem'Mem, hWorldEq⟩ := hFwd sem hSemMem
    rw [PreHistory.worldEq_spec] at hWorldEq
    obtain ⟨hPlaceEq, hEventEq, hTimeEq⟩ := hWorldEq
    let w' : WId b := ⟨sem'.place, b.encodeMaybeEvent sem'.event, ev.timeIndexOf sem'.time⟩
    simp only [semDw, List.any_eq_true]
    use w', WId.mem_allWorlds b w'
    have hSameSig : sameSig b w w' = true := by
      unfold sameSig
      simp only [beq_iff_eq, w']
      split_ifs with hP
      · rw [b.decodeMaybeEvent_encodeMaybeEvent sem'.event, ← hEventEq, hEvent]
        cases sem.event <;> simp
      · exfalso
        apply hP
        rw [← hPlace, hPlaceEq]
    simp only [hSameSig, ↓reduceIte, semY, Bool.and_eq_true]
    constructor
    · simp only [worldInPrehistory, decide_eq_true_eq]
      exact ⟨sem', hSem'Mem, rfl, b.decodeMaybeEvent_encodeMaybeEvent sem'.event, rfl⟩
    · simp only [preEqAt, decide_eq_true_eq, w']
      have hSemReach : sem.time ∈ reachablePreHistories M.history.val :=
        time_mem_reachablePreHistories_of_mem_history hReach hSemMem
      have hSem'Reach : sem'.time ∈ reachablePreHistories M.history.val :=
        time_mem_reachablePreHistories_of_mem_history hReach' hSem'Mem
      rw [← hTime, prehistoryOfTime_of_reachable ev hSemReach,
          prehistoryOfTime_of_reachable ev hSem'Reach]
      exact hTimeEq
  · -- hInPre : ¬worldInPrehistory ev t w = true, so !worldInPrehistory = true
    have hInPreFalse : worldInPrehistory ev t w = false := Bool.eq_false_iff.mpr hInPre
    rw [hInPreFalse]
    simp only [Bool.not_false, Bool.true_or]

omit [DecidableEq (Signature.Value S)] [DecidableEq S.AtomicPredType] in
/-- If prehistoryOfTime returns empty, semObligationChain from that time is true.
    This is because worldInPrehistory returns false for all worlds in an empty prehistory,
    so semOw = !false || _ = true for all worlds. -/
lemma semObligationChain_of_empty
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (t t' : b.times)
    (hEmpty : prehistoryOfTime ev t = PreHistory.empty) :
    semObligationChain ev t t' = true := by
  simp only [semObligationChain, List.all_eq_true]
  intro w _
  simp only [semOw]
  -- worldInPrehistory ev t w = false since prehistoryOfTime ev t is empty
  have hNotIn : worldInPrehistory ev t w = false := by
    simp only [worldInPrehistory, decide_eq_false_iff_not, not_exists, not_and]
    intro sem hSemMem _ _ _
    rw [hEmpty] at hSemMem
    exact PreHistory.not_mem_empty hSemMem
  rw [hNotIn]
  simp only [Bool.not_false, Bool.true_or]

omit [DecidableEq (Signature.Value S)] [DecidableEq S.AtomicPredType] in
/-- If prehistoryOfTime returns empty for t but non-empty for t', then
    semObligationChain from t' to t is false. -/
lemma semObligationChain_to_empty_of_nonempty
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (t t' : b.times)
    (hEmpty : prehistoryOfTime ev t = PreHistory.empty)
    (hNonempty : ∃ sem, sem ∈ prehistoryOfTime ev t') :
    semObligationChain ev t' t = false := by
  obtain ⟨sem, hSemMem⟩ := hNonempty
  -- Need to show (WId.allWorlds b).all (semOw ev t' t) = false
  -- This means some world w has semOw ev t' t w = false
  simp only [semObligationChain]
  rw [Bool.eq_false_iff]
  intro hAll
  -- Construct w from sem
  let w : WId b := ⟨sem.place, b.encodeMaybeEvent sem.event, ev.timeIndexOf sem.time⟩
  have hOw := List.all_eq_true.mp hAll w (WId.mem_allWorlds b w)
  simp only [semOw] at hOw
  -- worldInPrehistory ev t' w = true since sem is in t'
  have hIn : worldInPrehistory ev t' w = true := by
    simp only [worldInPrehistory, decide_eq_true_eq]
    exact ⟨sem, hSemMem, rfl, b.decodeMaybeEvent_encodeMaybeEvent sem.event, rfl⟩
  rw [hIn] at hOw
  simp only [Bool.not_true, Bool.false_or] at hOw
  -- semDw ev t w = true, but this is impossible since prehistoryOfTime ev t is empty
  simp only [semDw, List.any_eq_true] at hOw
  obtain ⟨w', _, hSameSigY⟩ := hOw
  by_cases hSameSig : sameSig b w w' = true
  · simp only [hSameSig, ↓reduceIte, semY, Bool.and_eq_true] at hSameSigY
    obtain ⟨hInPre', _⟩ := hSameSigY
    simp only [worldInPrehistory, decide_eq_true_eq] at hInPre'
    obtain ⟨sem', hSem'Mem, _, _, _⟩ := hInPre'
    rw [hEmpty] at hSem'Mem
    exact PreHistory.not_mem_empty hSem'Mem
  · simp only [if_neg hSameSig] at hSameSigY
    exact absurd hSameSigY Bool.false_ne_true

omit [DecidableEq (Signature.Value S)] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: if no element is in a prehistory, it equals empty -/
lemma prehistory_eq_empty_of_forall_not_mem
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (t : b.times)
    (h : ∀ sem, sem ∉ prehistoryOfTime ev t) :
    prehistoryOfTime ev t = PreHistory.empty := by
  cases hpH : prehistoryOfTime ev t with
  | mk l =>
    simp only [PreHistory.empty]
    congr
    by_contra hne
    have ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hne
    have : x ∈ PreHistory.mk l := PreHistory.mem_mk.mpr hx
    rw [← hpH] at this
    exact h x this

omit [DecidableEq (Signature.Value S)] [DecidableEq S.AtomicPredType] in
/-- The semantic PreEq computation equals the definitional preEqAt check.
    This holds for all time indices, including non-reachable ones. -/
lemma semPreEqFull_eq_preEqAt
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (t t' : b.times) :
    semPreEqFull hFits.view t t' = preEqAt hFits.view t t' := by
  classical
  let ev := hFits.view
  -- Case split on whether prehistories are empty
  by_cases hEmptyT : prehistoryOfTime ev t = PreHistory.empty
  · -- t is empty (non-reachable)
    by_cases hEmptyT' : prehistoryOfTime ev t' = PreHistory.empty
    · -- Both empty: both sides are true
      simp only [semPreEqFull, preEqAt]
      rw [semObligationChain_of_empty ev t t' hEmptyT,
          semObligationChain_of_empty ev t' t hEmptyT']
      simp only [Bool.and_self]
      rw [hEmptyT, hEmptyT']
      rw [eq_comm, decide_eq_true_eq]
      exact PreHistory.histEq_refl _
    · -- t empty, t' non-empty: both sides are false
      have hNonempty : ∃ sem, sem ∈ prehistoryOfTime ev t' := by
        by_contra h
        push_neg at h
        exact hEmptyT' (prehistory_eq_empty_of_forall_not_mem ev t' h)
      simp only [semPreEqFull, preEqAt]
      rw [semObligationChain_of_empty ev t t' hEmptyT,
          semObligationChain_to_empty_of_nonempty ev t t' hEmptyT hNonempty]
      simp only [Bool.true_and]
      rw [hEmptyT]
      rw [eq_comm, decide_eq_false_iff_not, PreHistory.histEq_spec]
      intro ⟨_, hBwd⟩
      obtain ⟨sem, hSemMem⟩ := hNonempty
      obtain ⟨w, hW, _⟩ := hBwd sem hSemMem
      exact PreHistory.not_mem_empty hW
  · -- t is non-empty (reachable)
    have hNonemptyT : ∃ sem, sem ∈ prehistoryOfTime ev t := by
      by_contra h
      push_neg at h
      exact hEmptyT (prehistory_eq_empty_of_forall_not_mem ev t h)
    obtain ⟨pH, hReach, _, hEq⟩ := prehistoryAt_nonempty_implies_reachable ev t hNonemptyT
    have hReachT : prehistoryOfTime ev t ∈ reachablePreHistories M.history.val := by
      rw [prehistoryOfTime, hEq]
      exact hReach
    by_cases hEmptyT' : prehistoryOfTime ev t' = PreHistory.empty
    · -- t non-empty, t' empty: both sides are false
      simp only [semPreEqFull, preEqAt]
      rw [semObligationChain_of_empty ev t' t hEmptyT',
          semObligationChain_to_empty_of_nonempty ev t' t hEmptyT' hNonemptyT]
      simp only [Bool.false_and]
      rw [hEmptyT']
      rw [eq_comm, decide_eq_false_iff_not, PreHistory.histEq_spec]
      intro ⟨hFwd, _⟩
      obtain ⟨sem, hSemMem⟩ := hNonemptyT
      obtain ⟨w, hW, _⟩ := hFwd sem hSemMem
      exact PreHistory.not_mem_empty hW
    · -- Both non-empty (reachable): use the original proof with reachability
      have hNonemptyT' : ∃ sem, sem ∈ prehistoryOfTime ev t' := by
        by_contra h
        push_neg at h
        exact hEmptyT' (prehistory_eq_empty_of_forall_not_mem ev t' h)
      obtain ⟨pH', hReach', _, hEq'⟩ := prehistoryAt_nonempty_implies_reachable ev t' hNonemptyT'
      have hReachT' : prehistoryOfTime ev t' ∈ reachablePreHistories M.history.val := by
        rw [prehistoryOfTime, hEq']
        exact hReach'
      -- Now use the original proof structure
      simp only [semPreEqFull, preEqAt]
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, PreHistory.histEq_spec]
      constructor
      · intro ⟨hChain, hChainRev⟩
        constructor
        · exact semObligationChain_implies_histEq_fwd hFits t t' hReachT hReachT' hChain
        · intro w₂ hw₂
          obtain ⟨w₁, hw₁, hEq''⟩ := semObligationChain_implies_histEq_fwd hFits t' t
              hReachT' hReachT hChainRev w₂ hw₂
          exact ⟨w₁, hw₁, PreHistory.worldEq_symm hEq''⟩
      · intro ⟨hFwd, hBwd⟩
        constructor
        · exact histEq_fwd_implies_semObligationChain hFits t t' hReachT hReachT' hFwd
        · apply histEq_fwd_implies_semObligationChain hFits t' t hReachT' hReachT
          intro sem hSem
          obtain ⟨sem', hSem', hEq''⟩ := hBwd sem hSem
          exact ⟨sem', hSem', PreHistory.worldEq_symm hEq''⟩

/-! ## Extension Construction

We construct the extension by defining what value each Fresh variable should have.
The extension agrees with assignmentOf on non-Fresh vars and sets Fresh vars
according to their semantic meaning in the encoding.

Rather than tracking exact indices, we use a key property: the encoding structure
is deterministic, so we can define semantic values based on what the encoding
would compute given the input values.
-/

/-- Extension of assignmentOf that sets Fresh vars to their semantic values.

    For Fresh vars allocated by addPreEqFrom, we set them according to the
    Tseytin semantics. For other Fresh vars, we keep assignmentOf's value (false).

    The startIdx parameter indicates where addPreEqFrom's Fresh vars begin.
    Fresh vars in [startIdx, endIdx) are set semantically; others stay false. -/
noncomputable def extendForPreEq
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H0 : b.times)
    (startIdx endIdx : Nat) : SAT.Assignment (Var b) :=
  let σ₀ := assignmentOf b M hFits
  let ev := hFits.view
  fun v =>
    match v with
    | Var.Fresh n =>
        if startIdx ≤ n ∧ n < endIdx then
          -- This Fresh var is from addPreEqFrom; compute semantic value
          -- For simplicity, we set all addPreEqFrom Fresh vars to the final PreEq value
          -- This is a simplification; the actual proof requires tracking structure
          preEqAt ev H0 H0  -- Placeholder; real value depends on encoding position
        else
          σ₀ v
    | _ => σ₀ v

/-! ## Clause Evaluation Agreement Lemmas

Key lemmas for showing that clause evaluation is unchanged when extending freshExt
to new indices, as long as the clause only contains Fresh vars below the threshold. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Literal evaluation agrees when freshExt functions agree on the literal's Fresh index. -/
lemma lit_eval_of_agree_on_fresh
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (freshExt freshExt' : Nat → Bool)
    (lit : SAT.Lit (Var b))
    (bound : Nat)
    (hLitBelow : litFreshBelow lit bound)
    (hAgree : ∀ n < bound, freshExt' n = freshExt n) :
    SAT.Lit.eval (fun v => match v with | Var.Fresh n => freshExt' n | _ => σ₀ v) lit =
    SAT.Lit.eval (fun v => match v with | Var.Fresh n => freshExt n | _ => σ₀ v) lit := by
  unfold litFreshBelow at hLitBelow
  cases lit with
  | pos v =>
    simp only [SAT.Lit.eval, SAT.Lit.getVar] at hLitBelow ⊢
    cases v with
    | Fresh n =>
      simp only at hLitBelow ⊢
      exact hAgree n hLitBelow
    | _ => rfl
  | neg v =>
    simp only [SAT.Lit.eval, SAT.Lit.getVar] at hLitBelow ⊢
    cases v with
    | Fresh n =>
      simp only at hLitBelow ⊢
      rw [hAgree n hLitBelow]
    | _ => rfl

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Clause evaluation agrees when freshExt functions agree on all Fresh indices in the clause. -/
lemma clause_eval_of_agree_on_fresh
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (freshExt freshExt' : Nat → Bool)
    (clause : SAT.Clause (Var b))
    (bound : Nat)
    (hClauseBelow : clauseFreshBelow clause bound)
    (hAgree : ∀ n < bound, freshExt' n = freshExt n) :
    SAT.Clause.eval (fun v => match v with | Var.Fresh n => freshExt' n | _ => σ₀ v) clause =
    SAT.Clause.eval (fun v => match v with | Var.Fresh n => freshExt n | _ => σ₀ v) clause := by
  unfold clauseFreshBelow at hClauseBelow
  rw [SAT.Clause.eval_eq_any, SAT.Clause.eval_eq_any]
  induction clause with
  | nil => rfl
  | cons lit rest ih =>
    simp only [List.any_cons]
    have hLitBelow := hClauseBelow lit List.mem_cons_self
    have hRestBelow : ∀ l ∈ rest, litFreshBelow l bound :=
      fun l hl => hClauseBelow l (List.mem_cons.mpr (Or.inr hl))
    rw [lit_eval_of_agree_on_fresh σ₀ freshExt freshExt' lit bound hLitBelow hAgree]
    rw [ih hRestBelow]

/-! ## Clause Satisfaction Lemmas

For each clause type in addPreEqFrom, we show it's satisfied when Fresh vars
are set to their semantic values. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkY forward clause [¬Mem, ¬PreEq, y] is satisfied when y = Mem ∧ PreEq. -/
lemma mkY_forward_clause_satisfied
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (t' : b.times) (w w' : WId b) (y : FVar b)
    (hY : σ (FVar.toVar b y) = (σ (Var.Mem t' w') && σ (Var.PreEq w.ti w'.ti))) :
    SAT.Clause.eval σ
      [SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
       SAT.Lit.pos (FVar.toVar b y)] = true := by
  simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
  by_cases hMem : σ (Var.Mem t' w') = true
  · by_cases hPreEq : σ (Var.PreEq w.ti w'.ti) = true
    · -- Both true, so y must be true
      simp [hMem, hPreEq] at hY
      simp [hY]
    · simp at hPreEq; simp [hPreEq]
  · simp at hMem; simp [hMem]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- addPreEqExpose forward clause [¬PreEq, eqFinal] satisfied when eqFinal = PreEq. -/
lemma addPreEqExpose_forward_clause_satisfied
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (H0 H' : b.times) (eqFinal : FVar b)
    (hEqFinal : σ (FVar.toVar b eqFinal) = σ (Var.PreEq H0 H')) :
    SAT.Clause.eval σ
      [SAT.Lit.neg (Var.PreEq H0 H'), SAT.Lit.pos (FVar.toVar b eqFinal)] = true := by
  simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
  by_cases hPreEq : σ (Var.PreEq H0 H') = true
  · simp [hPreEq, hEqFinal]
  · simp at hPreEq; simp [hPreEq]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- addPreEqExpose backward clause [¬eqFinal, PreEq] satisfied when eqFinal = PreEq. -/
lemma addPreEqExpose_backward_clause_satisfied
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (H0 H' : b.times) (eqFinal : FVar b)
    (hEqFinal : σ (FVar.toVar b eqFinal) = σ (Var.PreEq H0 H')) :
    SAT.Clause.eval σ
      [SAT.Lit.neg (FVar.toVar b eqFinal), SAT.Lit.pos (Var.PreEq H0 H')] = true := by
  simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
  by_cases hEq : σ (FVar.toVar b eqFinal) = true
  · -- eqFinal = true, so PreEq = true by hEqFinal
    rw [hEqFinal] at hEq
    simp [hEq]
  · simp at hEq; simp [hEq]

/-! ## Semantic Extension Construction

Rather than tracking exact Fresh indices, we use the key property of Tseytin encodings:
given fixed input values, there is a UNIQUE satisfying assignment to internal variables.

For each Fresh var allocated by addPreEqFrom, we compute its semantic value based on
the encoding structure. This is well-defined because the encoding is deterministic.

The extension assigns each Fresh n in [st.nextFresh, st'.nextFresh) to its semantic
value, computed by simulating the encoding with assignmentOf's values for inputs.
-/


/-! ## Tseytin Gadget Satisfiability

Each Tseytin gadget produces clauses that are satisfiable when the output variable
is set to the correct function of its inputs. We prove this for each gadget type. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkY clauses are satisfied when y = Mem ∧ PreEq.

    mkY adds three clauses:
    - [¬y, Mem] - backward: y → Mem
    - [¬y, PreEq] - backward: y → PreEq
    - [¬Mem, ¬PreEq, y] - forward: Mem ∧ PreEq → y

    Setting y = (Mem && PreEq) satisfies all three. -/
lemma mkY_clauses_satisfiable
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (t' : b.times) (w w' : WId b) (st : EncState b)
    (hY : σ (FVar.toVar b (mkY b t' w w' st).1) =
          (σ (Var.Mem t' w') && σ (Var.PreEq w.ti w'.ti)))
    (clause : SAT.Clause (Var b))
    (hNew : clause ∈ (mkY b t' w w' st).2.clauses)
    (hNotOld : clause ∉ st.clauses) :
    SAT.Clause.eval σ clause = true := by
  -- The new clauses are exactly 3:
  -- c1 = [¬y, Mem], c2 = [¬y, PreEq], c3 = [¬Mem, ¬PreEq, y]
  unfold mkY at hNew hY
  cases hAlloc : EncState.allocFresh b st with
  | mk y st1 =>
    simp only [hAlloc] at hNew hY
    -- Trace through addClause to identify which clause we have
    -- st1.clauses = st.clauses (allocFresh preserves clauses)
    have hSt1 : st1.clauses = st.clauses := by
      have := EncState.allocFresh_clauses_eq (b := b) (st := st)
      simp [hAlloc] at this
      exact this
    -- After 3 addClauses, the new clauses are at the front
    simp only [EncState.addClause] at hNew
    -- clause is in [c3] :: [c2] :: [c1] :: st1.clauses
    -- Need to trace through List.mem_cons
    cases hNew with
    | head _ =>
      -- clause = c3 = [¬Mem, ¬PreEq, y]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
      by_cases hMem : σ (Var.Mem t' w') = true
      · by_cases hPreEq : σ (Var.PreEq w.ti w'.ti) = true
        · -- Mem = true, PreEq = true, so y = true
          simp [hMem, hPreEq] at hY
          simp [hY]
        · simp at hPreEq; simp [hPreEq]
      · simp at hMem; simp [hMem]
    | tail _ hRest =>
      cases hRest with
      | head _ =>
        -- clause = c2 = [¬y, PreEq]
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
        by_cases hYTrue : σ (FVar.toVar b y) = true
        · -- y = true, so Mem = true and PreEq = true by hY
          simp [hY] at hYTrue
          simp [hYTrue.2]
        · simp at hYTrue; simp [hYTrue]
      | tail _ hRest2 =>
        cases hRest2 with
        | head _ =>
          -- clause = c1 = [¬y, Mem]
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
          by_cases hYTrue : σ (FVar.toVar b y) = true
          · simp [hY] at hYTrue
            simp [hYTrue.1]
          · simp at hYTrue; simp [hYTrue]
        | tail _ hRest3 =>
          -- clause ∈ st1.clauses = st.clauses, contradicts hNotOld
          rw [hSt1] at hRest3
          exact absurd hRest3 hNotOld

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkOw clauses are satisfied when o = ¬Mem ∨ d.

    mkOw adds three clauses:
    - [¬o, ¬Mem, d] - backward: o → (¬Mem ∨ d)
    - [o, Mem] - forward when Mem false
    - [o, ¬d] - forward when d false -/
lemma mkOw_clauses_satisfiable
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (t : b.times) (w : WId b) (d : FVar b) (st : EncState b)
    (hO : σ (FVar.toVar b (mkOw b t w d st).1) =
          (!(σ (Var.Mem t w)) || σ (FVar.toVar b d)))
    (clause : SAT.Clause (Var b))
    (hNew : clause ∈ (mkOw b t w d st).2.clauses)
    (hNotOld : clause ∉ st.clauses) :
    SAT.Clause.eval σ clause = true := by
  unfold mkOw at hNew hO
  cases hAlloc : EncState.allocFresh b st with
  | mk o st1 =>
    simp only [hAlloc] at hNew hO
    have hSt1 : st1.clauses = st.clauses := by
      have := EncState.allocFresh_clauses_eq (b := b) (st := st)
      simp [hAlloc] at this
      exact this
    simp only [EncState.addClause] at hNew
    -- clause is in [c3] :: [c2] :: [c1] :: st1.clauses where
    -- c1 = [¬o, ¬Mem, d], c2 = [o, Mem], c3 = [o, ¬d]
    cases hNew with
    | head _ =>
      -- clause = c3 = [o, ¬d]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
      by_cases hd : σ (FVar.toVar b d) = true
      · -- d = true, so o = true (since ¬Mem ∨ d = true)
        simp [hd] at hO
        simp [hO]
      · simp at hd; simp [hd]
    | tail _ hRest =>
      cases hRest with
      | head _ =>
        -- clause = c2 = [o, Mem]
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
        by_cases hMem : σ (Var.Mem t w) = true
        · simp [hMem]
        · -- Mem = false, so o = true (since ¬Mem = true)
          simp at hMem
          simp [hMem] at hO
          simp [hO]
      | tail _ hRest2 =>
        cases hRest2 with
        | head _ =>
          -- clause = c1 = [¬o, ¬Mem, d]
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
          by_cases ho : σ (FVar.toVar b o) = true
          · -- o = true, so ¬Mem ∨ d = true
            simp [ho] at hO
            by_cases hMem : σ (Var.Mem t w) = true
            · simp [hMem] at hO
              simp [hO]
            · simp at hMem; simp [hMem]
          · simp at ho; simp [ho]
        | tail _ hRest3 =>
          rw [hSt1] at hRest3
          exact absurd hRest3 hNotOld

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkBigOrIff backward clauses: each [¬v, u] is satisfied when u = ∨vs. -/
lemma mkBigOrIff_backward_clause_satisfied
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (vs : List (Var b)) (u : FVar b)
    (hU : σ (FVar.toVar b u) = vs.any σ)
    (v : Var b) (hV : v ∈ vs) :
    SAT.Clause.eval σ [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)] = true := by
  simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
  by_cases hv : σ v = true
  · -- v = true, so u = true (since ∨vs = true)
    have : vs.any σ = true := List.any_eq_true.mpr ⟨v, hV, hv⟩
    simp [hU, this]
  · simp at hv; simp [hv]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: foldl with or over true stays true. -/
lemma foldl_or_true_stays_true
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (lits : List (SAT.Lit (Var b))) :
    List.foldl (fun acc lit => acc || SAT.Lit.eval σ lit) true lits = true := by
  induction lits with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons, Bool.true_or]
    exact ih

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: if any v in vs has σ v = true, then the clause (vs.map Lit.pos) evaluates to true. -/
lemma clause_any_true_of_map_pos
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (vs : List (Var b)) (hAny : vs.any σ = true) :
    SAT.Clause.eval σ (vs.map SAT.Lit.pos) = true := by
  rw [SAT.Clause.eval]
  induction vs with
  | nil => simp at hAny
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldl_cons, Bool.false_or, SAT.Lit.eval]
    simp only [List.any_cons, Bool.or_eq_true] at hAny
    cases hAny with
    | inl hHd =>
      simp only [hHd]
      exact foldl_or_true_stays_true σ (tl.map SAT.Lit.pos)
    | inr hTl =>
      cases hSigmaHd : (σ hd)
      · -- σ hd = false, need to recurse
        exact ih hTl
      · -- σ hd = true
        exact foldl_or_true_stays_true σ (tl.map SAT.Lit.pos)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkBigOrIff forward clause: [¬u, v₁, ...] is satisfied when u = ∨vs. -/
lemma mkBigOrIff_forward_clause_satisfied
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (vs : List (Var b)) (u : FVar b)
    (hU : σ (FVar.toVar b u) = vs.any σ) :
    SAT.Clause.eval σ (SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos) = true := by
  simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl_cons, Bool.false_or]
  by_cases hu : σ (FVar.toVar b u) = true
  · -- u = true, so ∨vs = true, so some v in vs is true
    rw [hU] at hu
    have hMapSat := clause_any_true_of_map_pos σ vs hu
    simp only [hu, hU, Bool.not_true]
    exact hMapSat
  · simp at hu
    simp only [hu, Bool.not_false]
    exact foldl_or_true_stays_true σ (vs.map SAT.Lit.pos)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- addAccStep clauses are satisfied when next = cur ∧ eqb.

    addAccStep adds three clauses:
    - [¬next, cur] - backward: next → cur
    - [¬next, eqb] - backward: next → eqb
    - [¬cur, ¬eqb, next] - forward: cur ∧ eqb → next -/
lemma addAccStep_clauses_satisfiable
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (cur next eqb : FVar b) (st : EncState b)
    (hNext : σ (FVar.toVar b next) = (σ (FVar.toVar b cur) && σ (FVar.toVar b eqb)))
    (clause : SAT.Clause (Var b))
    (hNew : clause ∈ (addAccStep b cur next eqb st).clauses)
    (hNotOld : clause ∉ st.clauses) :
    SAT.Clause.eval σ clause = true := by
  unfold addAccStep at hNew
  simp only [EncState.addClause] at hNew
  -- Clauses: c3 :: c2 :: c1 :: st.clauses
  -- c1 = [¬next, cur], c2 = [¬next, eqb], c3 = [¬cur, ¬eqb, next]
  cases hNew with
  | head _ =>
    -- c3 = [¬cur, ¬eqb, next]
    simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
    by_cases hCur : σ (FVar.toVar b cur) = true
    · by_cases hEqb : σ (FVar.toVar b eqb) = true
      · simp [hCur, hEqb] at hNext; simp [hNext]
      · simp at hEqb; simp [hEqb]
    · simp at hCur; simp [hCur]
  | tail _ hRest =>
    cases hRest with
    | head _ =>
      -- c2 = [¬next, eqb]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
      by_cases hNextT : σ (FVar.toVar b next) = true
      · simp [hNextT] at hNext
        simp [hNext.2]
      · simp at hNextT; simp [hNextT]
    | tail _ hRest2 =>
      cases hRest2 with
      | head _ =>
        -- c1 = [¬next, cur]
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
        by_cases hNextT : σ (FVar.toVar b next) = true
        · simp [hNextT] at hNext
          simp [hNext.1]
        · simp at hNextT; simp [hNextT]
      | tail _ hRest3 =>
        exact absurd hRest3 hNotOld

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- addPreEqExpose clauses are satisfied when v = PreEq(H0, H'). -/
lemma addPreEqExpose_clauses_satisfiable
    {b : Bounds S} (σ : SAT.Assignment (Var b))
    (H0 H' : b.times) (v : FVar b) (st : EncState b)
    (hV : σ (FVar.toVar b v) = σ (Var.PreEq H0 H'))
    (clause : SAT.Clause (Var b))
    (hNew : clause ∈ (addPreEqExpose b H0 H' v st).clauses)
    (hNotOld : clause ∉ st.clauses) :
    SAT.Clause.eval σ clause = true := by
  unfold addPreEqExpose at hNew
  simp only [EncState.addClause] at hNew
  -- Clauses: c2 :: c1 :: st.clauses
  -- c1 = [¬PreEq, v], c2 = [¬v, PreEq]
  cases hNew with
  | head _ =>
    -- c2 = [¬v, PreEq]
    simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
    by_cases hVT : σ (FVar.toVar b v) = true
    · rw [hV] at hVT; simp [hVT]
    · simp at hVT; simp [hVT]
  | tail _ hRest =>
    cases hRest with
    | head _ =>
      -- c1 = [¬PreEq, v]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
      by_cases hPreEq : σ (Var.PreEq H0 H') = true
      · simp [hPreEq, hV]
      · simp at hPreEq; simp [hPreEq]
    | tail _ hRest2 =>
      exact absurd hRest2 hNotOld

/-! ## Assignment Agreement Lemmas -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If two assignments agree on all variables in a clause, the clause evaluates the same. -/
lemma clause_eval_ext {b : Bounds S} (σ₁ σ₂ : SAT.Assignment (Var b))
    (clause : SAT.Clause (Var b))
    (hAgree : ∀ lit ∈ clause, σ₁ lit.getVar = σ₂ lit.getVar) :
    SAT.Clause.eval σ₁ clause = SAT.Clause.eval σ₂ clause := by
  rw [SAT.Clause.eval, SAT.Clause.eval]
  -- Show foldl preserves equality when literal evaluations are equal
  suffices h : ∀ acc, List.foldl (fun a l => a || SAT.Lit.eval σ₁ l) acc clause =
                      List.foldl (fun a l => a || SAT.Lit.eval σ₂ l) acc clause by
    exact h false
  intro acc
  induction clause generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hHd := hAgree hd (by simp)
    have hTl : ∀ lit ∈ tl, σ₁ lit.getVar = σ₂ lit.getVar :=
      fun lit hLit => hAgree lit (by simp [hLit])
    -- Show SAT.Lit.eval σ₁ hd = SAT.Lit.eval σ₂ hd
    have hEvalEq : SAT.Lit.eval σ₁ hd = SAT.Lit.eval σ₂ hd := by
      simp only [SAT.Lit.eval, SAT.Lit.getVar] at hHd ⊢
      cases hd with
      | pos v => exact hHd
      | neg v => simp only [hHd]
    rw [hEvalEq]
    exact ih hTl _

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- For a well-formed state, if σ₁ and σ₂ agree on Fresh vars below nextFresh
    and on non-Fresh vars, then they agree on clause evaluation for all clauses. -/
lemma wf_clause_eval_ext {b : Bounds S} (st : EncState b)
    (hWF : st.WellFormed)
    (σ₁ σ₂ : SAT.Assignment (Var b))
    (hFreshAgree : ∀ n, n < st.nextFresh → σ₁ (Var.Fresh n) = σ₂ (Var.Fresh n))
    (hNonFreshAgree : ∀ v, ¬Var.isFresh v → σ₁ v = σ₂ v)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ st.clauses) :
    SAT.Clause.eval σ₁ clause = SAT.Clause.eval σ₂ clause := by
  apply clause_eval_ext
  intro lit hLit
  cases hVar : lit.getVar with
  | Fresh n =>
    apply hFreshAgree
    exact hWF.fresh_lt_nextFresh clause hClause lit hLit n hVar
  | _ => exact hNonFreshAgree _ (by simp [Var.isFresh])

/-! ## Tseytin Equisatisfiability for addPreEqPair

The key lemma: addPreEqPair's new clauses are satisfiable when Fresh vars are set
to their semantic values. This follows from the Tseytin equisatisfiability property.

We prove this by induction on the gadget construction within addPreEqPair_core.
-/

/-! ### Gadget-Level Preservation Lemmas

Each gadget (mkY, mkDw, mkOw, addAccStep, addPreEqExpose) preserves satisfiability
when we extend freshExt to set the new Fresh var to its semantic value. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkY preserves satisfiability when we set the new Fresh var to Mem ∧ PreEq.

mkY adds 3 clauses encoding y ↔ (Mem ∧ PreEq):
- [¬y, Mem]: if y then Mem
- [¬y, PreEq]: if y then PreEq
- [¬Mem, ¬PreEq, y]: if Mem ∧ PreEq then y

Setting y = Mem && PreEq satisfies all three. -/
lemma mkY_preserves_sat
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (t' : b.times) (w w' : WId b) (st : EncState b)
    (hWF : st.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : st.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true) :
    let semVal := σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti)
    let freshExt' := fun n => if n = st.nextFresh then semVal else freshExt n
    (∀ n < st.nextFresh, freshExt' n = freshExt n) ∧
    (mkY b t' w w' st).2.WellFormed ∧
    (mkY b t' w w' st).2.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt' n
        | _ => σ₀ v)) = true := by
  -- mkY allocates one Fresh var and adds 3 clauses
  unfold mkY
  cases hAlloc : EncState.allocFresh b st with
  | mk yVar st1 =>
    simp only []

    have hYVar : yVar.id = st.nextFresh := by
      have := EncState.allocFresh_fst b st
      simp only [hAlloc] at this; exact this
    have hNextFresh : st1.nextFresh = st.nextFresh + 1 := by
      have := EncState.allocFresh_nextFresh b st
      simp only [hAlloc] at this; exact this
    have hSt1Clauses : st1.clauses = st.clauses := by
      have := EncState.allocFresh_clauses_eq b st
      simp only [hAlloc] at this; exact this
    have hWF1 : st1.WellFormed := by
      have := EncState.allocFresh_wf hWF
      simp only [hAlloc] at this; exact this

    -- Define the assignment
    let semVal := σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti)
    let freshExt' := fun n => if n = st.nextFresh then semVal else freshExt n

    constructor
    · -- Agreement below st.nextFresh
      intro n hn
      simp only [ne_of_lt hn, ↓reduceIte]

    constructor
    · -- Well-formedness after adding 3 clauses
      -- st1 → addClause → addClause → addClause
      -- Note: addClause preserves nextFresh
      let st2 := EncState.addClause b st1
        [SAT.Lit.neg (FVar.toVar b yVar), SAT.Lit.pos (Var.Mem t' w')]
      let st3 := EncState.addClause b st2
        [SAT.Lit.neg (FVar.toVar b yVar), SAT.Lit.pos (Var.PreEq w.ti w'.ti)]
      have hSt2Next : st2.nextFresh = st1.nextFresh :=
        EncState.addClause_nextFresh b st1 _
      have hSt3Next : st3.nextFresh = st2.nextFresh :=
        EncState.addClause_nextFresh b st2 _
      have hWF2 : st2.WellFormed := by
        apply EncState.addClause_wf hWF1
        intro lit hLit
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
        rcases hLit with rfl | rfl
        · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hYVar, hNextFresh]; omega
        · simp only [SAT.Lit.getVar, litFreshBelow]
      have hWF3 : st3.WellFormed := by
        apply EncState.addClause_wf hWF2
        intro lit hLit
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
        rcases hLit with rfl | rfl
        · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hYVar, hSt2Next, hNextFresh]; omega
        · simp only [SAT.Lit.getVar, litFreshBelow]
      apply EncState.addClause_wf hWF3
      intro lit hLit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
      rcases hLit with rfl | rfl | rfl
      · simp only [SAT.Lit.getVar, litFreshBelow]
      · simp only [SAT.Lit.getVar, litFreshBelow]
      · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hYVar, hSt3Next, hSt2Next, hNextFresh]
        omega

    · -- Satisfaction of all clauses
      rw [List.all_eq_true]
      intro clause hClause
      -- The final state has 3 new clauses prepended to st1.clauses
      simp only [EncState.addClause] at hClause
      cases hClause with
      | head _ =>
        -- Clause 3: [¬Mem, ¬PreEq, y]
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hYVar]
        simp only [↓reduceIte]
        cases h1 : σ₀ (Var.Mem t' w') <;> cases h2 : σ₀ (Var.PreEq w.ti w'.ti) <;> simp
      | tail _ hClause =>
        cases hClause with
        | head _ =>
          -- Clause 2: [¬y, PreEq]
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hYVar]
          simp only [↓reduceIte]
          cases h1 : σ₀ (Var.Mem t' w') <;> cases h2 : σ₀ (Var.PreEq w.ti w'.ti) <;> simp
        | tail _ hClause =>
          cases hClause with
          | head _ =>
            -- Clause 1: [¬y, Mem]
            simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hYVar]
            simp only [↓reduceIte]
            cases h1 : σ₀ (Var.Mem t' w') <;> cases h2 : σ₀ (Var.PreEq w.ti w'.ti) <;> simp
          | tail _ hClause =>
            -- Old clause from st1.clauses = st.clauses
            rw [hSt1Clauses] at hClause
            have hOld := List.all_eq_true.mp hSat clause hClause
            -- Use wf_clause_eval_ext: freshExt' agrees with freshExt on Fresh < nextFresh
            rw [wf_clause_eval_ext st hWF _ _ _ _ clause hClause]
            · exact hOld
            · -- Fresh agreement below nextFresh
              intro n hn
              simp only [ne_of_lt hn, ↓reduceIte]
            · -- Non-Fresh agreement (both use σ₀)
              intro v hNotFresh
              cases v <;> simp [Var.isFresh] at hNotFresh <;> rfl

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkOw preserves satisfiability when we set the new Fresh var to ¬Mem ∨ d. -/
lemma mkOw_preserves_sat
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (t : b.times) (w : WId b) (d : FVar b) (st : EncState b)
    (hWF : st.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : st.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true)
    (hD : d.id < st.nextFresh) :
    let dVal := freshExt d.id
    let semVal := !(σ₀ (Var.Mem t w)) || dVal
    let freshExt' := fun n => if n = st.nextFresh then semVal else freshExt n
    (∀ n < st.nextFresh, freshExt' n = freshExt n) ∧
    (mkOw b t w d st).2.WellFormed ∧
    (mkOw b t w d st).2.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt' n
        | _ => σ₀ v)) = true := by
  -- mkOw allocates one Fresh var and adds 3 clauses
  unfold mkOw
  cases hAlloc : EncState.allocFresh b st with
  | mk oVar st1 =>
    simp only []

    have hOVar : oVar.id = st.nextFresh := by
      have := EncState.allocFresh_fst b st
      simp only [hAlloc] at this; exact this
    have hNextFresh : st1.nextFresh = st.nextFresh + 1 := by
      have := EncState.allocFresh_nextFresh b st
      simp only [hAlloc] at this; exact this
    have hSt1Clauses : st1.clauses = st.clauses := by
      have := EncState.allocFresh_clauses_eq b st
      simp only [hAlloc] at this; exact this
    have hWF1 : st1.WellFormed := by
      have := EncState.allocFresh_wf hWF
      simp only [hAlloc] at this; exact this

    -- Define the assignment
    let dVal := freshExt d.id
    let semVal := !(σ₀ (Var.Mem t w)) || dVal
    let freshExt' := fun n => if n = st.nextFresh then semVal else freshExt n

    constructor
    · -- Agreement below st.nextFresh
      intro n hn
      simp only [ne_of_lt hn, ↓reduceIte]

    constructor
    · -- Well-formedness after adding 3 clauses
      let st2 := EncState.addClause b st1
        [SAT.Lit.neg (FVar.toVar b oVar), SAT.Lit.neg (Var.Mem t w), SAT.Lit.pos (FVar.toVar b d)]
      let st3 := EncState.addClause b st2
        [SAT.Lit.pos (FVar.toVar b oVar), SAT.Lit.pos (Var.Mem t w)]
      have hSt2Next : st2.nextFresh = st1.nextFresh := EncState.addClause_nextFresh b st1 _
      have hSt3Next : st3.nextFresh = st2.nextFresh := EncState.addClause_nextFresh b st2 _
      have hWF2 : st2.WellFormed := by
        apply EncState.addClause_wf hWF1
        intro lit hLit
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
        rcases hLit with rfl | rfl | rfl
        · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hOVar, hNextFresh]; omega
        · simp only [SAT.Lit.getVar, litFreshBelow]
        · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hNextFresh]; omega
      have hWF3 : st3.WellFormed := by
        apply EncState.addClause_wf hWF2
        intro lit hLit
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
        rcases hLit with rfl | rfl
        · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hOVar, hSt2Next, hNextFresh]; omega
        · simp only [SAT.Lit.getVar, litFreshBelow]
      apply EncState.addClause_wf hWF3
      intro lit hLit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
      rcases hLit with rfl | rfl
      · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hOVar, hSt3Next, hSt2Next, hNextFresh]
        omega
      · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hSt3Next, hSt2Next, hNextFresh]; omega

    · -- Satisfaction of all clauses
      rw [List.all_eq_true]
      intro clause hClause
      simp only [EncState.addClause] at hClause
      cases hClause with
      | head _ =>
        -- Clause 3: [o, ¬d]
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hOVar]
        simp only [↓reduceIte]
        cases hMem : σ₀ (Var.Mem t w) <;> cases hDVal : freshExt d.id <;> simp
      | tail _ hClause =>
        cases hClause with
        | head _ =>
          -- Clause 2: [o, Mem]
          simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hOVar]
          simp only [↓reduceIte]
          cases hMem : σ₀ (Var.Mem t w) <;> cases hDVal : freshExt d.id <;> simp
        | tail _ hClause =>
          cases hClause with
          | head _ =>
            -- Clause 1: [¬o, ¬Mem, d]
            simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hOVar]
            simp only [↓reduceIte]
            -- Need: !(!Mem || d) || !Mem || d = true
            -- !(!Mem || d) = Mem && !d
            -- So: (Mem && !d) || !Mem || d
            -- If Mem = false: !false || d = true || d = true ✓
            -- If Mem = true: (!true || d) = d, so !d || !true || d = !d || d = true ✓
            cases hMem : σ₀ (Var.Mem t w) <;> cases hDVal : freshExt d.id <;> simp
          | tail _ hClause =>
            -- Old clause from st1.clauses = st.clauses
            rw [hSt1Clauses] at hClause
            have hOld := List.all_eq_true.mp hSat clause hClause
            rw [wf_clause_eval_ext st hWF _ _ _ _ clause hClause]
            · exact hOld
            · intro n hn
              simp only [ne_of_lt hn, ↓reduceIte]
            · intro v hNotFresh
              cases v <;> simp [Var.isFresh] at hNotFresh <;> rfl

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- addAccStep preserves satisfiability when we set next = cur && eqb.

addAccStep encodes next ↔ (cur ∧ eqb) using three clauses:
- [¬next, cur]: if next then cur
- [¬next, eqb]: if next then eqb
- [¬cur, ¬eqb, next]: if cur ∧ eqb then next

Setting next = cur && eqb satisfies all three clauses. -/
lemma addAccStep_preserves_sat
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (cur next eqb : FVar b) (st : EncState b)
    (hWF : st.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : st.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true)
    (hNext : next.id < st.nextFresh)
    (hCur : cur.id < st.nextFresh)
    (hEqb : eqb.id < st.nextFresh)
    (hNextVal : freshExt next.id = (freshExt cur.id && freshExt eqb.id)) :
    (addAccStep b cur next eqb st).WellFormed ∧
    (addAccStep b cur next eqb st).clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true := by
  -- addAccStep adds 3 clauses (no Fresh allocation)
  unfold addAccStep

  constructor
  · -- Well-formedness after adding 3 clauses
    let st1 := EncState.addClause b st
      [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)]
    let st2 := EncState.addClause b st1
      [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)]
    have hSt1Next : st1.nextFresh = st.nextFresh := EncState.addClause_nextFresh b st _
    have hSt2Next : st2.nextFresh = st1.nextFresh := EncState.addClause_nextFresh b st1 _
    have hWF1 : st1.WellFormed := by
      apply EncState.addClause_wf hWF
      intro lit hLit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
      rcases hLit with rfl | rfl
      · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow]; omega
      · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow]; omega
    have hWF2 : st2.WellFormed := by
      apply EncState.addClause_wf hWF1
      intro lit hLit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
      rcases hLit with rfl | rfl
      · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hSt1Next]; omega
      · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hSt1Next]; omega
    apply EncState.addClause_wf hWF2
    intro lit hLit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
    rcases hLit with rfl | rfl | rfl
    · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hSt2Next, hSt1Next]; omega
    · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hSt2Next, hSt1Next]; omega
    · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hSt2Next, hSt1Next]; omega

  · -- Satisfaction of all clauses
    rw [List.all_eq_true]
    intro clause hClause
    simp only [EncState.addClause, List.mem_cons] at hClause
    rcases hClause with rfl | rfl | rfl | hClause
    · -- Clause 3: [¬cur, ¬eqb, next]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hNextVal]
      cases hCurVal : freshExt cur.id <;> cases hEqbVal : freshExt eqb.id <;> simp
    · -- Clause 2: [¬next, eqb]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hNextVal]
      cases hCurVal : freshExt cur.id <;> cases hEqbVal : freshExt eqb.id <;> simp
    · -- Clause 1: [¬next, cur]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hNextVal]
      cases hCurVal : freshExt cur.id <;> cases hEqbVal : freshExt eqb.id <;> simp
    · -- Old clause from st.clauses
      exact List.all_eq_true.mp hSat clause hClause

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- addPreEqExpose preserves satisfiability when eqFinal value equals PreEq.

addPreEqExpose encodes eqFinal ↔ PreEq(H0, H') using two clauses:
- [¬PreEq, eqFinal]: if PreEq then eqFinal
- [¬eqFinal, PreEq]: if eqFinal then PreEq

When freshExt(eqFinal) = σ₀(PreEq), both clauses are satisfied. -/
lemma addPreEqExpose_preserves_sat
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (H0 H' : b.times) (eqFinal : FVar b) (st : EncState b)
    (hWF : st.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : st.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true)
    (hEqFinal : eqFinal.id < st.nextFresh)
    (hEqFinalVal : freshExt eqFinal.id = σ₀ (Var.PreEq H0 H')) :
    (addPreEqExpose b H0 H' eqFinal st).WellFormed ∧
    (addPreEqExpose b H0 H' eqFinal st).clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true := by
  unfold addPreEqExpose
  -- Track state through the two addClause calls
  let st1 := EncState.addClause b st
    [SAT.Lit.neg (Var.PreEq H0 H'), SAT.Lit.pos (FVar.toVar b eqFinal)]
  have hSt1Next : st1.nextFresh = st.nextFresh := EncState.addClause_nextFresh b st _
  have hWF1 : st1.WellFormed := by
    apply EncState.addClause_wf hWF
    intro lit hLit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
    rcases hLit with rfl | rfl
    · simp only [SAT.Lit.getVar, litFreshBelow]
    · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow]; omega

  constructor
  · -- Well-formedness after adding 2 clauses
    apply EncState.addClause_wf hWF1
    intro lit hLit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
    rcases hLit with rfl | rfl
    · simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hSt1Next]; omega
    · simp only [SAT.Lit.getVar, litFreshBelow]

  · -- Satisfaction of all clauses
    rw [List.all_eq_true]
    intro clause hClause
    simp only [EncState.addClause, List.mem_cons] at hClause
    rcases hClause with rfl | rfl | hClause
    · -- Clause 2: [¬eqFinal, PreEq(H0,H')]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hEqFinalVal]
      cases h : σ₀ (Var.PreEq H0 H') <;> simp
    · -- Clause 1: [¬PreEq(H0,H'), eqFinal]
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, hEqFinalVal]
      cases h : σ₀ (Var.PreEq H0 H') <;> simp
    · -- Old clause from st.clauses
      exact List.all_eq_true.mp hSat clause hClause

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkBigOrIff preserves satisfiability when we set u = vs.any σ.

mkBigOrIff encodes u ↔ (∨ vs) using:
- Backward clauses: [¬v, u] for each v ∈ vs (if any v then u)
- Forward clause: [¬u, v₁, ..., vₙ] (if u then some v)

Setting u = vs.any σ satisfies all clauses:
- Backward: if v=true then u=true (since u = ∨vs)
- Forward: if u=true then some v=true (by definition of any) -/
lemma mkBigOrIff_preserves_sat
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (vs : List (Var b)) (st : EncState b)
    (hWF : st.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : st.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true)
    (hVsSafe : ∀ v ∈ vs, ¬Var.isFresh v ∨ (∃ n, v = Var.Fresh n ∧ n < st.nextFresh)) :
    let σ_ext := fun v => match v with
      | Var.Fresh n => freshExt n
      | _ => σ₀ v
    let semVal := vs.any σ_ext
    let freshExt' := fun n => if n = st.nextFresh then semVal else freshExt n
    (∀ n < st.nextFresh, freshExt' n = freshExt n) ∧
    (mkBigOrIff b vs st).2.WellFormed ∧
    (mkBigOrIff b vs st).2.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt' n
        | _ => σ₀ v)) = true := by
  -- Unfold mkBigOrIff to see the structure
  unfold mkBigOrIff
  simp only

  -- Step 1: allocFresh
  let allocResult := EncState.allocFresh b st
  let u := allocResult.1
  let st1 := allocResult.2

  have hUId : u.id = st.nextFresh := EncState.allocFresh_fst b st
  have hSt1Next : st1.nextFresh = st.nextFresh + 1 := EncState.allocFresh_nextFresh b st
  have hSt1Clauses : st1.clauses = st.clauses := EncState.allocFresh_clauses_eq b st
  have hWF1 : st1.WellFormed := EncState.allocFresh_wf hWF

  -- Step 2: fold adding backward clauses [¬v, u]
  let st2 := vs.foldl (fun stCur v =>
    EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]) st1

  -- Step 3: add forward clause [¬u, v₁, ..., vₙ]
  let st3 := EncState.addClause b st2
    (SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos)

  -- Define the extended assignment
  let σ_ext := fun v => match v with
    | Var.Fresh n => freshExt n
    | _ => σ₀ v
  let semVal := vs.any σ_ext
  let freshExt' := fun n => if n = st.nextFresh then semVal else freshExt n

  constructor
  · -- Agreement: n < st.nextFresh → freshExt' n = freshExt n
    intro n hn
    simp only [ne_of_lt hn, ↓reduceIte]

  constructor
  · -- Well-formedness of st3
    -- Key: addClause preserves nextFresh, so fold states have nextFresh = st1.nextFresh
    -- u.id = st.nextFresh < st1.nextFresh, so u's Fresh index is below all fold states' nextFresh
    -- All vs have Fresh indices < st.nextFresh < st1.nextFresh by hVsSafe

    -- First establish st2.nextFresh = st1.nextFresh
    have hSt2Next : st2.nextFresh = st1.nextFresh := by
      simp only [st2]
      -- addClause doesn't change nextFresh, so fold over addClause preserves nextFresh
      have hFoldNext : ∀ (vsPrefix : List (Var b)) (stInit : EncState b),
          (vsPrefix.foldl (fun st' v =>
            EncState.addClause b st' [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)])
          stInit).nextFresh = stInit.nextFresh := by
        intro vsPrefix
        induction vsPrefix with
        | nil => intro _; rfl
        | cons _ rest ih =>
          intro stInit
          simp only [List.foldl_cons]
          rw [ih, EncState.addClause_nextFresh]
      exact hFoldNext vs st1

    -- Show st2 is WF using suffices with an invariant
    have hWF2 : st2.WellFormed := by
      simp only [st2]
      suffices h : ∀ (vsPrefix : List (Var b)) (stCur : EncState b),
          stCur.WellFormed → stCur.nextFresh = st1.nextFresh →
          (∀ v ∈ vsPrefix, ¬Var.isFresh v ∨ (∃ n, v = Var.Fresh n ∧ n < st.nextFresh)) →
          (vsPrefix.foldl (fun st' v =>
            EncState.addClause b st' [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)])
          stCur).WellFormed by
        exact h vs st1 hWF1 rfl hVsSafe
      intro vsPrefix stCur hCurWF hCurNext hVsPrefSafe
      induction vsPrefix generalizing stCur with
      | nil => exact hCurWF
      | cons v rest ih =>
        simp only [List.foldl_cons]
        let stNext := EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]
        have hNextWF : stNext.WellFormed := by
          apply EncState.addClause_wf hCurWF
          intro lit hLit
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
          rcases hLit with rfl | rfl
          · -- ¬v
            simp only [SAT.Lit.getVar, litFreshBelow]
            have hVMem : v ∈ v :: rest := by simp
            rcases hVsPrefSafe v hVMem with hNotFresh | ⟨n, hVEq, hn⟩
            · unfold Var.isFresh at hNotFresh
              cases v <;> simp at hNotFresh <;> trivial
            · simp only [hVEq, hCurNext, hSt1Next]; omega
          · -- u
            simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow, hUId, hCurNext, hSt1Next]; omega
        have hNextNext : stNext.nextFresh = st1.nextFresh := by
          simp only [stNext, EncState.addClause_nextFresh, hCurNext]
        have hRestSafe : ∀ v ∈ rest, ¬Var.isFresh v ∨ (∃ n, v = Var.Fresh n ∧ n < st.nextFresh) :=
          fun v hv => hVsPrefSafe v (List.mem_cons_of_mem _ hv)
        exact ih stNext hNextWF hNextNext hRestSafe

    -- Finally show st3 is WF
    apply EncState.addClause_wf hWF2
    intro lit hLit
    simp only [List.mem_cons, List.mem_map] at hLit
    rcases hLit with rfl | ⟨v, hv, rfl⟩
    · -- ¬u
      simp only [SAT.Lit.getVar, FVar.toVar, litFreshBelow]
      rw [hUId, hSt2Next, hSt1Next]; omega
    · -- some v from vs
      simp only [SAT.Lit.getVar, litFreshBelow]
      rcases hVsSafe v hv with hNotFresh | ⟨n, hVEq, hn⟩
      · unfold Var.isFresh at hNotFresh
        cases v <;> simp at hNotFresh <;> trivial
      · rw [hVEq, hSt2Next, hSt1Next]; omega

  · -- Clause satisfaction
    -- st3 = addClause st2 (forward clause), so st3.clauses = forward :: st2.clauses
    -- Need to show all clauses satisfied
    rw [List.all_eq_true]
    intro clause hInSt3
    -- st3.clauses = forward_clause :: st2.clauses
    simp only [EncState.addClause_clauses_eq, List.mem_cons] at hInSt3
    rcases hInSt3 with rfl | hInSt2
    · -- Forward clause [¬u, v₁, ..., vₙ]
      -- If u=semVal=true then some vi is true; if u=false then ¬u is true
      rw [SAT.Clause.eval_eq_any, List.any_eq_true]
      -- Define σ' explicitly
      let σ' := fun v => match v with
        | Var.Fresh n => freshExt' n
        | _ => σ₀ v
      -- u evaluates to semVal under σ'
      have hUEval : σ' (FVar.toVar b u) = semVal := by
        simp only [FVar.toVar, σ']
        simp only [freshExt', hUId, ↓reduceIte]
      by_cases hsv : semVal = true
      · -- semVal = true, so some v ∈ vs has σ_ext v = true
        rw [List.any_eq_true] at hsv
        obtain ⟨v, hv, hvTrue⟩ := hsv
        use SAT.Lit.pos v
        constructor
        · simp only [List.mem_cons, List.mem_map]
          right; exact ⟨v, hv, rfl⟩
        · simp only [SAT.Lit.eval]
          -- Show σ' v = σ_ext v = true
          cases hvc : v with
          | Fresh n =>
            simp only []
            -- n < st.nextFresh by hVsSafe
            have hn : n < st.nextFresh := by
              rcases hVsSafe v hv with hNotFresh | ⟨m, hEq, hm⟩
              · simp [Var.isFresh, hvc] at hNotFresh
              · simp [hvc] at hEq; omega
            simp only [ne_of_lt hn, ↓reduceIte]
            simp only [hvc] at hvTrue
            exact hvTrue
          | _ =>
            simp only []
            simp only [hvc] at hvTrue
            exact hvTrue
      · -- semVal = false, so u = false, and ¬u is true
        use SAT.Lit.neg (FVar.toVar b u)
        constructor
        · simp only [allocResult, u, List.mem_cons]; left; trivial
        · simp only [SAT.Lit.eval]
          -- Need to show !σ' (FVar.toVar b u) = true
          -- σ' (FVar.toVar b u) = semVal and semVal ≠ true
          simp only [FVar.toVar, hUId, ↓reduceIte]
          -- Now goal is !vs.any (fun v => match...) = true and hsv : ¬semVal = true
          cases hGoal : vs.any fun v => match v with | Var.Fresh n => freshExt n | _ => σ₀ v with
          | false => rfl
          | true =>
            -- Contradiction: hsv says vs.any ≠ true, but hGoal says = true
            exact absurd hGoal hsv
    · -- Clause is in st2.clauses (backward clauses or old clauses)
      -- st2 = foldl (fun st' v => addClause [¬v, u]) st1
      -- Use foldl_addClause_mem_iff to classify
      rw [foldl_addClause_mem_iff] at hInSt2
      rcases hInSt2 with hOld | ⟨v, hv, hEq⟩
      · -- Old clause from st1.clauses = st.clauses
        rw [hSt1Clauses] at hOld
        -- Use clause_eval_of_agree_on_fresh: freshExt' agrees with freshExt below st.nextFresh
        have hAgree : ∀ n < st.nextFresh, freshExt' n = freshExt n := fun n hn =>
          by simp only [freshExt', ne_of_lt hn, ↓reduceIte]
        have hClauseBelow : clauseFreshBelow clause st.nextFresh := hWF clause hOld
        have hEqEval := clause_eval_of_agree_on_fresh σ₀ freshExt freshExt' clause st.nextFresh
          hClauseBelow hAgree
        -- Goal: SAT.Clause.eval (fun v => ..freshExt'..) clause = true
        -- hEqEval: clause under freshExt' = clause under freshExt
        -- hSat: st.clauses.all (SAT.Clause.eval (fun v => ..freshExt..)) = true
        simp only [freshExt'] at hEqEval
        exact hEqEval ▸ List.all_eq_true.mp hSat clause hOld
      · -- Backward clause [¬v, u] for v ∈ vs
        rw [hEq]
        -- Need to show u evaluates to semVal under σ'
        -- Define σ' as the extended assignment
        let σ' := fun w => match w with
          | Var.Fresh n => freshExt' n
          | _ => σ₀ w
        have hU : σ' (FVar.toVar b u) = vs.any σ_ext := by
          simp only [σ', FVar.toVar, freshExt', hUId, ↓reduceIte, semVal, σ_ext]
        -- Use mkBigOrIff_backward_clause_satisfied
        -- But we need σ' (FVar.toVar u) = vs.any σ'
        -- Key: for v ∈ vs, σ' v = σ_ext v (since v is not Fresh with id ≥ st.nextFresh)
        have hVsAgree : vs.any σ' = vs.any σ_ext := by
          have hPtwise : ∀ w ∈ vs, σ' w = σ_ext w := by
            intro w hwMem
            rcases hVsSafe w hwMem with hNotFresh | ⟨n, hwEq, hn⟩
            · -- w is not Fresh, so σ' w = σ₀ w = σ_ext w
              cases w with
              | Fresh _ => simp [Var.isFresh] at hNotFresh
              | _ => simp only [σ', σ_ext]
            · -- w = Fresh n with n < st.nextFresh
              simp only [hwEq, σ', σ_ext, freshExt', ne_of_lt hn, ↓reduceIte]
          rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
          constructor <;> intro ⟨w, hwMem, hw⟩
          · exact ⟨w, hwMem, (hPtwise w hwMem).symm ▸ hw⟩
          · exact ⟨w, hwMem, (hPtwise w hwMem) ▸ hw⟩
        rw [← hVsAgree] at hU
        exact mkBigOrIff_backward_clause_satisfied σ' vs u hU v hv

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] [DecidableEq S.Value] in
/-- Helper: fold of mkY preserves satisfiability with an accumulator.

Generalized version that handles arbitrary initial accumulator (ysAcc, stAcc). -/
lemma mkY_fold_preserves_sat_aux
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (t' : b.times) (w : WId b)
    (cands : List (WId b))
    (ysAcc : List (Var b)) (stAcc : EncState b)
    (hWF : stAcc.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : stAcc.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true)
    -- Each existing y in ysAcc is a Fresh var below stAcc.nextFresh
    (hYsAcc : ∀ y ∈ ysAcc, ∃ n, y = Var.Fresh n ∧ n < stAcc.nextFresh)
    -- Semantic property of accumulator: ysAcc.any freshExt = accSem
    (accSem : Bool)
    (hAccSem : ysAcc.any (fun y => match y with | Var.Fresh n => freshExt n | _ => σ₀ y) = accSem) :
    let (ys, st') := cands.foldl
      (fun (acc : List (Var b) × EncState b) w' =>
        let (vs, st') := acc
        let (y, st'') := mkY b t' w w' st'
        (FVar.toVar b y :: vs, st''))
      (ysAcc, stAcc)
    ∃ freshExt' : Nat → Bool,
      (∀ n < stAcc.nextFresh, freshExt' n = freshExt n) ∧
      st'.WellFormed ∧
      st'.clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt' n
          | _ => σ₀ v)) = true ∧
      (∀ y ∈ ys, ∃ n, y = Var.Fresh n ∧ n < st'.nextFresh) ∧
      (ys.any (fun y => match y with | Var.Fresh n => freshExt' n | _ => σ₀ y) =
       (accSem || cands.any (fun w' => σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti)))) := by
  induction cands generalizing ysAcc stAcc freshExt accSem with
  | nil =>
    simp only [List.foldl_nil, List.any_nil, Bool.or_false]
    use freshExt
    refine ⟨fun _ _ => rfl, hWF, hSat, hYsAcc, ?_⟩
    exact hAccSem
  | cons c cs ih =>
    simp only [List.foldl_cons, List.any_cons]
    -- Apply mkY_preserves_sat for the first candidate c
    have hMkY := mkY_preserves_sat σ₀ t' w c stAcc hWF freshExt hSat
    obtain ⟨hAgree1, hWF1, hSat1⟩ := hMkY
    let y := (mkY b t' w c stAcc).1
    let st1 := (mkY b t' w c stAcc).2
    let semVal_c := σ₀ (Var.Mem t' c) && σ₀ (Var.PreEq w.ti c.ti)
    let freshExt1 := fun n => if n = stAcc.nextFresh then semVal_c else freshExt n
    have hYId : y.id = stAcc.nextFresh := mkY_fst_id b t' w c stAcc
    have hSt1Next : st1.nextFresh = stAcc.nextFresh + 1 := mkY_nextFresh b t' w c stAcc
    -- New accumulator
    let ysAcc1 := FVar.toVar b y :: ysAcc
    -- Each y in new acc is Fresh below st1.nextFresh
    have hYsAcc1 : ∀ yv ∈ ysAcc1, ∃ n, yv = Var.Fresh n ∧ n < st1.nextFresh := by
      intro yv hyv
      simp only [ysAcc1, List.mem_cons] at hyv
      rcases hyv with rfl | hyv
      · use y.id
        refine ⟨rfl, ?_⟩
        rw [hYId, hSt1Next]; omega
      · obtain ⟨n, hEq, hn⟩ := hYsAcc yv hyv
        use n
        refine ⟨hEq, ?_⟩
        rw [hSt1Next]; omega
    -- New accumulator semantic value
    let accSem1 := accSem || semVal_c
    have hAccSem1 : ysAcc1.any (fun yv =>
        match yv with | Var.Fresh n => freshExt1 n | _ => σ₀ yv) = accSem1 := by
      simp only [ysAcc1, List.any_cons, accSem1]
      -- y evaluates to semVal_c under freshExt1
      have hYEval : (fun yv =>
          match yv with | Var.Fresh n => freshExt1 n | _ => σ₀ yv) (FVar.toVar b y) = semVal_c := by
        simp only [FVar.toVar, freshExt1, hYId, ↓reduceIte]
      simp only [hYEval]
      -- ysAcc.any under freshExt1 = accSem (freshExt1 agrees with freshExt below stAcc.nextFresh)
      have hYsAccEval : ysAcc.any (fun yv =>
          match yv with | Var.Fresh n => freshExt1 n | _ => σ₀ yv) = accSem := by
        rw [Bool.eq_iff_iff, List.any_eq_true]
        have hAccSemIff :
            (∃ x ∈ ysAcc, (match x with | Var.Fresh n => freshExt n | _ => σ₀ x) = true)
            ↔ (accSem = true) := by rw [← List.any_eq_true]; exact Bool.eq_iff_iff.mp hAccSem
        constructor
        · intro ⟨yv, hyv, hEval⟩
          obtain ⟨n, hEq, hn⟩ := hYsAcc yv hyv
          -- Use subst to replace yv with Var.Fresh n
          subst hEq
          simp only [freshExt1, ne_of_lt hn, ↓reduceIte] at hEval
          exact hAccSemIff.1 ⟨Var.Fresh n, hyv, hEval⟩
        · intro hAcc
          obtain ⟨yv, hyv, hEval⟩ := hAccSemIff.2 hAcc
          use yv, hyv
          obtain ⟨n, hEq, hn⟩ := hYsAcc yv hyv
          subst hEq
          simp only [freshExt1, ne_of_lt hn, ↓reduceIte]
          exact hEval
      simp only [hYsAccEval, Bool.or_comm semVal_c accSem]
    -- Apply IH
    have hIH := ih ysAcc1 st1 hWF1 freshExt1 hSat1 hYsAcc1 accSem1 hAccSem1
    obtain ⟨freshExt', hAgree', hWF', hSat', hYsFresh, hYsSem⟩ := hIH
    use freshExt'
    constructor
    · -- Agreement below stAcc.nextFresh
      intro n hn
      have h1 := hAgree' n (by simp only [hSt1Next]; omega)
      simp only [freshExt1, ne_of_lt hn, ↓reduceIte] at h1
      exact h1
    refine ⟨hWF', hSat', hYsFresh, ?_⟩
    -- Semantic value
    simp only [accSem1, Bool.or_assoc] at hYsSem
    exact hYsSem

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] [DecidableEq S.Value] in
/-- Helper: fold of mkY preserves satisfiability starting from empty accumulator. -/
lemma mkY_fold_preserves_sat
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (t' : b.times) (w : WId b)
    (cands : List (WId b))
    (st : EncState b)
    (hWF : st.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : st.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true) :
    let (ys, st') := cands.foldl
      (fun (acc : List (Var b) × EncState b) w' =>
        let (vs, st') := acc
        let (y, st'') := mkY b t' w w' st'
        (FVar.toVar b y :: vs, st''))
      ([], st)
    ∃ freshExt' : Nat → Bool,
      (∀ n < st.nextFresh, freshExt' n = freshExt n) ∧
      st'.WellFormed ∧
      st'.clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt' n
          | _ => σ₀ v)) = true ∧
      (∀ y ∈ ys, ∃ n, y = Var.Fresh n ∧ n < st'.nextFresh) ∧
      (ys.any (fun y => match y with | Var.Fresh n => freshExt' n | _ => σ₀ y) =
       cands.any (fun w' => σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti))) := by
  have h := mkY_fold_preserves_sat_aux σ₀ t' w cands [] st hWF freshExt hSat
    (fun _ h => (List.not_mem_nil h).elim) false (by simp)
  simp only [Bool.false_or] at h
  exact h

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkDw preserves satisfiability. mkDw either:
    1. Creates a false Fresh var (if no candidates), or
    2. Folds mkY over candidates and uses mkBigOrIff to create d = ∨ys

For empty candidates: semVal = false, d is set to false, clause [¬d] is satisfied.
For non-empty candidates:
  - Each mkY creates y = Mem(t', w') ∧ PreEq(w.ti, w'.ti)
  - mkBigOrIff creates d = ∨ys
  - semVal = (∃ w' with sameSig, Mem ∧ PreEq) = ∨ys by definition -/
lemma mkDw_preserves_sat
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (t' : b.times) (w : WId b) (st : EncState b)
    (hWF : st.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : st.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true) :
    let (_, st') := mkDw b t' w st
    -- Semantic value: d = ∃ w' with sameSig, Mem(t', w') ∧ PreEq(w.ti, w'.ti)
    let semVal := (WId.allWorlds b).any (fun w' =>
      if sameSig b w w' then σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti) else false)
    ∃ freshExt' : Nat → Bool,
      (∀ n < st.nextFresh, freshExt' n = freshExt n) ∧
      freshExt' (st'.nextFresh - 1) = semVal ∧
      st'.WellFormed ∧
      st'.clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt' n
          | _ => σ₀ v)) = true := by
  -- Define the candidate list
  let cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  -- Case split on whether cands is empty
  cases hCands : cands with
  | nil =>
    -- Case 1: cands = [] (no candidates with sameSig)
    -- mkDw allocates d, adds clause [¬d], and d is forced to false
    -- semVal = false since no w' has sameSig
    -- First show what mkDw evaluates to in this case
    have hCandsEq : (WId.allWorlds b).filter (fun w' => sameSig b w w') = [] := hCands
    -- mkDw with empty cands: allocate d, add [¬d]
    let d := (EncState.allocFresh b st).1
    let st1 := (EncState.allocFresh b st).2
    let st' := EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b d)]
    have hMkDwEq : mkDw b t' w st = (d, st') := by
      unfold mkDw
      simp only [hCandsEq, d, st1, st']
    have hDId : d.id = st.nextFresh := EncState.allocFresh_fst b st
    have hSt1Next : st1.nextFresh = st.nextFresh + 1 := EncState.allocFresh_nextFresh b st
    have hSt1Clauses : st1.clauses = st.clauses := EncState.allocFresh_clauses_eq b st
    have hWF1 : st1.WellFormed := EncState.allocFresh_wf hWF
    -- semVal = false because cands = []
    have hSemVal : (WId.allWorlds b).any (fun w' =>
        if sameSig b w w'
        then σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti)
        else false) = false := by
      -- Prove by showing no witness exists
      by_contra hContra
      have hTrue : (WId.allWorlds b).any (fun w' =>
          if sameSig b w w'
          then σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti)
          else false) = true :=
        Bool.eq_true_of_not_eq_false hContra
      rw [List.any_eq_true] at hTrue
      obtain ⟨w', _, hw'Val⟩ := hTrue
      -- w' must have sameSig = true for hw'Val to be true
      split_ifs at hw'Val with hSig
      -- sameSig = true means w' ∈ cands, but cands = []
      have hMem : w' ∈ (WId.allWorlds b).filter (fun w'' => sameSig b w w'') :=
        List.mem_filter.mpr ⟨WId.mem_allWorlds b w', hSig⟩
      rw [hCandsEq] at hMem
      exact (List.not_mem_nil hMem).elim
    -- Define freshExt' with d set to false
    let freshExt' := fun n => if n = st.nextFresh then false else freshExt n
    rw [hMkDwEq]
    use freshExt'
    constructor
    · -- Agreement below st.nextFresh
      intro n hn
      simp only [freshExt', ne_of_lt hn, ↓reduceIte]
    constructor
    · -- freshExt' (st'.nextFresh - 1) = semVal
      have hStNext' : st'.nextFresh = st.nextFresh + 1 := by
        simp only [st', EncState.addClause_nextFresh, hSt1Next]
      simp only [hStNext', Nat.add_sub_cancel, freshExt', ↓reduceIte, hSemVal]
    constructor
    · -- st'.WellFormed
      apply EncState.addClause_wf hWF1
      intro lit hLit
      simp only [List.mem_singleton] at hLit
      rw [hLit]
      unfold litFreshBelow SAT.Lit.getVar FVar.toVar
      simp only
      rw [hDId, hSt1Next]; omega
    · -- Clauses satisfied
      apply List.all_eq_true.mpr
      intro clause hClause
      simp only [st', EncState.addClause] at hClause
      rcases List.mem_cons.mp hClause with hNew | hOld
      · -- New clause [¬d]
        rw [hNew]
        simp only [SAT.Clause.eval, List.foldl, SAT.Lit.eval, FVar.toVar, freshExt', hDId,
          ↓reduceIte, Bool.not_false, Bool.or_true]
      · -- Old clause from st1.clauses = st.clauses
        rw [hSt1Clauses] at hOld
        have hAgree : ∀ n < st.nextFresh, freshExt' n = freshExt n := fun n hn =>
          by simp only [freshExt', ne_of_lt hn, ↓reduceIte]
        have hClauseBelow : clauseFreshBelow clause st.nextFresh := hWF clause hOld
        have hEqEval := clause_eval_of_agree_on_fresh σ₀ freshExt freshExt' clause st.nextFresh
          hClauseBelow hAgree
        exact hEqEval ▸ List.all_eq_true.mp hSat clause hOld
  | cons c cs =>
    -- Case 2: cands = c :: cs (has candidates)
    -- mkDw = fold mkY, then mkBigOrIff
    have hCandsEq : (WId.allWorlds b).filter (fun w' => sameSig b w w') = c :: cs := hCands
    -- Define fold result
    let foldResult := (c :: cs).foldl
      (fun (acc : List (Var b) × EncState b) w' =>
        let (vs, st') := acc
        let (y, st'') := mkY b t' w w' st'
        (FVar.toVar b y :: vs, st''))
      ([], st)
    let ys := foldResult.1
    let st1 := foldResult.2
    let st' := mkBigOrIff b ys st1
    have hMkDwEq : mkDw b t' w st = st' := by
      unfold mkDw
      simp only [hCandsEq, foldResult, ys, st1, st']
    -- Step 1: fold mkY over cands
    have hFold := mkY_fold_preserves_sat σ₀ t' w (c :: cs) st hWF freshExt hSat
    obtain ⟨freshExt1, hAgree1, hWF1, hSat1, hYsFresh, hYsSem⟩ := hFold
    -- Step 2: Apply mkBigOrIff_preserves_sat
    -- First establish that all ys are safe (Fresh vars below st1.nextFresh)
    have hYsSafe : ∀ v ∈ ys, ¬Var.isFresh v ∨ (∃ n, v = Var.Fresh n ∧ n < st1.nextFresh) := by
      intro v hv
      right
      exact hYsFresh v hv
    have hBigOr := mkBigOrIff_preserves_sat σ₀ ys st1 hWF1 freshExt1 hSat1 hYsSafe
    obtain ⟨hAgree2, hWF2, hSat2⟩ := hBigOr
    -- Define the extended assignment for mkBigOrIff
    let σ_ext1 := fun v => match v with
      | Var.Fresh n => freshExt1 n
      | _ => σ₀ v
    let semVal_ys := ys.any σ_ext1
    let freshExt' := fun n => if n = st1.nextFresh then semVal_ys else freshExt1 n
    rw [hMkDwEq]
    use freshExt'
    -- Fold nextFresh calculation
    have hSt1NextFresh : st1.nextFresh = st.nextFresh + (c :: cs).length := by
      simp only [st1, foldResult]
      exact mkDw_fold_nextFresh b t' w (c :: cs) ([], st)
    constructor
    · -- Agreement below st.nextFresh
      intro n hn
      have h1 : freshExt' n = freshExt1 n := hAgree2 n (by
        -- Need: n < st1.nextFresh
        rw [hSt1NextFresh]; omega)
      have h2 : freshExt1 n = freshExt n := hAgree1 n hn
      exact h1.trans h2
    constructor
    · -- freshExt' (st'.nextFresh - 1) = semVal
      -- The goal has mkBigOrIff expanded - need to show nextFresh = st1.nextFresh + 1
      -- mkBigOrIff structure: allocFresh then fold of addClause then final addClause
      -- addClause preserves nextFresh, so only allocFresh's +1 matters
      have hAddClauseFold : ∀ (st'' : EncState b) (vs' : List (Var b)),
          (vs'.foldl (fun stCur v =>
            EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b ⟨st1.nextFresh⟩)])
            st'').nextFresh = st''.nextFresh := by
        intro st'' vs'
        induction vs' generalizing st'' with
        | nil => simp
        | cons v vs' ih =>
          simp only [List.foldl_cons]
          rw [ih]
          exact EncState.addClause_nextFresh b st'' _
      have hGoalNextFresh :
          (EncState.addClause b
            (ys.foldl (fun stCur v =>
              EncState.addClause b stCur
                [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b ⟨st1.nextFresh⟩)])
              {nextFresh := st1.nextFresh + 1, clauses := st1.clauses})
            (SAT.Lit.neg (FVar.toVar b ⟨st1.nextFresh⟩) ::
              List.map SAT.Lit.pos ys)).nextFresh
          = st1.nextFresh + 1 := by
        rw [EncState.addClause_nextFresh]
        rw [hAddClauseFold]
      -- Goal: freshExt' (nextFresh - 1) = semVal
      -- nextFresh = st1.nextFresh + 1, so nextFresh - 1 = st1.nextFresh
      have hIdx : (EncState.addClause b
            (ys.foldl (fun stCur v =>
              EncState.addClause b stCur
                [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b ⟨st1.nextFresh⟩)])
              {nextFresh := st1.nextFresh + 1, clauses := st1.clauses})
            (SAT.Lit.neg (FVar.toVar b ⟨st1.nextFresh⟩) ::
              List.map SAT.Lit.pos ys)).nextFresh - 1
          = st1.nextFresh := by rw [hGoalNextFresh]; omega
      simp only [hIdx, freshExt', ↓reduceIte]
      -- Need: semVal_ys = semVal
      -- semVal = allWorlds.any (if sameSig then Mem && PreEq else false)
      -- semVal_ys = ys.any σ_ext1
      -- From hYsSem: ys.any (freshExt1-based) = (c :: cs).any (Mem && PreEq)
      -- And (c :: cs) = cands = filter (sameSig) allWorlds
      -- So semVal_ys = semVal
      -- Need: semVal_ys = semVal
      -- semVal_ys = ys.any σ_ext1, and σ_ext1 agrees with the match function on Fresh vars
      -- hYsSem: ys.any (match-based) = (c :: cs).any (Mem && PreEq)
      -- hCandsEq: (c :: cs) = filter sameSig allWorlds
      -- Key: filter.any f = allWorlds.any (if condition then f else false)
      have hFilterAny : ∀ (l : List (WId b)) (p : WId b → Bool) (f : WId b → Bool),
          (l.filter p).any f = l.any (fun x => if p x then f x else false) := by
        intro l p f
        induction l with
        | nil => simp
        | cons x xs ih =>
          rw [List.any_cons]
          by_cases hp : p x = true
          · rw [List.filter_cons_of_pos hp, List.any_cons, ih]
            simp only [hp, ↓reduceIte]
          · rw [List.filter_cons_of_neg hp, ih]
            have hpf : p x = false := Bool.eq_false_iff.mpr hp
            simp only [hpf, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      -- Show ys.any σ_ext1 = ys.any (match-based)
      have hYsEvalEq : ys.any σ_ext1 =
          ys.any (fun y => match y with | Var.Fresh n => freshExt1 n | _ => σ₀ y) := rfl
      -- Use hYsSem to get (c :: cs).any (Mem && PreEq)
      have hYsVal : ys.any σ_ext1 =
          (c :: cs).any (fun w' => σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti)) := by
        rw [hYsEvalEq]
        exact hYsSem
      -- Show (c :: cs).any f = allWorlds.any (if sameSig then f else false)
      have hCandsVal : (c :: cs).any (fun w' => σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti)) =
          (WId.allWorlds b).any (fun w' =>
            if sameSig b w w' then σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti) else false) := by
        rw [← hCandsEq]
        have h := hFilterAny (WId.allWorlds b) (fun w' => sameSig b w w')
          (fun w' => σ₀ (Var.Mem t' w') && σ₀ (Var.PreEq w.ti w'.ti))
        -- h : filter.any = allWorlds.any (if p x = true then ...)
        -- goal: filter.any = allWorlds.any (if p x then ...)
        -- These are definitionally equal since Bool if and =true if are the same
        exact h
      simp only [semVal_ys]
      rw [hYsVal, hCandsVal]
    constructor
    · -- st'.WellFormed
      exact hWF2
    · -- Clauses satisfied
      exact hSat2

omit [DecidableEq S.AtomicPredType] in
/-- preEqObligationStep preserves satisfiability and tracks semantic value.
    preEqObligationStep = mkDw then mkOw for a single world.

    The new obligation `o` (the head of lst') has semantic value `semOw ev t t' w`. -/
lemma preEqObligationStep_preserves_sat
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (t t' : b.times) (w : WId b)
    (acc : List (FVar b) × EncState b)
    (hWF : acc.2.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : acc.2.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => assignmentOf b M hFits v)) = true)
    (hAccFresh : ∀ o ∈ acc.1, o.id < acc.2.nextFresh) :
    let (lst', st') := preEqObligationStep b t t' acc w
    let σ₀ := assignmentOf b M hFits
    ∃ freshExt' : Nat → Bool,
      (∀ n < acc.2.nextFresh, freshExt' n = freshExt n) ∧
      st'.WellFormed ∧
      st'.clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt' n
          | _ => σ₀ v)) = true ∧
      (∀ o ∈ lst', o.id < st'.nextFresh) ∧
      -- The new obligation has the correct semantic value
      -- lst' = [newObl] ++ acc.1, so lst'[0] is the new obligation
      freshExt' (lst'.getD 0 ⟨0⟩).id = semOw hFits.view t t' w := by
  let σ₀ := assignmentOf b M hFits
  -- Composition of mkDw_preserves_sat and mkOw_preserves_sat
  -- mkDw returns (d, st₁) where d encodes "∃ matching w' with sameSig"
  -- mkOw returns (o, st₂) where o encodes "¬Mem(t,w) ∨ d"
  -- The result is (o :: acc.1, st₂)
  unfold preEqObligationStep
  simp only
  -- Introduce shorthand for results
  let d := (mkDw b t' w acc.2).1
  let st₁ := (mkDw b t' w acc.2).2
  -- Step 1: Apply mkDw_preserves_sat
  have hMkDw := mkDw_preserves_sat σ₀ t' w acc.2 hWF freshExt hSat
  obtain ⟨freshExt₁, hAgree1, hDSem, hWF1, hSat1⟩ := hMkDw
  -- Step 2: Apply mkOw_preserves_sat
  -- Need to show d.id < st₁.nextFresh
  have hDFresh : d.id < st₁.nextFresh := mkDw_fst_lt_snd_nextFresh b t' w acc.2
  have hMkOw := mkOw_preserves_sat σ₀ t w d st₁ hWF1 freshExt₁ hSat1 hDFresh
  obtain ⟨hAgree2, hWF2, hSat2⟩ := hMkOw
  -- Define the final freshExt'
  let dVal := freshExt₁ d.id
  let semVal := !(σ₀ (Var.Mem t w)) || dVal
  let freshExt' := fun n => if n = st₁.nextFresh then semVal else freshExt₁ n
  use freshExt'
  constructor
  · -- Agreement below acc.2.nextFresh
    intro n hn
    have h1 : freshExt' n = freshExt₁ n := hAgree2 n (by
      have hMono : acc.2.nextFresh + 1 ≤ st₁.nextFresh := mkDw_snd_nextFresh_ge b t' w acc.2
      omega)
    have h2 : freshExt₁ n = freshExt n := hAgree1 n hn
    exact h1.trans h2
  constructor
  · exact hWF2
  constructor
  · exact hSat2
  constructor
  · -- All FVars in lst' have id < st'.nextFresh
    intro o ho
    simp only [List.mem_cons] at ho
    rcases ho with hNew | hOld
    · -- o is the new mkOw result
      rw [hNew]
      -- mkOw_fst_id: (mkOw ...).1.id = st₁.nextFresh
      -- mkOw_nextFresh: (mkOw ...).2.nextFresh = st₁.nextFresh + 1
      have hOId := mkOw_fst_id b t w d st₁
      have hONext := mkOw_nextFresh b t w d st₁
      simp only [d, st₁] at hOId hONext
      omega
    · -- o is from acc.1
      have hOFresh := hAccFresh o hOld
      have hMkDwMono := mkDw_snd_nextFresh_ge b t' w acc.2
      have hMkOwNext := mkOw_nextFresh b t w d st₁
      simp only [d, st₁] at hMkOwNext hMkDwMono
      omega
  · -- The new obligation has the correct semantic value
    -- lst' = [mkOw result] ++ acc.1, so lst'.getD 0 default = mkOw result
    -- mkOw result has id = st₁.nextFresh
    -- freshExt' (st₁.nextFresh) = semVal = !(σ₀ (Var.Mem t w)) || dVal
    -- Need: semVal = semOw hFits.view t t' w
    have hOId := mkOw_fst_id b t w d st₁
    simp only [List.getD_cons_zero, d, st₁] at hOId ⊢
    simp only [freshExt', st₁, hOId, ↓reduceIte, semVal]
    -- Goal: !(σ₀ (Var.Mem t w)) || dVal = semOw hFits.view t t' w
    simp only [semOw]
    -- Key: dVal = freshExt₁ d.id, and hDSem says freshExt₁ (st₁.nextFresh - 1) = semVal_d
    -- where semVal_d equals semDw. We need d.id = st₁.nextFresh - 1.
    -- From mkDw structure: d.id = st₁.nextFresh - 1 always (the last fresh var allocated)
    have hDIdEq : d.id = st₁.nextFresh - 1 := by
      simp only [d, st₁]
      have hFstId := mkDw_fst_id b t' w acc.2
      have hSndNext := mkDw_snd_nextFresh_eq b t' w acc.2
      set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
      simp only at hFstId hSndNext
      cases hEmpty : cands.isEmpty
      · simp only [hEmpty, ↓reduceIte, Bool.false_eq_true] at hFstId hSndNext; omega
      · simp only [hEmpty, ↓reduceIte] at hFstId hSndNext; omega
    have hDValEq : dVal = semDw hFits.view t' w := by
      -- dVal = freshExt₁ d.id = freshExt₁ (st₁.nextFresh - 1) = hDSem's semVal
      -- hDSem : freshExt₁ ((mkDw b t' w acc.2).2.nextFresh - 1) = semDw hFits.view t' w
      calc dVal = freshExt₁ d.id := rfl
        _ = freshExt₁ (st₁.nextFresh - 1) := by rw [hDIdEq]
        _ = freshExt₁ ((mkDw b t' w acc.2).2.nextFresh - 1) := rfl
        _ = semDw hFits.view t' w := hDSem
    rw [hDValEq]
    -- Now: !(σ₀ (Var.Mem t w)) || semDw ... = !worldInPrehistory ... || semDw ...
    rfl

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] [DecidableEq S.Value] in
/-- preEqAccStep preserves satisfiability.
    preEqAccStep = allocFresh then addAccStep. -/
lemma preEqAccStep_preserves_sat
    {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (acc : FVar b × EncState b) (o : FVar b)
    (hWF : acc.2.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : acc.2.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true)
    (hCur : acc.1.id < acc.2.nextFresh)
    (hO : o.id < acc.2.nextFresh) :
    let (next, st') := preEqAccStep b acc o
    let curVal := freshExt acc.1.id
    let oVal := freshExt o.id
    let semVal := curVal && oVal
    let freshExt' := fun n => if n = acc.2.nextFresh then semVal else freshExt n
    (∀ n < acc.2.nextFresh, freshExt' n = freshExt n) ∧
    st'.WellFormed ∧
    st'.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt' n
        | _ => σ₀ v)) = true ∧
    next.id < st'.nextFresh := by
  -- preEqAccStep unfolds to: allocFresh then addAccStep
  unfold preEqAccStep
  simp only

  -- Let (nextVar, st₁) := allocFresh
  -- Then addAccStep b acc.1 nextVar o st₁
  let nextVar := (EncState.allocFresh b acc.2).1
  let st₁ := (EncState.allocFresh b acc.2).2

  have hNextVar : nextVar.id = acc.2.nextFresh := EncState.allocFresh_fst b acc.2
  have hSt₁Next : st₁.nextFresh = acc.2.nextFresh + 1 := EncState.allocFresh_nextFresh b acc.2
  have hSt₁Clauses : st₁.clauses = acc.2.clauses := EncState.allocFresh_clauses_eq b acc.2
  have hWF₁ : st₁.WellFormed := EncState.allocFresh_wf hWF

  -- Clauses unchanged by allocFresh, so hSat still holds for st₁
  have hSat₁ : st₁.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true := by
    rw [hSt₁Clauses]; exact hSat

  -- Now apply addAccStep_preserves_sat
  have hCurLt : acc.1.id < st₁.nextFresh := by omega
  have hOLt : o.id < st₁.nextFresh := by omega

  -- The semantic value for next should be cur && o
  let semVal' := freshExt acc.1.id && freshExt o.id
  let freshExt' := fun n => if n = acc.2.nextFresh then semVal' else freshExt n

  have hNextLt : nextVar.id < st₁.nextFresh := by
    simp only [hNextVar, hSt₁Next]; omega

  -- Need freshExt' nextVar.id = freshExt' acc.1.id && freshExt' o.id
  have hNextVal : freshExt' nextVar.id = (freshExt' acc.1.id && freshExt' o.id) := by
    simp only [hNextVar, freshExt', semVal', ne_of_lt hCur, ne_of_lt hO, ↓reduceIte]

  -- Need st₁ satisfaction under freshExt'
  -- Key: freshExt' = freshExt on indices < acc.2.nextFresh
  -- All Fresh vars in acc.2.clauses have index < acc.2.nextFresh by hWF
  -- So the two assignments give the same result on each clause
  have hSat₁' : st₁.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt' n
        | _ => σ₀ v)) = true := by
    rw [hSt₁Clauses]
    rw [List.all_eq_true] at hSat ⊢
    intro clause hClause
    have hEval := hSat clause hClause
    have hClauseBelow : clauseFreshBelow clause acc.2.nextFresh := hWF clause hClause
    have hAgree : ∀ n < acc.2.nextFresh, freshExt' n = freshExt n := by
      intro n hn; simp only [freshExt', ne_of_lt hn, ↓reduceIte]
    rw [clause_eval_of_agree_on_fresh σ₀ freshExt freshExt' clause acc.2.nextFresh
      hClauseBelow hAgree]
    exact hEval

  -- Now apply addAccStep_preserves_sat
  have hCurLt' : acc.1.id < st₁.nextFresh := by omega
  have hOLt' : o.id < st₁.nextFresh := by omega

  have hAccStep := addAccStep_preserves_sat σ₀ acc.1 nextVar o st₁ hWF₁ freshExt'
    hSat₁' hNextLt hCurLt' hOLt' hNextVal

  constructor
  · -- Agreement: n < acc.2.nextFresh → freshExt' n = freshExt n
    intro n hn
    simp only [ne_of_lt hn, ↓reduceIte]
  constructor
  · -- WellFormed
    exact hAccStep.1
  constructor
  · -- Satisfaction
    exact hAccStep.2
  · -- next.id < st'.nextFresh
    simp only [addAccStep, EncState.addClause_nextFresh]
    omega

/-! ## Fold Monotonicity Lemmas -/

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- preEqObligationStep increases nextFresh -/
lemma preEqObligationStep_nextFresh_mono {b : Bounds S} (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b) :
    acc.2.nextFresh ≤ (preEqObligationStep b t t' acc w).2.nextFresh := by
  unfold preEqObligationStep
  simp only
  have hMkDw := mkDw_snd_nextFresh_ge b t' w acc.2
  have hMkOw := mkOw_nextFresh b t w (mkDw b t' w acc.2).1 (mkDw b t' w acc.2).2
  omega

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] [DecidableEq S.Value] in
/-- preEqAccStep strictly increases nextFresh -/
lemma preEqAccStep_nextFresh_lt {b : Bounds S} (acc : FVar b × EncState b) (o : FVar b) :
    acc.2.nextFresh < (preEqAccStep b acc o).2.nextFresh := by
  unfold preEqAccStep
  simp only
  have hAlloc := EncState.allocFresh_nextFresh b acc.2
  have hAdd : (EncState.allocFresh b acc.2).2.nextFresh =
      (addAccStep b acc.1 (EncState.allocFresh b acc.2).1 o
        (EncState.allocFresh b acc.2).2).nextFresh := by
    simp only [addAccStep, EncState.addClause_nextFresh]
  omega

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- obligation_fold increases nextFresh -/
lemma obligation_fold_nextFresh_mono {b : Bounds S} (t t' : b.times)
    (worlds : List (WId b)) (acc : List (FVar b) × EncState b) :
    acc.2.nextFresh ≤ (worlds.foldl (preEqObligationStep b t t') acc).2.nextFresh := by
  induction worlds generalizing acc with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldl_cons]
    have hStep := preEqObligationStep_nextFresh_mono t t' acc w
    have hIH := ih (preEqObligationStep b t t' acc w)
    omega

/-! ## Fold Preservation Lemmas -/

omit [DecidableEq S.AtomicPredType] in
/-- Fold of preEqObligationStep preserves satisfiability and tracks semantic values.
    Starting with empty accumulator, the result lst' satisfies:
    lst'.all (freshExt' ·.id) = worlds.all (semOw hFits.view t t' ·)

    The key invariant is: lst'.all = worlds.all semOw && acc.all freshExt
    When acc = [], this gives lst'.all = worlds.all semOw. -/
lemma obligation_fold_preserves_sat {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (t t' : b.times) (worlds : List (WId b))
    (st : EncState b)
    (hWF : st.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : st.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => assignmentOf b M hFits v)) = true) :
    let (lst', st') := worlds.foldl (preEqObligationStep b t t') ([], st)
    let σ₀ := assignmentOf b M hFits
    ∃ freshExt' : Nat → Bool,
      (∀ n < st.nextFresh, freshExt' n = freshExt n) ∧
      st'.WellFormed ∧
      st'.clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt' n
          | _ => σ₀ v)) = true ∧
      (∀ o ∈ lst', o.id < st'.nextFresh) ∧
      lst'.all (fun o => freshExt' o.id) = worlds.all (fun w => semOw hFits.view t t' w) := by
  -- Helper with correct invariant: lst'.all = worlds.all semOw && acc.all freshExt
  suffices h : ∀ (acc : List (FVar b)) (st : EncState b) (freshExt : Nat → Bool),
      st.WellFormed →
      st.clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt n
          | _ => assignmentOf b M hFits v)) = true →
      (∀ o ∈ acc, o.id < st.nextFresh) →
      let (lst', st') := worlds.foldl (preEqObligationStep b t t') (acc, st)
      ∃ freshExt' : Nat → Bool,
        (∀ n < st.nextFresh, freshExt' n = freshExt n) ∧
        st'.WellFormed ∧
        st'.clauses.all (SAT.Clause.eval
          (fun v => match v with
            | Var.Fresh n => freshExt' n
            | _ => assignmentOf b M hFits v)) = true ∧
        (∀ o ∈ lst', o.id < st'.nextFresh) ∧
        -- Key invariant: lst'.all = worlds.all semOw && acc.all freshExt
        lst'.all (fun o => freshExt' o.id) =
          (worlds.all (fun w => semOw hFits.view t t' w) && acc.all (fun o => freshExt o.id)) by
    have hRes := h [] st freshExt hWF hSat (by simp)
    simp only [List.all_nil, Bool.and_true] at hRes
    exact hRes
  intro acc st₀ freshExt₀ hWF₀ hSat₀ hAccFresh
  induction worlds generalizing acc st₀ freshExt₀ with
  | nil =>
    simp only [List.foldl_nil, List.all_nil, Bool.true_and]
    use freshExt₀
    refine ⟨fun _ _ => rfl, hWF₀, hSat₀, hAccFresh, rfl⟩
  | cons w ws ih =>
    simp only [List.foldl_cons, List.all_cons]
    have hStep := preEqObligationStep_preserves_sat hFits t t' w (acc, st₀) hWF₀ freshExt₀
        hSat₀ hAccFresh
    obtain ⟨freshExt1, hAgree1, hWF1, hSat1, hFresh1, hSemNew⟩ := hStep
    let acc1 := preEqObligationStep b t t' (acc, st₀) w
    have hAcc1Fresh : ∀ o ∈ acc1.1, o.id < acc1.2.nextFresh := hFresh1
    -- Apply IH to get lst' and freshExt'
    have hIH := ih acc1.1 acc1.2 freshExt1 hWF1 hSat1 hAcc1Fresh
    obtain ⟨freshExt', hAgree', hWF', hSat', hFresh', hSem'⟩ := hIH
    use freshExt'
    constructor
    · intro n hn
      have hMono : st₀.nextFresh ≤ acc1.2.nextFresh :=
        preEqObligationStep_nextFresh_mono t t' (acc, st₀) w
      rw [hAgree' n (Nat.lt_of_lt_of_le hn hMono), hAgree1 n hn]
    constructor
    · exact hWF'
    constructor
    · exact hSat'
    constructor
    · exact hFresh'
    · -- Need: lst'.all freshExt' = (semOw w && ws.all semOw) && acc.all freshExt₀
      -- hSem' : lst'.all freshExt' = ws.all semOw && acc1.1.all freshExt1
      -- acc1.1 = [o_w] ++ acc where o_w.id has value semOw w under freshExt1
      rw [hSem']
      -- Unfold acc1 structure: preEqObligationStep gives (newO :: acc, st')
      -- so acc1.1.all = newO && acc.all, and hSemNew says freshExt1 newO.id = semOw
      -- First show acc1.1.all = semOw w && acc.all
      have hAcc1Struct :
          acc1.1 = (mkOw b t w (mkDw b t' w st₀).1 (mkDw b t' w st₀).2).1 :: acc := by
        simp only [acc1, preEqObligationStep]
      have hNewId : acc1.1.getD 0 ⟨0⟩ = (mkOw b t w (mkDw b t' w st₀).1 (mkDw b t' w st₀).2).1 := by
        simp only [hAcc1Struct, List.getD_cons_zero]
      have hAcc1All : acc1.1.all (fun o => freshExt1 o.id) =
          (semOw hFits.view t t' w && acc.all (fun o => freshExt1 o.id)) := by
        rw [hAcc1Struct, List.all_cons]
        congr 1
      rw [hAcc1All]
      -- acc.all freshExt1 = acc.all freshExt₀ by agreement
      have hAccAgree : acc.all (fun o => freshExt1 o.id) = acc.all (fun o => freshExt₀ o.id) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true]
        constructor
        · intro h o ho
          rw [← hAgree1 o.id (hAccFresh o ho)]; exact h o ho
        · intro h o ho
          rw [hAgree1 o.id (hAccFresh o ho)]; exact h o ho
      rw [hAccAgree]
      -- ws.all sem && (sem w && acc.all fresh) = (sem w && ws.all sem) && acc.all fresh
      -- Bool.and is associative and commutative
      cases ws.all (fun w => semOw hFits.view t t' w) <;>
      cases semOw hFits.view t t' w <;>
      cases acc.all (fun o => freshExt₀ o.id) <;>
      rfl

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: fold of preEqAccStep preserves satisfiability and tracks semantic value. -/
lemma acc_fold_preserves_sat {b : Bounds S}
    (σ₀ : SAT.Assignment (Var b))
    (obligations : List (FVar b))
    (acc : FVar b × EncState b)
    (hWF : acc.2.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : acc.2.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => σ₀ v)) = true)
    (hCur : acc.1.id < acc.2.nextFresh)
    (hOsFresh : ∀ o ∈ obligations, o.id < acc.2.nextFresh) :
    let (eqFinal, st') := obligations.foldl (preEqAccStep b) acc
    ∃ freshExt' : Nat → Bool,
      (∀ n < acc.2.nextFresh, freshExt' n = freshExt n) ∧
      st'.WellFormed ∧
      st'.clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt' n
          | _ => σ₀ v)) = true ∧
      eqFinal.id < st'.nextFresh ∧
      freshExt' eqFinal.id = (freshExt acc.1.id && obligations.all (fun o => freshExt o.id)) := by
  induction obligations generalizing acc freshExt with
  | nil =>
    simp only [List.foldl_nil, List.all_nil, Bool.and_true]
    exact ⟨freshExt, fun _ _ => rfl, hWF, hSat, hCur, rfl⟩
  | cons o os ih =>
    simp only [List.foldl_cons, List.all_cons]
    have hOLt := hOsFresh o List.mem_cons_self
    have hStep := preEqAccStep_preserves_sat σ₀ acc o hWF freshExt hSat hCur hOLt
    obtain ⟨hAgree1, hWF1, hSat1, hNextFresh1⟩ := hStep
    let freshExt1 := fun n => if n = acc.2.nextFresh then
      (freshExt acc.1.id && freshExt o.id) else freshExt n
    let acc1 := preEqAccStep b acc o
    have hMono : acc.2.nextFresh < acc1.2.nextFresh := preEqAccStep_nextFresh_lt acc o
    have hOsFreshRest : ∀ o' ∈ os, o'.id < acc1.2.nextFresh := by
      intro o' hMem
      have := hOsFresh o' (List.mem_cons_of_mem _ hMem)
      omega
    have hAcc1Id : acc1.1.id = acc.2.nextFresh := by
      simp only [acc1, preEqAccStep, EncState.allocFresh_fst]
    have hCur1 : acc1.1.id < acc1.2.nextFresh := hNextFresh1
    have hIH := ih acc1 hWF1 freshExt1 hSat1 hCur1 hOsFreshRest
    obtain ⟨freshExt', hAgree', hWF', hSat', hFresh', hSem'⟩ := hIH
    use freshExt'
    refine ⟨?_, hWF', hSat', hFresh', ?_⟩
    · intro n hn
      have h1 : freshExt1 n = freshExt n := by
        simp only [freshExt1]
        split_ifs with heq
        · omega
        · rfl
      have h' := hAgree' n (Nat.lt_trans hn hMono)
      rw [← h1]; exact h'
    · -- Semantic value: freshExt' eqFinal.id = freshExt acc.1.id && freshExt o.id && os.all ...
      rw [hSem']
      -- hSem' : freshExt' eqFinal.id = freshExt1 acc1.1.id && os.all (freshExt1 ·.id)
      -- freshExt1 acc1.1.id = freshExt acc.1.id && freshExt o.id (by hAcc1Id)
      have hFE1_acc1 : freshExt1 acc1.1.id = (freshExt acc.1.id && freshExt o.id) := by
        simp only [freshExt1, hAcc1Id, ↓reduceIte]
      -- os.all (freshExt1 ·.id) = os.all (freshExt ·.id) (agreement below acc.2.nextFresh)
      have hOsAgree : os.all (fun o' => freshExt1 o'.id) = os.all (fun o' => freshExt o'.id) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true]
        constructor
        · intro h o' ho'
          have := h o' ho'
          have hO'Fresh := hOsFresh o' (List.mem_cons_of_mem _ ho')
          simp only [freshExt1] at this
          split_ifs at this with heq
          · omega
          · exact this
        · intro h o' ho'
          have := h o' ho'
          have hO'Fresh := hOsFresh o' (List.mem_cons_of_mem _ ho')
          simp only [freshExt1]
          split_ifs with heq
          · omega
          · exact this
      rw [hFE1_acc1, hOsAgree, Bool.and_assoc]

omit [DecidableEq S.AtomicPredType] in
/-- Helper: addPreEqPair_core preserves satisfiability -/
lemma addPreEqPair_core_equisat
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (H0 H' : b.times)
    (stk : EncState b)
    (hWFstk : stk.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : stk.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => assignmentOf b M hFits v)) = true) :
    ∃ freshExt' : Nat → Bool,
      (∀ n < stk.nextFresh, freshExt' n = freshExt n) ∧
      (addPreEqPair_core b H0 H' stk).clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt' n
          | _ => assignmentOf b M hFits v)) = true := by
  classical
  let σ₀ := assignmentOf b M hFits

  -- Unfold addPreEqPair_core to see its structure
  unfold addPreEqPair_core

  -- Step 1: First fold of preEqObligationStep for H0→H'
  let fold1 :=
    (WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], stk)
  let os := fold1.1
  let st1 := fold1.2

  have hFold1 :=
    obligation_fold_preserves_sat hFits H0 H' (WId.allWorlds b) stk hWFstk freshExt hSat
  obtain ⟨freshExt1, hAgree1, hWF1, hSat1, hOsFresh1, hSem1⟩ := hFold1

  -- Step 2: Second fold of preEqObligationStep for H'→H0
  have hFold2 :=
    obligation_fold_preserves_sat hFits H' H0 (WId.allWorlds b) st1 hWF1 freshExt1 hSat1
  obtain ⟨freshExt2, hAgree2, hWF2, hSat2, hOsFresh2, hSem2⟩ := hFold2

  let fold2 := (WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], st1)
  let os' := fold2.1
  let st2 := fold2.2

  -- Step 3: Allocate base and add [base]
  let baseAlloc := EncState.allocFresh b st2
  let base := baseAlloc.1
  let st3a := baseAlloc.2
  let st3 := EncState.addClause b st3a [SAT.Lit.pos (FVar.toVar b base)]

  have hBaseId : base.id = st2.nextFresh := EncState.allocFresh_fst b st2
  have hSt3aNext : st3a.nextFresh = st2.nextFresh + 1 := EncState.allocFresh_nextFresh b st2
  have hWF3a : st3a.WellFormed := EncState.allocFresh_wf hWF2
  have hSt3aClauses : st3a.clauses = st2.clauses := EncState.allocFresh_clauses_eq b st2

  -- freshExt3 sets base to true
  let freshExt3 := fun n => if n = st2.nextFresh then true else freshExt2 n

  have hSat3a : st3a.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt3 n
        | _ => σ₀ v)) = true := by
    rw [hSt3aClauses]
    rw [List.all_eq_true] at hSat2 ⊢
    intro clause hClause
    have hEval := hSat2 clause hClause
    have hClauseBelow : clauseFreshBelow clause st2.nextFresh := hWF2 clause hClause
    have hAgree : ∀ n < st2.nextFresh, freshExt3 n = freshExt2 n := by
      intro n hn; simp only [freshExt3, ne_of_lt hn, ↓reduceIte]
    rw [clause_eval_of_agree_on_fresh σ₀ freshExt2 freshExt3 clause st2.nextFresh
      hClauseBelow hAgree]
    exact hEval

  -- [base] clause is satisfied since base = true
  have hWF3 : st3.WellFormed := by
    apply EncState.addClause_wf hWF3a
    intro lit hLit
    simp only [List.mem_singleton] at hLit
    simp only [hLit, SAT.Lit.getVar, FVar.toVar, litFreshBelow, hBaseId, hSt3aNext]
    omega

  have hSat3 : st3.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt3 n
        | _ => σ₀ v)) = true := by
    -- The [base] clause is satisfied since freshExt3(base.id) = true
    -- Old clauses are satisfied by hSat3a
    rw [List.all_eq_true]
    intro clause hClause
    simp only [st3, EncState.addClause, List.mem_cons] at hClause
    rcases hClause with rfl | hClause
    · -- The new [base] clause
      simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, FVar.toVar, freshExt3, hBaseId,
        ↓reduceIte]
      decide
    · -- Old clause from st3a.clauses
      exact List.all_eq_true.mp hSat3a clause hClause

  have hBaseFresh : base.id < st3.nextFresh := by
    -- base.id = st2.nextFresh, st3.nextFresh = st2.nextFresh + 1
    simp only [st3, st3a, EncState.addClause_nextFresh, hSt3aNext, hBaseId]
    omega

  -- Step 4 & 5: Fold preEqAccStep over os and os'
  have hAccFold := acc_fold_preserves_sat σ₀ (os ++ os') (base, st3)
    hWF3 freshExt3 hSat3 hBaseFresh
    (by
      -- Each o in os has o.id < st1.nextFresh ≤ st2.nextFresh < st3.nextFresh
      -- Each o in os' has o.id < st2.nextFresh < st3.nextFresh
      intro o ho
      -- The goal involves (base, st3).2.nextFresh = st3.nextFresh
      simp only
      rw [List.mem_append] at ho
      have hSt3Next' : st3.nextFresh = st2.nextFresh + 1 := by
        simp only [st3, st3a, EncState.addClause_nextFresh, hSt3aNext]
      have hMono1to2 : st1.nextFresh ≤ st2.nextFresh := by
        have h := obligation_fold_nextFresh_mono H' H0 (WId.allWorlds b) ([], st1)
        simp only at h
        simp only [fold2, st2] at h ⊢
        exact h
      rcases ho with ho | ho'
      · -- o ∈ os, so o.id < st1.nextFresh ≤ st2.nextFresh < st3.nextFresh
        have hOFresh : o.id < st1.nextFresh := by
          have h := hOsFresh1 o ho
          exact h
        omega
      · -- o ∈ os', so o.id < st2.nextFresh < st3.nextFresh
        have hOFresh : o.id < st2.nextFresh := by
          have h := hOsFresh2 o ho'
          exact h
        omega)
  obtain ⟨freshExt4, hAgree4, hWF4, hSat4, hEqFinalFresh, hSemVal⟩ := hAccFold

  -- The eqFinal from the fold - note the actual definition uses two separate folds
  -- (os ++ os').foldl step init = os'.foldl step (os.foldl step init)
  let accFold := (os ++ os').foldl (preEqAccStep b) (base, st3)
  let eqFinal := accFold.1
  let st5 := accFold.2

  -- Show the foldl structure matches the definition
  have hFoldEq : (os ++ os').foldl (preEqAccStep b) (base, st3) =
                 os'.foldl (preEqAccStep b) (os.foldl (preEqAccStep b) (base, st3)) := by
    rw [List.foldl_append]

  -- Derive semantic value from hSem1 and hSem2 via agreement
  -- os.all (freshExt3 ·.id) = os.all (freshExt1 ·.id) (agreement below st1.nextFresh)
  have hMono1to2 : st1.nextFresh ≤ st2.nextFresh :=
    obligation_fold_nextFresh_mono H' H0 (WId.allWorlds b) ([], st1)
  have hOsAgree3to1 : os.all (fun o => freshExt3 o.id) = os.all (fun o => freshExt1 o.id) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro h o ho
      have := h o ho
      have hOFresh : o.id < st1.nextFresh := hOsFresh1 o ho
      simp only [freshExt3] at this
      split_ifs at this with heq
      · omega
      · rw [hAgree2 o.id hOFresh] at this; exact this
    · intro h o ho
      have := h o ho
      have hOFresh : o.id < st1.nextFresh := hOsFresh1 o ho
      simp only [freshExt3]
      split_ifs with heq
      · omega
      · rw [hAgree2 o.id hOFresh]; exact this

  -- os'.all (freshExt3 ·.id) = os'.all (freshExt2 ·.id) (agreement below st2.nextFresh)
  have hOs'Agree3to2 : os'.all (fun o => freshExt3 o.id) = os'.all (fun o => freshExt2 o.id) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro h o ho
      have := h o ho
      have hOFresh : o.id < st2.nextFresh := hOsFresh2 o ho
      simp only [freshExt3] at this
      split_ifs at this with heq
      · omega
      · exact this
    · intro h o ho
      have := h o ho
      have hOFresh : o.id < st2.nextFresh := hOsFresh2 o ho
      simp only [freshExt3]
      split_ifs with heq
      · omega
      · exact this

  -- Combine: (os ++ os').all (freshExt3 ·.id) = semPreEqFull H0 H'
  have hSemCombined :
      (os ++ os').all (fun o => freshExt3 o.id) = semPreEqFull hFits.view H0 H' := by
    rw [List.all_append, hOsAgree3to1, hOs'Agree3to2, hSem1, hSem2]
    simp only [semPreEqFull, semObligationChain]

  -- Step 6: addPreEqExpose links eqFinal ↔ PreEq
  have hExposeWF := addPreEqExpose_wf b H0 H' eqFinal st5 hWF4 hEqFinalFresh
  have hExpose := addPreEqExpose_preserves_sat σ₀ H0 H' eqFinal st5 hWF4 freshExt4 hSat4
    hEqFinalFresh
    (by
      -- Need: freshExt4 eqFinal.id = σ₀ (Var.PreEq H0 H')
      -- hSemVal : freshExt4 eqFinal.id = freshExt3 base.id && (os ++ os').all (freshExt3 ·.id)
      -- freshExt3 base.id = true (since base.id = st2.nextFresh and freshExt3 sets that to true)
      have hBase : freshExt3 base.id = true := by simp only [freshExt3, hBaseId, ↓reduceIte]
      rw [hSemVal, hBase, Bool.true_and, hSemCombined, semPreEqFull_eq_preEqAt hFits H0 H']
      exact (assignmentOf_PreEq hFits H0 H').symm)

  obtain ⟨hWF5, hSat5⟩ := hExpose

  use freshExt4
  constructor
  · -- Agreement below stk.nextFresh
    intro n hn
    have h1 := hAgree1 n hn
    have hMono1 : stk.nextFresh ≤ st1.nextFresh :=
      obligation_fold_nextFresh_mono H0 H' (WId.allWorlds b) ([], stk)
    have h2 := hAgree2 n (Nat.lt_of_lt_of_le hn hMono1)
    have hMono2 : st1.nextFresh ≤ st2.nextFresh :=
      obligation_fold_nextFresh_mono H' H0 (WId.allWorlds b) ([], st1)
    have hSt3Next : st3.nextFresh = st2.nextFresh + 1 := by
      simp only [st3, st3a, EncState.addClause_nextFresh, hSt3aNext]
    have hn3 : n < st3.nextFresh := by omega
    have h4 := hAgree4 n hn3
    simp only [freshExt3] at h4
    split_ifs at h4 with heq
    · omega
    · -- h4 : freshExt4 n = freshExt2 n
      -- h2 : freshExt2 n = freshExt1 n
      -- h1 : freshExt1 n = freshExt n
      rw [h4, h2, h1]
  · -- Need to show (addPreEqPair_core ...).clauses.all ... = true
    -- The actual definition uses two separate folds which equals (os ++ os').foldl by hFoldEq
    -- Show the goal matches hSat5 using the foldl equivalence
    simp only [accFold, eqFinal, st5, hFoldEq] at hSat5 ⊢
    exact hSat5

omit [DecidableEq S.AtomicPredType] in
/-- For any well-formed state and assignment satisfying its clauses,
    addPreEqPair's clauses are satisfiable by extending the assignment.

    Structure of proof:
    - addPreEqPair = addPreEqPair_core, then if H0=H' also add [PreEq H0 H']
    - addPreEqPair_core builds obligations via preEqObligationStep folds,
      chains them via preEqAccStep folds, and links via addPreEqExpose
    - Each step is handled by a preservation lemma:
      * preEqObligationStep_preserves_sat (uses mkDw_preserves_sat + mkOw_preserves_sat)
      * preEqAccStep_preserves_sat (uses addAccStep_preserves_sat)
      * addPreEqExpose_preserves_sat -/
lemma addPreEqPair_equisat
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (H0 H' : b.times)
    (stk : EncState b)
    (hWFstk : stk.WellFormed)
    (freshExt : Nat → Bool)
    (hSat : stk.clauses.all (SAT.Clause.eval
      (fun v => match v with
        | Var.Fresh n => freshExt n
        | _ => assignmentOf b M hFits v)) = true) :
    ∃ freshExt' : Nat → Bool,
      (∀ n < stk.nextFresh, freshExt' n = freshExt n) ∧
      (addPreEqPair b H0 H' stk).clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt' n
          | _ => assignmentOf b M hFits v)) = true := by
  classical
  let σ₀ := assignmentOf b M hFits

  -- addPreEqPair = addPreEqPair_core, then if H0=H' add [PreEq H0 H']
  unfold addPreEqPair

  -- First prove for addPreEqPair_core
  have hCore := addPreEqPair_core_equisat b M hFits H0 H' stk hWFstk freshExt hSat

  obtain ⟨freshExtCore, hAgreeCore, hSatCore⟩ := hCore

  -- Now handle the if-then-else
  by_cases hEq : H0 = H'
  · -- H0 = H': add [PreEq H0 H']
    subst hEq
    simp only [↓reduceIte]
    use freshExtCore
    constructor
    · exact hAgreeCore
    · rw [List.all_eq_true]
      intro clause hClause
      simp only [EncState.addClause] at hClause
      cases hClause with
      | head _ =>
        -- The new clause [PreEq H0 H0]
        simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, Bool.false_or]
        -- PreEq H0 H0 = true by reflexivity: preEqAt ev H H = decide (histEq pH pH) = true
        simp only [assignmentOf, preEqAt, decide_eq_true_eq]
        exact PreHistory.histEq_refl _
      | tail _ hRest =>
        -- Old clause from addPreEqPair_core
        exact List.all_eq_true.mp hSatCore clause hRest
  · -- H0 ≠ H': just addPreEqPair_core
    simp only [hEq, ↓reduceIte]
    exact ⟨freshExtCore, hAgreeCore, hSatCore⟩

/-! ## Main Theorem

The proof proceeds by showing that when Fresh vars are set to their semantic values
(as determined by the Tseytin encoding structure), all clauses are satisfied.
-/

omit [DecidableEq S.AtomicPredType] in
theorem addPreEqFrom_clauses_satisfiable
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (H0 : b.times)
    (st : EncState b)
    (hWF : st.WellFormed)
    (hBase : st.clauses.all (SAT.Clause.eval (assignmentOf b M hFits)) = true) :
    ∃ σ_ext : SAT.Assignment (Var b),
      (∀ v, ¬Var.isFresh v → σ_ext v = assignmentOf b M hFits v) ∧
      (addPreEqFrom b H0 st).clauses.all (SAT.Clause.eval σ_ext) = true := by
  classical
  let σ₀ := assignmentOf b M hFits
  let ev := hFits.view
  let st' := addPreEqFrom b H0 st

  -- We need to construct an assignment that:
  -- 1. Agrees with σ₀ on non-Fresh vars
  -- 2. Agrees with σ₀ on Fresh vars < st.nextFresh
  -- 3. Sets Fresh vars in [st.nextFresh, st'.nextFresh) to their semantic values
  --
  -- The key insight: addPreEqFrom creates Tseytin gadgets that encode:
  --   PreEq(H0, H') ↔ (all obligations satisfied)
  --
  -- Since assignmentOf sets PreEq(H0, H') correctly (by preEqAt_correct),
  -- and Mem vars correctly, the Tseytin encoding has a unique satisfying extension.
  --
  -- Approach: Use structural determinism. Each gadget type has a unique satisfying
  -- value for its output given its inputs. We define σ_ext to set each Fresh var
  -- to this unique value.

  -- For the proof, we use a simplified approach:
  -- The clauses from addPreEqFrom encode logical equivalences.
  -- For each equivalence, when inputs have their correct values,
  -- setting output = f(inputs) satisfies all related clauses.

  -- The detailed proof requires tracking Fresh indices through the encoding.
  -- For now, we establish the structure and defer the index tracking.

  -- Define σ_ext that sets Fresh vars to their correct semantic values
  -- For vars in [st.nextFresh, st'.nextFresh), we need the Tseytin semantic value
  -- For other vars, use σ₀

  -- Rather than computing exact values, we use Classical.choice on the existence
  -- of a satisfying assignment (which follows from Tseytin equisatisfiability).

  -- The key insight: addPreEqFrom creates Tseytin gadgets that encode logical equivalences.
  -- For each gadget, there is a unique satisfying extension given the input values.
  --
  -- We construct the extension by setting each Fresh var to its semantic value:
  -- - mkY vars: y = Mem(t', w') && PreEq(w.ti, w'.ti)
  -- - mkDw vars: d = ∃ w' with sameSig. y_{w,w'}
  -- - mkOw vars: o = ¬Mem(t, w) || d
  -- - base var: true
  -- - chain vars: conjunction of all preceding obligations
  -- - eqFinal: = PreEq(H0, H')
  --
  -- Since assignmentOf sets Mem and PreEq to their correct semantic values,
  -- the Tseytin encoding has a satisfying extension.

  -- For now, we construct the witness abstractly using Classical.choice.
  -- A fully constructive proof would require tracking Fresh indices through the fold.

  -- Key lemma: addPreEqFrom is a fold that preserves satisfiability.
  -- At each step, addPreEqPair adds clauses for one (H0, H') pair.
  -- These clauses encode: eqFinal ↔ PreEq(H0, H')
  -- Since σ₀ sets PreEq(H0, H') correctly, we can set eqFinal = σ₀(PreEq(H0, H'))
  -- and the internal gadget vars to their semantic values.

  -- We use the fold structure to build the extension incrementally.
  -- For now, we defer to a helper lemma about fold satisfiability.

  -- We construct freshExt by induction on the fold structure.
  -- The approach: use foldl to build up both the clauses and the satisfying extension.
  --
  -- Key observation: at each step of the fold, addPreEqPair adds clauses that are
  -- satisfiable when internal Fresh vars are set to their semantic values.
  --
  -- We use the fold lemma structure to prove this.

  -- First, establish that st.clauses are satisfied by σ₀ (given by hBase)
  have hBaseSat : st.clauses.all (SAT.Clause.eval σ₀) = true := hBase

  -- The fold preserves satisfiability with an extended assignment.
  -- We prove by induction on timesL.

  -- Define the satisfiability predicate for states:
  -- A state is "satisfiable from σ₀" if there exists a freshExt such that
  -- all clauses are satisfied by (σ₀ with Fresh vars from freshExt)
  -- We also track monotonicity: st.nextFresh ≤ stk.nextFresh
  let satProp (stk : EncState b) : Prop :=
    st.nextFresh ≤ stk.nextFresh ∧
    stk.WellFormed ∧
    ∃ freshExt : Nat → Bool,
      (∀ n < st.nextFresh, freshExt n = σ₀ (Var.Fresh n)) ∧
      stk.clauses.all (SAT.Clause.eval
        (fun v => match v with
          | Var.Fresh n => freshExt n
          | _ => σ₀ v)) = true

  -- Base case: st satisfies satProp
  have hBaseCase : satProp st := by
    refine ⟨le_refl _, hWF, fun n => σ₀ (Var.Fresh n), ?_, ?_⟩
    · intro n _; rfl
    · -- Need to show σ₀ = (fun v => match v with | Fresh n => σ₀ (Fresh n) | _ => σ₀ v)
      -- on the relevant clauses. This is trivial since they're extensionally equal.
      convert hBase using 2
      ext clause
      congr 1
      ext v
      cases v <;> rfl

  -- For the induction, we need to show:
  -- satProp stk → satProp (addPreEqPair b H0 H' stk)
  -- This follows because addPreEqPair adds Tseytin clauses that are satisfiable
  -- when internal Fresh vars are set to their semantic values.

  -- Key step lemma: addPreEqPair preserves satProp
  -- This requires showing that when we extend freshExt to set new Fresh vars
  -- to their semantic values, all new clauses are satisfied.
  have hStep : ∀ H' stk, satProp stk → satProp (addPreEqPair b H0 H' stk) := by
    intro H' stk ⟨hMono, hWFstk, freshExt, hBase', hSat⟩
    let stk' := addPreEqPair b H0 H' stk

    -- The assignment using existing freshExt
    let σstk : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => freshExt n
      | _ => σ₀ v

    -- Key insight: addPreEqPair creates Tseytin gadgets encoding:
    --   Fresh vars ↔ functions of (Mem, PreEq) values
    -- For each gadget type, there is a unique satisfying assignment to the output
    -- given the input values. We define freshExt' by simulation.

    -- The semantic value for the final variable is σ₀(PreEq H0 H').
    -- All intermediate vars have semantic values determined by the encoding structure.
    -- We use Classical choice to pick a satisfying extension.

    -- The Tseytin structure guarantees: if we set each gadget's output to its
    -- semantic value (determined by inputs), all clauses are satisfied.
    -- Since addPreEqPair only uses Mem and PreEq values (which σ₀ handles correctly),
    -- and Fresh vars from stk (which freshExt handles), there exists such extension.

    -- Use Classical.choose on the existence of freshExt' extending freshExt
    -- Key property: Tseytin encodings are equisatisfiable with unique extensions

    -- For the base clause [pos base], we need base = true.
    -- For mkY clauses, we need y = Mem && PreEq.
    -- For mkOw clauses, we need o = !Mem || d.
    -- For addAccStep, we need next = cur && eqb.
    -- For addPreEqExpose, we need v = PreEq(H0, H').

    -- Define freshExt' that extends freshExt with correct semantic values
    -- For n < stk.nextFresh: use freshExt n
    -- For n >= stk.nextFresh: simulate the encoding to compute semantic value

    -- The existence of freshExt' follows from the Tseytin equisatisfiability:
    -- each gadget can be satisfied by setting output = f(inputs).
    -- We prove this by constructing freshExt' explicitly.

    -- First, we show clauses from stk are still satisfied (subset property)
    have hStkSubset : stk.clauses ⊆ stk'.clauses :=
      addPreEqPair_clauses_subset b H0 H' stk

    -- The new clauses are exactly those from addPreEqPair_core + possible reflexivity
    -- Each gadget type can be satisfied by setting outputs to semantic values.

    -- For now, we use the equisatisfiability argument abstractly.
    -- The key insight: addPreEqPair_core creates gadgets where each output variable
    -- can be set to make all its clauses true, given correct input values.

    -- We construct freshExt' by simulating the encoding:
    -- This is complex because it requires tracking which Fresh index corresponds
    -- to which gadget. Instead, we use the abstract existence argument.

    -- Abstract existence: There exists a Boolean function f : Nat → Bool such that
    -- extending freshExt with f for indices in [stk.nextFresh, stk'.nextFresh)
    -- satisfies all clauses from addPreEqPair.

    -- The proof of existence follows from the Tseytin structure:
    -- 1. For base var: set to true
    -- 2. For mkY vars: set y = σ₀(Mem) && σ₀(PreEq)
    -- 3. For mkBigOrIff vars: set u = any of inputs
    -- 4. For mkOw vars: set o = !σ₀(Mem) || d
    -- 5. For addAccStep vars: set next = cur && eqb
    -- Each choice makes all clauses from that gadget true.

    -- Since the encoding structure is deterministic and each gadget has
    -- a satisfying assignment, the composition satisfies all clauses.

    -- Use propositional completeness: for any CNF that is satisfiable given
    -- some assignment to input vars, there exists an extension to all vars.

    -- The Tseytin encoding is satisfiable iff PreEq(H0, H') = chain result.
    -- Since we're encoding an equivalence (not assuming either side),
    -- ANY truth value for PreEq(H0, H') leads to a satisfying extension.

    -- Monotonicity and well-formedness for stk'
    have hMono' : st.nextFresh ≤ stk'.nextFresh :=
      le_trans hMono (addPreEqPair_nextFresh_mono b H0 H' stk)
    have hWFstk' : stk'.WellFormed := addPreEqPair_wf b H0 H' stk hWFstk

    -- Key lemma: addPreEqPair's new clauses are satisfiable given correct input values.
    -- We use existence via Classical choice rather than explicit construction.
    --
    -- The existence follows from Tseytin equisatisfiability:
    -- Each gadget (mkY, mkOw, addAccStep, addPreEqExpose) encodes an equivalence
    -- of the form: output ↔ f(inputs). For any assignment to inputs, setting
    -- output = f(inputs) satisfies all clauses from that gadget.
    --
    -- Since addPreEqPair composes these gadgets sequentially, and σstk correctly
    -- sets all input values (Mem, PreEq from σ₀, and Fresh vars from freshExt),
    -- there exists an extension that satisfies all new clauses.

    -- Define the property we need: existence of satisfying extension
    let extProp (f : Nat → Bool) : Prop :=
      (∀ n < stk.nextFresh, f n = freshExt n) ∧
      stk'.clauses.all (SAT.Clause.eval (fun v =>
        match v with
        | Var.Fresh n => f n
        | _ => σ₀ v)) = true

    -- Prove existence of such f using the equisatisfiability lemma
    have hExtExists : ∃ f, extProp f := by
      exact addPreEqPair_equisat b M hFits H0 H' stk hWFstk freshExt hSat

    -- Use Classical.choose to get freshExt'
    let freshExt' := Classical.choose hExtExists
    have hFreshExt' := Classical.choose_spec hExtExists

    refine ⟨hMono', hWFstk', freshExt', ?_, ?_⟩

    -- First goal: freshExt' agrees with σ₀ on Fresh vars < st.nextFresh
    · intro n hn
      have hMonoFresh : n < stk.nextFresh := Nat.lt_of_lt_of_le hn hMono
      have hAgree := hFreshExt'.1 n hMonoFresh
      simp only [freshExt'] at hAgree ⊢
      rw [hAgree]
      exact hBase' n hn

    -- Second goal: all clauses in stk'.clauses are satisfied
    · exact hFreshExt'.2

  -- Apply foldl induction with the step lemma
  -- We prove by induction that foldl preserves satProp
  have hFoldProp : ∀ (ts : List b.times) (stk : EncState b),
      satProp stk → satProp (ts.foldl (fun acc H' => addPreEqPair b H0 H' acc) stk) := by
    intro ts
    induction ts with
    | nil => intro stk hSat; simp only [List.foldl_nil]; exact hSat
    | cons H' rest ih =>
        intro stk hSat
        simp only [List.foldl_cons]
        exact ih (addPreEqPair b H0 H' stk) (hStep H' stk hSat)

  have hSatExt : satProp st' := by
    simp only [st']
    unfold addPreEqFrom
    exact hFoldProp (Bounds.timesL b) st hBaseCase

  obtain ⟨_, _, freshExt, hFreshBase, hFreshSat⟩ := hSatExt

  let σ_ext : SAT.Assignment (Var b) := fun v =>
    match v with
    | Var.Fresh n => freshExt n
    | _ => σ₀ v

  use σ_ext

  constructor
  · -- Non-Fresh vars agree with σ₀
    intro v hNotFresh
    cases v with
    | Fresh n => exfalso; exact hNotFresh rfl
    | _ => rfl

  · -- All clauses satisfied
    rw [List.all_eq_true]
    intro clause hClause
    have := List.all_eq_true.mp hFreshSat clause hClause
    -- σ_ext and the function in satProp are definitionally equal
    exact this

end Encoding
