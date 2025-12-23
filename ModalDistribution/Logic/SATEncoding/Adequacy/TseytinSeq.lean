import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.WFViews
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.PreEqSoundness
import ModalDistribution.Logic.SATEncoding.PreEqCompleteness
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly
import ModalDistribution.Logic.SATEncoding.Adequacy.HereditaryTransitivity

/-!
# Tseytin Correctness for Sequentiality (seq)

This file proves that the Tseytin encoding correctly captures the semantics of
the sequentiality formula.

## Main Result

- `encode_seq_correct`: If the encoding produces control variable u for sequentiality,
  then u = true iff the decoded world satisfies the sequentiality property.

## Strategy

The sequentiality encoding checks that the world is in the root prehistory.
-/

open ModalDistribution Encoding Logic PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.Value S)]
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]

/-! ## Tseytin Correctness for Sequentiality -/

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The sequentiality encoding produces a bi-conditional u ↔ Seq(w.ti, w.p).

    Forward direction: if u = true, then Seq(w.ti, w.p) = true. -/
lemma encode_seq_forward (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u : FVar b) (clauses : List (SAT.Clause (Var b)))
    (w : WId b)
    (hEncoding : clauses = [[SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)],
                             [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true)
    (hU : σ (FVar.toVar b u) = true) :
    σ (Var.Seq w.ti w.p) = true := by
  -- The first clause is [¬u, Seq(w.ti, w.p)]
  -- If σ(u) = true and the clause is satisfied, then σ(Seq(w.ti, w.p)) = true
  have hClauseIn : [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)] ∈ clauses := by
    rw [hEncoding]
    simp

  have hClauseTrue : SAT.Clause.eval σ
      [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)] = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Evaluate the clause
  unfold SAT.Clause.eval at hClauseTrue
  simp [SAT.Lit.eval, hU] at hClauseTrue
  exact hClauseTrue

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The sequentiality encoding produces a bi-conditional u ↔ Seq(w.ti, w.p).

    Backward direction: if Seq(w.ti, w.p) = true, then u = true. -/
lemma encode_seq_backward (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u : FVar b) (clauses : List (SAT.Clause (Var b)))
    (w : WId b)
    (hEncoding : clauses = [[SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)],
                             [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true)
    (hSeq : σ (Var.Seq w.ti w.p) = true) :
    σ (FVar.toVar b u) = true := by
  -- The second clause is [¬Seq(w.ti, w.p), u]
  -- If σ(Seq(w.ti, w.p)) = true and the clause is satisfied, then σ(u) = true
  have hClauseIn : [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)] ∈ clauses := by
    rw [hEncoding]
    simp

  have hClauseTrue : SAT.Clause.eval σ
      [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)] = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Evaluate the clause
  unfold SAT.Clause.eval at hClauseTrue
  simp [SAT.Lit.eval, hSeq] at hClauseTrue
  exact hClauseTrue

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Main correctness: σ(u) = true ↔ σ(Var.Seq w.ti w.p) = true.

    The seq encoding correctly captures the bi-conditional via two clauses. -/
lemma encode_seq_correct (b : Bounds S) (σ : SAT.Assignment (Var b))
    (u : FVar b) (clauses : List (SAT.Clause (Var b)))
    (w : WId b)
    (hEncoding : clauses = [[SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)],
                             [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)]])
    (hSat : clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b u) = true) ↔ (σ (Var.Seq w.ti w.p) = true) := by
  constructor
  · exact encode_seq_forward b σ u clauses w hEncoding hSat
  · exact encode_seq_backward b σ u clauses w hEncoding hSat

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma cnfExists_forward_clause_mem
    (b : Bounds S) (H : b.times) (w : WId b) :
    [ SAT.Lit.neg (Var.Mem H w)
    , SAT.Lit.pos (Var.Exists H w.p w.ti) ] ∈
      (cnfExists b).clauses := by
  unfold cnfExists
  refine List.mem_flatMap.mpr ?_
  refine ⟨H, ?_, ?_⟩
  · simp [Bounds.timesL]
  · refine List.mem_map.mpr ?_
    refine ⟨w, ?_, rfl⟩
    simpa using WId.mem_allWorlds b w

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- A satisfying assignment witnessing `Mem` forces the corresponding `Exists`. -/
lemma exists_forward (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ)
    {H : b.times} {w : WId b}
    (hMem : σ (Var.Mem H w) = true) :
    σ (Var.Exists H w.p w.ti) = true := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, hExists, _, _⟩ :=
    (cnfWellFormed_eval_iff b σ).mp hWF
  have hAll : (cnfExists b).clauses.all (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hExists
  have hClauseEval :
      SAT.Clause.eval σ
          [SAT.Lit.neg (Var.Mem H w),
           SAT.Lit.pos (Var.Exists H w.p w.ti)] = true := by
    have hAll' := List.all_eq_true.mp hAll
    exact hAll' _ (cnfExists_forward_clause_mem (b := b) (H := H) (w := w))
  unfold SAT.Clause.eval at hClauseEval
  simp [SAT.Lit.eval, hMem] at hClauseEval
  exact hClauseEval

/-! ### Decoder data for sequence witnesses -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Unpack a membership proof `w ∈ decodePre H` into its SAT witnesses.
    This also returns the event equality: w.event = b.decodeMaybeEvent wid.ei -/
lemma decodePre_mem_witness (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times)
    {w : World (Fin b.nParticipants) S.EventType}
    (hMem : w ∈ decodePre b σ hWF H) :
    ∃ wid : WId b,
      σ (Var.Mem H wid) = true ∧
      w.fst = wid.p ∧
      World.event w = b.decodeMaybeEvent wid.ei ∧
      w.snd.snd = decodePre b σ hWF wid.ti := by
  classical
  obtain ⟨wid, hwEq, hMemVar⟩ :=
    exists_memVar_of_mem_decodePre b σ hWF H hMem
  refine ⟨wid, hMemVar, ?_, ?_, ?_⟩
  · have hfst := congrArg Prod.fst hwEq
    simpa using hfst.symm
  · have hsnd := congrArg Prod.snd hwEq
    have hEvent := congrArg Prod.fst hsnd
    simpa [World.event] using hEvent.symm
  · have hsnd := congrArg Prod.snd hwEq
    have hTail := congrArg Prod.snd hsnd
    simpa using hTail.symm

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Membership in `decodePre` produces the corresponding `Exists` literal. -/
lemma decodePre_mem_exists (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times)
    {w : World (Fin b.nParticipants) S.EventType}
    (hMem : w ∈ decodePre b σ hWF H) :
    ∃ ti : b.times,
      w.snd.snd = decodePre b σ hWF ti ∧
      σ (Var.Exists H w.fst ti) = true := by
  classical
  obtain ⟨wid, hMemVar, hPlace, _, hTail⟩ :=
    decodePre_mem_witness b σ hWF H hMem
  refine ⟨wid.ti, ?_, ?_⟩
  · exact hTail
  · simpa [hPlace] using exists_forward (b := b) (σ := σ) (hWF := hWF)
      (H := H) (w := wid) hMemVar

/-! ### Sequentiality adequacy (world-level encoding) -/

omit [DecidableEq S.AtomicPredType] in
lemma Seq_implies_isSequentialModel (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (p : b.participants)
    (stPreEq : EncState b)
    (hPreEq : (addPreEqAll b stPreEq).clauses.all (SAT.Clause.eval σ) = true) :
    σ (Var.Seq H p) = true → isSequential p (decodePre b σ hWF H) := by
  classical
  intro hSeq w1 w2 hMem1 hMem2 hPlace1 hPlace2
  -- obtain witness identifiers for the decoded worlds
  obtain ⟨wId1, hwId1_mem, hwId1_eq⟩ :=
    (mem_decodePre_iff_memVar (b := b) (σ := σ) (hWF := hWF) (H := H) (w := w1)).mp hMem1
  obtain ⟨wId2, hwId2_mem, hwId2_eq⟩ :=
    (mem_decodePre_iff_memVar (b := b) (σ := σ) (hWF := hWF) (H := H) (w := w2)).mp hMem2
  -- align participant equalities
  have hp1 : wId1.p = p := by
    have h := congrArg Prod.fst hwId1_eq
    have hPlace1' : w1.fst = p := by simpa [World.place] using hPlace1
    simpa [hPlace1'] using h
  have hp2 : wId2.p = p := by
    have h := congrArg Prod.fst hwId2_eq
    have hPlace2' : w2.fst = p := by simpa [World.place] using hPlace2
    simpa [hPlace2'] using h
  -- apply sequentiality clause - now returns Acc/PreEq comparability
  have hComp :=
    seq_world_comparable (b := b) (σ := σ) (hWF := hWF) (H := H) (p := p)
      wId1 wId2 hp1 hp2 hSeq hwId1_mem hwId2_mem
  -- hComp : (∃ w₃, Acc(wId1,wId2,w₃)) ∨ (∃ w₃, Acc(wId2,wId1,w₃))
  --       ∨ (wId1.ei=wId2.ei ∧ PreEq(t1,t2))
  -- Need to convert to semantic: accessible w1 w2 ∨ accessible w2 w1 ∨ worldEq w1 w2
  rcases hComp with hAcc12 | hAcc21 | ⟨hEventEq, hPreEqVar⟩
  · -- Acc(wId1, wId2, w₃) = true → accessible w1 w2
    obtain ⟨w₃, hw₃mem, hAccTrue⟩ := hAcc12
    simp only [accWitnesses, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hw₃mem
    obtain ⟨_, hw₃p, hw₃ei⟩ := hw₃mem
    have hMemW3 : σ (Var.Mem wId2.ti w₃) = true :=
      acc_implies_mem b σ hWF H p wId1 wId2 w₃ hp1 hp2 hw₃p hw₃ei hAccTrue
    have hPreEqW3 : σ (Var.PreEq w₃.ti wId1.ti) = true :=
      acc_implies_preEq b σ hWF H p wId1 wId2 w₃ hp1 hp2 hw₃p hw₃ei hAccTrue
    let v : World (Fin b.nParticipants) S.EventType :=
      (w₃.p, b.decodeMaybeEvent w₃.ei, decodePre b σ hWF w₃.ti)
    have hVMem : v ∈ decodePre b σ hWF wId2.ti :=
      mem_decodePre_of_memVar (b := b) (σ := σ) (hWF := hWF) (H := wId2.ti) (w := w₃) hMemW3
    have hHistEqV : histEq (decodePre b σ hWF w₃.ti) (decodePre b σ hWF wId1.ti) :=
      preEq_sound b σ hWF w₃.ti wId1.ti stPreEq hPreEq hPreEqW3
    left
    rw [World.accessible_iff]
    have hW2Time : World.time w2 = decodePre b σ hWF wId2.ti := by
      have hTime2 := congrArg Prod.snd (congrArg Prod.snd hwId2_eq)
      simp [World.time] at hTime2 ⊢; exact hTime2.symm
    rw [hW2Time]
    refine ⟨v, hVMem, ?_⟩
    rw [PreHistory.worldEq_spec]
    constructor
    · simp only [World.place]
      have hW1Place : w1.1 = wId1.p := by
        have h := congrArg Prod.fst hwId1_eq; simp at h; exact h.symm
      rw [hW1Place]
      exact hw₃p.symm
    constructor
    · -- Event equality: w1.event = v.event
      have hW1Event : World.event w1 = b.decodeMaybeEvent wId1.ei := by
        have hEv1 := congrArg (Prod.fst ∘ Prod.snd) hwId1_eq
        simp [World.event] at hEv1 ⊢; exact hEv1.symm
      have hVEvent : World.event v = b.decodeMaybeEvent w₃.ei := rfl
      rw [hW1Event, hVEvent, hw₃ei]
    · have hW1Time : World.time w1 = decodePre b σ hWF wId1.ti := by
        have hTime1 := congrArg Prod.snd (congrArg Prod.snd hwId1_eq)
        simp [World.time] at hTime1 ⊢; exact hTime1.symm
      have hVTime : World.time v = decodePre b σ hWF w₃.ti := rfl
      rw [hW1Time, hVTime]
      exact histEq_symm hHistEqV
  · -- Acc(wId2, wId1, w₃) = true → accessible w2 w1
    obtain ⟨w₃, hw₃mem, hAccTrue⟩ := hAcc21
    simp only [accWitnesses, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hw₃mem
    obtain ⟨_, hw₃p, hw₃ei⟩ := hw₃mem
    have hMemW3 : σ (Var.Mem wId1.ti w₃) = true :=
      acc_implies_mem b σ hWF H p wId2 wId1 w₃ hp2 hp1 hw₃p hw₃ei hAccTrue
    have hPreEqW3 : σ (Var.PreEq w₃.ti wId2.ti) = true :=
      acc_implies_preEq b σ hWF H p wId2 wId1 w₃ hp2 hp1 hw₃p hw₃ei hAccTrue
    let v : World (Fin b.nParticipants) S.EventType :=
      (w₃.p, b.decodeMaybeEvent w₃.ei, decodePre b σ hWF w₃.ti)
    have hVMem : v ∈ decodePre b σ hWF wId1.ti :=
      mem_decodePre_of_memVar (b := b) (σ := σ) (hWF := hWF) (H := wId1.ti) (w := w₃) hMemW3
    have hHistEqV : histEq (decodePre b σ hWF w₃.ti) (decodePre b σ hWF wId2.ti) :=
      preEq_sound b σ hWF w₃.ti wId2.ti stPreEq hPreEq hPreEqW3
    right; left
    rw [World.accessible_iff]
    have hW1Time : World.time w1 = decodePre b σ hWF wId1.ti := by
      have hTime1 := congrArg Prod.snd (congrArg Prod.snd hwId1_eq)
      simp [World.time] at hTime1 ⊢; exact hTime1.symm
    rw [hW1Time]
    refine ⟨v, hVMem, ?_⟩
    rw [PreHistory.worldEq_spec]
    constructor
    · simp only [World.place]
      have hW2Place : w2.1 = wId2.p := by
        have h := congrArg Prod.fst hwId2_eq; simp at h; exact h.symm
      rw [hW2Place]
      exact hw₃p.symm
    constructor
    · -- Event equality: w2.event = v.event
      have hW2Event : World.event w2 = b.decodeMaybeEvent wId2.ei := by
        have hEv2 := congrArg (Prod.fst ∘ Prod.snd) hwId2_eq
        simp [World.event] at hEv2 ⊢; exact hEv2.symm
      have hVEvent : World.event v = b.decodeMaybeEvent w₃.ei := rfl
      rw [hW2Event, hVEvent, hw₃ei]
    · have hW2Time : World.time w2 = decodePre b σ hWF wId2.ti := by
        have hTime2 := congrArg Prod.snd (congrArg Prod.snd hwId2_eq)
        simp [World.time] at hTime2 ⊢; exact hTime2.symm
      have hVTime : World.time v = decodePre b σ hWF w₃.ti := rfl
      rw [hW2Time, hVTime]
      exact histEq_symm hHistEqV
  · -- wId1.ei = wId2.ei ∧ PreEq(wId1.ti, wId2.ti) = true → worldEq w1 w2
    have hHistEq := preEq_sound b σ hWF wId1.ti wId2.ti stPreEq hPreEq hPreEqVar
    right; right
    have hPlaceEq : World.place w1 = World.place w2 := by
      simp only [World.place]
      have h1 : w1.1 = p := by simp [World.place] at hPlace1; exact hPlace1
      have h2 : w2.1 = p := by simp [World.place] at hPlace2; exact hPlace2
      rw [h1, h2]
    have hEventEqSem : World.event w1 = World.event w2 := by
      have h1 : World.event w1 = b.decodeMaybeEvent wId1.ei := by
        have hEv1 := congrArg (Prod.fst ∘ Prod.snd) hwId1_eq
        simp [World.event] at hEv1 ⊢; exact hEv1.symm
      have h2 : World.event w2 = b.decodeMaybeEvent wId2.ei := by
        have hEv2 := congrArg (Prod.fst ∘ Prod.snd) hwId2_eq
        simp [World.event] at hEv2 ⊢; exact hEv2.symm
      rw [h1, h2, hEventEq]
    have hTimeEq : histEq (World.time w1) (World.time w2) := by
      have hT1 : World.time w1 = decodePre b σ hWF wId1.ti := by
        have hTime1 := congrArg Prod.snd (congrArg Prod.snd hwId1_eq)
        simp [World.time] at hTime1 ⊢; exact hTime1.symm
      have hT2 : World.time w2 = decodePre b σ hWF wId2.ti := by
        have hTime2 := congrArg Prod.snd (congrArg Prod.snd hwId2_eq)
        simp [World.time] at hTime2 ⊢; exact hTime2.symm
      rw [hT1, hT2]
      exact hHistEq
    rw [PreHistory.worldEq_spec]
    exact ⟨hPlaceEq, hEventEqSem, hTimeEq⟩

omit [DecidableEq S.AtomicPredType] in
lemma Seq_iff_isSequentialModel (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (p : b.participants)
    (stPreEq : EncState b)
    (hPreEq : (addPreEqAll b stPreEq).clauses.all (SAT.Clause.eval σ) = true) :
    σ (Var.Seq H p) = true ↔ isSequential p (decodePre b σ hWF H) := by
  constructor
  · intro hSeq
    exact Seq_implies_isSequentialModel (b := b) (σ := σ) (hWF := hWF) (H := H) (p := p)
      stPreEq hPreEq hSeq
  · intro hIsSeq
    -- Use seq_from_sequential, which requires showing all WId pairs have CmpTime
    apply seq_from_sequential (b := b) (σ := σ) (hWF := hWF) (H := H) (p := p)
    -- Must show: ∀ w₁ w₂, w₁.p = p → w₂.p = p → Mem(H,w₁) → Mem(H,w₂) →
    --            ∃ w₃, Acc(w₁,w₂,w₃) ∨ ∃ w₃, Acc(w₂,w₁,w₃) ∨ (w₁.ei=w₂.ei ∧ PreEq(w₁.ti,w₂.ti))
    intro w₁ w₂ hp₁ hp₂ hMem₁ hMem₂
    -- The decoded world from wId w is (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti)
    let t₁ : World (Fin b.nParticipants) S.EventType :=
      (w₁.p, b.decodeMaybeEvent w₁.ei, decodePre b σ hWF w₁.ti)
    let t₂ : World (Fin b.nParticipants) S.EventType :=
      (w₂.p, b.decodeMaybeEvent w₂.ei, decodePre b σ hWF w₂.ti)
    -- Get membership in decodePre H
    have hW₁ : t₁ ∈ decodePre b σ hWF H :=
      mem_decodePre_of_memVar (b := b) (σ := σ) (hWF := hWF) (H := H) (w := w₁) hMem₁
    have hW₂ : t₂ ∈ decodePre b σ hWF H :=
      mem_decodePre_of_memVar (b := b) (σ := σ) (hWF := hWF) (H := H) (w := w₂) hMem₂
    -- Get place equalities
    have hPlace₁ : World.place t₁ = p := hp₁
    have hPlace₂ : World.place t₂ = p := hp₂
    -- Apply isSequential to get semantic comparability
    have hComp := hIsSeq hW₁ hW₂ hPlace₁ hPlace₂
    -- hComp : accessible t₁ t₂ ∨ accessible t₂ t₁ ∨ worldEq t₁ t₂
    -- Need to convert to SAT-level:
    -- ∃ w₃, Acc(w₁,w₂,w₃) ∨ ∃ w₃, Acc(w₂,w₁,w₃) ∨ (w₁.ei=w₂.ei ∧ PreEq(w₁.ti,w₂.ti))
    rcases hComp with hAcc12 | hAcc21 | hWorldEq
    · -- accessible t₁ t₂: there exists v ∈ t₂.time with worldEq t₁ v
      rw [World.accessible_iff] at hAcc12
      obtain ⟨v, hVMem, hWorldEqV⟩ := hAcc12
      -- v ∈ t₂.time = decodePre(w₂.ti)
      have hVIn : v ∈ decodePre b σ hWF w₂.ti := hVMem
      -- Find w₃ : WId b that decodes to v
      obtain ⟨w₃, hMemW3, hW3Place, hW3Event, hW3Time⟩ :=
        decodePre_mem_witness b σ hWF w₂.ti hVIn
      -- From worldEq t₁ v: place, event, time equal
      rw [PreHistory.worldEq_spec] at hWorldEqV
      obtain ⟨hPlaceEq, hEventEq, hHistEq⟩ := hWorldEqV
      -- Show w₃.p = w₁.p (place)
      have hw₃p : w₃.p = w₁.p := by
        -- hW3Place : v.1 = w₃.p
        -- hPlaceEq : t₁.place = v.place, where t₁.place = w₁.p and v.place = v.1
        simp only [World.place] at hPlaceEq
        -- hPlaceEq : w₁.p = v.1
        rw [hW3Place.symm, hPlaceEq.symm]
      -- Show w₃.ei = w₁.ei (event)
      have hw₃ei : w₃.ei = w₁.ei := by
        -- t₁.event = b.decodeMaybeEvent w₁.ei (by definition of t₁)
        have hT1Event : World.event t₁ = b.decodeMaybeEvent w₁.ei := rfl
        -- v.event = b.decodeMaybeEvent w₃.ei (from decodePre_mem_witness)
        have hVEvent : World.event v = b.decodeMaybeEvent w₃.ei := hW3Event
        -- hEventEq : t₁.event = v.event (from worldEq_spec)
        have hDecodeEq : b.decodeMaybeEvent w₁.ei = b.decodeMaybeEvent w₃.ei := by
          rw [← hT1Event, ← hVEvent]
          exact hEventEq
        exact b.decodeMaybeEvent_injective w₃.ei w₁.ei hDecodeEq.symm
      left
      refine ⟨w₃, ?_, ?_⟩
      · -- w₃ ∈ accWitnesses b w₁
        rw [accWitnesses, List.mem_filter]
        refine ⟨WId.mem_allWorlds b w₃, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hw₃p, hw₃ei⟩
      · -- Acc(w₁,w₂,w₃) = true via backward clause
        -- Need: Mem(w₂.ti, w₃) = true (have hMemW3)
        -- Need: PreEq(w₃.ti, w₁.ti) = true (from histEq)
        have hPreEqW3 : σ (Var.PreEq w₃.ti w₁.ti) = true := by
          have hT1Time : World.time t₁ = decodePre b σ hWF w₁.ti := rfl
          have hVTime : v.snd.snd = decodePre b σ hWF w₃.ti := hW3Time
          have hHistEqDec : histEq (decodePre b σ hWF w₃.ti) (decodePre b σ hWF w₁.ti) := by
            rw [← hVTime, ← hT1Time]
            exact histEq_symm hHistEq
          exact preEq_complete b σ hWF w₃.ti w₁.ti stPreEq hPreEq hHistEqDec
        exact mem_preEq_implies_acc b σ hWF H p w₁ w₂ w₃ hp₁ hp₂ hw₃p hw₃ei hMemW3 hPreEqW3
    · -- accessible t₂ t₁: symmetric case
      rw [World.accessible_iff] at hAcc21
      obtain ⟨v, hVMem, hWorldEqV⟩ := hAcc21
      have hVIn : v ∈ decodePre b σ hWF w₁.ti := hVMem
      obtain ⟨w₃, hMemW3, hW3Place, hW3Event, hW3Time⟩ :=
        decodePre_mem_witness b σ hWF w₁.ti hVIn
      rw [PreHistory.worldEq_spec] at hWorldEqV
      obtain ⟨hPlaceEq, hEventEq, hHistEq⟩ := hWorldEqV
      have hw₃p : w₃.p = w₂.p := by
        simp only [World.place] at hPlaceEq
        rw [hW3Place.symm, hPlaceEq.symm]
      have hw₃ei : w₃.ei = w₂.ei := by
        -- t₂.event = b.decodeMaybeEvent w₂.ei (by definition of t₂)
        have hT2Event : World.event t₂ = b.decodeMaybeEvent w₂.ei := rfl
        -- v.event = b.decodeMaybeEvent w₃.ei (from decodePre_mem_witness)
        have hVEvent : World.event v = b.decodeMaybeEvent w₃.ei := hW3Event
        -- hEventEq : t₂.event = v.event (from worldEq_spec)
        have hDecodeEq : b.decodeMaybeEvent w₂.ei = b.decodeMaybeEvent w₃.ei := by
          rw [← hT2Event, ← hVEvent]
          exact hEventEq
        exact b.decodeMaybeEvent_injective w₃.ei w₂.ei hDecodeEq.symm
      right; left
      refine ⟨w₃, ?_, ?_⟩
      · rw [accWitnesses, List.mem_filter]
        refine ⟨WId.mem_allWorlds b w₃, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hw₃p, hw₃ei⟩
      · have hPreEqW3 : σ (Var.PreEq w₃.ti w₂.ti) = true := by
          have hT2Time : World.time t₂ = decodePre b σ hWF w₂.ti := rfl
          have hVTime : v.snd.snd = decodePre b σ hWF w₃.ti := hW3Time
          have hHistEqDec : histEq (decodePre b σ hWF w₃.ti) (decodePre b σ hWF w₂.ti) := by
            rw [← hVTime, ← hT2Time]
            exact histEq_symm hHistEq
          exact preEq_complete b σ hWF w₃.ti w₂.ti stPreEq hPreEq hHistEqDec
        exact mem_preEq_implies_acc b σ hWF H p w₂ w₁ w₃ hp₂ hp₁ hw₃p hw₃ei hMemW3 hPreEqW3
    · -- worldEq t₁ t₂: event and time equal
      rw [PreHistory.worldEq_spec] at hWorldEq
      obtain ⟨hPlaceEq, hEventEq, hHistEq⟩ := hWorldEq
      right; right
      constructor
      · -- w₁.ei = w₂.ei from event equality
        have hT1Event : World.event t₁ = b.decodeMaybeEvent w₁.ei := rfl
        have hT2Event : World.event t₂ = b.decodeMaybeEvent w₂.ei := rfl
        have hDecodeEq : b.decodeMaybeEvent w₁.ei = b.decodeMaybeEvent w₂.ei := by
          rw [← hT1Event, ← hT2Event]
          exact hEventEq
        exact b.decodeMaybeEvent_injective w₁.ei w₂.ei hDecodeEq
      · -- PreEq(w₁.ti, w₂.ti) = true from histEq
        have hHistEqDec : histEq (decodePre b σ hWF w₁.ti) (decodePre b σ hWF w₂.ti) := by
          have hT1Time : World.time t₁ = decodePre b σ hWF w₁.ti := rfl
          have hT2Time : World.time t₂ = decodePre b σ hWF w₂.ti := rfl
          rw [← hT1Time, ← hT2Time]
          exact hHistEq
        exact preEq_complete b σ hWF w₁.ti w₂.ti stPreEq hPreEq hHistEqDec

/-- Adequacy for encodeFormula seq case: σ(u) = true ↔ seq holds.

    The proof relies on:
    1. cnfSeq from hWF for the Seq ↔ (no Incomp) encoding
    2. PreEq soundness from addPreEqAll clauses (provided via hPreEq hypothesis)
    3. Path soundness from cnfPathWitness in hWF -/
lemma encodeFormula_seq_adequate (b : Bounds S)
    (w : WId b) (st : EncState b) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (hClauses : (encodeFormula b .seq w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (stPreEq : EncState b)
    (hPreEq : (addPreEqAll b stPreEq).clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b (encodeFormula b .seq w st).1) = true) ↔
    Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti) .seq := by
  classical
  constructor
  · -- Forward: σ(u) = true → Sat (isSequential)
    intro hU
    obtain hAll := List.all_eq_true.mp hClauses
    -- Extract Seq(w.ti, w.p) = true from the biconditional clauses
    have hClauseMem :
        [ SAT.Lit.neg (FVar.toVar b (encodeFormula b .seq w st).1)
        , SAT.Lit.pos (Var.Seq w.ti w.p) ]
          ∈ (encodeFormula b .seq w st).2.clauses := by
      simp only [encodeFormula]
      cases hAlloc : EncState.allocFresh b st with
      | mk u st1 =>
        simp only []
        -- The clause is in st2.clauses, then st2 ⊆ st3
        have h1 : [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)] ∈
            (EncState.addClause b st1
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)]).clauses := by
          simp [EncState.addClause]
        have h2 := EncState.addClause_subset_clauses b
          (EncState.addClause b st1
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)])
          [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)]
        exact h2 h1
    have hClauseEval := hAll _ hClauseMem
    have hSeqTrue : σ (Var.Seq w.ti w.p) = true := by
      unfold SAT.Clause.eval at hClauseEval
      simpa [SAT.Lit.eval, hU] using hClauseEval

    -- Now prove isSequential using seq_time_comparable and PreEq/Path soundness
    rw [Sat]
    intro w1 w2 hMem1 hMem2 hPlace1 hPlace2

    -- Get WId witnesses for the decoded worlds
    obtain ⟨wId1, hwId1_mem, hwId1_eq⟩ :=
      (mem_decodePre_iff_memVar (b := b) (σ := σ) (hWF := hWF) (H := w.ti) (w := w1)).mp hMem1
    obtain ⟨wId2, hwId2_mem, hwId2_eq⟩ :=
      (mem_decodePre_iff_memVar (b := b) (σ := σ) (hWF := hWF) (H := w.ti) (w := w2)).mp hMem2

    have hp1 : wId1.p = w.p := by
      have h := congrArg Prod.fst hwId1_eq
      have hPlace1' : w1.fst = w.p := by simpa [World.place] using hPlace1
      simpa [hPlace1'] using h
    have hp2 : wId2.p = w.p := by
      have h := congrArg Prod.fst hwId2_eq
      have hPlace2' : w2.fst = w.p := by simpa [World.place] using hPlace2
      simpa [hPlace2'] using h

    -- Get world-level comparability from seq_world_comparable
    have hComp := seq_world_comparable (b := b) (σ := σ) (hWF := hWF)
      (H := w.ti) (p := w.p) wId1 wId2 hp1 hp2 hSeqTrue hwId1_mem hwId2_mem

    -- Convert Acc/PreEq to semantic comparability
    -- hComp : (∃ w₃, Acc(wId1,wId2,w₃)) ∨ (∃ w₃, Acc(wId2,wId1,w₃))
    --         ∨ (wId1.ei=wId2.ei ∧ PreEq(wId1.ti,wId2.ti))
    -- Target: accessible w1 w2 ∨ accessible w2 w1 ∨ worldEq w1 w2
    rcases hComp with ⟨w₃, hAcc12⟩ | ⟨w₃, hAcc21⟩ | ⟨hEventEq, hPreEqVar⟩
    · -- Acc(wId1, wId2, w₃) = true → accessible w1 w2
      -- Extract membership and Acc truth from the existential
      obtain ⟨hw₃mem, hAccTrue⟩ := hAcc12
      -- hw₃mem : w₃ ∈ accWitnesses b wId1, meaning w₃.p = wId1.p ∧ w₃.ei = wId1.ei
      simp only [accWitnesses, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hw₃mem
      obtain ⟨_, hw₃p, hw₃ei⟩ := hw₃mem
      -- Use acc_implies_mem and acc_implies_preEq
      have hMemW3 : σ (Var.Mem wId2.ti w₃) = true :=
        acc_implies_mem b σ hWF w.ti w.p wId1 wId2 w₃ hp1 hp2 hw₃p hw₃ei hAccTrue
      have hPreEqW3 : σ (Var.PreEq w₃.ti wId1.ti) = true :=
        acc_implies_preEq b σ hWF w.ti w.p wId1 wId2 w₃ hp1 hp2 hw₃p hw₃ei hAccTrue
      -- decoded w₃ is in w2.time = decodePre wId2.ti
      let v : World (Fin b.nParticipants) S.EventType :=
        (w₃.p, b.decodeMaybeEvent w₃.ei, decodePre b σ hWF w₃.ti)
      have hVMem : v ∈ decodePre b σ hWF wId2.ti :=
        mem_decodePre_of_memVar (b := b) (σ := σ) (hWF := hWF) (H := wId2.ti) (w := w₃) hMemW3
      -- Use preEq_sound to get histEq
      have hHistEqV : histEq (decodePre b σ hWF w₃.ti) (decodePre b σ hWF wId1.ti) :=
        preEq_sound b σ hWF w₃.ti wId1.ti stPreEq hPreEq hPreEqW3
      -- accessible w1 w2 = ∃ v ∈ w2.time, worldEq w1 v
      left
      rw [World.accessible_iff]
      -- w2.time = decodePre wId2.ti (from hwId2_eq)
      have hW2Time : World.time w2 = decodePre b σ hWF wId2.ti := by
        have hTime2 := congrArg Prod.snd (congrArg Prod.snd hwId2_eq)
        simp [World.time] at hTime2 ⊢
        exact hTime2.symm
      rw [hW2Time]
      refine ⟨v, hVMem, ?_⟩
      -- Show worldEq w1 v
      rw [PreHistory.worldEq_spec]
      constructor
      · -- Place equality: w1.place = v.place
        -- w1.1 = wId1.p (from hwId1_eq) and v.1 = w₃.p
        -- hw₃p : w₃.p = wId1.p, so wId1.p = w₃.p = v.1
        simp only [World.place]
        have hW1Place : w1.1 = wId1.p := by
          have h := congrArg Prod.fst hwId1_eq; simp at h; exact h.symm
        rw [hW1Place]
        exact hw₃p.symm
      constructor
      · -- Event equality: w1.event = b.decodeMaybeEvent
        -- wId1.ei = b.decodeMaybeEvent w₃.ei = v.event
        have hW1Event : World.event w1 = b.decodeMaybeEvent wId1.ei := by
          have hEv1 := congrArg (Prod.fst ∘ Prod.snd) hwId1_eq
          simp [World.event] at hEv1 ⊢; exact hEv1.symm
        have hVEvent : World.event v = b.decodeMaybeEvent w₃.ei := rfl
        rw [hW1Event, hVEvent, hw₃ei]
      · -- Time histEq: w1.time = decodePre wId1.ti, v.time = decodePre w₃.ti
        have hW1Time : World.time w1 = decodePre b σ hWF wId1.ti := by
          have hTime1 := congrArg Prod.snd (congrArg Prod.snd hwId1_eq)
          simp [World.time] at hTime1 ⊢; exact hTime1.symm
        have hVTime : World.time v = decodePre b σ hWF w₃.ti := rfl
        rw [hW1Time, hVTime]
        exact histEq_symm hHistEqV
    · -- Acc(wId2, wId1, w₃) = true → accessible w2 w1
      -- Symmetric case
      obtain ⟨hw₃mem, hAccTrue⟩ := hAcc21
      simp only [accWitnesses, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hw₃mem
      obtain ⟨_, hw₃p, hw₃ei⟩ := hw₃mem
      have hMemW3 : σ (Var.Mem wId1.ti w₃) = true :=
        acc_implies_mem b σ hWF w.ti w.p wId2 wId1 w₃ hp2 hp1 hw₃p hw₃ei hAccTrue
      have hPreEqW3 : σ (Var.PreEq w₃.ti wId2.ti) = true :=
        acc_implies_preEq b σ hWF w.ti w.p wId2 wId1 w₃ hp2 hp1 hw₃p hw₃ei hAccTrue
      let v : World (Fin b.nParticipants) S.EventType :=
        (w₃.p, b.decodeMaybeEvent w₃.ei, decodePre b σ hWF w₃.ti)
      have hVMem : v ∈ decodePre b σ hWF wId1.ti :=
        mem_decodePre_of_memVar (b := b) (σ := σ) (hWF := hWF) (H := wId1.ti) (w := w₃) hMemW3
      have hHistEqV : histEq (decodePre b σ hWF w₃.ti) (decodePre b σ hWF wId2.ti) :=
        preEq_sound b σ hWF w₃.ti wId2.ti stPreEq hPreEq hPreEqW3
      right; left
      rw [World.accessible_iff]
      have hW1Time : World.time w1 = decodePre b σ hWF wId1.ti := by
        have hTime1 := congrArg Prod.snd (congrArg Prod.snd hwId1_eq)
        simp [World.time] at hTime1 ⊢; exact hTime1.symm
      rw [hW1Time]
      refine ⟨v, hVMem, ?_⟩
      rw [PreHistory.worldEq_spec]
      constructor
      · -- Place equality: w2.place = v.place
        -- w2.1 = wId2.p and v.1 = w₃.p
        -- hw₃p : w₃.p = wId2.p, so wId2.p = w₃.p = v.1
        simp only [World.place]
        have hW2Place : w2.1 = wId2.p := by
          have h := congrArg Prod.fst hwId2_eq; simp at h; exact h.symm
        rw [hW2Place]
        exact hw₃p.symm
      constructor
      · have hW2Event : World.event w2 = b.decodeMaybeEvent wId2.ei := by
          have hEv2 := congrArg (Prod.fst ∘ Prod.snd) hwId2_eq
          simp [World.event] at hEv2 ⊢; exact hEv2.symm
        have hVEvent : World.event v = b.decodeMaybeEvent w₃.ei := rfl
        rw [hW2Event, hVEvent, hw₃ei]
      · have hW2Time : World.time w2 = decodePre b σ hWF wId2.ti := by
          have hTime2 := congrArg Prod.snd (congrArg Prod.snd hwId2_eq)
          simp [World.time] at hTime2 ⊢; exact hTime2.symm
        have hVTime : World.time v = decodePre b σ hWF w₃.ti := rfl
        rw [hW2Time, hVTime]
        exact histEq_symm hHistEqV
    · -- wId1.ei = wId2.ei ∧ PreEq(wId1.ti, wId2.ti) = true → worldEq w1 w2
      -- Use PreEq soundness: PreEq true → histEq on decoded prehistories
      have hHistEq := preEq_sound b σ hWF wId1.ti wId2.ti stPreEq hPreEq hPreEqVar
      -- We have:
      -- - histEq on decoded prehistories (from hHistEq)
      -- - place equality (hp1, hp2, and hPlace1, hPlace2)
      -- - event equality (from hEventEq)
      -- So we can derive worldEq w1 w2
      right; right
      -- worldEq w1 w2 = worldEqAt fuel w1 w2 = (place eq ∧ event eq ∧ histEq times)
      -- We construct this directly via the worldEq_spec or by showing the components
      have hPlaceEq : World.place w1 = World.place w2 := by
        simp only [World.place]
        -- w1.1 = wId1.p (from hwId1_eq) and hPlace1 : w1.place = w.p
        -- w2.1 = wId2.p (from hwId2_eq) and hPlace2 : w2.place = w.p
        have h1 : w1.1 = w.p := by simp [World.place] at hPlace1; exact hPlace1
        have h2 : w2.1 = w.p := by simp [World.place] at hPlace2; exact hPlace2
        rw [h1, h2]
      have hEventEqSem : World.event w1 = World.event w2 := by
        have h1 : World.event w1 = b.decodeMaybeEvent wId1.ei := by
          have hEv1 := congrArg (Prod.fst ∘ Prod.snd) hwId1_eq
          simp [World.event] at hEv1 ⊢
          exact hEv1.symm
        have h2 : World.event w2 = b.decodeMaybeEvent wId2.ei := by
          have hEv2 := congrArg (Prod.fst ∘ Prod.snd) hwId2_eq
          simp [World.event] at hEv2 ⊢
          exact hEv2.symm
        rw [h1, h2, hEventEq]
      have hTimeEq : histEq (World.time w1) (World.time w2) := by
        have hT1 : World.time w1 = decodePre b σ hWF wId1.ti := by
          have hTime1 := congrArg Prod.snd (congrArg Prod.snd hwId1_eq)
          simp [World.time] at hTime1 ⊢
          exact hTime1.symm
        have hT2 : World.time w2 = decodePre b σ hWF wId2.ti := by
          have hTime2 := congrArg Prod.snd (congrArg Prod.snd hwId2_eq)
          simp [World.time] at hTime2 ⊢
          exact hTime2.symm
        rw [hT1, hT2]
        exact hHistEq
      -- Use worldEq_spec to construct worldEq from the components
      exact worldEq_spec w1 w2 |>.mpr ⟨hPlaceEq, hEventEqSem, hTimeEq⟩

  · -- Backward: Sat → σ(u) = true
    intro hSat
    rw [Sat] at hSat
    obtain hAll := List.all_eq_true.mp hClauses

    -- Need to show Seq(w.ti, w.p) = true from isSequential, then u = true
    -- This requires the backward direction: isSequential → CmpTime for all pairs
    -- which in turn requires setting Path/PreEq variables correctly
    -- This is the completeness direction and relies on the assignment being correct
    have hSeq : σ (Var.Seq w.ti w.p) = true := by
      -- Use seq_from_sequential with CmpTime hypothesis
      apply seq_from_sequential (b := b) (σ := σ) (hWF := hWF) (H := w.ti) (p := w.p)
      intro wId1 wId2 hp1 hp2 hMem1 hMem2
      -- Decoded worlds are comparable by isSequential
      let t1 : World (Fin b.nParticipants) S.EventType :=
        (wId1.p, b.decodeMaybeEvent wId1.ei, decodePre b σ hWF wId1.ti)
      let t2 : World (Fin b.nParticipants) S.EventType :=
        (wId2.p, b.decodeMaybeEvent wId2.ei, decodePre b σ hWF wId2.ti)
      have hW1 := mem_decodePre_of_memVar (b := b) (σ := σ) (hWF := hWF)
        (H := w.ti) (w := wId1) hMem1
      have hW2 := mem_decodePre_of_memVar (b := b) (σ := σ) (hWF := hWF)
        (H := w.ti) (w := wId2) hMem2
      have hCompSem := hSat hW1 hW2 hp1 hp2
      -- Semantic comparability:
      --   accessible t1 t2 ∨ accessible t2 t1 ∨ worldEq t1 t2
      -- Need to convert to SAT-level:
      --   ∃ w₃, Acc(wId1,wId2,w₃) ∨ ∃ w₃, Acc(wId2,wId1,w₃) ∨ (ei eq ∧ PreEq)
      rcases hCompSem with hAcc12 | hAcc21 | hWorldEq
      · -- accessible t1 t2: there exists v ∈ t2.time with worldEq t1 v
        rw [World.accessible_iff] at hAcc12
        obtain ⟨v, hVMem, hWorldEqV⟩ := hAcc12
        have hVIn : v ∈ decodePre b σ hWF wId2.ti := hVMem
        obtain ⟨w₃, hMemW3, hW3Place, hW3Event, hW3Time⟩ :=
          decodePre_mem_witness b σ hWF wId2.ti hVIn
        rw [PreHistory.worldEq_spec] at hWorldEqV
        obtain ⟨hPlaceEq, hEventEq, hHistEq⟩ := hWorldEqV
        have hw₃p : w₃.p = wId1.p := by
          simp only [World.place] at hPlaceEq
          rw [hW3Place.symm, hPlaceEq.symm]
        have hw₃ei : w₃.ei = wId1.ei := by
          have hT1Event : World.event t1 = b.decodeMaybeEvent wId1.ei := rfl
          have hVEvent : World.event v = b.decodeMaybeEvent w₃.ei := hW3Event
          have hDecodeEq : b.decodeMaybeEvent wId1.ei = b.decodeMaybeEvent w₃.ei := by
            rw [← hT1Event, ← hVEvent]
            exact hEventEq
          exact b.decodeMaybeEvent_injective w₃.ei wId1.ei hDecodeEq.symm
        left
        refine ⟨w₃, ?_, ?_⟩
        · rw [accWitnesses, List.mem_filter]
          refine ⟨WId.mem_allWorlds b w₃, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hw₃p, hw₃ei⟩
        · have hPreEqW3 : σ (Var.PreEq w₃.ti wId1.ti) = true := by
            have hT1Time : World.time t1 = decodePre b σ hWF wId1.ti := rfl
            have hVTime : v.snd.snd = decodePre b σ hWF w₃.ti := hW3Time
            have hHistEqDec : histEq (decodePre b σ hWF w₃.ti)
                (decodePre b σ hWF wId1.ti) := by
              rw [← hVTime, ← hT1Time]
              exact histEq_symm hHistEq
            exact preEq_complete b σ hWF w₃.ti wId1.ti stPreEq hPreEq hHistEqDec
          exact mem_preEq_implies_acc b σ hWF w.ti w.p wId1 wId2 w₃ hp1 hp2
            hw₃p hw₃ei hMemW3 hPreEqW3
      · -- accessible t2 t1: symmetric case
        rw [World.accessible_iff] at hAcc21
        obtain ⟨v, hVMem, hWorldEqV⟩ := hAcc21
        have hVIn : v ∈ decodePre b σ hWF wId1.ti := hVMem
        obtain ⟨w₃, hMemW3, hW3Place, hW3Event, hW3Time⟩ :=
          decodePre_mem_witness b σ hWF wId1.ti hVIn
        rw [PreHistory.worldEq_spec] at hWorldEqV
        obtain ⟨hPlaceEq, hEventEq, hHistEq⟩ := hWorldEqV
        have hw₃p : w₃.p = wId2.p := by
          simp only [World.place] at hPlaceEq
          rw [hW3Place.symm, hPlaceEq.symm]
        have hw₃ei : w₃.ei = wId2.ei := by
          have hT2Event : World.event t2 = b.decodeMaybeEvent wId2.ei := rfl
          have hVEvent : World.event v = b.decodeMaybeEvent w₃.ei := hW3Event
          have hDecodeEq : b.decodeMaybeEvent wId2.ei = b.decodeMaybeEvent w₃.ei := by
            rw [← hT2Event, ← hVEvent]
            exact hEventEq
          exact b.decodeMaybeEvent_injective w₃.ei wId2.ei hDecodeEq.symm
        right; left
        refine ⟨w₃, ?_, ?_⟩
        · rw [accWitnesses, List.mem_filter]
          refine ⟨WId.mem_allWorlds b w₃, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hw₃p, hw₃ei⟩
        · have hPreEqW3 : σ (Var.PreEq w₃.ti wId2.ti) = true := by
            have hT2Time : World.time t2 = decodePre b σ hWF wId2.ti := rfl
            have hVTime : v.snd.snd = decodePre b σ hWF w₃.ti := hW3Time
            have hHistEqDec : histEq (decodePre b σ hWF w₃.ti)
                (decodePre b σ hWF wId2.ti) := by
              rw [← hVTime, ← hT2Time]
              exact histEq_symm hHistEq
            exact preEq_complete b σ hWF w₃.ti wId2.ti stPreEq hPreEq hHistEqDec
          exact mem_preEq_implies_acc b σ hWF w.ti w.p wId2 wId1 w₃ hp2 hp1
            hw₃p hw₃ei hMemW3 hPreEqW3
      · -- worldEq t1 t2: event and time equal
        rw [PreHistory.worldEq_spec] at hWorldEq
        obtain ⟨hPlaceEq, hEventEq, hHistEq⟩ := hWorldEq
        right; right
        constructor
        · -- wId1.ei = wId2.ei from event equality
          have hT1Event : World.event t1 = b.decodeMaybeEvent wId1.ei := rfl
          have hT2Event : World.event t2 = b.decodeMaybeEvent wId2.ei := rfl
          have hDecodeEq : b.decodeMaybeEvent wId1.ei = b.decodeMaybeEvent wId2.ei := by
            rw [← hT1Event, ← hT2Event]
            exact hEventEq
          exact b.decodeMaybeEvent_injective wId1.ei wId2.ei hDecodeEq
        · -- PreEq(wId1.ti, wId2.ti) = true from histEq
          have hHistEqDec : histEq (decodePre b σ hWF wId1.ti) (decodePre b σ hWF wId2.ti) := by
            have hT1Time : World.time t1 = decodePre b σ hWF wId1.ti := rfl
            have hT2Time : World.time t2 = decodePre b σ hWF wId2.ti := rfl
            rw [← hT1Time, ← hT2Time]
            exact hHistEq
          exact preEq_complete b σ hWF wId1.ti wId2.ti stPreEq hPreEq hHistEqDec

    -- Now extract u = true from the biconditional
    have hClauseMem :
        [ SAT.Lit.neg (Var.Seq w.ti w.p)
        , SAT.Lit.pos (FVar.toVar b (encodeFormula b .seq w st).1) ]
          ∈ (encodeFormula b .seq w st).2.clauses := by
      simp only [encodeFormula]
      cases hAlloc : EncState.allocFresh b st with
      | mk u st1 =>
        simp only []
        have h1 : [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)] ∈
            (EncState.addClause b
              (EncState.addClause b st1
                [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (Var.Seq w.ti w.p)])
              [SAT.Lit.neg (Var.Seq w.ti w.p), SAT.Lit.pos (FVar.toVar b u)]).clauses := by
          simp [EncState.addClause]
        exact h1
    have hClauseEval := hAll _ hClauseMem
    have hU : σ (FVar.toVar b (encodeFormula b .seq w st).1) = true := by
      unfold SAT.Clause.eval at hClauseEval
      simpa [SAT.Lit.eval, hSeq] using hClauseEval
    exact hU

end Encoding
