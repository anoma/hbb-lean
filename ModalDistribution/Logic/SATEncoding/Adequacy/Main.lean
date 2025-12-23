import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.Syntax
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.Bitmask.Core
import ModalDistribution.Logic.SATEncoding.ListLemmas
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction
import ModalDistribution.Logic.SATEncoding.Adequacy.HereditaryTransitivity
import ModalDistribution.Logic.SATEncoding.Adequacy.LearnerConstruction
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinBot
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinEq
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinSeq
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinImp
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinAtEnd
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinForall
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinPast
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinDiamond
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinPred
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinEvent
import ModalDistribution.Logic.SATEncoding.AssumptionEncoding


/-!
# Main Adequacy Theorem

This file contains the main adequacy result: if a SAT assignment satisfies the encoded
assumptions, then there exists a semantic model that satisfies those assumptions.

## Main Results

- `assumptions_adequate`: The main adequacy theorem

## Overview

The adequacy proof has three layers:

1. **Model Construction** (proven in previous files):
   - Hereditary transitivity from WF constraints
   - Learner semifilters from learner CNF
   - Full Model assembly

2. **Formula Encoding Correctness** (to be completed):
   - Per-constructor lemmas showing Tseytin encoding correctness
   - Connection between control variables and semantic satisfaction

3. **Main Theorem** (this file):
   - Combines the above to prove assumptions_adequate
   - Shows that encoded assumptions imply semantic satisfaction

## Proof Architecture

The main theorem `assumptions_adequate` relies on:

## References

- Plan.md section "Formula Encoding Adequacy"
- FormulaEncoding.lean for encoding definitions
- Model.lean for semantic definitions
-/

open ModalDistribution Encoding Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-- **Formula Encoding Adequacy**: The control variable is true iff the formula
    semantically holds at that world in the extracted model.

    This is the main bridge between SAT and semantics. It proves bi-directional
    adequacy (local completeness) by induction on formula structure, using the
    bi-directional Tseytin clauses for each constructor.

    The hPreEq hypothesis provides PreEq clauses needed for event and seq adequacy.
    These clauses are added once in encodeAssumptions via addPreEqAll. -/
lemma encodeFormula_adequate (b : Bounds S) (φ : Formula S) (w : WId b)
    (st : EncState b) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (hClauses : (encodeFormula b φ w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (stPreEq : EncState b)
    (hPreEq : (addPreEqAll b stPreEq).clauses.all (SAT.Clause.eval σ) = true) :
    (σ (FVar.toVar b (encodeFormula b φ w st).1) = true) ↔
    Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti) φ := by
  -- Proof by induction on formula structure
  induction φ generalizing w st with
  | bot =>
      -- For bot: encodeFormula adds [¬u], so u=true is impossible (iff false)
      -- Sat M w ⊥ ↔ False by semantics
      calc σ (FVar.toVar b (encodeFormula b Formula.bot w st).1) = true
          ↔ False := encodeFormula_bot_adequate b w st σ hClauses
        _ ↔ Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti)
              Formula.bot := by unfold Sat; simp

  | eq v1 v2 =>
      -- For eq: encodeFormula adds [u] if v1=v2, or [¬u] if v1≠v2 (iff)
      -- Sat M w (v1 ≃ v2) ↔ v1 = v2 by semantics
      calc σ (FVar.toVar b (encodeFormula b (Formula.eq v1 v2) w st).1) = true
          ↔ v1 = v2 := encodeFormula_eq_adequate b w st σ v1 v2 hClauses
        _ ↔ Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti)
              (Formula.eq v1 v2) := by unfold Sat; simp

  | imp φ₁ φ₂ ih₁ ih₂ =>
      -- For imp: encodeFormula recursively encodes φ₁ and φ₂
      -- and adds Tseytin clauses for implication (iff)
      -- Now both IHs give iff, so we can pass them directly
      classical
      let ihLeft_iff : ∀ st₀ : EncState b,
          let res := encodeFormula b φ₁ w st₀
          let uLeft := res.1
          let st₁ := res.2
          st₁.clauses.all (SAT.Clause.eval σ) = true →
          (σ (FVar.toVar b uLeft) = true ↔
           Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
             (decodePre b σ hWF w.ti) φ₁) :=
        fun st₀ hClauses₁ => by
          classical
          let res := encodeFormula b φ₁ w st₀
          let uLeft := res.1
          let st₁ := res.2
          have hEq : encodeFormula b φ₁ w st₀ = (uLeft, st₁) := rfl
          simpa [hEq] using ih₁ w st₀ hClauses₁
      let ihRight_iff : ∀ st₀ : EncState b,
          let res := encodeFormula b φ₂ w st₀
          let uRight := res.1
          let st₂ := res.2
          st₂.clauses.all (SAT.Clause.eval σ) = true →
          (σ (FVar.toVar b uRight) = true ↔
           Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
             (decodePre b σ hWF w.ti) φ₂) :=
        fun st₀ hClauses₁ => by
          classical
          let res := encodeFormula b φ₂ w st₀
          let uRight := res.1
          let st₂ := res.2
          have hEq : encodeFormula b φ₂ w st₀ = (uRight, st₂) := rfl
          simpa [hEq] using ih₂ w st₀ hClauses₁
      exact encodeFormula_imp_adequate b φ₁ φ₂ w st σ hWF
        ihLeft_iff ihRight_iff hClauses

  | predicate atom =>
      -- For predicate: encodeFormula connects u to Pred variables (iff)
      calc σ (FVar.toVar b (encodeFormula b (Formula.predicate atom) w st).1) = true
          ↔ ⟨atom.sym, atom.args⟩ ∈ predInterp b σ hWF w.p (decodePre b σ hWF w.ti) :=
            encodeFormula_pred_adequate b atom w st σ hWF hClauses stPreEq hPreEq
        _ ↔ Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei) (decodePre b σ hWF w.ti)
              (Formula.predicate atom) := by
            unfold Sat modelOf; simp [modelDataOf]
            -- The semantic definition has an existential over histEq-equivalent prehistories.
            -- predInterp is defined using histEq-based time index selection, so we can
            -- shuttle witnesses across hEq using predInterp_of_histEq.
            constructor
            · intro h
              -- mp: witness the existential with the prehistory itself
              exact ⟨decodePre b σ hWF w.ti, PreHistory.histEq_refl _, h⟩
            · intro ⟨H', hEq, h⟩
              -- mpr: transfer membership from H' to decodePre w.ti using PreEq
              exact predInterp_of_histEq b σ hWF w.p ⟨atom.sym, atom.args⟩
                (decodePre b σ hWF w.ti) H' hEq h

  | event atom =>
      -- For event: encodeFormula connects u to EvSel and Mem variables (iff)
      exact encodeFormula_event_adequate b atom w st σ hWF hClauses stPreEq hPreEq

  | seq =>
      -- For seq: encodeFormula encodes the sequencing modality (iff)
      exact encodeFormula_seq_adequate b w st σ hWF hClauses stPreEq hPreEq

  | «forall» body ih =>
      -- For forall: encodeFormula recursively encodes body(v) for each value (iff)
      let ihBody_iff : ∀ v (st₀ : EncState b),
          let res := encodeFormula b (body v) w st₀
          let uBody := res.1
          let stBody := res.2
          stBody.clauses.all (SAT.Clause.eval σ) = true →
            (σ (FVar.toVar b uBody) = true ↔
              Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
                (decodePre b σ hWF w.ti) (body v)) :=
        fun v st₀ hClauses₀ => by
          classical
          let res := encodeFormula b (body v) w st₀
          let uBody := res.1
          let stBody := res.2
          have hEq : encodeFormula b (body v) w st₀ = (uBody, stBody) := rfl
          simpa [hEq] using ih v w st₀ hClauses₀
      exact encodeFormula_forall_adequate b body w st σ hWF ihBody_iff hClauses

  | atEnd φ ih =>
      -- For atEnd: encodeFormula checks if at root and encodes φ (iff)
      let wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
      let ihAtEnd : ∀ st₀ : EncState b,
          let res := encodeFormula b φ wEnd st₀
          let uBody := res.1
          let stBody := res.2
          stBody.clauses.all (SAT.Clause.eval σ) = true →
            (σ (FVar.toVar b uBody) = true ↔
              Sat (modelOf b σ hWF) w.p † (decodePre b σ hWF b.root) φ) :=
        fun st₀ hClauses₀ => by
          classical
          -- Use the IH from induction at wEnd
          have ihRes := ih wEnd st₀ hClauses₀
          -- wEnd has participant w.p, event index 0 (†), and time b.root
          simp only [wEnd] at ihRes
          exact ihRes
      exact encodeFormula_atEnd_adequate b φ w st σ hWF ihAtEnd hClauses

  | diamond learners φ ih =>
      -- For diamond: encodeFormula creates quorum-witness clauses (iff)
      let ihDiamond : ∀ (w' : WId b) (st₀ : EncState b),
          let res := encodeFormula b φ w' st₀
          let uBody := res.1
          let stBody := res.2
          stBody.clauses.all (SAT.Clause.eval σ) = true →
            (σ (FVar.toVar b uBody) = true ↔
              Sat (modelOf b σ hWF) w'.p (b.decodeMaybeEvent w'.ei)
                (decodePre b σ hWF w'.ti) φ) :=
        fun w' st₀ hClauses₀ => by
          classical
          let res := encodeFormula b φ w' st₀
          let uBody := res.1
          let stBody := res.2
          have hEq : encodeFormula b φ w' st₀ = (uBody, stBody) := rfl
          simpa [hEq] using ih w' st₀ hClauses₀
      exact encodeFormula_diamond_adequate b learners φ w st σ hWF ihDiamond hClauses
        (fun ℓ _ => all_values_in_classValues b ℓ)

  | past φ ih =>
      -- For past: encodeFormula recursively encodes φ at all predecessor worlds (iff)
      let ihPast : ∀ (w' : WId b) (st₀ : EncState b),
          let res := encodeFormula b φ w' st₀
          let uBody := res.1
          let stBody := res.2
          stBody.clauses.all (SAT.Clause.eval σ) = true →
            (σ (FVar.toVar b uBody) = true ↔
              Sat (modelOf b σ hWF) w'.p (b.decodeMaybeEvent w'.ei)
                (decodePre b σ hWF w'.ti) φ) :=
        fun w' st₀ hClauses₀ => by
          classical
          let res := encodeFormula b φ w' st₀
          let uBody := res.1
          let stBody := res.2
          have hEq : encodeFormula b φ w' st₀ = (uBody, stBody) := rfl
          simpa [hEq] using ih w' st₀ hClauses₀
      exact encodeFormula_past_adequate b φ w st σ hWF ihPast hClauses

/-! ## Adequacy Theorem

The main adequacy result: if a SAT assignment satisfies the encoded assumptions,
then there exists a semantic model that satisfies those assumptions.

This theorem relies on all the infrastructure:
- Hereditary transitivity (proven)
- Learner semifilter construction (proven)
- Formula encoding correctness (stubbed above, requires ~2000-3000 lines)
-/

/-! ## Assumption Encoding Soundness

These lemmas connect the encoding of assumptions to their semantic meaning. -/

/-- Helper: For any participant p, the clauses from encodeEndStep for p are preserved
    in the final encodeEnd result. -/
lemma encodeEnd_step_clauses_preserved (b : Bounds S) (φ : Formula S)
    (st : EncState b) (p : b.participants) :
    ∃ stBefore : EncState b,
      (encodeEndStep b φ stBefore p).clauses ⊆ (encodeEnd b φ st).clauses := by
  classical
  -- p is in the participant list
  have hMem : p ∈ Bounds.partsL b := by simp [Bounds.partsL]
  -- Split the list at p
  obtain ⟨before, after, hSplit⟩ := List.append_of_mem hMem
  -- The fold can be decomposed
  have hFold : (encodeEnd b φ st) =
      (after.foldl (encodeEndStep b φ)
        (encodeEndStep b φ (before.foldl (encodeEndStep b φ) st) p)) := by
    unfold encodeEnd
    rw [hSplit]
    simp only [List.foldl_append, List.foldl_cons]
  -- The state before p
  let stBefore := before.foldl (encodeEndStep b φ) st
  use stBefore
  -- Clauses from step(stBefore, p) are preserved in the final result
  rw [hFold]
  apply foldl_subset_state (b := b)
    (f := encodeEndStep b φ)
    (hStep := fun stAcc q => encodeEndStep_clauses_subset b φ stAcc q)
    (xs := after)
    (init := encodeEndStep b φ stBefore p)

/-- If encodeEnd clauses are satisfied, then the formula holds at the end for all participants. -/
lemma encodeEnd_sound (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (φ : Formula S) (st : EncState b)
    (hClauses : (encodeEnd b φ st).clauses.all (SAT.Clause.eval σ) = true)
    (stPreEq : EncState b)
    (hPreEq : (addPreEqAll b stPreEq).clauses.all (SAT.Clause.eval σ) = true) :
    EndValid (modelOf b σ hWF) φ := by
  classical
  simp only [EndValid]
  intro p
  -- Get the state where p was processed
  obtain ⟨stBefore, hSubset⟩ := encodeEnd_step_clauses_preserved b φ st p
  -- The clauses from encodeEndStep for p are satisfied
  have hStepClauses : (encodeEndStep b φ stBefore p).clauses.all (SAT.Clause.eval σ) = true :=
    all_true_of_subset hSubset hClauses
  -- Unfold encodeEndStep to get the world and formula encoding
  let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
  set res := encodeFormula b φ wEnd stBefore with hRes
  -- The unit clause [pos u] is in the step result
  have hUnitIn : [SAT.Lit.pos (FVar.toVar b res.1)] ∈ (encodeEndStep b φ stBefore p).clauses := by
    unfold encodeEndStep
    simp only [wEnd, hRes]
    simp [EncState.addClause]
  -- The unit clause is satisfied
  have hUnitEval : SAT.Clause.eval σ [SAT.Lit.pos (FVar.toVar b res.1)] = true :=
    (List.all_eq_true.mp hStepClauses) _ hUnitIn
  -- This means σ(u) = true
  have hUTrue : σ (FVar.toVar b res.1) = true := by
    simp [SAT.Clause.eval, SAT.Lit.eval] at hUnitEval
    exact hUnitEval
  -- The formula encoding clauses are also satisfied
  have hFormulaSubset : res.2.clauses ⊆ (encodeEndStep b φ stBefore p).clauses := by
    unfold encodeEndStep
    simp only [wEnd, hRes]
    intro clause hClause
    exact EncState.addClause_subset_clauses b res.2 _ hClause
  have hFormulaClauses : res.2.clauses.all (SAT.Clause.eval σ) = true :=
    all_true_of_subset hFormulaSubset hStepClauses
  -- Apply encodeFormula_adequate
  have hAdequate := encodeFormula_adequate b φ wEnd stBefore σ hWF hFormulaClauses stPreEq hPreEq
  -- The forward direction gives us the semantic result
  have hSat : Sat (modelOf b σ hWF) wEnd.p (b.decodeMaybeEvent wEnd.ei)
      (decodePre b σ hWF wEnd.ti) φ := hAdequate.mp hUTrue
  -- Connect to the goal
  -- wEnd.p = p, wEnd.ei = ⟨0, _⟩, wEnd.ti = b.root
  -- decodeMaybeEvent ⟨0, _⟩ = MaybeEvent.none = †
  -- decodePre b σ hWF b.root = (modelOf b σ hWF).history.val
  have hEvent : b.decodeMaybeEvent wEnd.ei = MaybeEvent.none := by
    simp [wEnd, Bounds.decodeMaybeEvent]
  have hTime : decodePre b σ hWF wEnd.ti = (modelOf b σ hWF).history.val := by
    simp [wEnd, modelOf, modelDataOf]
  simp only [wEnd] at hSat
  rw [hEvent, hTime] at hSat
  exact hSat

/-- Helper: For any WId w, the clauses from encodeAllWorldStep for w are preserved
    in the final encodeAllWorld result. -/
lemma encodeAllWorld_step_clauses_preserved (b : Bounds S) (φ : Formula S)
    (st : EncState b) (w : WId b) :
    ∃ stBefore : EncState b,
      (encodeAllWorldStep b φ stBefore w).clauses ⊆ (encodeAllWorld b φ st).clauses := by
  classical
  -- w is in the world list
  have hMem : w ∈ WId.allWorlds b := WId.mem_allWorlds b w
  -- Split the list at w
  obtain ⟨before, after, hSplit⟩ := exists_split_of_mem hMem
  -- The fold can be decomposed
  have hFold : (encodeAllWorld b φ st) =
      (after.foldl (encodeAllWorldStep b φ)
        (encodeAllWorldStep b φ (before.foldl (encodeAllWorldStep b φ) st) w)) := by
    unfold encodeAllWorld
    rw [hSplit]
    simp only [List.foldl_append, List.foldl_cons]
  -- The state before w
  let stBefore := before.foldl (encodeAllWorldStep b φ) st
  use stBefore
  -- Clauses from step(stBefore, w) are preserved in the final result
  rw [hFold]
  apply foldl_subset_state (b := b)
    (f := encodeAllWorldStep b φ)
    (hStep := fun stAcc w' => encodeAllWorldStep_clauses_subset b φ stAcc w')
    (xs := after)
    (init := encodeAllWorldStep b φ stBefore w)

/-- If encodeAllWorld clauses are satisfied, then the formula holds at all reachable worlds. -/
lemma encodeAllWorld_sound (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (φ : Formula S) (st : EncState b)
    (hClauses : (encodeAllWorld b φ st).clauses.all (SAT.Clause.eval σ) = true)
    (stPreEq : EncState b)
    (hPreEq : (addPreEqAll b stPreEq).clauses.all (SAT.Clause.eval σ) = true) :
    ∀ {t : World (Fin b.nParticipants) S.EventType},
      t.time ⪯ (modelOf b σ hWF).history.val →
        Sat (modelOf b σ hWF) t.place t.event t.time φ := by
  classical
  intro t hReach
  -- Find the time index for t.time
  -- Case: t.time = root (reflexive) or t.time ≺− root (strict predecessor)
  rcases hReach with hStrict | hEq
  · -- Strict case: t.time is a proper sub-prehistory of the root
    -- There exists (p', e', t.time) ∈ decodePre b.root
    rcases hStrict with ⟨p', e', hMem⟩
    -- Decode the member world witnessing t.time
    obtain ⟨wWitness, hMemRoot, hDecodePre⟩ :=
      decodePre_member_witness b σ hWF b.root p' e' t.time hMem
    -- wWitness.ti decodes to t.time
    -- ReachT propagates from root to wWitness.ti
    have hReachTi : σ (Var.ReachT wWitness.ti) = true :=
      reachT_for_decoded_worlds b σ hWF wWitness hMemRoot
    -- Construct the WId for t: same place and time as wWitness, but matching event
    -- For the event, we encode t.event (possibly mapping to 0 if not decodable)
    let ei := b.encodeMaybeEvent t.event
    let w : WId b := ⟨t.place, ei, wWitness.ti⟩
    -- Get the clauses for this WId
    obtain ⟨stBefore, hSubset⟩ := encodeAllWorld_step_clauses_preserved b φ st w
    have hStepClauses :
        (encodeAllWorldStep b φ stBefore w).clauses.all (SAT.Clause.eval σ) = true :=
      all_true_of_subset hSubset hClauses
    -- Extract the formula result and implication clause
    set res := encodeFormula b φ w stBefore with hRes
    -- The implication clause [¬ReachT w.ti, pos u] is in the step result
    have hImpIn : [SAT.Lit.neg (Var.ReachT w.ti), SAT.Lit.pos (FVar.toVar b res.1)] ∈
        (encodeAllWorldStep b φ stBefore w).clauses := by
      unfold encodeAllWorldStep
      simp only [w, hRes]
      simp [EncState.addClause]
    -- The implication clause is satisfied
    have hImpEval : SAT.Clause.eval σ [SAT.Lit.neg (Var.ReachT w.ti),
        SAT.Lit.pos (FVar.toVar b res.1)] = true :=
      (List.all_eq_true.mp hStepClauses) _ hImpIn
    -- Since ReachT w.ti = true, we have σ(u) = true
    have hReachW : σ (Var.ReachT w.ti) = true := hReachTi
    have hUTrue : σ (FVar.toVar b res.1) = true := by
      simp [SAT.Clause.eval, SAT.Lit.eval, hReachW] at hImpEval
      exact hImpEval
    -- The formula encoding clauses are also satisfied
    have hFormulaSubset : res.2.clauses ⊆ (encodeAllWorldStep b φ stBefore w).clauses := by
      unfold encodeAllWorldStep
      simp only [w, hRes]
      intro clause hClause
      exact EncState.addClause_subset_clauses b res.2 _ hClause
    have hFormulaClauses : res.2.clauses.all (SAT.Clause.eval σ) = true :=
      all_true_of_subset hFormulaSubset hStepClauses
    -- Apply encodeFormula_adequate
    have hAdequate := encodeFormula_adequate b φ w stBefore σ hWF hFormulaClauses stPreEq hPreEq
    -- The forward direction gives us the semantic result at w
    have hSatW : Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
        (decodePre b σ hWF w.ti) φ := hAdequate.mp hUTrue
    -- Connect to the goal
    -- w.p = t.place (by construction)
    -- w.ti = wWitness.ti, and decodePre wWitness.ti = t.time (by hDecodePre)
    -- For the event, we need decodeMaybeEvent (encodeMaybeEvent t.event) = t.event
    -- This is true if t.event is decodable, otherwise both map to MaybeEvent.none
    have hTime : decodePre b σ hWF w.ti = t.time := by
      simp only [w]
      exact hDecodePre
    -- The event round-trips correctly by events_complete
    simp only [w] at hSatW
    rw [hTime] at hSatW
    rw [b.decodeMaybeEvent_encodeMaybeEvent t.event] at hSatW
    exact hSatW
  · -- Reflexive case: t.time = decodePre b.root = M.history.val
    -- ReachT root = true by reachT_root
    have hReachRoot : σ (Var.ReachT b.root) = true := reachT_root b σ hWF
    -- Construct WId for t
    let ei := b.encodeMaybeEvent t.event
    let w : WId b := ⟨t.place, ei, b.root⟩
    -- Get the clauses for this WId
    obtain ⟨stBefore, hSubset⟩ := encodeAllWorld_step_clauses_preserved b φ st w
    have hStepClauses :
        (encodeAllWorldStep b φ stBefore w).clauses.all (SAT.Clause.eval σ) = true :=
      all_true_of_subset hSubset hClauses
    -- Extract the formula result and implication clause
    set res := encodeFormula b φ w stBefore with hRes
    -- The implication clause is satisfied
    have hImpIn : [SAT.Lit.neg (Var.ReachT w.ti), SAT.Lit.pos (FVar.toVar b res.1)] ∈
        (encodeAllWorldStep b φ stBefore w).clauses := by
      unfold encodeAllWorldStep
      simp only [w, hRes]
      simp [EncState.addClause]
    have hImpEval : SAT.Clause.eval σ [SAT.Lit.neg (Var.ReachT w.ti),
        SAT.Lit.pos (FVar.toVar b res.1)] = true :=
      (List.all_eq_true.mp hStepClauses) _ hImpIn
    -- Since ReachT w.ti = ReachT root = true
    have hReachW : σ (Var.ReachT w.ti) = true := by simp only [w]; exact hReachRoot
    have hUTrue : σ (FVar.toVar b res.1) = true := by
      simp [SAT.Clause.eval, SAT.Lit.eval, hReachW] at hImpEval
      exact hImpEval
    -- Formula clauses are satisfied
    have hFormulaSubset : res.2.clauses ⊆ (encodeAllWorldStep b φ stBefore w).clauses := by
      unfold encodeAllWorldStep
      simp only [w, hRes]
      intro clause hClause
      exact EncState.addClause_subset_clauses b res.2 _ hClause
    have hFormulaClauses : res.2.clauses.all (SAT.Clause.eval σ) = true :=
      all_true_of_subset hFormulaSubset hStepClauses
    -- Apply encodeFormula_adequate
    have hAdequate := encodeFormula_adequate b φ w stBefore σ hWF hFormulaClauses stPreEq hPreEq
    have hSatW : Sat (modelOf b σ hWF) w.p (b.decodeMaybeEvent w.ei)
        (decodePre b σ hWF w.ti) φ := hAdequate.mp hUTrue
    -- Connect to goal
    have hTime : decodePre b σ hWF w.ti = t.time := by
      simp only [w]
      rw [hEq]
      simp [modelOf, modelDataOf]
    -- The event round-trips correctly by events_complete
    simp only [w] at hSatW
    rw [hTime] at hSatW
    rw [b.decodeMaybeEvent_encodeMaybeEvent t.event] at hSatW
    exact hSatW

/-- Helper lemma: clause satisfaction implies semantic assumptions. -/
lemma encodeΓ_sound (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (stPreEq : EncState b)
    (hPreEq : (addPreEqAll b stPreEq).clauses.all (SAT.Clause.eval σ) = true) :
    ∀ Γ (st : EncState b),
      (encodeΓ b Γ st).clauses.all (SAT.Clause.eval σ) = true →
        assumptionsHold (modelOf b σ (wf_from_eval b σ hWF)) Γ := by
  classical
  refine List.rec ?base ?step
  · intro st hClauses a hMem
    cases hMem
  · intro a Γ ih st hClauses
    cases a with
    | endFormula φ =>
        let stHead := encodeEnd b φ st
        have hTailClauses : (encodeΓ b Γ stHead).clauses.all (SAT.Clause.eval σ) = true := by
          unfold encodeΓ at hClauses
          exact hClauses
        have hHeadEval : stHead.clauses.all (SAT.Clause.eval σ) = true := by
          have hSubset := encodeΓ_clauses_subset b Γ stHead
          exact all_true_of_subset hSubset hTailClauses
        have hTail := ih stHead hTailClauses
        intro assumption hMem
        cases hMem with
        | head =>
            have hEnd := encodeEnd_sound b σ hWF φ st hHeadEval stPreEq hPreEq
            unfold assumptionHolds
            exact hEnd
        | tail _ hMemTail =>
            exact hTail _ hMemTail
    | worldFormula φ =>
        let stHead := encodeAllWorld b φ st
        have hTailClauses : (encodeΓ b Γ stHead).clauses.all (SAT.Clause.eval σ) = true := by
          unfold encodeΓ at hClauses
          exact hClauses
        have hHeadEval : stHead.clauses.all (SAT.Clause.eval σ) = true := by
          have hSubset := encodeΓ_clauses_subset b Γ stHead
          exact all_true_of_subset hSubset hTailClauses
        have hTail := ih stHead hTailClauses
        intro assumption hMem
        cases hMem with
        | head =>
            simp only [assumptionHolds, AllWorldValid]
            exact encodeAllWorld_sound b σ hWF φ st hHeadEval stPreEq hPreEq
        | tail _ hMemTail =>
            exact hTail _ hMemTail

/-- **Adequacy Theorem**: If a SAT assignment satisfies the encoded assumptions,
    then the model constructed from that assignment semantically satisfies those assumptions. -/
theorem assumptions_adequate
    (b : Bounds S)
    {Γ : List (Assumption S)}
    {σ : SAT.Assignment (Var b)}
    (hWF : (cnfWellFormed b).eval σ = true)
    (hAssumptions : assumptions b σ Γ = true) :
    assumptionsHold (modelOf b σ (wf_from_eval b σ hWF)) Γ := by
  classical
  unfold assumptions encodeAssumptions encodeAssumptionsWithState at hAssumptions
  set st := encodeΓ b Γ (EncState.empty b) with hSt
  set stWithPreEq := addPreEqAll b st with hStPreEq
  -- band [F, G] = F.and (band [G]) = F.and (G.and (band [])) = F.and (G.and empty)
  unfold SAT.CNF.band at hAssumptions
  rw [SAT.CNF.eval_and] at hAssumptions
  unfold SAT.CNF.band at hAssumptions
  rw [SAT.CNF.eval_and] at hAssumptions
  unfold SAT.CNF.band at hAssumptions
  rw [SAT.CNF.eval_empty] at hAssumptions
  simp only [Bool.and_true, Bool.and_eq_true] at hAssumptions
  have hConj :
      (cnfWellFormed b).eval σ = true ∧ (SAT.CNF.mk stWithPreEq.clauses).eval σ = true := by
    exact of_eq_true hAssumptions
  have hClausesPreEq : stWithPreEq.clauses.all (SAT.Clause.eval σ) = true := by
    simp only [SAT.CNF.eval] at hConj
    exact hConj.2
  -- Extract st.clauses satisfaction from stWithPreEq.clauses
  have hClauses : st.clauses.all (SAT.Clause.eval σ) = true := by
    have hSub := addPreEqAll_clauses_subset (b := b) (st := st)
    exact all_true_of_subset hSub hClausesPreEq
  -- The PreEq clauses are satisfied from stWithPreEq = addPreEqAll b st
  have hWF' : WF b σ := wf_from_eval b σ hWF
  exact
    encodeΓ_sound
      (b := b) (σ := σ) (hWF := hWF') (stPreEq := st) (hPreEq := hClausesPreEq)
      (Γ := Γ) (st := EncState.empty b) hClauses

end Encoding
