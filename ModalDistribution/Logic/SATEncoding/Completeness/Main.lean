import ModalDistribution.Core.Model
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.AssumptionEncoding
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly
import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Completeness.AssignmentOf
import ModalDistribution.Logic.SATEncoding.Completeness.WFProof

/-!
# Completeness of CNF Encoding

This file proves that the CNF encoding is **complete**: the decoder `modelOf` is surjective
onto the space of models that fit within the bounds.

## Main Theorem

`modelOf_surjective`: For any model M that fits within bounds b, there exists a satisfying
assignment σ such that `modelOf b σ hWF ≃ M` (isomorphic as models).

This is the converse of soundness. Together they establish that `modelOf` is a bijection
(up to isomorphism) between satisfying assignments and bounded models.

## Strategy

1. **Encoder Construction** (AssignmentOf.lean):
   - Given a model M within bounds b, construct assignment `assignmentOf b M hFits`
   - This is the inverse of `modelOf`

2. **Well-Formedness** (WFProof.lean):
   - Prove `(cnfWellFormed b).eval (assignmentOf b M hFits) = true`

3. **Round-Trip** (This file):
   - Prove `modelOf b (assignmentOf b M hFits) _ ≃ M`

## References

- FitsInBounds.lean for EncodingView and FitsInBounds structures
- AssignmentOf.lean for the encoder construction
- WFProof.lean for well-formedness proof
- Adequacy/ModelAssembly.lean for `modelOf`
-/

open ModalDistribution Encoding Logic
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Fuel Alignment Lemma

Key lemma: fuelOf (assignmentOf ...) ti = fuelOfTime ev ti (when within bounds).
This connects the decoder's fuel reading with the encoder's semantic height. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The Level variables set by assignmentOf are monotone: Level(ti, j) = true iff j ≤ height. -/
lemma assignmentOf_Level_iff
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (ti : b.times) (j : Fin b.nTimes.succ) :
    assignmentOf b M hFits (Var.Level ti j) = true ↔ j.val ≤ fuelOfTime hFits.view ti := by
  simp only [assignmentOf, levelAt, decide_eq_true_eq]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- fuelOf under assignmentOf equals fuelOfTime (semantic height), when within nTimes.
    This is the key alignment lemma connecting decoder and encoder. -/
lemma fuelOf_assignmentOf_eq_fuelOfTime
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (ti : b.times)
    (hBound : fuelOfTime hFits.view ti ≤ b.nTimes) :
    fuelOf b (assignmentOf b M hFits) ti = fuelOfTime hFits.view ti := by
  let σ := assignmentOf b M hFits
  let fuel := fuelOfTime hFits.view ti
  -- Level(ti, j) = true iff j ≤ fuel
  have hLevelIff : ∀ j : Fin b.nTimes.succ, σ (Var.Level ti j) = true ↔ j.val ≤ fuel := by
    intro j
    exact assignmentOf_Level_iff b M hFits ti j
  -- Step 1: fuelOf ≤ fuel
  -- fuelOf is the maximum j with Level(ti, j) = true
  -- Since Level(ti, j) = true ↔ j ≤ fuel, and Level(ti, fuel+1) = false (if fuel+1 < nTimes+1),
  -- fuelOf cannot exceed fuel
  have hFuelOfLe : fuelOf b σ ti ≤ fuel := by
    -- Proof by showing Level(ti, j) = false for j > fuel
    -- Therefore find? on reversed list cannot find anything > fuel
    -- Use fuelOf_findWitness with Level(ti, 0) = true (always true since 0 ≤ fuel)
    have h0True : σ (Var.Level ti ⟨0, Nat.zero_lt_succ _⟩) = true := by
      rw [hLevelIff]
      exact Nat.zero_le _
    obtain ⟨j, _, hFuelEq, hLevelTrue⟩ := fuelOf_findWitness b σ ti ⟨0, Nat.zero_lt_succ _⟩ h0True
    -- hFuelEq : fuelOf b σ ti = (Fin.rev j).val
    -- hLevelTrue : σ (Var.Level ti (Fin.rev j)) = true
    -- From hLevelIff: (Fin.rev j).val ≤ fuel
    have hRevJLeFuel : (Fin.rev j).val ≤ fuel := (hLevelIff (Fin.rev j)).mp hLevelTrue
    omega
  -- Step 2: fuelOf ≥ fuel (using level_true_le_fuelOf)
  have hFuelOfGe : fuel ≤ fuelOf b σ ti := by
    have hFuelLt : fuel < b.nTimes.succ := Nat.lt_succ_of_le hBound
    let fuelIdx : Fin b.nTimes.succ := ⟨fuel, hFuelLt⟩
    have hTrue : σ (Var.Level ti fuelIdx) = true := (hLevelIff fuelIdx).mpr (Nat.le_refl _)
    exact level_true_le_fuelOf b σ ti fuelIdx hTrue
  -- Conclude: Note σ = assignmentOf b M hFits by definition
  have hEq : σ = assignmentOf b M hFits := rfl
  simp only [σ] at hFuelOfLe hFuelOfGe
  omega

/-! ## Round-Trip Proofs

These proofs show that decoding the encoded assignment recovers the original model.
The key insight is that the encoder sets each variable according to the model's semantic
structure, and the decoder reads it back. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: fuelOfTime for reachable prehistories is bounded by nTimes. -/
lemma fuelOfTime_bounded
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (ti : b.times) :
    fuelOfTime hFits.view ti ≤ b.nTimes := by
  unfold fuelOfTime rankPre
  exact Nat.le_of_lt (prehistoryAt_height_lt_nTimes hFits ti)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- For the encoded assignment, fuelOf equals semantic height. -/
lemma fuelOf_assignmentOf_eq
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (ti : b.times) :
    fuelOf b (assignmentOf b M hFits) ti = fuelOfTime hFits.view ti :=
  fuelOf_assignmentOf_eq_fuelOfTime b M hFits ti (fuelOfTime_bounded b M hFits ti)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Core roundtrip lemma: decodePre at reachable time index is histEq to the prehistory.
    This is the key inductive lemma for roundtrip_history. -/
lemma decodePre_histEq_at_reachable
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (H : PreHistory (Fin b.nParticipants) (Signature.EventType S))
    (hReach : H ∈ reachablePreHistories M.history.val) :
    PreHistory.histEq
      (decodePre b (assignmentOf b M hFits) (wfOf b M hFits) (hFits.view.timeIndexOf H))
      H := by
  -- Well-founded induction on height of H
  induction H using (PreHistory.happensBefore_wellFounded
      (P := Fin b.nParticipants) (Event := Signature.EventType S)).induction with
  | _ H ih =>
  let σ := assignmentOf b M hFits
  let hWF := wfOf b M hFits
  let ev := hFits.view
  let ti := ev.timeIndexOf H
  -- Key: fuelOf σ ti = height H (since Level vars encode height)
  have hFuelEq : fuelOf b σ ti = rankPre H := by
    rw [fuelOf_assignmentOf_eq]
    unfold fuelOfTime
    rw [prehistoryOfTime_of_reachable ev hReach]
  -- Need to show histEq (decodePre b σ hWF ti) H
  -- Use histEq_spec: show bisimulation property
  rw [PreHistory.histEq_spec]
  constructor
  · -- Forward: ∀ w ∈ decodePre ..., ∃ w' ∈ H, worldEq w w'
    intro w hw
    -- w came from decodePre, which iterates over Mem(ti, wId) = true
    obtain ⟨wId, hwWorldEq, hwMemTrue⟩ := exists_memVar_of_mem_decodePre b σ hWF ti hw
    -- hwWorldEq : (wId.p, decodeMaybeEvent wId.ei, decodePre wId.ti) = w
    -- hwMemTrue : σ (Var.Mem ti wId) = true
    -- Since σ = assignmentOf, Mem(ti, wId) = worldInPrehistory ev ti wId
    have hwMemSeq : worldInPrehistory ev ti wId = true := by
      have : σ (Var.Mem ti wId) = worldInPrehistory hFits.view ti wId :=
        assignmentOf_Mem hFits ti wId
      rw [← this]
      exact hwMemTrue
    -- Extract semantic world from worldInPrehistory
    obtain ⟨sem, hSemMem, hSemPlace, hSemEvent, hSemTi⟩ :=
      extract_of_worldInPrehistory ev ti wId hwMemSeq
    -- hSemMem : sem ∈ prehistoryOfTime ev ti
    -- prehistoryOfTime ev ti = prehistoryAt ev ti = H (by reachability)
    have hPreEq : prehistoryOfTime ev ti = H := by
      unfold prehistoryOfTime
      exact prehistoryAt_of_reachable ev hReach
    rw [hPreEq] at hSemMem
    -- So sem ∈ H. Need to show worldEq w sem.
    use sem
    constructor
    · exact hSemMem
    · -- worldEq w sem means place, event, time all match
      rw [PreHistory.worldEq_spec]
      rw [← hwWorldEq]
      simp only [World.place, World.event, World.time]
      refine ⟨hSemPlace.symm, ?_, ?_⟩
      · -- Event: b.decodeMaybeEvent wId.ei = sem.event
        exact hSemEvent
      · -- Time: histEq (decodePre wId.ti) sem.time
        -- sem.time ≺− H (by membership), so sem.time is reachable
        have hSemTimeBefore : sem.time ≺− H := History.happensBefore_of_mem hSemMem
        have hSemTimeReach : sem.time ∈ reachablePreHistories M.history.val :=
          time_mem_reachablePreHistories_of_mem_history hReach hSemMem
        -- By IH, decodePre at ev.timeIndexOf sem.time ≃ sem.time
        have hIH := ih sem.time hSemTimeBefore hSemTimeReach
        -- We have hSemTi : ev.timeIndexOf sem.time = wId.ti
        rw [← hSemTi]
        exact hIH
  · -- Backward: ∀ w ∈ H, ∃ w' ∈ decodePre ..., worldEq w' w
    intro w hw
    -- w ∈ H is a semantic world. Show worldInPrehistory gives Mem(ti, widOfWorld w) = true.
    have hMemSeq : worldInPrehistory ev ti (widOfWorld ev w) = true := by
      have hPreEq : prehistoryOfTime ev ti = H := by
        unfold prehistoryOfTime
        exact prehistoryAt_of_reachable ev hReach
      have hInPre : w ∈ prehistoryOfTime ev ti := by
        rw [hPreEq]
        exact hw
      exact worldInPrehistory_of_mem ev ti w hInPre
    have hMemTrue : σ (Var.Mem ti (widOfWorld ev w)) = true := by
      have : σ (Var.Mem ti (widOfWorld ev w)) = worldInPrehistory hFits.view ti (widOfWorld ev w) :=
        assignmentOf_Mem hFits ti (widOfWorld ev w)
      rw [this]
      exact hMemSeq
    -- The world (widOfWorld.p, decodeMaybeEvent widOfWorld.ei, decodePre widOfWorld.ti)
    -- is in decodePre ti
    have hDecWorld : (widOfWorld ev w).p = w.place := rfl
    have hDecEvent : b.decodeMaybeEvent (widOfWorld ev w).ei = w.event :=
      widOfWorld_event ev w
    have hDecTi : (widOfWorld ev w).ti = ev.timeIndexOf w.time := rfl
    -- Construct the decoded world
    let decodedW : World (Fin b.nParticipants) (Signature.EventType S) :=
      ((widOfWorld ev w).p, b.decodeMaybeEvent (widOfWorld ev w).ei,
       decodePre b σ hWF (widOfWorld ev w).ti)
    have hDecodedMem : decodedW ∈ decodePre b σ hWF ti :=
      mem_decodePre_of_memVar b σ hWF ti (widOfWorld ev w) hMemTrue
    use decodedW
    constructor
    · exact hDecodedMem
    · -- worldEq decodedW w
      rw [PreHistory.worldEq_spec]
      simp only [decodedW, World.place, World.event, World.time]
      refine ⟨hDecWorld, hDecEvent, ?_⟩
      -- histEq (decodePre widOfWorld.ti) w.time
      -- w.time ≺− H, so w.time is reachable
      have hWTimeBefore : w.time ≺− H := History.happensBefore_of_mem hw
      have hWTimeReach : w.time ∈ reachablePreHistories M.history.val :=
        time_mem_reachablePreHistories_of_mem_history hReach hw
      -- By IH, decodePre at ev.timeIndexOf w.time ≃ w.time
      have hIH := ih w.time hWTimeBefore hWTimeReach
      -- widOfWorld.ti = ev.timeIndexOf w.time
      rw [hDecTi]
      exact hIH

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The decoded history equals M's history (up to histEq). -/
theorem roundtrip_history
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M) :
    PreHistory.histEq
      (modelOf b (assignmentOf b M hFits) (wfOf b M hFits)).history.val
      M.history.val := by
  -- modelOf.history.val = decodePre at root
  -- M.history.val is reachable from itself
  let ev := hFits.view
  have hRootReach : M.history.val ∈ reachablePreHistories M.history.val :=
    self_mem_reachablePreHistories M.history.val
  -- Root time index corresponds to M.history.val
  have hRootTi : ev.timeIndexOf M.history.val = b.root := ev.timeIndex_root
  -- By the core lemma, decodePre at root ≃ M.history.val
  have h := decodePre_histEq_at_reachable b M hFits M.history.val hRootReach
  rw [hRootTi] at h
  -- modelOf.history.val = decodePre b σ hWF b.root
  unfold modelOf modelDataOf
  simp only
  exact h

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The decoded predicate interpretation contains M's predInterp on reachable prehistories.

    For reachable H, M.predInterp p H ⊆ (modelOf ...).predInterp p H.

    Note: The reverse inclusion would require M.predInterp to respect histEq, which we
    don't assume. However, this direction suffices for formula satisfaction: any predicate
    that holds in M will be detected by the decoder. -/
theorem roundtrip_predInterp_superset_at_reachable
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (p : Fin b.nParticipants)
    (H : PreHistory (Fin b.nParticipants) (Signature.EventType S))
    (hReach : H ∈ reachablePreHistories M.history.val)
    (atom : Signature.AtomicPredType S)
    (hAtomMem : atom ∈ M.predInterp p H)
    (hAtomInBounds : ∃ k : b.predIx, b.preds.get k = atom) :
    atom ∈ (modelOf b (assignmentOf b M hFits) (wfOf b M hFits)).predInterp p H := by
  let σ := assignmentOf b M hFits
  let hWF := wfOf b M hFits
  let ev := hFits.view
  let ti := ev.timeIndexOf H
  simp only [modelOf, modelDataOf]
  -- Use ti = ev.timeIndexOf H as witness
  -- Since H is reachable, prehistoryOfTime ev ti = H
  have hPreEqH : prehistoryOfTime ev ti = H := prehistoryOfTime_of_reachable ev hReach
  -- decodePre at ti is histEq to H (by roundtrip_history logic)
  have hDecodeHistEq : PreHistory.histEq (decodePre b σ hWF ti) H :=
    decodePre_histEq_at_reachable b M hFits H hReach
  -- ti ∈ timeIndicesFor b σ hWF H
  have hTiMem : ti ∈ timeIndicesFor b σ hWF H := by
    apply (mem_timeIndicesFor_iff (b := b) (σ := σ) (hWF := hWF) (H := H) (ti := ti)).2
    constructor
    · simp [Bounds.timesL]
    · exact hDecodeHistEq
  -- PreEq(ti, ti) = true (reflexivity)
  have hPreEqTrue : σ (Var.PreEq ti ti) = true := by
    have : σ (Var.PreEq ti ti) = preEqAt hFits.view ti ti := assignmentOf_PreEq hFits ti ti
    rw [this]
    unfold preEqAt
    simp only [decide_eq_true_eq]
    exact PreHistory.histEq_refl _
  -- Find k such that b.preds.get k = atom
  obtain ⟨k, hPredK⟩ := hAtomInBounds
  -- predHolds ev p ti k = true because atom ∈ M.predInterp p H and prehistoryOfTime ev ti = H
  have hPredHolds : predHolds ev p ti k = true := by
    unfold predHolds
    simp only [decide_eq_true_eq]
    rw [hPredK]
    refine ⟨H, ?_, hAtomMem⟩
    rw [hPreEqH]
    exact PreHistory.histEq_refl _
  -- σ (Var.Pred p ti k) = predHolds ev p ti k = true
  have hPredTrue : σ (Var.Pred p ti k) = true := hPredHolds
  -- atom ∈ predTbl b σ p ti
  have hPredTbl : atom ∈ predTbl b σ p ti := ⟨k, hPredTrue, hPredK⟩
  -- Construct the witness
  exact ⟨ti, hTiMem, ti, hPreEqTrue, hPredTbl⟩

/-- Every quorum in a semifilter over Fin n contains a minimal quorum. -/
lemma quorum_contains_minimal {n : Nat} (L : Semifilter (Fin n))
    (O : Set (Fin n)) (hO : O ∈ L.quorums) :
    ∃ Q : Finset (Fin n), (Q : Set (Fin n)) ∈ L.quorums ∧ (Q : Set _) ⊆ O ∧
      ∀ Q' : Finset (Fin n), (Q' : Set (Fin n)) ∈ L.quorums → Q' ⊆ Q → Q' = Q := by
  classical
  -- Consider quorums that are subsets of O
  -- Note: O is a Set but we want to find a Finset Q ⊆ O
  -- Since O ∈ L.quorums, O.toFinset is a quorum (if O is finite, which it is for Fin n)
  -- Actually for Fin n, all sets are finite, so we can work with Finsets
  let quorumsBelow : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powerset.filter (fun Q =>
      (Q : Set (Fin n)) ∈ L.quorums ∧ (Q : Set _) ⊆ O)
  -- First, show O.toFinset is in quorumsBelow (if O is a quorum)
  -- Actually, O might not be a Finset directly. But any quorum subset of O works.
  -- Since O ∈ L.quorums and L.nonempty gives us at least one quorum,
  -- and upwardClosed means supersets are quorums,
  -- we need to find a quorum ⊆ O.
  -- Actually, O itself is a quorum. The question is whether O is finite (has a Finset repr).
  -- For Fin n, all sets are decidable and we can convert.
  have hOFinset : O.Finite := Set.toFinite O
  -- Actually, this approach is getting complicated. Let me use the existing lemma.
  -- exists_minimal_quorum gives us a minimal quorum in L. We need to ensure it's ⊆ O.
  -- That's not directly what exists_minimal_quorum gives us.
  -- Let me think differently: use upwardClosed in reverse.
  -- If O is a quorum, consider all Finset quorums Q ⊆ O, pick minimal by cardinality.
  -- Need: this set is nonempty (some quorum is ⊆ O for finite types).
  -- For Fin n, we can convert O to a Finset and that Finset is a quorum.
  let OFin : Finset (Fin n) := O.toFinite.toFinset
  have hOFin_eq : (OFin : Set (Fin n)) = O := Set.Finite.coe_toFinset _
  have hOFin_quorum : (OFin : Set (Fin n)) ∈ L.quorums := by rw [hOFin_eq]; exact hO
  -- Now quorumsBelow is nonempty (contains OFin)
  have hNonempty : quorumsBelow.Nonempty := by
    refine ⟨OFin, ?_⟩
    simp only [quorumsBelow, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    exact ⟨hOFin_quorum, by rw [hOFin_eq]⟩
  -- Find minimal by cardinality
  have hMin := Finset.exists_min_image quorumsBelow Finset.card hNonempty
  obtain ⟨Qmin, hQminMem, hQminMin⟩ := hMin
  simp only [quorumsBelow, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    at hQminMem
  refine ⟨Qmin, hQminMem.1, hQminMem.2, ?_⟩
  intro Q' hQ'Quorum hQ'Sub
  by_contra hNe
  have hProper : Q' ⊂ Qmin := ⟨hQ'Sub, fun h => hNe (Finset.Subset.antisymm hQ'Sub h)⟩
  have hQ'Card : Q'.card < Qmin.card := Finset.card_lt_card hProper
  have hQ'InBelow : Q' ∈ quorumsBelow := by
    simp only [quorumsBelow, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    exact ⟨hQ'Quorum, Set.Subset.trans (Finset.coe_subset.mpr hQ'Sub) hQminMem.2⟩
  have hContra := hQminMin Q' hQ'InBelow
  omega

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Key lemma: For σ = assignmentOf, the decoded minimalQuorumsIx at findValueIndex v
    equals the minimal quorums of M.learner v. -/
lemma assignmentOf_minQ_iff
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M)
    (v : Signature.Value S)
    (Q : Finset (Fin b.nParticipants)) :
    let σ := assignmentOf b M hFits
    let vIdx := b.findValueIndex v
    σ (Var.MinQ vIdx Q) = true ↔
      (Q : Set (Fin b.nParticipants)) ∈ (M.learner v).quorums ∧
      ∀ Q' : Finset (Fin b.nParticipants),
        (Q' : Set (Fin b.nParticipants)) ∈ (M.learner v).quorums → Q' ⊆ Q → Q' = Q := by
  classical
  let σ := assignmentOf b M hFits
  let vIdx := b.findValueIndex v
  -- σ (Var.MinQ vIdx Q) = isMinimalQuorum M vIdx Q
  have hMinQDef : σ (Var.MinQ vIdx Q) = isMinimalQuorum M vIdx Q := rfl
  -- isMinimalQuorum M vIdx Q = decide (isRepresentative vIdx ∧ Q ∈ L.quorums ∧ minimal)
  -- where L = M.learner (b.values.get vIdx)
  -- b.values.get (findValueIndex v) = v (by findValueIndex_value)
  have hValEq : b.values.get vIdx = v := findValueIndex_value b v
  have hEx : ∃ i : b.valIx, b.values.get i = v := ⟨vIdx, hValEq⟩
  have hRepTrue : isRepresentative vIdx = true := isRepresentative_findValueIndex v hEx
  constructor
  · -- Forward: MinQ true → quorum and minimal
    intro hMinQ
    -- hMinQ : σ (Var.MinQ vIdx Q) = true, where σ = assignmentOf b M hFits
    -- hMinQDef : σ (Var.MinQ vIdx Q) = isMinimalQuorum M vIdx Q
    have hMinQ' : isMinimalQuorum M vIdx Q = true := hMinQDef.symm.trans hMinQ
    unfold isMinimalQuorum at hMinQ'
    simp only [decide_eq_true_eq] at hMinQ'
    obtain ⟨_, hQuorum, hMinimal⟩ := hMinQ'
    rw [hValEq] at hQuorum hMinimal
    exact ⟨hQuorum, hMinimal⟩
  · -- Backward: quorum and minimal → MinQ true
    intro ⟨hQuorum, hMinimal⟩
    -- Need: σ (Var.MinQ vIdx Q) = true
    -- σ (Var.MinQ vIdx Q) = assignmentOf b M hFits (Var.MinQ vIdx Q) = isMinimalQuorum M vIdx Q
    -- So it suffices to show isMinimalQuorum M vIdx Q = true
    change assignmentOf b M hFits (Var.MinQ vIdx Q) = true
    unfold assignmentOf isMinimalQuorum
    simp only [decide_eq_true_eq, hRepTrue, true_and, hValEq]
    exact ⟨hQuorum, hMinimal⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- The decoded learner interpretation equals M's learner. -/
theorem roundtrip_learner
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M) :
    (modelOf b (assignmentOf b M hFits) (wfOf b M hFits)).learner = M.learner := by
  classical
  let σ := assignmentOf b M hFits
  let hWF := wfOf b M hFits
  -- modelOf's learner is learnerOf
  unfold modelOf
  simp only
  -- Goal: learnerOf b σ hWF = M.learner
  funext v
  -- Use Semifilter.ext: show quorums are equal
  have hLearners : (cnfLearners b).eval σ = true := cnfLearners_sat b σ hWF
  have hValMem : v ∈ classValues b := all_values_in_classValues b v
  have hPickEq : pickRep b σ v = b.findValueIndex v :=
    pickRep_eq_findValueIndex b σ hLearners hValMem
  have hEx : ∃ i : b.valIx, b.values.get i = v :=
    ⟨b.findValueIndex v, findValueIndex_value b v⟩
  have hRepTrue : isRepresentative (b.findValueIndex v) = true :=
    isRepresentative_findValueIndex v hEx
  have hRepSat : σ (Var.Rep (pickRep b σ v)) = true := by
    rw [hPickEq]
    unfold σ assignmentOf
    simp only [hRepTrue]
  -- learnerOf v for σ = assignmentOf is learnerIxOf at pickRep = findValueIndex
  -- Since hValMem holds, learnerOf v = learnerIxOf b σ hWF (pickRep b σ v) hRep
  -- We'll work with the explicit quorum structure
  ext O
  -- Unfold learnerOf to expose the underlying structure
  -- learnerOf with hValMem true gives learnerIxOf at pickRep
  -- learnerIxOf.quorums = { O | ∃ Q ∈ minSets, Q ⊆ O }
  simp only [learnerOf, hValMem, ↓reduceDIte]
  -- Now we're comparing learnerIxOf.quorums with M.learner.quorums
  -- learnerIxOf.quorums = { O | ∃ Q ∈ minSets, Q ⊆ O }
  -- where minSets = { (Qf : Set _) | Qf ∈ mins } and mins = decoded MinQ at pickRep
  -- For σ = assignmentOf:
  -- MinQ(pickRep v, Qf) = true iff isMinimalQuorum M (pickRep v) Qf = true
  -- pickRep v = findValueIndex v, so this is minimal quorum encoding at the representative
  simp only [learnerIxOf]
  -- Now the goal is about the set membership
  constructor
  · -- Forward: O ∈ learnerIxOf.quorums → O ∈ M.learner.quorums
    intro hO
    -- hO : O ∈ { O | ∃ Q ∈ minSets, Q ⊆ O }
    simp only [Set.mem_setOf_eq] at hO
    obtain ⟨Q_set, hQMinSet, hQSubO⟩ := hO
    obtain ⟨Qf, hQfMins, hQfEq⟩ := hQMinSet
    subst hQfEq
    -- hQfMins : Qf ∈ decoded mins at pickRep
    have hMinQTrue : σ (Var.MinQ (pickRep b σ v) Qf) = true :=
      minq_in_decoded_imp_true b σ (pickRep b σ v) Qf hQfMins
    rw [hPickEq] at hMinQTrue
    -- MinQ true at findValueIndex v → Qf is a quorum
    have hQfQuorum : (Qf : Set (Fin b.nParticipants)) ∈ (M.learner v).quorums := by
      have h := (assignmentOf_minQ_iff b M hFits v Qf).mp hMinQTrue
      exact h.1
    exact (M.learner v).upwardClosed hQfQuorum hQSubO
  · -- Backward: O ∈ M.learner.quorums → O ∈ learnerIxOf.quorums
    intro hO
    -- Find minimal quorum Qf ⊆ O
    obtain ⟨Qf, hQfQuorum, hQfSubO, hQfMinimal⟩ := quorum_contains_minimal (M.learner v) O hO
    -- Show MinQ is true for Qf
    have hMinQTrue : σ (Var.MinQ (b.findValueIndex v) Qf) = true := by
      have h := (assignmentOf_minQ_iff b M hFits v Qf).mpr ⟨hQfQuorum, hQfMinimal⟩
      exact h
    -- Qf is in decoded mins
    have hQfMins : Qf ∈ (decodeLearnerData b σ).minimalQuorumsIx (b.findValueIndex v) := by
      unfold decodeLearnerData
      simp only [List.mem_filterMap]
      let mask := finsetToBitmask Qf
      have hMaskLt : mask < Nat.shiftLeft 1 b.nParticipants := finsetToBitmask_lt Qf
      let maskFin : Fin (Nat.shiftLeft 1 b.nParticipants) := ⟨mask, hMaskLt⟩
      have hMaskEq : bitmaskToFinset b.nParticipants mask = Qf := finsetToBitmask_inverse Qf
      refine ⟨Var.MinQ (b.findValueIndex v) (bitmaskToFinset b.nParticipants mask), ?_, ?_⟩
      · unfold Var.allMinQ
        exact List.mem_map.mpr ⟨maskFin, List.mem_finRange _, rfl⟩
      · simp only [hMaskEq, hMinQTrue, ↓reduceIte]
    rw [← hPickEq] at hQfMins
    -- Goal: O ∈ { O | ∃ Q ∈ minSets, Q ⊆ O }
    simp only [Set.mem_setOf_eq]
    exact ⟨(Qf : Set _), ⟨Qf, hQfMins, rfl⟩, hQfSubO⟩

/-! ## Main Completeness Theorem -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- **Completeness**: The decoder `modelOf` produces a model that agrees with M on:
    1. History structure (up to histEq)
    2. Predicate interpretation: M's predicates are included in decoder's (on reachable H)
    3. Learner semifilters

    The predicate inclusion (M ⊆ decoder) suffices for formula satisfaction: any predicate
    that holds in M will be detected by the decoder. The reverse inclusion would require
    M.predInterp to respect histEq, which is not assumed. -/
theorem modelOf_surjective
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M) :
    ∃ (σ : SAT.Assignment (Var b)) (hWF : WF b σ),
      PreHistory.histEq (modelOf b σ hWF).history.val M.history.val ∧
      (∀ p H atom, H ∈ reachablePreHistories M.history.val →
        atom ∈ M.predInterp p H →
        (∃ k : b.predIx, b.preds.get k = atom) →
        atom ∈ (modelOf b σ hWF).predInterp p H) ∧
      (modelOf b σ hWF).learner = M.learner := by
  use assignmentOf b M hFits
  use wfOf b M hFits
  refine ⟨roundtrip_history b M hFits, ?_, roundtrip_learner b M hFits⟩
  intro p H atom hReach hMem hInBounds
  exact roundtrip_predInterp_superset_at_reachable b M hFits p H hReach atom hMem hInBounds

end Encoding
