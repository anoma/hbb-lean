import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.TseytinGadgets
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly
import ModalDistribution.Logic.SATEncoding.Adequacy.LearnerConstruction

-- Disable long line warnings: this file contains inline expressions that must match
-- the exact syntactic form produced by `simp only [encodeFormula]`
set_option linter.style.longLine false
-- Disable unused variable warnings: decidable if-then-else requires named hypotheses
-- even when unused in the branch body
set_option linter.unusedVariables false

/-!
# Tseytin Correctness for Diamond (◊)

This file proves that the Tseytin encoding correctly captures the semantics of
diamond modal operator formulas.

## Main Result

- `encode_diamond_correct`: If the encoding produces control variable u for ◊ φ
  with learner values, quorum tuples, and witness variables, then the SAT encoding
  correctly represents the diamond semantics.

## Strategy

The diamond encoding is the most complex constructor. For each tuple of minimal quorums
(one per learner value), it creates a clause:
- [¬u, ¬MinQ(ℓ₁,Q₁), ..., ¬MinQ(ℓₖ,Qₖ), u_p₁, ..., u_pₙ]

Where:
- The MinQ guards represent minimal quorum selection for each learner
- The u_pᵢ are witness variables for φ at participants in Q₁ ∩ ... ∩ Qₖ

This represents: u ∧ MinQ(ℓ₁,Q₁) ∧ ... ∧ MinQ(ℓₖ,Qₖ) → (∃ p ∈ ∩Qᵢ. φ@p)

## Note

The diamond encoding uses one-way implications (similar to past and forall backward).
The full semantic bi-conditional requires additional constraints from the structure CNF.
-/

open ModalDistribution Encoding Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.Value S)]

open SAT

/-! ## Helper Definitions -/

/-- A tuple of quorums with their corresponding learner indices. -/
structure QuorumTuple (b : Bounds S) where
  /-- Learner value indices -/
  learnerIndices : List b.valIx
  /-- Quorum sets, one per learner -/
  quorums : List (Finset b.participants)
  /-- The two lists have the same length -/
  hLength : learnerIndices.length = quorums.length

/-- Compute the intersection of all quorums in a tuple. -/
def QuorumTuple.intersection (b : Bounds S) (qt : QuorumTuple b) : Finset b.participants :=
  qt.quorums.foldl (· ∩ ·) Finset.univ

/-- The guard literals for a quorum tuple: ¬MinQ(ℓᵢ, Qᵢ) for each i. -/
def QuorumTuple.guards (b : Bounds S) (qt : QuorumTuple b) : List (Lit (Var b)) :=
  (qt.learnerIndices.zip qt.quorums).map fun (vIdx, Q) =>
    Lit.neg (Var.MinQ vIdx Q)

/-! ## Tseytin Correctness for Diamond -/

omit [DecidableEq S.Value] in
/-- For each quorum tuple clause, if u and all MinQ guards are true,
    then at least one witness in the intersection must be true.

    This captures the forward direction of the diamond encoding. -/
lemma encode_diamond_tuple (b : Bounds S) (σ : Assignment (Var b))
    (u : FVar b)
    (qt : QuorumTuple b)
    (witnessPairs : List (FVar b × Fin b.nParticipants))
    (clause : Clause (Var b))
    (hClause : clause =
      [Lit.neg (FVar.toVar b u)] ++
      qt.guards b ++
      witnessPairs.map (fun (uWit, _) => Lit.pos (FVar.toVar b uWit)))
    (hSat : Clause.eval σ clause = true)
    (hU : σ (FVar.toVar b u) = true)
    (hGuards : ∀ pair ∈ qt.learnerIndices.zip qt.quorums,
      σ (Var.MinQ pair.1 pair.2) = true) :
    ∃ pair ∈ witnessPairs, σ (FVar.toVar b pair.1) = true := by
  classical
  -- Convert to `any` form
  have hAny := Clause.eval_eq_any (σ := σ) (C := clause)
  rw [hAny] at hSat

  -- Extract a literal that evaluates to true
  obtain ⟨lit, hMem, hEval⟩ := (List.any_eq_true).mp hSat
  rw [hClause] at hMem

  -- Show that lit must be one of the witness literals
  have hInParts : lit ∈ [Lit.neg (FVar.toVar b u)] ++
      qt.guards b ++ witnessPairs.map (fun (uWit, _) => Lit.pos (FVar.toVar b uWit)) := hMem

  have hNotU : Lit.neg (FVar.toVar b u) ≠ lit := by
    intro h
    rw [← h, Lit.eval] at hEval
    simp [hU] at hEval

  have hNotGuards : ∀ g ∈ qt.guards b, g ≠ lit := by
    intro g hg
    unfold QuorumTuple.guards at hg
    obtain ⟨pair, hPair, rfl⟩ := List.mem_map.mp hg
    intro h
    rw [← h, Lit.eval] at hEval
    have := hGuards pair hPair
    simp [this] at hEval

  -- lit must be in witness literals
  have : lit ∈ witnessPairs.map (fun (uWit, _) => Lit.pos (FVar.toVar b uWit)) := by
    have := List.mem_append.mp hInParts
    cases this with
    | inl h =>
        have := List.mem_append.mp h
        cases this with
        | inl hU' =>
            have := List.mem_singleton.mp hU'
            exact absurd this.symm hNotU
        | inr hG =>
            have hIn := hG
            have hNeq := hNotGuards _ hIn
            exact absurd rfl hNeq
    | inr h => exact h

  -- Extract the witness pair
  obtain ⟨pair, hPairIn, hPairEq⟩ := List.mem_map.mp this
  use pair, hPairIn
  obtain ⟨uWit, p⟩ := pair
  rw [← hPairEq, Lit.eval] at hEval
  exact hEval

omit [DecidableEq S.Value] in
/-- Main correctness for diamond encoding.

    If the full clause list represents the diamond encoding for all quorum tuples,
    and u = true with appropriate MinQ assignments, then the witness conditions hold. -/
lemma encode_diamond_correct (b : Bounds S) (σ : Assignment (Var b))
    (u : FVar b)
    (tuples : List (QuorumTuple b))
    (clauses : List (Clause (Var b)))
    (hTuples : ∀ qt ∈ tuples,
      ∃ (witnessPairs : List (FVar b × Fin b.nParticipants))
        (clause : Clause (Var b)),
        (∀ pair ∈ witnessPairs, pair.2 ∈ qt.intersection b) ∧
        clause = [Lit.neg (FVar.toVar b u)] ++ qt.guards b ++
          witnessPairs.map (fun (uWit, _) => Lit.pos (FVar.toVar b uWit)) ∧
        clause ∈ clauses)
    (hSat : clauses.all (Clause.eval σ) = true)
    (hU : σ (FVar.toVar b u) = true) :
    ∀ qt ∈ tuples,
      (∀ pair ∈ qt.learnerIndices.zip qt.quorums,
        σ (Var.MinQ pair.1 pair.2) = true) →
      ∃ p ∈ qt.intersection b,
        ∃ uWit, σ (FVar.toVar b uWit) = true := by
  intro qt hQt hGuards
  -- Extract witness information for this tuple
  obtain ⟨witnessPairs, clause, hInIntersection, hClause, hClauseIn⟩ :=
    hTuples qt hQt

  -- The clause is satisfied
  have hClauseSat : Clause.eval σ clause = true := by
    have hAll := List.all_eq_true.mp hSat
    exact hAll _ hClauseIn

  -- Apply encode_diamond_tuple to get a witness pair
  obtain ⟨⟨uWit, p⟩, hPairIn, hWitTrue⟩ :=
    encode_diamond_tuple b σ u qt witnessPairs clause
      hClause hClauseSat hU hGuards

  -- Show p is in the intersection (p = pair.2 where pair = (uWit, p))
  have hPInIntersection : p ∈ qt.intersection b :=
    hInIntersection (uWit, p) hPairIn

  -- Provide the witness
  use p, hPInIntersection, uWit, hWitTrue

/-- From semantic membership in `learnerIxOf`, extract a true `MinQ` literal for
    some minimal quorum contained in the given quorum. -/
lemma learnerIxOf_minQ_true_subset (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (vIdx : b.valIx) (hRep : σ (Var.Rep vIdx) = true)
    (Q : Finset b.participants)
    (hQuorum : (Q : Set _) ∈ (learnerIxOf b σ hWF vIdx hRep).quorums) :
    ∃ Qmin : Finset b.participants, Qmin ⊆ Q ∧ σ (Var.MinQ vIdx Qmin) = true := by
  classical
  -- Unfold the quorum definition inside learnerIxOf
  unfold learnerIxOf at hQuorum
  rcases hQuorum with ⟨QSet, hQSetMin, hSubset⟩
  -- hQSetMin witnesses membership in minSets
  rcases hQSetMin with ⟨Qf, hQf_mins, hQSetEq⟩
  subst hQSetEq
  -- From decoded membership we recover MinQ = true
  have hMinQ_true : σ (Var.MinQ vIdx Qf) = true :=
    minq_in_decoded_imp_true b σ vIdx Qf hQf_mins
  refine ⟨Qf, ?_, hMinQ_true⟩
  intro p hp
  exact hSubset hp

/-- Value-keyed version: semantic quorum membership yields a contained minimal quorum
    whose `MinQ` literal is true. -/
lemma learnerOf_minQ_true_subset (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (v : S.Value) (hVal : v ∈ classValues b)
    (Q : Finset b.participants)
    (hQuorum : (Q : Set _) ∈ (learnerOf b σ hWF v).quorums) :
    ∃ Qmin : Finset b.participants, Qmin ⊆ Q ∧
      σ (Var.MinQ (pickRep b σ v) Qmin) = true := by
  classical
  -- learnerOf takes the `hVal` branch
  unfold learnerOf at hQuorum
  simp [hVal] at hQuorum
  -- pickRep provides the representative with Rep = true
  have hLearners := cnfLearners_sat b σ hWF
  have hRep : σ (Var.Rep (pickRep b σ v)) = true :=
    pickRep_rep_true b σ hLearners hVal
  -- Apply the index-keyed lemma
  exact learnerIxOf_minQ_true_subset b σ hWF (pickRep b σ v) hRep Q hQuorum

omit [DecidableEq S.Value] in
/-- Monotonicity of `Sat.check` in the accumulator set. -/
lemma Sat_check_mono_acc {P : Type _} [Nonempty P] (M : Model S P) (H : PreHistory P S.EventType)
    (φ : Formula S) {ts : List S.Value} {acc₁ acc₂ : Set P}
    (hSubset : acc₁ ⊆ acc₂) :
    Sat.check M H φ ts acc₁ → Sat.check M H φ ts acc₂ := by
  classical
  induction ts generalizing acc₁ acc₂ with
  | nil =>
      intro hCheck
      simp only [Logic.Sat.Sat_check_nil] at hCheck ⊢
      rcases hCheck with ⟨p, hp, hSat⟩
      exact ⟨p, hSubset hp, hSat⟩
  | cons v vs ih =>
      intro hCheck
      simp only [Logic.Sat.Sat_check_cons] at hCheck ⊢
      intro O hO
      have h := hCheck O hO
      have hSubset' : acc₁ ∩ O ⊆ acc₂ ∩ O := by
        intro p hp
        exact ⟨hSubset hp.1, hp.2⟩
      exact ih hSubset' h

variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.EventType S)]

/-- Minimal quorum list for a learner value, matching the encoding's `getMinQs`. -/
def diamondGetMinQs (b : Bounds S) (ℓ : S.Value) : List (Finset b.participants) :=
  let vIdx := b.findValueIndex ℓ
  (Var.allMinQ b vIdx).filterMap fun v =>
    match v with
    | Var.MinQ _ Q => some Q
    | _ => none

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- A witness quorum (mask `0`) always appears in `diamondGetMinQs`. -/
lemma diamondGetMinQs_nonempty (b : Bounds S) (ℓ : S.Value) :
    diamondGetMinQs (b := b) ℓ ≠ [] := by
  classical
  -- mask `0` is always within the range
  have hMaskPos : 0 < Nat.shiftLeft 1 b.nParticipants := by
    change 0 < 1 <<< b.nParticipants
    exact Nat.one_shiftLeft b.nParticipants ▸ Nat.two_pow_pos b.nParticipants
  let mask : Fin (Nat.shiftLeft 1 b.nParticipants) := ⟨0, hMaskPos⟩
  have hMask_mem : mask ∈ List.finRange (Nat.shiftLeft 1 b.nParticipants) := by
    simp [List.mem_finRange]
  have hMem_all :
      Var.MinQ (b.findValueIndex ℓ) (Encoding.bitmaskToFinset b.nParticipants mask) ∈
        Var.allMinQ b (b.findValueIndex ℓ) := by
    unfold Var.allMinQ
    exact List.mem_map.mpr ⟨mask, hMask_mem, rfl⟩
  have hMem_get :
      Encoding.bitmaskToFinset b.nParticipants mask ∈ diamondGetMinQs (b := b) ℓ := by
    unfold diamondGetMinQs
    simp only [List.mem_filterMap]
    exact ⟨Var.MinQ (b.findValueIndex ℓ) (bitmaskToFinset b.nParticipants mask),
           hMem_all, rfl⟩
  exact List.ne_nil_of_mem hMem_get

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- Any quorum `Q` appears in `diamondGetMinQs` (by bitmask enumerability). -/
lemma minQ_in_diamondGetMinQs (b : Bounds S) (ℓ : S.Value) (Q : Finset b.participants) :
    Q ∈ diamondGetMinQs (b := b) ℓ := by
  classical
  -- Represent Q as a bitmask and note the corresponding MinQ literal is in allMinQ
  let mask := finsetToBitmask Q
  have hMaskLt : mask < Nat.shiftLeft 1 b.nParticipants := finsetToBitmask_lt Q
  let maskFin : Fin (Nat.shiftLeft 1 b.nParticipants) := ⟨mask, hMaskLt⟩
  have hMem_all :
      Var.MinQ (b.findValueIndex ℓ) (bitmaskToFinset b.nParticipants mask) ∈
        Var.allMinQ b (b.findValueIndex ℓ) := by
    unfold Var.allMinQ
    refine List.mem_map.mpr ?_
    refine ⟨maskFin, ?_, rfl⟩
    exact List.mem_finRange _
  -- Filter-map extracts Q
  unfold diamondGetMinQs
  refine List.mem_filterMap.mpr ?_
  have hInverse : bitmaskToFinset b.nParticipants mask = Q := finsetToBitmask_inverse Q
  refine ⟨Var.MinQ (b.findValueIndex ℓ) (bitmaskToFinset b.nParticipants mask),
          hMem_all, ?_⟩
  simp only [hInverse]

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- Build a cartesian-product membership from pointwise membership in each component list. -/
lemma tuple_mem_cartesianProduct_of_mem
    (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (hLen : tuple.length = learners.length)
    (hMem : ∀ pair ∈ learners.zip tuple,
      pair.2 ∈ diamondGetMinQs (b := b) pair.1) :
    tuple ∈ cartesianProduct (learners.map (diamondGetMinQs (b := b))) := by
  classical
  revert tuple hLen hMem
  induction learners with
  | nil =>
      intro tuple hLen hMem
      cases tuple with
      | nil =>
          simp [cartesianProduct]
      | cons _ _ =>
          cases hLen
  | cons ℓ ls ih =>
      intro tuple hLen hMem
      cases tuple with
      | nil =>
          cases hLen
      | cons Q qs =>
          -- align lengths
          have hLen_tail : qs.length = ls.length := by
            simpa using Nat.succ.inj hLen
          -- head membership: (ℓ,Q) is in zip
          have hHead : Q ∈ diamondGetMinQs (b := b) ℓ := by
            have hPair_mem : (ℓ, Q) ∈ (ℓ :: ls).zip (Q :: qs) := by simp
            exact hMem (ℓ, Q) hPair_mem
          -- tail membership hypothesis
          have hTail : ∀ pair ∈ ls.zip qs,
              pair.2 ∈ diamondGetMinQs (b := b) pair.1 := by
            intro pair hPair
            have hPair_mem : pair ∈ (ℓ :: ls).zip (Q :: qs) := by
              simp [hPair]
            exact hMem pair hPair_mem
          -- apply IH to tail
          have hQs_mem :
              qs ∈ cartesianProduct (ls.map (diamondGetMinQs (b := b))) :=
            ih qs hLen_tail hTail
          -- assemble membership for the full tuple
          simp [cartesianProduct, hHead, hQs_mem]

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- The tuple list used by the diamond encoding is nonempty. -/
lemma diamondTuples_nonempty (b : Bounds S) (learners : List S.Value) :
    cartesianProduct (learners.map (diamondGetMinQs (b := b))) ≠ [] := by
  classical
  have hAll_nonempty :
      ∀ xs ∈ learners.map (diamondGetMinQs (b := b)), xs ≠ [] := by
    intro xs hxs
    rcases List.mem_map.mp hxs with ⟨ℓ, hℓ, rfl⟩
    exact diamondGetMinQs_nonempty (b := b) ℓ
  exact cartesianProduct_ne_nil hAll_nonempty

/-- Package a raw tuple into a `QuorumTuple` indexed by the learner list. -/
def tupleToQuorumTuple (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (hLen : tuple.length = learners.length) : QuorumTuple b :=
{ learnerIndices := learners.map b.findValueIndex
  quorums := tuple
  hLength := by simp [hLen] }

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
@[simp] lemma tupleToQuorumTuple_quorums (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants)) (hLen) :
    (tupleToQuorumTuple (b := b) learners tuple hLen).quorums = tuple := rfl

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
@[simp] lemma tupleToQuorumTuple_learnerIndices (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants)) (hLen) :
    (tupleToQuorumTuple (b := b) learners tuple hLen).learnerIndices =
      learners.map b.findValueIndex := rfl

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
@[simp] lemma tupleToQuorumTuple_intersection (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants)) (hLen) :
    (tupleToQuorumTuple (b := b) learners tuple hLen).intersection b =
      tuple.foldl (· ∩ ·) Finset.univ := rfl

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
lemma tuple_mem_cartesianProduct_length (b : Bounds S) (learners : List S.Value)
    {tuple : List (Finset b.participants)}
    (hMem : tuple ∈ cartesianProduct (learners.map (diamondGetMinQs (b := b)))) :
    tuple.length = learners.length := by
  have h := cartesianProduct_mem_length hMem
  simp only [List.length_map] at h
  exact h

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- In `encodeTupleControl`, every guard clause `[MinQ(ℓ,Q), uTuple]` is present
    for each `(ℓ,Q)` in the zipped learner/quorum list. -/
lemma encodeTupleControl_guard_clause (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants)) (witnessVars : List (Var b)) (st : EncState b)
    (pair : S.Value × Finset b.participants)
    (hPair : pair ∈ learners.zip tuple) :
    let res := encodeTupleControl b learners tuple witnessVars st
    [SAT.Lit.pos (Var.MinQ (b.findValueIndex pair.1) pair.2),
     SAT.Lit.pos (FVar.toVar b res.1)] ∈ res.2.clauses := by
  classical
  -- Unfold encodeTupleControl by cases on allocFresh
  simp only [encodeTupleControl]
  cases hAlloc : EncState.allocFresh b st with
  | mk u stAlloc =>
      -- Name intermediate states
      set guards := (learners.zip tuple).map fun (ℓ, Q) =>
        SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)
      set st1 :=
        EncState.addClause b stAlloc
          ([SAT.Lit.neg (FVar.toVar b u)] ++ guards ++ witnessVars.map SAT.Lit.pos)
      set st2 :=
        (learners.zip tuple).foldl (fun stAcc (ℓ, Q) =>
          EncState.addClause b stAcc
            [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
             SAT.Lit.pos (FVar.toVar b u)]) st1
      set st3 :=
        witnessVars.foldl (fun stAcc v =>
          EncState.addClause b stAcc
            [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]) st2
      -- The guard clause is added during the foldl over learners.zip tuple
      have hExists :=
        foldl_exists_state_subset
          (f := fun stAcc (pq : S.Value × Finset b.participants) =>
            EncState.addClause b stAcc
              [SAT.Lit.pos (Var.MinQ (b.findValueIndex pq.1) pq.2),
               SAT.Lit.pos (FVar.toVar b u)])
          (hStep := by
            intro stAcc pq
            exact EncState.addClause_subset_clauses (b := b) stAcc _)
          (xs := learners.zip tuple)
          (x := pair) (init := st1) hPair
      rcases hExists with ⟨st_k, hSub⟩
      have hIn :
          [SAT.Lit.pos (Var.MinQ (b.findValueIndex pair.1) pair.2),
           SAT.Lit.pos (FVar.toVar b u)] ∈
            (EncState.addClause b st_k
              [SAT.Lit.pos (Var.MinQ (b.findValueIndex pair.1) pair.2),
               SAT.Lit.pos (FVar.toVar b u)]).clauses := by
        simp [EncState.addClause]
      -- Show the fold result st2 contains the clause
      have hIn_st2 :
          [SAT.Lit.pos (Var.MinQ (b.findValueIndex pair.1) pair.2),
           SAT.Lit.pos (FVar.toVar b u)] ∈ st2.clauses := hSub hIn
      -- Show st3 contains st2's clauses
      have hSub_st3 : st2.clauses ⊆ st3.clauses :=
        foldl_subset_state
          (f := fun stAcc v =>
            EncState.addClause b stAcc
              [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)])
          (hStep := by
            intro stAcc v
            exact EncState.addClause_subset_clauses (b := b) stAcc _)
          (xs := witnessVars)
          (init := st2)
      exact hSub_st3 hIn_st2

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- In `encodeTupleControl`, the witness→tuple clause `[¬w, uTuple]` is present
    for every witness variable `w`. -/
lemma encodeTupleControl_witness_clause (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants)) (witnessVars : List (Var b)) (st : EncState b)
    (v : Var b) (hMem : v ∈ witnessVars) :
    let res := encodeTupleControl b learners tuple witnessVars st
    [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b res.1)] ∈ res.2.clauses := by
  classical
  -- Unfold encodeTupleControl by cases on allocFresh
  simp only [encodeTupleControl]
  cases hAlloc : EncState.allocFresh b st with
  | mk u stAlloc =>
      -- Name intermediate states
      set guards := (learners.zip tuple).map fun (ℓ, Q) =>
        SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)
      set st1 :=
        EncState.addClause b stAlloc
          ([SAT.Lit.neg (FVar.toVar b u)] ++ guards ++ witnessVars.map SAT.Lit.pos)
      set st2 :=
        (learners.zip tuple).foldl (fun stAcc (ℓ, Q) =>
          EncState.addClause b stAcc
            [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
             SAT.Lit.pos (FVar.toVar b u)]) st1
      set st3 :=
        witnessVars.foldl (fun stAcc v' =>
          EncState.addClause b stAcc
            [SAT.Lit.neg v', SAT.Lit.pos (FVar.toVar b u)]) st2
      -- Use foldl_exists_state_subset over the witness fold
      have hExists :=
        foldl_exists_state_subset
          (f := fun stAcc v' =>
            EncState.addClause b stAcc
              [SAT.Lit.neg v', SAT.Lit.pos (FVar.toVar b u)])
          (hStep := by
            intro stAcc v'
            exact EncState.addClause_subset_clauses (b := b) stAcc _)
          (xs := witnessVars) (x := v) (init := st2) hMem
      rcases hExists with ⟨st_k, hSub⟩
      have hIn :
          [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)] ∈
            (EncState.addClause b st_k
              [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]).clauses := by
        simp [EncState.addClause]
      -- Show the fold result st3 contains the clause
      have hIn_st3 :
          [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)] ∈ st3.clauses := hSub hIn
      exact hIn_st3

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- The guards list in `encodeTupleControl` matches `QuorumTuple.guards` for
    a tuple drawn from the diamond encoding. -/
lemma guards_eq_tuple_guards (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (hLen : tuple.length = learners.length) :
    (learners.zip tuple).map (fun (ℓ, Q) =>
      SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)) =
      (tupleToQuorumTuple (b := b) learners tuple hLen).guards b := by
  simp only [QuorumTuple.guards, tupleToQuorumTuple_learnerIndices]
  exact map_zip_left_map b.findValueIndex (fun vIdx Q => SAT.Lit.neg (Var.MinQ vIdx Q))
    learners tuple

omit [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
/-- The forward clause `[¬uTuple] ++ guards ++ witnesses` is present in the
    state returned by `encodeTupleControl`. -/
lemma encodeTupleControl_forward_clause (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants)) (witnessVars : List (Var b)) (st : EncState b) :
    let guards := (learners.zip tuple).map fun (ℓ, Q) =>
      SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)
    [SAT.Lit.neg (FVar.toVar b (encodeTupleControl b learners tuple witnessVars st).1)] ++
        guards ++ witnessVars.map SAT.Lit.pos ∈
      (encodeTupleControl b learners tuple witnessVars st).2.clauses := by
  classical
  intro guards
  -- unfold and chase the first addClause
  dsimp [encodeTupleControl]
  -- name intermediate states
  rcases EncState.allocFresh b st with ⟨u, stAlloc⟩
  set st1 :=
    EncState.addClause b stAlloc
      ([SAT.Lit.neg (FVar.toVar b u)] ++ guards ++ witnessVars.map SAT.Lit.pos)
  set st2 :=
    (learners.zip tuple).foldl (fun stAcc (ℓ, Q) =>
      EncState.addClause b stAcc
        [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
         SAT.Lit.pos (FVar.toVar b u)]) st1
  set st3 :=
    witnessVars.foldl (fun stAcc v =>
      EncState.addClause b stAcc
        [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]) st2
  have hIn_st1 :
      [SAT.Lit.neg (FVar.toVar b u)] ++ guards ++
          witnessVars.map SAT.Lit.pos ∈ st1.clauses := by
    simp [st1, EncState.addClause]
  have hSub_st2 :
      st1.clauses ⊆ st2.clauses := by
    refine foldl_subset_state
      (f := fun stAcc (ℓ, Q) =>
        EncState.addClause b stAcc
          [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
           SAT.Lit.pos (FVar.toVar b u)])
      (hStep := by
        intro stAcc pair
        exact EncState.addClause_subset_clauses (b := b) stAcc _)
      (xs := learners.zip tuple)
      (init := st1)
  have hSub_st3 :
      st2.clauses ⊆ st3.clauses := by
    refine foldl_subset_state
      (f := fun stAcc v =>
        EncState.addClause b stAcc
          [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)])
      (hStep := by
        intro stAcc v
        exact EncState.addClause_subset_clauses (b := b) stAcc _)
      (xs := witnessVars)
      (init := st2)
  have hIn_st3 : [SAT.Lit.neg (FVar.toVar b u)] ++ guards ++
      witnessVars.map SAT.Lit.pos ∈ st3.clauses :=
    hSub_st3 (hSub_st2 hIn_st1)
  -- st3 is the final state of encodeTupleControl
  simpa [st1, st2, st3, EncState.addClause]
    using hIn_st3

/-- The witness fold helper used in the diamond encoding. -/
def diamondWitnessFold (b : Bounds S) (φ : Logic.Formula S) (w : WId b)
    (intersection : Finset b.participants) (st : EncState b) :
    List (FVar b × b.participants) × EncState b :=
  (Bounds.partsL b).foldl
    (fun (acc : List (FVar b × b.participants) × EncState b) p =>
      if _ : p ∈ intersection then
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let (uWit, stNew) := encodeFormula b φ wEnd acc.2
        (acc.1 ++ [(uWit, p)], stNew)
      else
        acc)
    ([], st)

/-- Each witness pair inserted by the diamond step carries a participant that
    lies in the tuple intersection. -/
lemma witnessFold_mem_intersection (b : Bounds S)
    (φ : Logic.Formula S) (w : WId b) (intersection : Finset b.participants)
    (st : EncState b) :
    ∀ pair ∈ (diamondWitnessFold b φ w intersection st).1, pair.2 ∈ intersection := by
  classical
  -- Use a generalized lemma about folds preserving membership
  suffices h : ∀ (init : List (FVar b × b.participants) × EncState b),
      (∀ p ∈ init.1, p.2 ∈ intersection) →
      ∀ pair ∈ ((Bounds.partsL b).foldl
        (fun (acc : List (FVar b × b.participants) × EncState b) p =>
          if _ : p ∈ intersection then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd acc.2
            (acc.1 ++ [(uWit, p)], stNew)
          else
            acc)
        init).1, pair.2 ∈ intersection by
    exact h ([], st) (by simp)
  intro init hInit
  induction Bounds.partsL b generalizing init with
  | nil =>
      intro pair hPair
      simp only [List.foldl_nil] at hPair
      exact hInit pair hPair
  | cons p ps ih =>
      intro pair hPair
      simp only [List.foldl_cons] at hPair
      by_cases hp : p ∈ intersection
      · -- Contribution from the current participant
        simp only [hp, ↓reduceDIte] at hPair
        -- The new init after this step includes the appended witness
        let uWit := (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ init.2).1
        have hNewInit : ∀ q ∈ init.1 ++ [((uWit, p) : FVar b × b.participants)],
            q.2 ∈ intersection := by
          intro q hq
          simp only [List.mem_append, List.mem_singleton] at hq
          rcases hq with hq | hq
          · exact hInit q hq
          · subst hq
            exact hp
        exact ih _ hNewInit pair hPair
      · -- Current participant ignored; fall back to IH
        simp only [hp, ↓reduceDIte] at hPair
        exact ih init hInit pair hPair

/-- Helper: elements in the accumulator are preserved through the witness fold. -/
lemma witnessFold_preserves_mem (b : Bounds S)
    (φ : Logic.Formula S) (w : WId b) (intersection : Finset b.participants)
    (xs : List b.participants) (acc : List (FVar b × b.participants) × EncState b)
    (pair : FVar b × b.participants) (hMem : pair ∈ acc.1) :
    pair ∈ (xs.foldl
      (fun (acc' : List (FVar b × b.participants) × EncState b) p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc'.2
          (acc'.1 ++ [(uWit, p)], stNew)
        else
          acc')
      acc).1 := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hMem
  | cons p ps ih =>
      simp only [List.foldl_cons]
      by_cases hp : p ∈ intersection
      · simp only [hp, ↓reduceDIte]
        apply ih
        simp only [List.mem_append]
        exact Or.inl hMem
      · simp only [hp, ↓reduceDIte]
        exact ih acc hMem

/-- If a participant lies in the intersection for a tuple, the witness fold
    introduces a pair with that participant. -/
lemma witnessFold_has_participant (b : Bounds S)
    (φ : Logic.Formula S) (w : WId b) (intersection : Finset b.participants)
    (st : EncState b) :
    ∀ p ∈ intersection, ∃ uWit, (uWit, p) ∈ (diamondWitnessFold b φ w intersection st).1 := by
  classical
  -- Unfold the let bindings
  simp only [diamondWitnessFold]
  -- Generalize: if p ∈ xs and p ∈ intersection, then (uWit, p) appears in the fold over xs
  suffices h : ∀ (xs : List b.participants) (init : List (FVar b × b.participants) × EncState b)
      (p : b.participants),
      p ∈ xs → p ∈ intersection →
      ∃ uWit, (uWit, p) ∈ (xs.foldl
        (fun (acc : List (FVar b × b.participants) × EncState b) p' =>
          if _ : p' ∈ intersection then
            let wEnd : WId b := ⟨p', ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd acc.2
            (acc.1 ++ [(uWit, p')], stNew)
          else
            acc)
        init).1 by
    intro p hp
    -- Since p : b.participants = Fin b.nParticipants, p ∈ partsL b = List.finRange b.nParticipants
    have hp_in_partsL : p ∈ Bounds.partsL b := by
      unfold Bounds.partsL
      exact List.mem_finRange p
    exact h (Bounds.partsL b) ([], st) p hp_in_partsL hp
  intro xs init p hp_xs hp_inter
  induction xs generalizing init with
  | nil => simp at hp_xs
  | cons p' ps ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hp_xs with hp_eq | hp_tail
      · -- p = p' (the current participant)
        subst hp_eq
        simp only [hp_inter, ↓reduceDIte]
        -- The witness is created for p in this step
        let uWit := (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ init.2).1
        refine ⟨uWit, ?_⟩
        -- The witness is appended and survives through the rest of the fold
        apply witnessFold_preserves_mem
        simp only [List.mem_append, List.mem_singleton]
        right
        rfl
      · -- p is in the tail
        by_cases hp' : p' ∈ intersection
        · simp only [hp', ↓reduceDIte]
          exact ih _ hp_tail
        · simp only [hp', ↓reduceDIte]
          exact ih init hp_tail

/-- If a pair (uWit, p) appears in witnessFold.1, then uWit is the encoding control variable
    for p at some intermediate state, and the encoding's clauses are a subset of the final
    witnessFold state's clauses. This allows applying the IH with the correct intermediate state. -/
lemma witnessFold_fst_is_encode (b : Bounds S)
    (φ : Logic.Formula S) (w : WId b) (intersection : Finset b.participants)
    (st : EncState b) (pair : FVar b × b.participants)
    (hMem : pair ∈ (diamondWitnessFold b φ w intersection st).1) :
    ∃ st_int : EncState b,
      pair.1 = (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).1 ∧
      (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).2.clauses ⊆
        (diamondWitnessFold b φ w intersection st).2.clauses := by
  classical
  simp only [diamondWitnessFold] at hMem ⊢
  -- Generalize over the fold
  suffices h : ∀ (xs : List b.participants) (init : List (FVar b × b.participants) × EncState b),
      pair ∈ (xs.foldl
        (fun (acc : List (FVar b × b.participants) × EncState b) p' =>
          if _ : p' ∈ intersection then
            let wEnd : WId b := ⟨p', ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd acc.2
            (acc.1 ++ [(uWit, p')], stNew)
          else
            acc)
        init).1 →
      (pair ∈ init.1 →
        ∃ st_int,
          pair.1 = (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).1 ∧
          (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).2.clauses ⊆
            init.2.clauses) →
      ∃ st_int,
        pair.1 = (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).1 ∧
        (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).2.clauses ⊆
          (xs.foldl
            (fun (acc : List (FVar b × b.participants) × EncState b) p' =>
              if _ : p' ∈ intersection then
                let wEnd : WId b := ⟨p', ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd acc.2
                (acc.1 ++ [(uWit, p')], stNew)
              else
                acc)
            init).2.clauses by
    let emptyInit : List (FVar b × b.participants) × EncState b := ([], st)
    have hInit : pair ∈ emptyInit.1 → ∃ st_int,
        pair.1 = (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).1 ∧
        (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).2.clauses ⊆
          emptyInit.2.clauses := by
      intro hAbs
      simp [emptyInit] at hAbs
    exact h (Bounds.partsL b) emptyInit hMem hInit
  intro xs
  induction xs with
  | nil =>
      intro init hMem hInit
      exact hInit hMem
  | cons p' ps ih =>
      intro init hMemFold hInit
      simp only [List.foldl_cons] at hMemFold
      by_cases hp' : p' ∈ intersection
      · simp only [hp', ↓reduceDIte] at hMemFold
        let wEnd : WId b := ⟨p', ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let res := encodeFormula b φ wEnd init.2
        let newInit := (init.1 ++ [(res.1, p')], res.2)
        have hNewInit : pair ∈ newInit.1 →
            ∃ st_int,
              pair.1 = (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).1 ∧
              (encodeFormula b φ ⟨pair.2, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).2.clauses ⊆
                newInit.2.clauses := by
          intro hMemNew
          simp only [List.mem_append, List.mem_singleton, newInit] at hMemNew
          rcases hMemNew with hOld | hNew
          · -- pair was in init.1
            obtain ⟨st_int, hEq, hSub⟩ := hInit hOld
            refine ⟨st_int, hEq, ?_⟩
            exact List.Subset.trans hSub (encodeFormula_clauses_subset b φ wEnd init.2)
          · -- pair is the newly added one: pair = (res.1, p')
            simp only [Prod.eq_iff_fst_eq_snd_eq] at hNew
            obtain ⟨hFst, hSnd⟩ := hNew
            refine ⟨init.2, ?_, ?_⟩
            · simp only [hFst, hSnd, res, wEnd]
            · simp only [hSnd, res, wEnd, newInit]
              exact List.Subset.refl _
        -- ih gives result for ps.foldl, convert to (p' :: ps).foldl
        have hFoldEq : (List.foldl
            (fun (acc : List (FVar b × b.participants) × EncState b) p'' =>
              if _ : p'' ∈ intersection then
                let wEnd' : WId b := ⟨p'', ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd' acc.2
                (acc.1 ++ [(uWit, p'')], stNew)
              else acc)
            newInit ps).2.clauses =
          ((p' :: ps).foldl
            (fun (acc : List (FVar b × b.participants) × EncState b) p'' =>
              if _ : p'' ∈ intersection then
                let wEnd' : WId b := ⟨p'', ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd' acc.2
                (acc.1 ++ [(uWit, p'')], stNew)
              else acc)
            init).2.clauses := by
          simp only [List.foldl_cons, hp', ↓reduceDIte, newInit, res, wEnd]
        obtain ⟨st_int, hEq, hSub⟩ := ih newInit hMemFold hNewInit
        exact ⟨st_int, hEq, hFoldEq ▸ hSub⟩
      · simp only [hp', ↓reduceDIte] at hMemFold
        have hFoldEq : (List.foldl
            (fun (acc : List (FVar b × b.participants) × EncState b) p'' =>
              if _ : p'' ∈ intersection then
                let wEnd' : WId b := ⟨p'', ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd' acc.2
                (acc.1 ++ [(uWit, p'')], stNew)
              else acc)
            init ps).2.clauses =
          ((p' :: ps).foldl
            (fun (acc : List (FVar b × b.participants) × EncState b) p'' =>
              if _ : p'' ∈ intersection then
                let wEnd' : WId b := ⟨p'', ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd' acc.2
                (acc.1 ++ [(uWit, p'')], stNew)
              else acc)
            init).2.clauses := by
          simp only [List.foldl_cons, hp', ↓reduceDIte]
        obtain ⟨st_int, hEq, hSub⟩ := ih init hMemFold hInit
        exact ⟨st_int, hEq, hFoldEq ▸ hSub⟩

/-- The step function for the diamond encoding fold. -/
def diamondStep (b : Bounds S) (learners : List S.Value) (φ : Logic.Formula S)
    (w : WId b)
    (acc : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) :
    List (FVar b) × EncState b :=
  let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
  let witnessFold := diamondWitnessFold b φ w intersection acc.2
  let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
  let (uTuple, stFinal) :=
    encodeTupleControl b learners tuple witnessVars witnessFold.2
  (acc.1 ++ [uTuple], stFinal)

/-- Monotonicity of the first component for the diamond step: the list of
    control variables only grows. -/
lemma diamond_step_fst_subset (b : Bounds S) (learners : List S.Value) (φ : Logic.Formula S)
    (w : WId b) :
    ∀ (st : List (FVar b) × EncState b) (tuple : List (Finset b.participants)),
      st.1 ⊆ (diamondStep b learners φ w st tuple).1 := by
  intro st tuple x hx
  -- after simplification goal becomes x ∈ st.1 → x ∈ st.1 ++ [uTuple]
  simp only [diamondStep, List.mem_append]
  left
  exact hx

/-- Monotonicity of the clause component for the diamond step. -/
lemma diamond_step_snd_subset (b : Bounds S) (learners : List S.Value) (φ : Logic.Formula S)
    (w : WId b) :
    ∀ (st : List (FVar b) × EncState b) (tuple : List (Finset b.participants)),
      st.2.clauses ⊆ (diamondStep b learners φ w st tuple).2.clauses := by
  classical
  intro st tuple clause hClause
  -- Unfold the step and chase subset relations
  dsimp [diamondStep]
  set intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
  set witnessFold := diamondWitnessFold b φ w intersection st.2

  -- Accumulate clauses through the witness fold
  have hWitness :
      st.2.clauses ⊆ witnessFold.2.clauses :=
    foldl_subset_snd
      (f := fun (acc : List (FVar b × b.participants) × EncState b) p =>
        if hp : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc.2
          (acc.1 ++ [(uWit, p)], stNew)
        else acc)
      (hStep := by
        intro acc p
        by_cases hp : p ∈ intersection
        · simp only [hp, ↓reduceDIte]
          -- encodeFormula preserves existing clauses
          intro clause hClause'
          have hSub :=
            (encodeFormula_clauses_subset (b := b) (φ := φ)
              (w := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩) (st := acc.2))
          -- simplify the target state (the second component of the encode result)
          have hSub' := hSub hClause'
          simpa using hSub'
        · simp [hp])
      (xs := Bounds.partsL b)
      (init := ([], st.2))

  -- encodeTupleControl preserves clauses
  have hTuple :
      witnessFold.2.clauses ⊆
        (encodeTupleControl b learners tuple
          (witnessFold.1.map (fun u => FVar.toVar b u.1)) witnessFold.2).2.clauses :=
    encodeTupleControl_clauses_subset b learners tuple
      (witnessFold.1.map (fun u => FVar.toVar b u.1)) witnessFold.2

  -- Finish by transitivity
  exact hTuple (hWitness hClause)

/-! ## Folding structure lemmas -/

lemma diamond_step_foldl_fst_append (b : Bounds S) (learners : List S.Value)
    (φ : Logic.Formula S) (w : WId b) :
    ∀ (xs : List (List (Finset b.participants))) (acc : List (FVar b) × EncState b),
      ∃ suffix,
        (xs.foldl (diamondStep b learners φ w) acc).1 = acc.1 ++ suffix := by
  classical
  intro xs acc
  induction xs generalizing acc with
  | nil =>
      exact ⟨[], by simp⟩
  | cons t ts ih =>
      rcases ih (diamondStep b learners φ w acc t) with ⟨suffix, hSuffix⟩
      let new :=
        (encodeTupleControl b learners t
          ((diamondWitnessFold b φ w (t.foldl (· ∩ ·) Finset.univ) acc.2).1.map
            (fun u => FVar.toVar b u.1))
          (diamondWitnessFold b φ w (t.foldl (· ∩ ·) Finset.univ) acc.2).2).1
      refine ⟨new :: suffix, ?_⟩
      calc
        ((t :: ts).foldl (diamondStep b learners φ w) acc).1
            = (ts.foldl (diamondStep b learners φ w)
                (diamondStep b learners φ w acc t)).1 := by simp
        _ = (diamondStep b learners φ w acc t).1 ++ suffix := hSuffix
        _ = acc.1 ++
            new :: suffix := by
              simp [diamondStep, new, List.append_assoc]

/-- The inline step in encodeFormula for diamond is definitionally equal to diamondStep. -/
lemma encodeFormula_diamond_step_eq (b : Bounds S) (learners : List S.Value) (φ : Logic.Formula S)
    (w : WId b) :
    (fun (acc : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      let accVars := acc.1
      let stCur := acc.2
      let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
      let witnessFold :=
        (Bounds.partsL b).foldl
          (fun (inner : List (FVar b × b.participants) × EncState b) p =>
            if _ : p ∈ intersection then
              let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
              let (uWit, stNew) := encodeFormula b φ wEnd inner.2
              (inner.1 ++ [(uWit, p)], stNew)
            else
              inner)
          ([], stCur)
      let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
      let (uTuple, stFinal) := encodeTupleControl b learners tuple witnessVars witnessFold.2
      (accVars ++ [uTuple], stFinal)) = diamondStep b learners φ w := by
  funext acc tuple
  simp only [diamondStep, diamondWitnessFold]

/-- The unfolded step in encodeFormula (after beta-reduction) equals diamondStep.
    This matches the exact form that `simp only [encodeFormula]` produces. -/
lemma encodeFormula_diamond_step_unfolded_eq (b : Bounds S) (learners : List S.Value)
    (φ : Logic.Formula S) (w : WId b) :
    (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      (x.1 ++
        [(encodeTupleControl b learners tuple
            (List.map (fun u => FVar.toVar b u.1)
              (List.foldl
                (fun acc p =>
                  if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                      (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                  else acc)
                ([], x.2) (Bounds.partsL b)).1)
            (List.foldl
              (fun acc p =>
                if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                    (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                else acc)
              ([], x.2) (Bounds.partsL b)).2).1],
      (encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                    (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                else acc)
              ([], x.2) (Bounds.partsL b)).1)
          (List.foldl
            (fun acc p =>
              if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                  (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
              else acc)
            ([], x.2) (Bounds.partsL b)).2).2)) = diamondStep b learners φ w := by
  funext x tuple
  simp only [diamondStep, diamondWitnessFold, encodeTupleControl]

/-- encodeFormula for diamond equals a match on the tuple fold result.
    This lemma "lifts" the match to top level so we can substitute the fold value. -/
lemma encodeFormula_diamond_match (b : Bounds S) (learners : List S.Value) (φ : Logic.Formula S)
    (w : WId b) (st : EncState b) :
    let tuples := cartesianProduct (learners.map (diamondGetMinQs (b := b)))
    let (tupleVars, stTuples) := tuples.foldl (diamondStep b learners φ w) ([], st)
    encodeFormula b (.diamond learners φ) w st =
      match tupleVars with
      | [] =>
        let (u', st') := EncState.allocFresh b stTuples
        let st'' := EncState.addClause b st' [SAT.Lit.pos (FVar.toVar b u')]
        (u', st'')
      | u0 :: us =>
        let res := us.foldl (fun (acc : FVar b × EncState b) u' =>
          let (uAcc, stAcc) := acc; mkAndIff b uAcc u' stAcc) (u0, stTuples)
        (res.1, res.2) := by
  -- Unfold encodeFormula to show definitional equality
  simp only [encodeFormula]
  rfl

lemma encodeFormula_diamond_structure (b : Bounds S) (learners : List S.Value) (φ : Logic.Formula S)
    (w : WId b) (st : EncState b) :
    let quorumSets := learners.map (diamondGetMinQs (b := b))
    let tuples := cartesianProduct quorumSets
    let (tupleVars, stTuples) := tuples.foldl (diamondStep b learners φ w) ([], st)
    match tupleVars with
    | [] => True
    | u0 :: us =>
      let res := us.foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (u0, stTuples)
      encodeFormula b (.diamond learners φ) w st = (res.1, res.2) := by
  classical
  intro quorumSets tuples

  -- Show the inline getMinQs equals diamondGetMinQs (after let-inlining)
  have hGetMinQs : (fun ℓ =>
      List.filterMap (fun v =>
        match v with
        | Var.MinQ _ Q => some Q
        | _ => none) (Var.allMinQ b (b.findValueIndex ℓ))) = diamondGetMinQs (b := b) := by
    funext ℓ; rfl

  -- The inline step equals diamondStep
  have hStep := encodeFormula_diamond_step_eq b learners φ w

  -- Work with the fold result
  generalize hFoldDef : tuples.foldl (diamondStep b learners φ w) ([], st) = foldRes
  obtain ⟨tupleVars, stTuples⟩ := foldRes

  cases hVars : tupleVars with
  | nil => trivial
  | cons u0 us =>
      -- The unfolded step equals diamondStep (matches beta-reduced form after simp)
      have hStepUnfolded := encodeFormula_diamond_step_unfolded_eq b learners φ w

      -- The unfolded fold equals the abstracted fold
      have hFoldEq : tuples.foldl (fun (x : List (FVar b) × EncState b)
            (tuple : List (Finset b.participants)) =>
          (x.1 ++
            [(encodeTupleControl b learners tuple
                (List.map (fun u => FVar.toVar b u.1)
                  (List.foldl
                    (fun acc p =>
                      if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                        (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                          (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                      else acc)
                    ([], x.2) (Bounds.partsL b)).1)
                (List.foldl
                  (fun acc p =>
                    if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                      (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                        (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                    else acc)
                  ([], x.2) (Bounds.partsL b)).2).1],
          (encodeTupleControl b learners tuple
              (List.map (fun u => FVar.toVar b u.1)
                (List.foldl
                  (fun acc p =>
                    if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                      (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                        (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                    else acc)
                  ([], x.2) (Bounds.partsL b)).1)
              (List.foldl
                (fun acc p =>
                  if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                      (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                  else acc)
                ([], x.2) (Bounds.partsL b)).2).2)) ([], st) =
          tuples.foldl (diamondStep b learners φ w) ([], st) := by
        rw [hStepUnfolded]

      -- Now show encodeFormula produces the same result
      let res := us.foldl (fun acc u' =>
        let (uAcc, stAcc) := acc; mkAndIff b uAcc u' stAcc) (u0, stTuples)
      change encodeFormula b (.diamond learners φ) w st = (res.1, res.2)

      -- The inline getMinQs produces the same quorumSets as diamondGetMinQs
      have hInlineGetMinQs : (fun ℓ =>
          List.filterMap (fun v =>
            match v with
            | Var.MinQ _ Q => some Q
            | _ => none) (Var.allMinQ b (b.findValueIndex ℓ))) = diamondGetMinQs (b := b) := by
        funext ℓ; rfl

      -- So the inline tuples equals our tuples
      have hInlineTuples : cartesianProduct (learners.map (fun ℓ =>
          List.filterMap (fun v =>
            match v with
            | Var.MinQ _ Q => some Q
            | _ => none) (Var.allMinQ b (b.findValueIndex ℓ)))) = tuples := by
        simp only [tuples, quorumSets]
        rw [hInlineGetMinQs]

      -- Show encodeFormula equals the expected result using definitional equality
      -- The inline step is definitionally equal to diamondStep by hStepUnfolded
      -- The inline tuples is definitionally equal to tuples by hInlineTuples
      -- Therefore, the fold results are equal, and the final result follows

      -- First, rewrite hFoldDef using the fact that the inline fold equals the diamond fold
      have hInlineFoldEq :
        (cartesianProduct (learners.map (fun ℓ =>
          List.filterMap (fun v => match v with | Var.MinQ _ Q => some Q | _ => none)
            (Var.allMinQ b (b.findValueIndex ℓ))))).foldl
          (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
            (x.1 ++ [(encodeTupleControl b learners tuple
                (List.map (fun u => FVar.toVar b u.1)
                  (List.foldl (fun acc p =>
                    if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                      (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                        (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                    else acc) ([], x.2) (Bounds.partsL b)).1)
                (List.foldl (fun acc p =>
                  if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                      (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                  else acc) ([], x.2) (Bounds.partsL b)).2).1],
            (encodeTupleControl b learners tuple
                (List.map (fun u => FVar.toVar b u.1)
                  (List.foldl (fun acc p =>
                    if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                      (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                        (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                    else acc) ([], x.2) (Bounds.partsL b)).1)
                (List.foldl (fun acc p =>
                  if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                      (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                  else acc) ([], x.2) (Bounds.partsL b)).2).2))
          ([], st) = (u0 :: us, stTuples) := by
        rw [hInlineTuples, hStepUnfolded, hFoldDef, hVars]

      -- Use function notation (List.foldl f init xs) not method notation (xs.foldl f init)
      -- to match the form that `simp only [encodeFormula]` produces
      have hInlineFold :
        List.foldl
          (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
            (x.1 ++ [(encodeTupleControl b learners tuple
                (List.map (fun u => FVar.toVar b u.1)
                  (List.foldl (fun acc p =>
                    if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                      (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                        (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                    else acc) ([], x.2) (Bounds.partsL b)).1)
                (List.foldl (fun acc p =>
                  if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                      (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                  else acc) ([], x.2) (Bounds.partsL b)).2).1],
            (encodeTupleControl b learners tuple
                (List.map (fun u => FVar.toVar b u.1)
                  (List.foldl (fun acc p =>
                    if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                      (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                        (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                    else acc) ([], x.2) (Bounds.partsL b)).1)
                (List.foldl (fun acc p =>
                  if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                      (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                  else acc) ([], x.2) (Bounds.partsL b)).2).2))
          ([], st)
          (cartesianProduct (learners.map (fun ℓ =>
            List.filterMap (fun v => match v with | Var.MinQ _ Q => some Q | _ => none)
              (Var.allMinQ b (b.findValueIndex ℓ))))) =
        List.foldl (diamondStep b learners φ w) ([], st) tuples := by
        -- Step 1: Rewrite the list argument (tuples)
        have hTuplesEq : cartesianProduct (learners.map (fun ℓ =>
            List.filterMap (fun v => match v with | Var.MinQ _ Q => some Q | _ => none)
              (Var.allMinQ b (b.findValueIndex ℓ)))) = tuples := hInlineTuples
        simp only [hTuplesEq]
        -- Step 2: Use congrArg to rewrite the step function
        exact congrArg (fun f => List.foldl f ([], st) tuples) hStepUnfolded

      -- Now show encodeFormula produces the expected result
      -- Strategy: Show inline fold = (u0 :: us, stTuples), then use simp_rw to substitute
      have hInlineFoldVal :
        List.foldl
          (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
            (x.1 ++ [(encodeTupleControl b learners tuple
                (List.map (fun u => FVar.toVar b u.1)
                  (List.foldl (fun acc p =>
                    if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                      (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                        (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                    else acc) ([], x.2) (Bounds.partsL b)).1)
                (List.foldl (fun acc p =>
                  if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                      (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                  else acc) ([], x.2) (Bounds.partsL b)).2).1],
            (encodeTupleControl b learners tuple
                (List.map (fun u => FVar.toVar b u.1)
                  (List.foldl (fun acc p =>
                    if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                      (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                        (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                    else acc) ([], x.2) (Bounds.partsL b)).1)
                (List.foldl (fun acc p =>
                  if h : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
                      (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
                  else acc) ([], x.2) (Bounds.partsL b)).2).2))
          ([], st)
          (cartesianProduct (learners.map (fun ℓ =>
            List.filterMap (fun v => match v with | Var.MinQ _ Q => some Q | _ => none)
              (Var.allMinQ b (b.findValueIndex ℓ))))) =
        (u0 :: us, stTuples) := by
        calc _ = List.foldl (diamondStep b learners φ w) ([], st) tuples := hInlineFold
           _ = tuples.foldl (diamondStep b learners φ w) ([], st) := rfl
           _ = (tupleVars, stTuples) := hFoldDef
           _ = (u0 :: us, stTuples) := by rw [hVars]

      -- Use encodeFormula_diamond_match to relate encodeFormula to the fold result
      -- The lemma gives us: encodeFormula = match (fold result) with ...
      have hMatch := encodeFormula_diamond_match b learners φ w st

      -- We need to show the tuples in the lemma match our tuples
      have hTuplesEq : cartesianProduct (learners.map (diamondGetMinQs (b := b))) = tuples := by
        simp only [tuples, quorumSets]

      -- Rewrite the lemma's fold to use our tuples
      simp only [hTuplesEq, hFoldDef, hVars] at hMatch
      -- Now hMatch : encodeFormula b (.diamond learners φ) w st =
      --   let res' := us.foldl ... (u0, stTuples); (res'.1, res'.2)
      exact hMatch

lemma encodeFormula_diamond_forward_check (b : Bounds S) (learners : List S.Value) (φ : Logic.Formula S)
    (w : WId b) (st : EncState b) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (ih : ∀ (w' : WId b) (st₀ : EncState b),
      let res := encodeFormula b φ w' st₀
      let uBody := res.1
      let stBody := res.2
      stBody.clauses.all (SAT.Clause.eval σ) = true →
        (σ (FVar.toVar b uBody) = true ↔
          Sat (modelOf b σ hWF) w'.p (b.decodeMaybeEvent w'.ei)
            (decodePre b σ hWF w'.ti) φ))
    (tuples : List (List (Finset b.participants)))
    (tupleVars : List (FVar b))
    (stTuples : EncState b)
    (hTuples : tuples = cartesianProduct (learners.map (diamondGetMinQs (b := b))))
    (hFold : tuples.foldl (diamondStep b learners φ w) ([], st) = (tupleVars, stTuples))
    (hClausesRes : stTuples.clauses.all (SAT.Clause.eval σ) = true)
    (hTupleVars_true : ∀ uTuple ∈ tupleVars, σ (FVar.toVar b uTuple) = true)
    (hLearnersValid : ∀ ℓ ∈ learners, ℓ ∈ classValues b) :
    Sat.check (modelOf b σ hWF) (decodePre b σ hWF w.ti) φ learners Set.univ := by
  classical
  -- Strategy: prove by generalized induction, carrying the accumulated minimal quorum tuple.
  -- At each step, given quorum O, find minimal Qmin ⊆ O with true guard.
  -- At the base case, use the complete tuple to extract a witness from the forward clause.
  suffices hGen : ∀ (pre suf : List S.Value)
      (hConcat : pre ++ suf = learners)
      (preMinQ : List (Finset b.participants))
      (hLenMinQ : preMinQ.length = pre.length)
      (hGuardsMinQ : ∀ pair ∈ pre.zip preMinQ,
        σ (Var.MinQ (b.findValueIndex pair.1) pair.2) = true)
      (acc : Set b.participants)
      (hAcc : acc = (preMinQ.foldl (· ∩ ·) Finset.univ : Finset _)),
      Sat.check (modelOf b σ hWF) (decodePre b σ hWF w.ti) φ suf acc by
    exact hGen [] learners rfl [] rfl (by simp) Set.univ (by simp [Finset.coe_univ])

  intro pre suf hConcat preMinQ hLenMinQ hGuardsMinQ acc hAcc
  induction suf generalizing pre preMinQ acc with
  | nil =>
      -- Base case: suf = [], need ∃ p ∈ acc, Sat p φ
      simp only [Logic.Sat.Sat_check_nil]
      -- pre = learners (since pre ++ [] = learners)
      have hPrefixEq : pre = learners := by
        simp only [List.append_nil] at hConcat; exact hConcat
      -- preMinQ is a complete tuple of length learners.length
      have hLenFull : preMinQ.length = learners.length := by
        rw [← hPrefixEq]; exact hLenMinQ

      -- Show preMinQ ∈ tuples using tuple_mem_cartesianProduct_of_mem
      have hTupleMem : preMinQ ∈ tuples := by
        have hMem : ∀ pair ∈ learners.zip preMinQ,
            pair.2 ∈ diamondGetMinQs (b := b) pair.1 :=
          fun pair _ => minQ_in_diamondGetMinQs b pair.1 pair.2
        rw [hTuples]
        exact tuple_mem_cartesianProduct_of_mem b learners preMinQ hLenFull hMem

      -- Find index and control variable
      obtain ⟨idx, hNthEq⟩ := Encoding.mem_get hTupleMem

      -- Length alignment between tuples and tupleVars
      have hStep_len :
          ∀ acc tuple, (diamondStep b learners φ w acc tuple).1.length = acc.1.length + 1 := by
        intro acc tuple
        simp [diamondStep, List.length_append]
      have hLen_tupleVars : tupleVars.length = tuples.length := by
        have hLen := foldl_length_succ
          (f := diamondStep b learners φ w) (xs := tuples) (init := ([], st)) hStep_len
        simpa [hFold] using hLen

      have hLtVars : idx.val < tupleVars.length := by
        rw [hLen_tupleVars]; exact idx.isLt
      have hUTupleTrue : σ (FVar.toVar b (tupleVars.get ⟨idx.val, hLtVars⟩)) = true :=
        hTupleVars_true _ (List.get_mem tupleVars ⟨idx.val, hLtVars⟩)

      -- Locate the state and witnessFold for this tuple
      have hPreMinQ_mem : preMinQ ∈ tuples := hNthEq ▸ List.get_mem tuples idx
      have hExists_state :
          ∃ st_k, (diamondStep b learners φ w st_k preMinQ).1 ⊆ tupleVars ∧
                  (diamondStep b learners φ w st_k preMinQ).2.clauses ⊆ stTuples.clauses := by
        have hStep_fst : ∀ stAcc t, stAcc.1 ⊆ (diamondStep b learners φ w stAcc t).1 := by
          intro stAcc t x hx
          simp only [diamondStep, List.mem_append]
          left; exact hx
        have hStep_snd : ∀ stAcc t, stAcc.2.clauses ⊆ (diamondStep b learners φ w stAcc t).2.clauses :=
          fun stAcc t => diamond_step_snd_subset b learners φ w stAcc t
        -- Use exists_split_of_mem to get the prefix/suffix split
        obtain ⟨as, bs, hSplit⟩ := exists_split_of_mem hPreMinQ_mem
        let st_k := as.foldl (diamondStep b learners φ w) ([], st)
        refine ⟨st_k, ?_, ?_⟩
        · -- fst subset: (diamondStep ... st_k preMinQ).1 ⊆ tupleVars
          have hFoldSplit : tuples.foldl (diamondStep b learners φ w) ([], st) =
              bs.foldl (diamondStep b learners φ w)
                (diamondStep b learners φ w st_k preMinQ) := by
            rw [hSplit, List.foldl_append, List.foldl_cons]
          have hSubsetFst := foldl_subset_fst (diamondStep b learners φ w) hStep_fst bs
            (diamondStep b learners φ w st_k preMinQ)
          intro x hx
          have hIn := hSubsetFst hx
          have hFstEq : (bs.foldl (diamondStep b learners φ w)
              (diamondStep b learners φ w st_k preMinQ)).1 = tupleVars := by
            calc (bs.foldl (diamondStep b learners φ w)
                    (diamondStep b learners φ w st_k preMinQ)).1
                = (tuples.foldl (diamondStep b learners φ w) ([], st)).1 := by rw [hFoldSplit]
              _ = (tupleVars, stTuples).1 := by rw [hFold]
              _ = tupleVars := rfl
          rw [hFstEq] at hIn
          exact hIn
        · -- snd subset: (diamondStep ... st_k preMinQ).2.clauses ⊆ stTuples.clauses
          have hFoldSplit : tuples.foldl (diamondStep b learners φ w) ([], st) =
              bs.foldl (diamondStep b learners φ w)
                (diamondStep b learners φ w st_k preMinQ) := by
            rw [hSplit, List.foldl_append, List.foldl_cons]
          have hSubsetSnd := foldl_subset_snd (diamondStep b learners φ w) hStep_snd bs
            (diamondStep b learners φ w st_k preMinQ)
          intro clause hClause
          have hIn := hSubsetSnd hClause
          have hSndEq : (bs.foldl (diamondStep b learners φ w)
              (diamondStep b learners φ w st_k preMinQ)).2.clauses = stTuples.clauses := by
            calc (bs.foldl (diamondStep b learners φ w)
                    (diamondStep b learners φ w st_k preMinQ)).2.clauses
                = (tuples.foldl (diamondStep b learners φ w) ([], st)).2.clauses := by rw [hFoldSplit]
              _ = (tupleVars, stTuples).2.clauses := by rw [hFold]
              _ = stTuples.clauses := rfl
          rw [hSndEq] at hIn
          exact hIn
      rcases hExists_state with ⟨st_k, hFstSub, hClauseSub⟩

      -- Define intersection and witnessFold for this tuple
      let intersection := preMinQ.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
      let witnessFold := diamondWitnessFold b φ w intersection st_k.2
      let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
      let stepRes := encodeTupleControl b learners preMinQ witnessVars witnessFold.2

      -- stepRes clauses are satisfied
      have hStepClauses : stepRes.2.clauses.all (SAT.Clause.eval σ) = true := by
        have hSub : stepRes.2.clauses ⊆ stTuples.clauses := by
          have hStep_eq : diamondStep b learners φ w (st_k.1, st_k.2) preMinQ =
              (st_k.1 ++ [stepRes.1], stepRes.2) := rfl
          simpa [hStep_eq] using hClauseSub
        exact all_true_of_subset hSub hClausesRes

      -- Guards for this tuple are true (pre = learners, so hGuardsMinQ applies directly)
      have hGuards_idx : ∀ pair ∈ learners.zip preMinQ,
          σ (Var.MinQ (b.findValueIndex pair.1) pair.2) = true := by
        intro pair hPair
        exact hGuardsMinQ pair (hPrefixEq ▸ hPair)

      -- The forward clause for this tuple
      have hForwardClause := encodeTupleControl_forward_clause b learners
        preMinQ witnessVars witnessFold.2
      have hClauseSat : SAT.Clause.eval σ
          ([SAT.Lit.neg (FVar.toVar b stepRes.1)] ++
            (learners.zip preMinQ).map (fun (ℓ, Q) =>
              SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)) ++
            witnessVars.map SAT.Lit.pos) = true := by
        have hAll := List.all_eq_true.mp hStepClauses
        exact hAll _ hForwardClause

      -- Build QuorumTuple for encode_diamond_tuple
      let qt : QuorumTuple b := tupleToQuorumTuple b learners preMinQ hLenFull
      have hGuards_qt : ∀ pair ∈ qt.learnerIndices.zip qt.quorums,
          σ (Var.MinQ pair.1 pair.2) = true := by
        change ∀ pair ∈ (tupleToQuorumTuple b learners preMinQ hLenFull).learnerIndices.zip
            (tupleToQuorumTuple b learners preMinQ hLenFull).quorums,
            σ (Var.MinQ pair.1 pair.2) = true
        simp only [tupleToQuorumTuple_learnerIndices, tupleToQuorumTuple_quorums]
        intro pair hPair
        -- pair ∈ (learners.map b.findValueIndex).zip preMinQ
        -- Use that zip of map is map of zip
        rw [List.zip_map_left] at hPair
        obtain ⟨orig, hOrig, hEq⟩ := List.mem_map.mp hPair
        -- hEq : (fun x => (b.findValueIndex x.1, x.2)) orig = pair
        rw [← hEq]
        exact hGuards_idx orig hOrig

      -- Build witness pairs from witnessFold
      let witnessPairs := witnessFold.1
      have hInIntersection : ∀ pair ∈ witnessPairs, pair.2 ∈ qt.intersection b := by
        change ∀ pair ∈ witnessFold.1,
          pair.2 ∈ (tupleToQuorumTuple b learners preMinQ hLenFull).intersection b
        simp only [tupleToQuorumTuple_intersection]
        exact witnessFold_mem_intersection b φ w intersection st_k.2

      -- Forward clause matches encode_diamond_tuple structure
      have hClauseForm : [SAT.Lit.neg (FVar.toVar b stepRes.1)] ++
          (learners.zip preMinQ).map (fun (ℓ, Q) =>
            SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)) ++
          witnessVars.map SAT.Lit.pos =
          [SAT.Lit.neg (FVar.toVar b stepRes.1)] ++ qt.guards b ++
            witnessPairs.map (fun (uWit, _) => SAT.Lit.pos (FVar.toVar b uWit)) := by
        -- Guards equality
        have hGuardsEq := guards_eq_tuple_guards b learners preMinQ hLenFull
        -- Witness vars equality: witnessVars.map Lit.pos = witnessPairs.map (fun (uWit, _) => ...)
        have hWitnessEq : witnessVars.map SAT.Lit.pos =
            witnessPairs.map (fun (uWit, _) => SAT.Lit.pos (FVar.toVar b uWit)) := by
          simp only [witnessVars, witnessPairs, List.map_map]
          rfl
        rw [hGuardsEq, hWitnessEq]

      -- Show stepRes.1 ∈ tupleVars using hFstSub from hExists_state
      have hStepRes_in_tupleVars : stepRes.1 ∈ tupleVars := by
        -- stepRes.1 ∈ (diamondStep ... st_k preMinQ).1 by definition
        have hStep_eq : diamondStep b learners φ w (st_k.1, st_k.2) preMinQ =
            (st_k.1 ++ [stepRes.1], stepRes.2) := rfl
        have hIn_step : stepRes.1 ∈ (diamondStep b learners φ w st_k preMinQ).1 := by
          rw [hStep_eq]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        exact hFstSub hIn_step

      have hStepResTrue : σ (FVar.toVar b stepRes.1) = true :=
        hTupleVars_true stepRes.1 hStepRes_in_tupleVars

      -- Apply encode_diamond_tuple to get a witness
      have hWit := encode_diamond_tuple b σ stepRes.1 qt witnessPairs
        ([SAT.Lit.neg (FVar.toVar b stepRes.1)] ++ qt.guards b ++
          witnessPairs.map (fun (uWit, _) => SAT.Lit.pos (FVar.toVar b uWit)))
        rfl (by rwa [← hClauseForm]) hStepResTrue hGuards_qt
      rcases hWit with ⟨⟨uWit, pWit⟩, hPairIn, hWitTrue⟩

      -- pWit ∈ intersection ⊆ acc
      have hpWitInt : pWit ∈ intersection := hInIntersection (uWit, pWit) hPairIn
      have hpWitAcc : (pWit : b.participants) ∈ acc := by
        simp only [hAcc]
        exact hpWitInt

      -- Use witnessFold_fst_is_encode to get the correct intermediate state
      -- This gives us st_int where uWit = (encodeFormula ... st_int).1 and clauses are subset
      obtain ⟨st_int, hUWit_eq, hEncode_sub⟩ :=
        witnessFold_fst_is_encode b φ w intersection st_k.2 (uWit, pWit) hPairIn

      -- Show encoding at st_int has satisfied clauses
      have hSubFormula : (encodeFormula b φ ⟨pWit, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          st_int).2.clauses.all (SAT.Clause.eval σ) = true := by
        have hSub2 : witnessFold.2.clauses ⊆ stepRes.2.clauses :=
          encodeTupleControl_clauses_subset b learners preMinQ witnessVars witnessFold.2
        have hSub3 : stepRes.2.clauses ⊆ stTuples.clauses := by
          have hStep_eq : diamondStep b learners φ w (st_k.1, st_k.2) preMinQ =
              (st_k.1 ++ [stepRes.1], stepRes.2) := rfl
          have hSnd_eq : (diamondStep b learners φ w (st_k.1, st_k.2) preMinQ).2 = stepRes.2 := by
            simp only [hStep_eq]
          rw [← hSnd_eq]; exact hClauseSub
        exact all_true_of_subset
          (List.Subset.trans hEncode_sub (List.Subset.trans hSub2 hSub3)) hClausesRes

      -- Apply IH to get semantic satisfaction
      have hSatφ : Sat (modelOf b σ hWF) pWit † (decodePre b σ hWF w.ti) φ := by
        -- Apply IH with st_int
        have hIH := ih ⟨pWit, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int
        -- hIH gives: clauses satisfied → (σ uBody = true ↔ Sat ...)
        -- We have: clauses are satisfied (hSubFormula)
        -- We have: σ uWit = true (hWitTrue)
        -- We need: uWit = uBody (hUWit_eq gives this)
        have hIH' := hIH hSubFormula
        rw [hUWit_eq] at hWitTrue
        exact hIH'.mp hWitTrue

      exact ⟨pWit, hpWitAcc, hSatφ⟩

  | cons ℓ ls ihSuffix =>
      -- Inductive case: suf = ℓ :: ls
      simp only [Logic.Sat.Sat_check_cons]
      intro O hO

      -- Find minimal Qmin ⊆ O with true guard
      have hValMem : ℓ ∈ classValues b := by
        -- ℓ ∈ suf, and suf ⊆ learners via hConcat
        apply hLearnersValid
        have hInSuf : ℓ ∈ ℓ :: ls := List.Mem.head _
        have hSuf_sub : ∀ x ∈ ℓ :: ls, x ∈ learners := fun x hx =>
          hConcat ▸ List.mem_append_right pre hx
        exact hSuf_sub ℓ hInSuf
      -- O is a Set from Sat_check_cons - convert to Finset and apply lemma
      -- modelOf.learner = learnerOf by definition
      have hLearnerEq : (modelOf b σ hWF).learner ℓ = learnerOf b σ hWF ℓ := rfl
      -- Since b.participants = Fin n, O.toFinset coerces back to O
      have hOFinset : (O.toFinset : Set _) = O := Set.coe_toFinset O
      have hOQuorum' : (O.toFinset : Set _) ∈ (learnerOf b σ hWF ℓ).quorums := by
        rw [hOFinset, ← hLearnerEq]
        exact hO
      obtain ⟨Qmin, hSubset, hMinQTrue⟩ :=
        learnerOf_minQ_true_subset b σ hWF ℓ hValMem O.toFinset hOQuorum'

      -- Convert guard from pickRep to findValueIndex
      have hMinQ_idx : σ (Var.MinQ (b.findValueIndex ℓ) Qmin) = true := by
        have hPick := pickRep_eq_findValueIndex b σ (cnfLearners_sat b σ hWF) hValMem
        simpa [hPick] using hMinQTrue

      -- Extend pre and preMinQ
      have hConcat' : (pre ++ [ℓ]) ++ ls = learners := by
        simp [← hConcat]
      have hLenMinQ' : (preMinQ ++ [Qmin]).length = (pre ++ [ℓ]).length := by
        simp [hLenMinQ]
      have hGuardsMinQ' : ∀ pair ∈ (pre ++ [ℓ]).zip (preMinQ ++ [Qmin]),
          σ (Var.MinQ (b.findValueIndex pair.1) pair.2) = true := by
        intro pair hPair
        simp only [List.zip_append, hLenMinQ] at hPair
        rcases List.mem_append.mp hPair with hOld | hNew
        · exact hGuardsMinQ pair hOld
        · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hNew
          simp [hNew, hMinQ_idx]

      -- New accumulator: acc' = (preMinQ ++ [Qmin]).foldl (· ∩ ·) Finset.univ
      let acc' : Set b.participants := ↑((preMinQ ++ [Qmin]).foldl (· ∩ ·) Finset.univ)
      have hAcc' : acc' = ↑((preMinQ ++ [Qmin]).foldl (· ∩ ·) Finset.univ) := rfl

      -- Show acc' ⊆ acc ∩ O using that Qmin ⊆ O.toFinset
      have hAcc'Sub : acc' ⊆ acc ∩ O := by
        intro p hp
        simp only [Set.mem_inter_iff]
        -- acc' = acc ∩ ↑Qmin
        have hFold : ((preMinQ ++ [Qmin]).foldl (· ∩ ·) Finset.univ) =
            preMinQ.foldl (· ∩ ·) Finset.univ ∩ Qmin := by
          simp [List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.inter_comm]
        simp only [acc', hFold, Finset.coe_inter, Set.mem_inter_iff] at hp
        constructor
        · rw [hAcc]; exact hp.1
        · -- hp.2 : p ∈ ↑Qmin, and Qmin ⊆ O.toFinset = O
          have hQminSub : (Qmin : Set _) ⊆ O := by
            intro q hq
            have h : q ∈ O.toFinset := hSubset (Finset.mem_coe.mp hq)
            exact Set.mem_toFinset.mp h
          exact hQminSub hp.2

      -- Apply IH with the new accumulator
      -- ihSuffix is the IH from induction, with generalized pre, preMinQ, acc
      -- The suffices statement is:
      --   ∀ pre suf, hConcat → ∀ preMinQ, hLenMinQ → hGuardsMinQ → ∀ acc, hAcc → Sat.check ...
      -- So with suf = ls fixed, the IH takes: pre, hConcat, preMinQ, hLenMinQ, hGuardsMinQ, acc, hAcc
      specialize ihSuffix (pre ++ [ℓ]) hConcat' (preMinQ ++ [Qmin]) hLenMinQ' hGuardsMinQ' acc' hAcc'

      -- Use monotonicity to get the goal
      exact Sat_check_mono_acc (modelOf b σ hWF) (decodePre b σ hWF w.ti) φ hAcc'Sub ihSuffix

lemma encodeFormula_diamond_backward_vars (b : Bounds S) (learners : List S.Value) (φ : Logic.Formula S)
    (w : WId b) (st : EncState b) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (ih : ∀ (w' : WId b) (st₀ : EncState b),
      let res := encodeFormula b φ w' st₀
      let uBody := res.1
      let stBody := res.2
      stBody.clauses.all (SAT.Clause.eval σ) = true →
        (σ (FVar.toVar b uBody) = true ↔
          Sat (modelOf b σ hWF) w'.p (b.decodeMaybeEvent w'.ei)
            (decodePre b σ hWF w'.ti) φ))
    (tuples : List (List (Finset b.participants)))
    (tupleVars : List (FVar b))
    (stTuples : EncState b)
    (hTuples : tuples = cartesianProduct (learners.map (diamondGetMinQs (b := b))))
    (hFold : tuples.foldl (diamondStep b learners φ w) ([], st) = (tupleVars, stTuples))
    (hClausesRes : stTuples.clauses.all (SAT.Clause.eval σ) = true)
    (hSat : Sat.check (modelOf b σ hWF) (decodePre b σ hWF w.ti) φ learners Set.univ)
    (hLearnersValid : ∀ ℓ ∈ learners, ℓ ∈ classValues b) :
    ∀ uTuple ∈ tupleVars, σ (FVar.toVar b uTuple) = true := by
  classical
  intro uTuple hMemTuple
  have hStep_len :
      ∀ acc tuple, (diamondStep b learners φ w acc tuple).1.length = acc.1.length + 1 := by
    intro acc tuple
    simp [diamondStep, List.length_append]
  have hLen_tupleVars : tupleVars.length = tuples.length := by
    have hLen :=
      foldl_length_succ (f := diamondStep b learners φ w) (xs := tuples) (init := ([], st))
        hStep_len
    simpa [hFold] using hLen

  obtain ⟨i, hNth⟩ := Encoding.mem_get hMemTuple
  have hLtTuples : i.val < tuples.length := by
    have hLtVars : i.val < tupleVars.length := i.isLt
    simpa [hLen_tupleVars] using hLtVars
  have hLtVars : i.val < tupleVars.length := by
    simpa [hLen_tupleVars] using hLtTuples
  let tuple := tuples.get ⟨i.val, hLtTuples⟩

  let pre := tuples.take i.val
  let post := tuples.drop i.val.succ
  have hSplit : tuples = pre ++ tuple :: post := by
    have hDrop : tuples.drop i.val = tuple :: post := by
      have h := drop_eq_get_cons_drop (l := tuples) (i := i.val) hLtTuples
      simp [tuple, post]
    have hTake := (List.take_append_drop i.val tuples).symm
    simpa [pre, post, hDrop, List.append_assoc] using hTake

  let stPre := pre.foldl (diamondStep b learners φ w) ([], st)
  have hLen_pre : stPre.1.length = i.val := by
    have hLen_pre' :=
      foldl_length_succ (f := diamondStep b learners φ w) (xs := pre) (init := ([], st))
        hStep_len
    have hi_le : i.val ≤ tuples.length := Nat.le_of_lt hLtTuples
    have hPre_len : pre.length = i.val := by
      have hmin : Nat.min i.val tuples.length = i.val := Nat.min_eq_left hi_le
      simp only [pre, List.length_take, hmin]
    have hLen_pre'' : stPre.1.length = pre.length := by
      simpa [stPre] using hLen_pre'
    exact hLen_pre''.trans hPre_len

  have hFold_rewrite :
      tuples.foldl (diamondStep b learners φ w) ([], st) =
        post.foldl (diamondStep b learners φ w)
          (diamondStep b learners φ w stPre tuple) := by
    have h := @List.foldl_append _ _ (diamondStep b learners φ w) ([], st) pre (tuple :: post)
    simp [hSplit, stPre]

  have hFold_post :
      post.foldl (diamondStep b learners φ w)
        (diamondStep b learners φ w stPre tuple) = (tupleVars, stTuples) := by
    have h := hFold_rewrite
    have h' : (tupleVars, stTuples) =
        post.foldl (diamondStep b learners φ w)
          (diamondStep b learners φ w stPre tuple) := by
      simpa [hFold] using h
    exact h'.symm

  let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
  let witnessFold := diamondWitnessFold b φ w intersection stPre.2
  let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
  let stepRes := encodeTupleControl b learners tuple witnessVars witnessFold.2
  have hStep_eq :
      diamondStep b learners φ w stPre tuple =
        (stPre.1 ++ [stepRes.1], stepRes.2) := by
    rfl

  have hFold_post' :
      post.foldl (diamondStep b learners φ w)
        (stPre.1 ++ [stepRes.1], stepRes.2) = (tupleVars, stTuples) := by
    simpa [hStep_eq] using hFold_post

  obtain ⟨suffix, hSuffix⟩ :=
    diamond_step_foldl_fst_append (b := b) (learners := learners) (φ := φ) (w := w)
      post (stPre.1 ++ [stepRes.1], stepRes.2)

  have hTupleVars_split :
      tupleVars = stPre.1 ++ stepRes.1 :: suffix := by
    have hFst := congrArg Prod.fst hFold_post'
    calc
      tupleVars =
          (post.foldl (diamondStep b learners φ w)
            (stPre.1 ++ [stepRes.1], stepRes.2)).1 := hFst.symm
      _ = (stPre.1 ++ [stepRes.1]) ++ suffix := hSuffix
      _ = stPre.1 ++ stepRes.1 :: suffix := by simp [List.append_assoc]

  have hDrop_tupleVars : tupleVars.drop i.val = stepRes.1 :: suffix := by
    simp [hTupleVars_split, hLen_pre]

  have hHead_eq :
      tupleVars.get ⟨i.val, hLtVars⟩ = stepRes.1 := by
    have hDrop_get :=
      drop_eq_get_cons_drop (l := tupleVars) (i := i.val) hLtVars
    have hCompare :
        stepRes.1 :: suffix =
          tupleVars.get ⟨i.val, hLtVars⟩ :: tupleVars.drop i.val.succ := by
      simp [hDrop_tupleVars]
    exact (List.cons.inj hCompare).1.symm

  have hUTuple_eq : stepRes.1 = uTuple := by
    -- hHead_eq.symm : stepRes.1 = tupleVars.get ⟨i.val, hLtVars⟩
    -- hNth : tupleVars.get i = uTuple (where i : Fin tupleVars.length)
    -- Need to connect these through index equality
    have hIdx_eq : (⟨i.val, hLtVars⟩ : Fin tupleVars.length) = i := rfl
    rw [hIdx_eq] at hHead_eq
    exact hHead_eq.symm.trans hNth

  subst hUTuple_eq

  have hClauseSub : stepRes.2.clauses ⊆ stTuples.clauses := by
    have hSubset :=
      foldl_subset_snd
        (f := diamondStep b learners φ w)
        (hStep := by
          intro stAcc t
          simpa using
            (diamond_step_snd_subset (b := b) (learners := learners) (φ := φ) (w := w)
              stAcc t))
        (xs := post) (init := (stPre.1 ++ [stepRes.1], stepRes.2))
    have hSnd := congrArg Prod.snd hFold_post'
    intro clause hClause
    have hIn := hSubset hClause
    simpa [hSnd] using hIn

  have hStepClauses :
      stepRes.2.clauses.all (SAT.Clause.eval σ) = true :=
    all_true_of_subset hClauseSub hClausesRes

  have hSatCheck :
      Sat.check (modelOf b σ hWF) (decodePre b σ hWF w.ti) φ learners Set.univ := hSat

  classical
  by_cases hAllGuards :
      ∀ pair ∈ learners.zip tuple,
        σ (Var.MinQ (b.findValueIndex pair.1) pair.2) = true
  ·
    have hQuorums :
        ∀ pair ∈ learners.zip tuple,
          (pair.2 : Set _) ∈
            (learnerOf b σ hWF pair.1).quorums := by
      intro pair hPair
      have hMinQ := hAllGuards pair hPair
      have hValMem : pair.1 ∈ classValues b := by
        -- pair.1 ∈ learners since pair ∈ learners.zip tuple
        apply hLearnersValid
        -- pair ∈ learners.zip tuple means pair.1 ∈ learners
        have hIn : pair.1 ∈ (learners.zip tuple).map Prod.fst := List.mem_map.mpr ⟨pair, hPair, rfl⟩
        -- tuple ∈ tuples, so tuple.length = learners.length
        have hTupleMem : tuple ∈ tuples := List.get_mem tuples ⟨i.val, hLtTuples⟩
        have hTupleLen : tuple.length = learners.length :=
          tuple_mem_cartesianProduct_length b learners (hTuples ▸ hTupleMem)
        have hLeLen : learners.length ≤ tuple.length := hTupleLen.symm ▸ Nat.le_refl _
        rw [List.map_fst_zip hLeLen] at hIn
        exact hIn
      have hQuorum_val :=
        MinQ_bridge (b := b) (σ := σ) (hWF := hWF)
          (vIdx := b.findValueIndex pair.1) (Q := pair.2)
          (by simpa using hMinQ)
      have hValEq : b.values.get (b.findValueIndex pair.1) = pair.1 :=
        findValueIndex_value (b := b) (v := pair.1)
      simpa [hValEq] using hQuorum_val

    have hWitness :
        ∃ p ∈ intersection,
          Sat (modelOf b σ hWF) p † (decodePre b σ hWF w.ti) φ := by
      let M := modelOf b σ hWF
      let H := decodePre b σ hWF w.ti
      have hTupleMem : tuple ∈ tuples := List.get_mem tuples ⟨i.val, hLtTuples⟩
      have hTupleLen : tuple.length = learners.length :=
        tuple_mem_cartesianProduct_length b learners (hTuples ▸ hTupleMem)
      -- Generalized lemma with accumulator and init
      let foldInter : Finset b.participants → Finset b.participants → Finset b.participants :=
        fun a b => a ∩ b
      suffices h : ∀ (ls : List S.Value) (qs : List (Finset b.participants))
          (acc : Set b.participants) (init : Finset b.participants),
          ls.length = qs.length →
          (∀ pair ∈ ls.zip qs, (pair.2 : Set _) ∈ (M.learner pair.1).quorums) →
          Sat.check M H φ ls (acc ∩ init) →
          ∃ p ∈ acc ∩ ↑(qs.foldl foldInter init), Sat M p † H φ by
        have hResult := h learners tuple Set.univ Finset.univ hTupleLen.symm hQuorums
          (by simp only [Finset.coe_univ, Set.univ_inter]; exact hSatCheck)
        simp only [Set.univ_inter] at hResult
        exact hResult
      intro ls qs acc init hLen hQs hCheck
      induction ls generalizing qs acc init with
      | nil =>
          cases qs with
          | nil =>
              simp only [Sat.Sat_check_nil] at hCheck
              rcases hCheck with ⟨p, hp, hSatφ⟩
              refine ⟨p, ?_, hSatφ⟩
              simp only [List.foldl_nil]
              exact hp
          | cons _ _ => simp at hLen
      | cons ℓ ls ih =>
          cases qs with
          | nil => simp at hLen
          | cons Q qs =>
              simp only [Sat.Sat_check_cons] at hCheck
              have hQQuorum : (Q : Set _) ∈ (M.learner ℓ).quorums := hQs (ℓ, Q) (by simp)
              have hTailCheck := hCheck (Q : Set _) hQQuorum
              have hTailQuorums : ∀ pair ∈ ls.zip qs,
                  (pair.2 : Set _) ∈ (M.learner pair.1).quorums := by
                intro pair hpair
                exact hQs pair (by simp only [List.zip_cons_cons, List.mem_cons]; right; exact hpair)
              have hTailLen : ls.length = qs.length := by simp at hLen; exact hLen
              have hAccAssoc : (acc ∩ ↑init) ∩ ↑Q = acc ∩ ↑(init ∩ Q) := by
                ext x; simp only [Set.mem_inter_iff, Finset.coe_inter, Finset.mem_coe]; tauto
              rw [hAccAssoc] at hTailCheck
              have hIH := ih qs acc (init ∩ Q) hTailLen hTailQuorums hTailCheck
              rcases hIH with ⟨p, hp, hSatφ⟩
              refine ⟨p, ?_, hSatφ⟩
              simp only [List.foldl_cons, foldInter]
              exact hp

    rcases hWitness with ⟨p, hpInt, hSatφ⟩
    have hWitInFold :
        ∃ uWit, (uWit, p) ∈ witnessFold.1 :=
      witnessFold_has_participant b φ w intersection stPre.2 p hpInt

    rcases hWitInFold with ⟨uWit, hPairIn⟩

    -- Use witnessFold_fst_is_encode to get the correct intermediate state
    obtain ⟨st_int, hUWit_eq, hEncode_sub⟩ :=
      witnessFold_fst_is_encode b φ w intersection stPre.2 (uWit, p) hPairIn

    -- Show encoding at st_int has satisfied clauses
    have hSubFormula :
        (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int).2.clauses.all
          (SAT.Clause.eval σ) = true := by
      have hSub2 :
          witnessFold.2.clauses ⊆ stepRes.2.clauses :=
        encodeTupleControl_clauses_subset b learners tuple witnessVars witnessFold.2
      have hSub3 :
          stepRes.2.clauses ⊆ stTuples.clauses := hClauseSub
      exact all_true_of_subset
        (List.Subset.trans hEncode_sub (List.Subset.trans hSub2 hSub3)) hClausesRes

    -- Apply IH backward to get σ uWit = true from Sat φ
    have hWitTrue :
        σ (FVar.toVar b uWit) = true := by
      have hIH := ih ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ st_int
      have hIH' := hIH hSubFormula
      -- hUWit_eq : (uWit, p).1 = (encodeFormula ...).1, simplifies to uWit = ...
      simp only at hUWit_eq
      rw [hUWit_eq]
      exact hIH'.mpr hSatφ

    have hClause_wit :
        [SAT.Lit.neg (FVar.toVar b uWit), SAT.Lit.pos (FVar.toVar b stepRes.1)] ∈
          stepRes.2.clauses := by
      have hMemVar : FVar.toVar b uWit ∈ witnessVars := by
        simp only [witnessVars, List.mem_map]
        refine ⟨(uWit, p), hPairIn, rfl⟩
      have hClause_in :=
        encodeTupleControl_witness_clause (b := b) (learners := learners)
          (tuple := tuple) (witnessVars := witnessVars) (st := witnessFold.2)
          (v := FVar.toVar b uWit) hMemVar
      simpa [stepRes] using hClause_in
    have hClauseSat : SAT.Clause.eval σ
        [SAT.Lit.neg (FVar.toVar b uWit), SAT.Lit.pos (FVar.toVar b stepRes.1)] = true := by
      have hAll := List.all_eq_true.mp hStepClauses
      exact hAll _ hClause_wit
    exact witness_clause_eval_implies σ hClauseSat hWitTrue

  ·
    have hExistsFalse :
        ∃ pair ∈ learners.zip tuple,
          σ (Var.MinQ (b.findValueIndex pair.1) pair.2) = false :=
      by
        classical
        by_contra hPos
        push_neg at hPos
        have hPos' : ∀ pair ∈ learners.zip tuple,
            σ (Var.MinQ (b.findValueIndex pair.1) pair.2) = true := by
          intro pair hPair
          exact Bool.ne_false_iff.mp (hPos pair hPair)
        exact hAllGuards hPos'
    rcases hExistsFalse with ⟨pair, hPairMem, hMinQFalse⟩

    have hGuardClause :
        [SAT.Lit.pos (Var.MinQ (b.findValueIndex pair.1) pair.2),
          SAT.Lit.pos (FVar.toVar b stepRes.1)] ∈ stepRes.2.clauses := by
      have hIn :=
        encodeTupleControl_guard_clause (b := b) (learners := learners)
          (tuple := tuple) (witnessVars := witnessVars) (st := witnessFold.2)
          (pair := pair) hPairMem
      simpa [stepRes] using hIn
    have hGuardSat :
        SAT.Clause.eval σ
          [SAT.Lit.pos (Var.MinQ (b.findValueIndex pair.1) pair.2),
            SAT.Lit.pos (FVar.toVar b stepRes.1)] = true := by
      have hAll := List.all_eq_true.mp hStepClauses
      exact hAll _ hGuardClause
    exact guard_clause_eval_implies σ hGuardSat hMinQFalse

/-- Adequacy for encodeFormula diamond case: σ(u) = true ↔ diamond φ holds. -/
lemma encodeFormula_diamond_adequate (b : Bounds S) (learners : List S.Value) (φ : Logic.Formula S)
    (w : WId b) (st : EncState b) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (ih : ∀ (w' : WId b) (st₀ : EncState b),
      let res := encodeFormula b φ w' st₀
      let uBody := res.1
      let stBody := res.2
      stBody.clauses.all (SAT.Clause.eval σ) = true →
        (σ (FVar.toVar b uBody) = true ↔
          Sat (modelOf b σ hWF) w'.p (b.decodeMaybeEvent w'.ei)
            (decodePre b σ hWF w'.ti) φ))
    (hClauses :
      (encodeFormula b (.diamond learners φ) w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hLearnersValid : ∀ ℓ ∈ learners, ℓ ∈ classValues b) :
    (σ (FVar.toVar b (encodeFormula b (.diamond learners φ) w st).1) = true) ↔
    Sat (modelOf b σ hWF)
        w.p
        (b.decodeMaybeEvent w.ei)
        (decodePre b σ hWF w.ti)
        (.diamond learners φ)
    := by
  classical

  -- Mirror the structure of `encodeFormula` to name intermediate results
  let quorumSets := learners.map (diamondGetMinQs (b := b))
  let tuples := cartesianProduct quorumSets
  let foldRes := tuples.foldl (diamondStep b learners φ w) ([], st)
  let tupleVars := foldRes.1
  let stTuples := foldRes.2

  -- Structural equivalence
  have hEncode := encodeFormula_diamond_structure b learners φ w st

  -- Length alignment
  have hStep_len :
      ∀ acc tuple, (diamondStep b learners φ w acc tuple).1.length = acc.1.length + 1 := by
    intro acc tuple
    simp [diamondStep, List.length_append]
  have hLen_tupleVars : tupleVars.length = tuples.length := by
    have hLen := foldl_length_succ (f := diamondStep b learners φ w) (xs := tuples) (init := ([], st)) hStep_len
    simp only [List.length_nil, tupleVars, foldRes] at hLen ⊢
    simpa using hLen

  have hTuples_nonempty : tuples ≠ [] := diamondTuples_nonempty (b := b) learners
  have hTupleVars_nonempty : tupleVars ≠ [] := by
    intro h
    have hLen := hLen_tupleVars
    rw [h, List.length_nil] at hLen
    exact hTuples_nonempty (List.length_eq_zero_iff.mp hLen.symm)

  match hMatch : tupleVars with
  | [] => exact absurd rfl (hMatch ▸ hTupleVars_nonempty)
  | u0 :: us =>
      -- Refine structural equivalence with match
      have hEncode' : encodeFormula b (.diamond learners φ) w st =
          ((us.foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (u0, stTuples)).1,
           (us.foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (u0, stTuples)).2) := by
        -- Show the fold result equals u0 :: us in a form simp can use
        have hTupleVarsVal : (List.foldl (diamondStep b learners φ w) ([], st)
            (cartesianProduct (List.map (diamondGetMinQs b) learners))).1 = u0 :: us := by
          calc (List.foldl (diamondStep b learners φ w) ([], st)
                (cartesianProduct (List.map (diamondGetMinQs b) learners))).1
              = tupleVars := rfl
            _ = u0 :: us := hMatch
        simp only [hTupleVarsVal] at hEncode
        exact hEncode

      -- The clauses for the fold result are satisfied
      have hClausesRes :
          (us.foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (u0, stTuples)).2.clauses.all (SAT.Clause.eval σ) = true := by
        have heq : (us.foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (u0, stTuples)).2.clauses =
            (encodeFormula b (.diamond learners φ) w st).2.clauses := by
          rw [hEncode']
        rw [heq]
        exact hClauses

      -- The control variable is the first component
      have hCtrl : (encodeFormula b (.diamond learners φ) w st).1 =
          (us.foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (u0, stTuples)).1 := by
        rw [hEncode']

      constructor

      · -- Forward: σ(u) = true → semantic diamond holds
        intro hU
        rw [hCtrl] at hU

        -- Use mkAndIff_fold_forward to get all tuple controls are true
        have hAllTrue := mkAndIff_fold_forward b us u0 stTuples σ hClausesRes hU

        -- Every tuple control variable evaluates to true
        have hTupleVars_true :
            ∀ uTuple ∈ tupleVars, σ (FVar.toVar b uTuple) = true := by
          intro uTuple hMem
          -- tupleVars = u0 :: us by hMatch
          rw [hMatch] at hMem
          cases hMem with
          | head => exact hAllTrue.1
          | tail _ hMemTail => exact hAllTrue.2 _ hMemTail

        -- Show clauses accumulated before the mkAndIff fold are satisfied
        have hSub_stTuples :
            stTuples.clauses ⊆
              (us.foldl (fun (acc : FVar b × EncState b) u' =>
                  let (uAcc, stAcc) := acc
                  mkAndIff b uAcc u' stAcc) (u0, stTuples)).2.clauses :=
          foldl_subset_snd
            (f := fun (acc : FVar b × EncState b) u' =>
              let (uAcc, stAcc) := acc
              mkAndIff b uAcc u' stAcc)
            (hStep := by
              intro acc u'
              cases acc with
              | mk uAcc stAcc =>
                  dsimp
                  exact mkAndIff_clauses_subset b uAcc u' stAcc)
            (xs := us) (init := (u0, stTuples))
        have hAll_stTuples :
            stTuples.clauses.all (SAT.Clause.eval σ) = true :=
          all_true_of_subset hSub_stTuples hClausesRes

        have hTuples_eq : tuples = cartesianProduct (learners.map (diamondGetMinQs (b := b))) := rfl
        have hFold_eq : tuples.foldl (diamondStep b learners φ w) ([], st) = (tupleVars, stTuples) := rfl
        -- Convert Sat.check to Sat for diamond
        simp only [Sat]
        exact encodeFormula_diamond_forward_check b learners φ w st σ hWF ih tuples tupleVars stTuples
          hTuples_eq hFold_eq hAll_stTuples hTupleVars_true hLearnersValid

      · -- Backward: semantic diamond holds → σ(u) = true
        intro hSat
        rw [hCtrl]

        -- Use mkAndIff_fold_backward: need to show all tuple controls are true
        apply mkAndIff_fold_backward b us u0 stTuples σ hClausesRes

        -- Show every tuple control variable is true
        have hSub_stTuples :
            stTuples.clauses ⊆
              (us.foldl (fun (acc : FVar b × EncState b) u' =>
                  let (uAcc, stAcc) := acc
                  mkAndIff b uAcc u' stAcc) (u0, stTuples)).2.clauses :=
          foldl_subset_snd
            (f := fun (acc : FVar b × EncState b) u' =>
              let (uAcc, stAcc) := acc
              mkAndIff b uAcc u' stAcc)
            (hStep := by
              intro acc u'
              cases acc with
              | mk uAcc stAcc =>
                  dsimp
                  exact mkAndIff_clauses_subset b uAcc u' stAcc)
            (xs := us) (init := (u0, stTuples))
        have hAll_stTuples :
            stTuples.clauses.all (SAT.Clause.eval σ) = true :=
          all_true_of_subset hSub_stTuples hClausesRes

        have hTuples_eq' : tuples = cartesianProduct (learners.map (diamondGetMinQs (b := b))) := rfl
        have hFold_eq' : tuples.foldl (diamondStep b learners φ w) ([], st) = (tupleVars, stTuples) := rfl
        -- Convert Sat of diamond to Sat.check
        have hSatCheck : Sat.check (modelOf b σ hWF) (decodePre b σ hWF w.ti) φ learners Set.univ := by
          simp only [Sat] at hSat
          exact hSat
        have hTupleVars_true :
            ∀ uTuple ∈ tupleVars, σ (FVar.toVar b uTuple) = true :=
          encodeFormula_diamond_backward_vars b learners φ w st σ hWF ih tuples tupleVars stTuples
            hTuples_eq' hFold_eq' hAll_stTuples hSatCheck hLearnersValid

        refine ⟨?_, ?_⟩
        · apply hTupleVars_true
          rw [hMatch]; exact List.Mem.head us
        · intro u' hMem
          apply hTupleVars_true
          rw [hMatch]; exact List.Mem.tail u0 hMem

end Encoding
