import ModalDistribution.Logic.SATEncoding.PreEqEncoding
import ModalDistribution.Logic.SATEncoding.TseytinGadgets

open ModalDistribution
open ModalDistribution.Logic
open PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]
def decodedSubset
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) : Prop :=
  ∀ world ∈ decodePre b σ hWF t,
    ∃ world' ∈ decodePre b σ hWF t', worldEq world world'

/-- Decoded histories match when each direction gives a decoded subset. -/
def decodedMatches
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) : Prop :=
  decodedSubset b σ hWF t t' ∧ decodedSubset b σ hWF t' t

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Decoded matches are equivalent to `histEq` on decoded prehistories. -/
lemma decodedMatches_iff_histEq
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) :
    decodedMatches b σ hWF t t' ↔
      histEq (decodePre b σ hWF t) (decodePre b σ hWF t') := by
  constructor
  · intro h
    refine (PreHistory.histEq_spec
      (decodePre b σ hWF t)
      (decodePre b σ hWF t')).mpr ⟨?_, ?_⟩
    · intro world hWorld
      obtain ⟨world', hWorld', hEq⟩ := h.1 world hWorld
      exact ⟨world', hWorld', hEq⟩
    · intro world' hWorld'
      obtain ⟨world, hWorld, hEq⟩ := h.2 world' hWorld'
      exact ⟨world, hWorld, PreHistory.worldEq_symm hEq⟩
  · intro h
    have hSubsets :=
      (PreHistory.histEq_spec
        (decodePre b σ hWF t)
        (decodePre b σ hWF t')).mp h
    constructor
    · intro world hWorld
      obtain ⟨world', hWorld', hEq⟩ := hSubsets.1 world hWorld
      exact ⟨world', hWorld', hEq⟩
    · intro world' hWorld'
      obtain ⟨world, hWorld, hEq⟩ := hSubsets.2 world' hWorld'
      exact ⟨world, hWorld, PreHistory.worldEq_symm hEq⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Reflexivity for decoded subset. -/
lemma decodedSubset_refl
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t : b.times) :
    decodedSubset b σ hWF t t := by
  intro world hWorld
  refine ⟨world, hWorld, ?_⟩
  simpa using
    (PreHistory.worldEq_refl
      (P := Fin b.nParticipants)
      (Event := Signature.EventType S)
      world)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Reflexivity for decoded matches. -/
lemma decodedMatches_refl
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t : b.times) :
    decodedMatches b σ hWF t t :=
  ⟨decodedSubset_refl b σ hWF t, decodedSubset_refl b σ hWF t⟩

/-- Fuel-based measure used for well-founded PreEq induction. -/
def preEqFuel (b : Bounds S) (σ : SAT.Assignment (Var b))
    (pair : b.times × b.times) : Nat :=
  fuelOf b σ pair.1 + fuelOf b σ pair.2

/-- Strengthened predicate bundling both soundness and cache invariants for PreEq. -/
def PreEqStrong (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) : Prop :=
  (∀ st0,
      (addPreEqFrom b t st0).clauses.all (SAT.Clause.eval σ) = true →
      σ (Var.PreEq t t') = true →
        decodedMatches b σ hWF t t') ∧
  (∀ st0,
      (addPreEqFrom b t st0).clauses.all (SAT.Clause.eval σ) = true →
      True)

omit [DecidableEq S.AtomicPredType] in
/-- Projection of the soundness component from `PreEqStrong`. -/
lemma PreEqStrong.sound {b : Bounds S} {σ : SAT.Assignment (Var b)} {hWF : WF b σ}
    {t t' : b.times}
    (h : PreEqStrong b σ hWF t t') :
    ∀ st0,
      (addPreEqFrom b t st0).clauses.all (SAT.Clause.eval σ) = true →
      σ (Var.PreEq t t') = true →
        decodedMatches b σ hWF t t' :=
  h.1

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Split `addPreEqFrom` at a designated time index `t'`. -/
lemma addPreEqFrom_split
    (b : Bounds S) (t : b.times) (st0 : EncState b)
    (t' : b.times) (before after : List (b.times))
    (hSplit : Bounds.timesL b = before ++ t' :: after) :
    addPreEqFrom b t st0 =
      (after.foldl (fun stCur u => addPreEqPair b t u stCur)
        (addPreEqPair b t t' (before.foldl (fun stCur u => addPreEqPair b t u stCur) st0))) := by
  classical
  simp [addPreEqFrom, List.foldl_append, hSplit]

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Clauses produced while encoding `(t, t')` remain satisfied in the final state. -/
lemma preEq_pair_clauses_true
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t : b.times) (t' : b.times) (st0 : EncState b)
    (before after : List (b.times))
    (hSplit : Bounds.timesL b = before ++ t' :: after)
    (hClauses :
        (addPreEqFrom b t st0).clauses.all (SAT.Clause.eval σ) = true) :
    let step := fun stCur u => addPreEqPair b t u stCur
    let stBefore := before.foldl step st0
    let stPair   := addPreEqPair b t t' stBefore
    stPair.clauses.all (SAT.Clause.eval σ) = true := by
  classical
  intro step stBefore stPair
  have hSplitEq :
      addPreEqFrom b t st0 =
        after.foldl step (addPreEqPair b t t' (before.foldl step st0)) :=
    addPreEqFrom_split (b := b) (t := t) (st0 := st0)
      (t' := t') (before := before) (after := after) hSplit
  have hClausesAfter :
      (after.foldl step stPair).clauses.all (SAT.Clause.eval σ) = true := by
    simpa [step, hSplitEq, stPair] using hClauses
  have hStepSubset :
      ∀ stCur u, stCur.clauses ⊆ (step stCur u).clauses := by
    intro stCur u
    simpa [step] using
      (addPreEqPair_clauses_subset
        (b := b) (H0 := t) (H' := u) (st := stCur))
  have hSubset :=
    foldl_subset_state
      (b := b)
      (f := step)
      (hStep := hStepSubset)
      (xs := after)
      (init := stPair)
  exact all_true_of_subset hSubset hClausesAfter

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Transfer decoded membership across matching witness worlds.

    If `w` belongs to `t` and `w'` belongs to `t'`, and the worlds agree on
    participant, event signature, and decoded sub-prehistory, then the decoded
    world for `w` also appears in `decodePre t'`.  This isolates the semantic
    step needed once the SAT obligations produce a matching witness and the IH
    shows the sub-prehistories are equal. -/
lemma mem_decodePre_transfer_of_matching
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    {t' : b.times} {w w' : WId b}
    (hMem' : σ (Var.Mem t' w') = true)
    (hp : w'.p = w.p)
    (hevent : b.decodeMaybeEvent w'.ei = b.decodeMaybeEvent w.ei)
    (hTail :
      histEq (decodePre b σ hWF w.ti) (decodePre b σ hWF w'.ti)) :
    ∃ world',
      world' ∈ decodePre b σ hWF t' ∧
        worldEq
          (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti) world' := by
  classical
  have hWorld' :
      (w'.p, b.decodeMaybeEvent w'.ei, decodePre b σ hWF w'.ti)
      ∈ decodePre b σ hWF t' :=
    mem_decodePre_of_memVar b σ hWF t' w' hMem'
  use (w'.p, b.decodeMaybeEvent w'.ei, decodePre b σ hWF w'.ti)
  constructor
  · exact hWorld'
  · -- Show worldEq between the two worlds
    unfold worldEq
    -- worldEq is worldEqAt (height w1 + height w2) w1 w2
    -- which for Nat.succ becomes: place equal, event equal, histEqAt n time1 time2
    have hHeight :
        0 <
          World.height (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti) +
            World.height (w'.p, b.decodeMaybeEvent w'.ei, decodePre b σ hWF w'.ti) := by
      have :=
        PreHistory.height_sum_pos
          (decodePre b σ hWF w.ti)
          (decodePre b σ hWF w'.ti)
      simpa [World.height] using this
    obtain ⟨n, hN⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hHeight)
    change worldEq _ _
    rw [worldEq, hN]
    simp only [worldEqAt, World.place, World.event, World.time]
    constructor
    · exact hp.symm
    · constructor
      · exact hevent.symm
      · -- Need to show histEqAt n (decodePre b σ hWF w.ti) (decodePre b σ hWF w'.ti)
        -- We have hTail : histEq (decodePre b σ hWF w.ti) (decodePre b σ hWF w'.ti)
        -- which is histEqAt (height ... + height ...) ...
        -- We need to use monotonicity of histEqAt
        have : histEqAt n (decodePre b σ hWF w.ti) (decodePre b σ hWF w'.ti) := by
          unfold histEq at hTail
          -- hTail : histEqAt (height ... + height ...) (decodePre ...) (decodePre ...)
          -- From the case split, n + 1 = total height
          have hEq :
              n + 1 = PreHistory.height (decodePre b σ hWF w.ti) +
                      PreHistory.height (decodePre b σ hWF w'.ti) := by
            have : World.height (w.p, b.decodeMaybeEvent w.ei, decodePre b σ hWF w.ti) =
                (decodePre b σ hWF w.ti).height := by simp [World.height]
            have : World.height (w'.p, b.decodeMaybeEvent w'.ei, decodePre b σ hWF w'.ti) =
                (decodePre b σ hWF w'.ti).height := by simp [World.height]
            omega
          rw [← hEq] at hTail
          exact histEqAt_of_succ (by omega) hTail
        exact this

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Reduce decoded subset inclusion to matching witness worlds.

    To prove decoded subset inclusion, it suffices to show that every
    `Mem t w` literal that is true yields a matching `w'` in `t'` with identical
    participant, event signature, and recursively equal decoded histories. -/
lemma decodePre_subset_of_memWitness
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    {t t' : b.times}
    (matchWitness :
      ∀ {w : WId b},
        σ (Var.Mem t w) = true →
          ∃ w' : WId b,
            w'.p = w.p ∧
              b.decodeMaybeEvent w'.ei = b.decodeMaybeEvent w.ei ∧
              σ (Var.Mem t' w') = true ∧
              histEq
                (decodePre b σ hWF w.ti)
                (decodePre b σ hWF w'.ti)) :
    decodedSubset b σ hWF t t' := by
  intro world hWorld
  obtain ⟨w, hwEq, hMem⟩ :=
    exists_memVar_of_mem_decodePre (b := b) (σ := σ) (hWF := hWF)
      (H := t) (w := world) hWorld
  obtain ⟨w', hp, hevent, hMem', hTail⟩ := matchWitness hMem
  obtain ⟨world', hWorld', hEq⟩ :=
    mem_decodePre_transfer_of_matching
      (b := b) (σ := σ) (hWF := hWF)
      (t' := t') (w := w) (w' := w')
      hMem' hp hevent hTail
  refine ⟨world', ?_, ?_⟩
  · simpa [hwEq] using hWorld'
  · simpa [hwEq] using hEq

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma preEqObligationStep_preserves_list
    (b : Bounds S) (t t' : b.times)
    (acc : List (FVar b) × EncState b) (w : WId b) :
    acc.1 ⊆ (preEqObligationStep b t t' acc w).1 := by
  classical
  rcases acc with ⟨lst, stc⟩
  unfold preEqObligationStep
  cases hDw : mkDw b t' w stc with
  | mk d stDw =>
      cases hOw : mkOw b t w d stDw with
      | mk o stOw =>
          simp only [hDw, hOw]
          intro oOld hMemOld
          simp [List.mem_cons, hMemOld]

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma preEqObligation_fold_preserves_list
    (b : Bounds S) (t t' : b.times)
    (xs : List (WId b))
    (acc : List (FVar b) × EncState b) :
    acc.1 ⊆
      (xs.foldl (preEqObligationStep b t t') acc).1 := by
  classical
  revert acc
  refine xs.recOn ?base ?step
  · intro acc
    simp
  · intro w ws ih acc
    have hSubset :
        acc.1 ⊆ (preEqObligationStep b t t' acc w).1 :=
      preEqObligationStep_preserves_list (b := b) (t := t) (t' := t') _ _
    exact
      (List.Subset.trans hSubset
        (ih (preEqObligationStep b t t' acc w)))

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma obligation_memWitness_forward
    (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t t' : b.times)
    {st st1 stFinal : EncState b} {os : List (FVar b)}
    (hFold :
      (os, st1) =
        (WId.allWorlds b).foldl
          (preEqObligationStep b t t') ([], st))
    (hSt1Subset : st1.clauses ⊆ stFinal.clauses)
    (hClausesFinal :
      stFinal.clauses.all (SAT.Clause.eval σ) = true)
    (hOblTrue :
      ∀ o ∈ os, σ (FVar.toVar b o) = true) :
    ∀ {w : WId b}, σ (Var.Mem t w) = true →
      ∃ w' : WId b,
        w'.p = w.p ∧
          b.decodeMaybeEvent w'.ei = b.decodeMaybeEvent w.ei ∧
          σ (Var.Mem t' w') = true ∧
          σ (Var.PreEq w.ti w'.ti) = true := by
  classical
  intro w hMem
  have hWorld : w ∈ WId.allWorlds b := WId.mem_allWorlds b w
  obtain ⟨before, after, hSplit⟩ :=
    exists_split_of_mem (a := w) (l := WId.allWorlds b) hWorld
  have hFoldAll :
      (os, st1) =
        (before ++ w :: after).foldl
          (preEqObligationStep b t t') ([], st) := by
    simpa [hSplit] using hFold
  set accBefore :=
    before.foldl (preEqObligationStep b t t') ([], st) with hAccBefore
  cases hAcc : accBefore with
  | mk lstBefore stBefore =>
      have hFoldSplit :
          (os, st1) =
            after.foldl (preEqObligationStep b t t')
              (preEqObligationStep b t t' (lstBefore, stBefore) w) := by
        rw [List.foldl_append, List.foldl_cons] at hFoldAll
        rw [← hAccBefore] at hFoldAll
        rw [hAcc] at hFoldAll
        exact hFoldAll
      cases hMkDw : mkDw b t' w stBefore with
      | mk d stDw =>
          cases hMkOw : mkOw b t w d stDw with
          | mk o stOw =>
              have hStepEval :
                  preEqObligationStep b t t' (lstBefore, stBefore) w =
                    (o :: lstBefore, stOw) := by
                simp [preEqObligationStep, hMkDw, hMkOw]
              have hFoldSplit' :
                  (os, st1) =
                    after.foldl (preEqObligationStep b t t')
                      (o :: lstBefore, stOw) := by
                simpa [hStepEval] using hFoldSplit
              have hOsEq :
                  os =
                    (after.foldl (preEqObligationStep b t t')
                      (o :: lstBefore, stOw)).1 :=
                congrArg Prod.fst hFoldSplit'
              have hStEq :
                  st1 =
                    (after.foldl (preEqObligationStep b t t')
                      (o :: lstBefore, stOw)).2 :=
                congrArg Prod.snd hFoldSplit'
              have hMemO :
                  o ∈
                    (after.foldl (preEqObligationStep b t t')
                      (o :: lstBefore, stOw)).1 := by
                have hSubset :=
                  preEqObligation_fold_preserves_list
                    (b := b) (t := t) (t' := t') (xs := after)
                    (acc := (o :: lstBefore, stOw))
                have hHead : o ∈ (o :: lstBefore) := by
                  simp
                exact hSubset hHead
              have hOblVal :
                  σ (FVar.toVar b o) = true := by
                have := hOblTrue o (by simpa [hOsEq] using hMemO)
                exact this
              have hStepSubset :
                  ∀ acc w,
                    acc.2.clauses ⊆
                      (preEqObligationStep b t t' acc w).2.clauses :=
                preEqObligationStep_clauses_subset (b := b) (t := t) (t' := t')
              have hOwSubset :
                  stOw.clauses ⊆ st1.clauses := by
                have hResult :=
                  foldl_subset_snd
                    (b := b)
                    (f := preEqObligationStep b t t')
                    (hStep := hStepSubset)
                    (xs := after)
                    (init := (o :: lstBefore, stOw))
                simpa [hStEq] using hResult
              have hDwSubset :
                  stDw.clauses ⊆ stOw.clauses := by
                have :=
                  mkOw_clauses_subset
                    (b := b) (t := t) (w := w) (d := d) (st := stDw)
                simpa [hMkOw] using this
              have hDwFinalSubset :
                  stDw.clauses ⊆ stFinal.clauses :=
                List.Subset.trans
                  (List.Subset.trans
                    (by
                      have :=
                        mkDw_clauses_subset
                          (b := b) (t' := t') (w := w) (st := stBefore)
                      simp)
                    hDwSubset)
                  (List.Subset.trans hOwSubset hSt1Subset)
              have hOwFinalSubset :
                  stOw.clauses ⊆ stFinal.clauses :=
                List.Subset.trans hOwSubset hSt1Subset
              have hClausesDw :
                  stDw.clauses.all (SAT.Clause.eval σ) = true :=
                all_true_of_subset hDwFinalSubset hClausesFinal
              have hClausesOw :
                  stOw.clauses.all (SAT.Clause.eval σ) = true :=
                all_true_of_subset hOwFinalSubset hClausesFinal
              have hMemDw :
                  σ (FVar.toVar b d) = true := by
                have := mkOw_adequate_forward
                  (b := b) (σ := σ) (t := t) (w := w)
                  (d := d) (st := stDw)
                  (hClauses := by simpa [hMkOw] using hClausesOw)
                  (hOw := by simpa [hMkOw] using hOblVal) (hMem := hMem)
                exact this
              obtain ⟨w', _, hSameSig, hMem', hPreEq⟩ := by
                have := mkDw_adequate_forward
                  (b := b) (σ := σ) (t' := t') (w := w) (st := stBefore)
                  (hClauses := by simpa [hMkDw] using hClausesDw)
                  (hDw := by simpa [hMkDw] using hMemDw)
                exact this
              have ⟨hp, hevent⟩ := sameSig_eq_true_iff b w w' |>.mp hSameSig
              exact ⟨w', hp, hevent, hMem', hPreEq⟩

omit [DecidableEq S.AtomicPredType] in
lemma decode_subset_from_obligations
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times)
    {st st1 stFinal : EncState b} {os : List (FVar b)}
    (hFold :
      (os, st1) =
        (WId.allWorlds b).foldl
          (preEqObligationStep b t t') ([], st))
    (hSt1Subset : st1.clauses ⊆ stFinal.clauses)
    (hClausesFinal :
      stFinal.clauses.all (SAT.Clause.eval σ) = true)
    (hOblTrue :
      ∀ o ∈ os, σ (FVar.toVar b o) = true)
    (IH :
      ∀ ⦃t₁ t₂ : b.times⦄,
        fuelOf b σ t₁ + fuelOf b σ t₂ <
            fuelOf b σ t + fuelOf b σ t' →
        σ (Var.PreEq t₁ t₂) = true →
          decodedMatches b σ hWF t₁ t₂) :
    decodedSubset b σ hWF t t' := by
  classical
  refine
    decodePre_subset_of_memWitness
      (b := b) (σ := σ) (hWF := hWF)
      (t := t) (t' := t')
      (matchWitness := ?_)
  intro w hMem
  obtain ⟨w', hp, hevent, hMem', hPreEqTail⟩ :=
    obligation_memWitness_forward
      (b := b) (σ := σ)
      (t := t) (t' := t')
      (st := st) (st1 := st1) (stFinal := stFinal)
      (os := os)
      (hFold := hFold)
      (hSt1Subset := hSt1Subset)
      (hClausesFinal := hClausesFinal)
      (hOblTrue := hOblTrue)
      (w := w) hMem
  have hFuelPos_t :
      0 < fuelOf b σ t :=
    fuel_pos_of_mem (b := b) (σ := σ) (hWF := hWF)
      (H := t) (w := w) hMem
  have hFuelPos_t' :
      0 < fuelOf b σ t' :=
    fuel_pos_of_mem (b := b) (σ := σ) (hWF := hWF)
      (H := t') (w := w') hMem'
  have hFuelLt_t :
      fuelOf b σ w.ti < fuelOf b σ t :=
    fuelOf_strict_decrease_mem
      (b := b) (σ := σ) (hWF := hWF)
      (H := t) (w := w) hMem hFuelPos_t
  have hFuelLt_t' :
      fuelOf b σ w'.ti < fuelOf b σ t' :=
    fuelOf_strict_decrease_mem
      (b := b) (σ := σ) (hWF := hWF)
      (H := t') (w := w') hMem' hFuelPos_t'
  have hFuelSum :
      fuelOf b σ w.ti + fuelOf b σ w'.ti <
        fuelOf b σ t + fuelOf b σ t' :=
    Nat.add_lt_add hFuelLt_t hFuelLt_t'
  have hTailDecode :
      histEq (decodePre b σ hWF w.ti) (decodePre b σ hWF w'.ti) :=
    (decodedMatches_iff_histEq b σ hWF w.ti w'.ti |>.1)
      (IH hFuelSum hPreEqTail)
  exact ⟨w', hp, hevent, hMem', hTailDecode⟩

omit [DecidableEq S.AtomicPredType] in
/-- Soundness of a single `(t, t')` encoding: if the clauses are satisfied and
    `PreEq t t'` is true, the decoded prehistories match. -/
lemma preEq_pair_sound
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) (st : EncState b)
    (hClauses : (addPreEqPair b t t' st).clauses.all (SAT.Clause.eval σ) = true)
    (hPreEq : σ (Var.PreEq t t') = true)
    (IH : ∀ ⦃t₁ t₂ : b.times⦄,
        fuelOf b σ t₁ + fuelOf b σ t₂ <
            fuelOf b σ t + fuelOf b σ t' →
        σ (Var.PreEq t₁ t₂) = true →
          decodedMatches b σ hWF t₁ t₂) :
    decodedMatches b σ hWF t t' := by
  classical
  by_cases hEq : t = t'
  · subst hEq
    exact decodedMatches_refl b σ hWF t

  -- Unfold the encoder structure
  set foldOs := (WId.allWorlds b).foldl (preEqObligationStep b t t') ([], st)
  let os := foldOs.1
  let stOs := foldOs.2
  set foldOs' := (WId.allWorlds b).foldl (preEqObligationStep b t' t) ([], stOs)
  let os' := foldOs'.1
  let stOs' := foldOs'.2

  cases hAllocBase : EncState.allocFresh b stOs' with | mk base stBase =>
  set stBasePos := EncState.addClause b stBase [SAT.Lit.pos (FVar.toVar b base)]

  set foldAcc := List.foldl (preEqAccStep b) (base, stBasePos) os
  let eqA := foldAcc.1
  let stAcc := foldAcc.2
  set foldAcc' := List.foldl (preEqAccStep b) (eqA, stAcc) os'
  let eqFinal := foldAcc'.1
  let stFinal := foldAcc'.2

  set stExpose := addPreEqExpose b t t' eqFinal stFinal

  have hClausesExpose :
      stExpose.clauses.all (SAT.Clause.eval σ) = true := by
    -- In the non-reflexive branch, addPreEqPair is definitionally stExpose.
    have hPairUnfold : addPreEqPair b t t' st = addPreEqPair_core b t t' st := by
      simp [addPreEqPair, if_neg hEq]
    rw [hPairUnfold] at hClauses
    -- Unfold addPreEqPair_core in terms of our local bindings
    have : addPreEqPair_core b t t' st = stExpose := by
      unfold addPreEqPair_core
      -- Match the fold structure
      have h1 : (WId.allWorlds b).foldl (preEqObligationStep b t t') ([], st) = foldOs := rfl
      have h2 : (WId.allWorlds b).foldl (preEqObligationStep b t' t) ([], foldOs.2) = foldOs' := rfl
      have h3 : EncState.allocFresh b foldOs'.2 = (base, stBase) := hAllocBase
      simp [h1, h2, h3]
      rfl
    rw [this] at hClauses
    exact hClauses

  -- Extract eqFinal truth from the expose gadget.
  have hEqFinal : σ (FVar.toVar b eqFinal) = true :=
    addPreEqExpose_extract b t t' eqFinal stFinal σ hClausesExpose hPreEq

  -- All earlier clauses remain true.
  have hClausesFinal : stFinal.clauses.all (SAT.Clause.eval σ) = true :=
    all_true_of_subset
      (addPreEqExpose_clauses_subset (b := b) (H0 := t) (H' := t') (v := eqFinal) (st := stFinal))
      hClausesExpose

  -- Subset chains for obligations and accumulators.
  have hSub1 : st.clauses ⊆ stOs.clauses :=
    preEqObligation_fold_clauses_subset b t t' (WId.allWorlds b) (init := ([], st)) rfl
  have hSub2 : stOs.clauses ⊆ stOs'.clauses :=
    preEqObligation_fold_clauses_subset b t' t (WId.allWorlds b) (init := ([], stOs)) rfl
  have hSub3 : stOs'.clauses ⊆ stBase.clauses := by
    have : stBase.clauses = stOs'.clauses := by
      simpa [hAllocBase] using EncState.allocFresh_clauses_eq (b := b) (st := stOs')
    simp [this]
  have hSub4 : stBase.clauses ⊆ stBasePos.clauses :=
    EncState.addClause_subset_clauses b stBase [SAT.Lit.pos (FVar.toVar b base)]
  have hSub5 : stBasePos.clauses ⊆ stAcc.clauses :=
    preEqAcc_fold_clauses_subset b os (init := (base, stBasePos)) rfl
  have hSub6 : stAcc.clauses ⊆ stFinal.clauses :=
    preEqAcc_fold_clauses_subset b os' (init := (eqA, stAcc)) rfl

  -- Base is true (from the unit clause)
  have hBaseTrue : σ (FVar.toVar b base) = true := by
    have hUnit : [SAT.Lit.pos (FVar.toVar b base)] ∈ stBasePos.clauses := by
      simp [stBasePos, EncState.addClause]
    have hInFinal : [SAT.Lit.pos (FVar.toVar b base)] ∈ stFinal.clauses :=
      hSub6 (hSub5 hUnit)
    exact (List.all_eq_true.mp hClausesFinal) _ hInFinal

  -- Accumulator results
  have hEqATrue : σ (FVar.toVar b eqA) = true :=
    preEqAcc_fold_base_true b σ os' rfl hClausesFinal hEqFinal
  have hOs'True : ∀ o ∈ os', σ (FVar.toVar b o) = true :=
    preEqAcc_fold_all_true b σ os' rfl hClausesFinal hEqFinal
  have hOsTrue : ∀ o ∈ os, σ (FVar.toVar b o) = true :=
    preEqAcc_fold_all_true b σ os rfl
      (all_true_of_subset hSub6 hClausesFinal) hEqATrue

  -- Forward coverage
  have hCover_forward : decodedSubset b σ hWF t t' := by
    apply decode_subset_from_obligations b σ hWF t t' rfl
    · apply List.Subset.trans hSub2
      apply List.Subset.trans hSub3
      apply List.Subset.trans hSub4
      apply List.Subset.trans hSub5
      exact hSub6
    · exact hClausesFinal
    · exact hOsTrue
    · exact IH

  -- Backward coverage
  have hCover_backward : decodedSubset b σ hWF t' t := by
    apply decode_subset_from_obligations b σ hWF t' t rfl
    · apply List.Subset.trans hSub3
      apply List.Subset.trans hSub4
      apply List.Subset.trans hSub5
      exact hSub6
    · exact hClausesFinal
    · exact hOs'True
    · intro t₁ t₂ hFuel hPre
      apply IH
      · omega
      · exact hPre

  exact ⟨hCover_forward, hCover_backward⟩

omit [DecidableEq S.AtomicPredType] in
/-- Soundness for a fixed source time `t`: if the encoding of all pairs from `t`
    is satisfied and `PreEq t t'` is true, the decoded prehistories match. -/
lemma preEq_sound_from_core
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t : b.times) (st0 : EncState b)
    (hClauses : (addPreEqFrom b t st0).clauses.all (SAT.Clause.eval σ) = true)
    (t' : b.times)
    (hPreEq : σ (Var.PreEq t t') = true)
    (IH :
      ∀ ⦃t₁ t₂ : b.times⦄,
        fuelOf b σ t₁ + fuelOf b σ t₂ <
            fuelOf b σ t + fuelOf b σ t' →
        σ (Var.PreEq t₁ t₂) = true →
          decodedMatches b σ hWF t₁ t₂) :
    decodedMatches b σ hWF t t' := by
  classical
  -- Isolate the `(t, t')` iteration inside the fold.
  let step := fun stCur (u : b.times) => addPreEqPair b t u stCur
  have hMem : t' ∈ Bounds.timesL b := by
    simp [Bounds.timesL]
  obtain ⟨before, after, hSplit⟩ :=
    exists_split_of_mem (a := t') (l := Bounds.timesL b) hMem
  have hSplitEq :
      addPreEqFrom b t st0 =
        after.foldl step (addPreEqPair b t t' (before.foldl step st0)) :=
    addPreEqFrom_split
      (b := b) (t := t) (st0 := st0)
      (t' := t') (before := before) (after := after) hSplit

  set stBefore := before.foldl step st0
  set stPair := addPreEqPair b t t' stBefore
  set stAfter := after.foldl step stPair

  have hClausesAfter :
      stAfter.clauses.all (SAT.Clause.eval σ) = true := by
    simpa [stAfter, stPair, stBefore, step, hSplitEq] using hClauses

  have hClausesPairRaw :=
    preEq_pair_clauses_true
      (b := b) (σ := σ) (t := t) (t' := t') (st0 := st0)
      (before := before) (after := after)
      (hSplit := hSplit) (hClauses := hClauses)
  have hClausesPair :
      stPair.clauses.all (SAT.Clause.eval σ) = true := by
    simpa [step, stBefore, stPair] using hClausesPairRaw

  -- Deduce soundness for the isolated pair.
  exact preEq_pair_sound
    (b := b) (σ := σ) (hWF := hWF) (t := t) (t' := t')
    (st := stBefore) (hClauses := hClausesPair) (hPreEq := hPreEq) (IH := IH)

omit [DecidableEq S.AtomicPredType] in
/-- Global soundness for PreEq: if all PreEq clauses are satisfied, then
    `PreEq t t'` implies decoded history equality. -/
lemma preEq_sound
    (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (t t' : b.times) (st : EncState b)
    (hClauses : (addPreEqAll b st).clauses.all (SAT.Clause.eval σ) = true)
    (hPreEq : σ (Var.PreEq t t') = true) :
    histEq (decodePre b σ hWF t) (decodePre b σ hWF t') := by
  revert hPreEq
  -- Induction on total fuel
  generalize hN : fuelOf b σ t + fuelOf b σ t' = n
  induction n using Nat.strong_induction_on generalizing t t' with
  | h n IH =>
    intro hPreEq
    -- We need to show decodedMatches b σ hWF t t'
    rw [← decodedMatches_iff_histEq]
    -- Find intermediate state st_k for addPreEqFrom
    have hExists : ∃ st_k, (addPreEqFrom b t st_k).clauses ⊆ (addPreEqAll b st).clauses := by
      apply foldl_exists_state_subset (b := b)
        (f := fun stCur u => addPreEqFrom b u stCur)
        (hStep := fun stCur u => addPreEqFrom_clauses_subset b u stCur)
        (xs := Bounds.timesL b)
        (x := t)
        (init := st)
        (hMem := by simp [Bounds.timesL])
    obtain ⟨st_k, hSub⟩ := hExists
    refine preEq_sound_from_core b σ hWF t st_k ?hClauses t' hPreEq ?IH
    · -- Goal: prove hClauses
      exact all_true_of_subset hSub hClauses
    · -- Goal: prove IH
      intro t₁ t₂ hLt hPreEq₁
      rw [decodedMatches_iff_histEq]
      have hLtN : fuelOf b σ t₁ + fuelOf b σ t₂ < n := by
        rw [← hN]; exact hLt
      exact IH _ hLtN t₁ t₂ rfl hPreEq₁

end Encoding
