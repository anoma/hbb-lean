import ModalDistribution.Logic.SATEncoding.FormulaEncoding

/-!
# Diamond Encoding Helper Lemmas

This file contains definitions and lemmas for the diamond case of formula encoding:
- `diamondGetMinQs`: Extract minimal quorum sets for a learner
- `diamondWitnessFold`: Witness encoding fold helper
- `diamondStep`: Step function for the diamond outer fold
- Various offset and length preservation lemmas

These are used by the main structural determinism proofs for the diamond case.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-! ## Diamond encoding step definitions

These definitions factor out the inline step function used in the diamond encoding,
allowing us to state and prove lemmas about the fold structure. -/

/-- Minimal quorum list for a learner value, matching the encoding's inline `getMinQs`. -/
def diamondGetMinQs (b : Bounds S) (ℓ : S.Value) : List (Finset b.participants) :=
  let vIdx := b.findValueIndex ℓ
  (Var.allMinQ b vIdx).filterMap fun v =>
    match v with
    | Var.MinQ _ Q => some Q
    | _ => none

/-- The witness fold helper used in the diamond encoding.
    This folds over participants, encoding φ at each participant in the intersection. -/
def diamondWitnessFold (b : Bounds S) (φ : Formula S) (w : WId b)
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

/-- The step function for the diamond encoding outer fold. -/
def diamondStep (b : Bounds S) (learners : List S.Value) (φ : Formula S)
    (w : WId b)
    (acc : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) :
    List (FVar b) × EncState b :=
  let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
  let witnessFold := diamondWitnessFold b φ w intersection acc.2
  let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
  let (uTuple, stFinal) :=
    encodeTupleControl b learners tuple witnessVars witnessFold.2
  (acc.1 ++ [uTuple], stFinal)

set_option linter.style.longLine false in
/-- The unfolded step in encodeFormula (after beta-reduction) equals diamondStep.
    This matches the exact form that `simp only [encodeFormula]` produces,
    using anonymous struct syntax and dot notation for partsL. -/
lemma encodeFormula_diamond_step_unfolded_eq (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b) :
    (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      (x.1 ++
        [(encodeTupleControl b learners tuple
            (List.map (fun u => FVar.toVar b u.1)
              (List.foldl
                (fun acc p =>
                  if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                    (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                      (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                  else acc)
                ([], x.2) b.partsL).1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).2).1],
      (encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).2)) = diamondStep b learners φ w := by
  funext x tuple
  simp only [diamondStep, diamondWitnessFold, encodeTupleControl]

/-- Helper: the inner fold in diamond encoding (over parts) preserves offset. -/
private lemma diamond_inner_fold_offset (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants)
    (st st' : EncState b) (offset : Nat) (hOffset : st'.nextFresh = st.nextFresh + offset)
    (ih : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w' st1').2.nextFresh =
        (encodeFormula b φ w' st1).2.nextFresh + off) :
    let innerFold := fun (acc : List (FVar b × b.participants) × EncState b) (p : b.participants) =>
      if _ : p ∈ intersection then
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let (uWit, stNew) := encodeFormula b φ wEnd acc.2
        (acc.1 ++ [(uWit, p)], stNew)
      else acc
    ((Bounds.partsL b).foldl innerFold ([], st')).2.nextFresh =
    ((Bounds.partsL b).foldl innerFold ([], st)).2.nextFresh + offset := by
  intro innerFold
  have hIndep : ∀ (ps : List b.participants)
      (acc1 acc2 : List (FVar b × b.participants) × EncState b),
      acc1.2 = acc2.2 →
      (ps.foldl innerFold acc1).2.nextFresh = (ps.foldl innerFold acc2).2.nextFresh := by
    intro ps acc1 acc2 hEq
    induction ps generalizing acc1 acc2 with
    | nil => simp only [List.foldl_nil]; exact congrArg (·.nextFresh) hEq
    | cons p ps' ih' =>
      simp only [List.foldl_cons]
      apply ih'
      simp only [innerFold]
      split_ifs <;> simp [hEq]
  induction (Bounds.partsL b) generalizing st st' with
  | nil => simp [hOffset]
  | cons p ps ih' =>
    simp only [List.foldl_cons]
    let step := innerFold ([], st) p
    let step' := innerFold ([], st') p
    have hStepOffset : step'.2.nextFresh = step.2.nextFresh + offset := by
      simp only [step, step', innerFold]
      split_ifs with hp
      · let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        exact ih wEnd st st' offset hOffset
      · exact hOffset
    have hIhApp := ih' step.2 step'.2 hStepOffset
    have hIndep1 := hIndep ps (innerFold ([], st) p) ([], (innerFold ([], st) p).2) rfl
    have hIndep2 := hIndep ps (innerFold ([], st') p) ([], (innerFold ([], st') p).2) rfl
    simp only [step, step'] at hIndep1 hIndep2 hIhApp
    rw [hIndep1, hIndep2]
    exact hIhApp

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: mkAndIff fold adds exactly us.length to nextFresh. -/
lemma mkAndIff_fold_nextFresh_eq (b : Bounds S)
    (u0 : FVar b) (us : List (FVar b)) (st : EncState b) :
    (us.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0, st)).2.nextFresh =
    st.nextFresh + us.length := by
  induction us generalizing u0 st with
  | nil => simp
  | cons u' us' ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    rw [mkAndIff_nextFresh]
    ring

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: mkAndIff fold preserves offset. -/
lemma mkAndIff_fold_offset (b : Bounds S)
    (u0 u0' : FVar b) (us us' : List (FVar b)) (st st' : EncState b) (offset : Nat)
    (hLen : us.length = us'.length) (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (us'.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0', st')).2.nextFresh =
    (us.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0, st)).2.nextFresh + offset := by
  rw [mkAndIff_fold_nextFresh_eq, mkAndIff_fold_nextFresh_eq, hOffset, hLen]
  ring

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: mkAndIff's first component has id equal to input state's nextFresh. -/
lemma mkAndIff_fst_id (b : Bounds S) (x y : FVar b) (st : EncState b) :
    (mkAndIff b x y st).1.id = st.nextFresh := by
  simp only [mkAndIff, EncState.allocFresh]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: mkAndIff fold fst id when the list is non-empty.
    When us has length n > 0, the result's fst.id = st.nextFresh + n - 1. -/
lemma mkAndIff_fold_fst_id_pos (b : Bounds S)
    (u0 : FVar b) (us : List (FVar b)) (st : EncState b) (hPos : 0 < us.length) :
    (us.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0, st)).1.id =
    st.nextFresh + us.length - 1 := by
  induction us generalizing u0 st with
  | nil => simp at hPos
  | cons u usTail ih =>
    simp only [List.foldl_cons, List.length_cons]
    cases husTail : usTail with
    | nil =>
      simp only [List.foldl_nil, mkAndIff_fst_id]
      simp
    | cons v vs =>
      subst husTail
      have hPos_tail : 0 < (v :: vs).length := by simp
      rw [ih _ _ hPos_tail, mkAndIff_nextFresh]
      simp only [List.length_cons]
      omega

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: When both us lists are non-empty and have same length, mkAndIff fold's
    first component id shifts by the state nextFresh offset. -/
lemma mkAndIff_fold_fst_id_shift_pos (b : Bounds S)
    (u0 u0' : FVar b) (us us' : List (FVar b)) (st st' : EncState b) (offset : Nat)
    (hLen : us.length = us'.length) (hPos : 0 < us.length)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (us'.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0', st')).1.id =
    (us.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0, st)).1.id + offset := by
  have hPos' : 0 < us'.length := by omega
  rw [mkAndIff_fold_fst_id_pos b u0 us st hPos]
  rw [mkAndIff_fold_fst_id_pos b u0' us' st' hPos']
  rw [hOffset, hLen]
  omega

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: encodeTupleControl's first component has id = st.nextFresh. -/
lemma encodeTupleControl_fst_id (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars : List (Var b)) (st : EncState b) :
    (encodeTupleControl b learners tuple witnessVars st).1.id = st.nextFresh := by
  simp only [encodeTupleControl, EncState.allocFresh]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: foldl preserves nextFresh if each step preserves it.
    This is a copy of the lemma defined later, needed for diamond case. -/
private lemma foldl_nextFresh_eq' {α : Type*} (b : Bounds S)
    (xs : List α) (st : EncState b)
    (f : EncState b → α → EncState b)
    (hPres : ∀ s x, (f s x).nextFresh = s.nextFresh) :
    (xs.foldl f st).nextFresh = st.nextFresh := by
  induction xs generalizing st with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih, hPres]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- encodeTupleControl increases nextFresh by exactly 1. Needed for diamond case. -/
lemma encodeTupleControl_nextFresh' (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars : List (Var b)) (st : EncState b) :
    (encodeTupleControl b learners tuple witnessVars st).2.nextFresh = st.nextFresh + 1 := by
  simp only [encodeTupleControl]
  have hAlloc := EncState.allocFresh_nextFresh b st
  rw [foldl_nextFresh_eq', foldl_nextFresh_eq', EncState.addClause, hAlloc]
  · intro s _; simp [EncState.addClause]
  · intro s _; simp [EncState.addClause]

/-- diamondStep from empty list produces singleton list. -/
lemma diamondStep_nil_fst_eq (b : Bounds S) (learners : List S.Value) (φ : Formula S)
    (w : WId b) (tuple : List (Finset b.participants)) (st : EncState b) :
    (diamondStep b learners φ w ([], st) tuple).1 =
    [(encodeTupleControl b learners tuple
      ((diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).1.map
        fun u => FVar.toVar b u.1)
      (diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).2).1] := by
  simp only [diamondStep, List.nil_append]

/-- For a singleton tuple list, the fold produces a singleton FVar list. -/
lemma diamondStep_foldl_singleton_eq (b : Bounds S) (learners : List S.Value) (φ : Formula S)
    (w : WId b) (tuple : List (Finset b.participants)) (st : EncState b) :
    ([tuple].foldl (diamondStep b learners φ w) ([], st)).1 =
    [(encodeTupleControl b learners tuple
      ((diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).1.map
        fun u => FVar.toVar b u.1)
      (diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).2).1] := by
  simp only [List.foldl_cons, List.foldl_nil]
  exact diamondStep_nil_fst_eq b learners φ w tuple st

/-- The element from diamondStep has id = witnessFold's final nextFresh. -/
lemma diamondStep_element_id_eq_nextFresh (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b) (tuple : List (Finset b.participants)) (st : EncState b) :
    let intersection := tuple.foldl (· ∩ ·) Finset.univ
    let witnessFold := diamondWitnessFold b φ w intersection st
    let witnessVars := witnessFold.1.map fun u => FVar.toVar b u.1
    (encodeTupleControl b learners tuple witnessVars witnessFold.2).1.id =
      witnessFold.2.nextFresh := by
  intro intersection witnessFold witnessVars
  exact encodeTupleControl_fst_id b learners tuple witnessVars witnessFold.2

/-- The fold over tuples produces a list with length = tuples.length. -/
lemma diamondStep_foldl_length (b : Bounds S) (learners : List S.Value) (φ : Formula S)
    (w : WId b) (tuples : List (List (Finset b.participants))) (st : EncState b) :
    (tuples.foldl (diamondStep b learners φ w) ([], st)).1.length = tuples.length := by
  have hGeneral : ∀ (ts' : List (List (Finset b.participants)))
      (acc : List (FVar b) × EncState b),
      (ts'.foldl (diamondStep b learners φ w) acc).1.length = acc.1.length + ts'.length := by
    intro ts' acc
    induction ts' generalizing acc with
    | nil => simp
    | cons t' ts'' ih' =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih']
      simp only [diamondStep, List.length_append, List.length_singleton]
      ring
  simp only [hGeneral, List.length_nil, zero_add]

/-- When the fold produces a singleton list [u0], we have tuples = [tuple] for some tuple,
    and u0 equals the encodeTupleControl result for that tuple. -/
lemma diamondStep_foldl_singleton_characterization (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b) (tuples : List (List (Finset b.participants)))
    (st : EncState b) (u0 : FVar b)
    (hSingleton : (tuples.foldl (diamondStep b learners φ w) ([], st)).1 = [u0]) :
    ∃ (tuple : List (Finset b.participants)),
      tuples = [tuple] ∧
      u0 = (encodeTupleControl b learners tuple
        ((diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).1.map
          fun u => FVar.toVar b u.1)
        (diamondWitnessFold b φ w (tuple.foldl (· ∩ ·) Finset.univ) st).2).1 := by
  have hLen : tuples.length = 1 := by
    have := diamondStep_foldl_length b learners φ w tuples st
    simp only [hSingleton, List.length_singleton] at this
    exact this.symm
  cases tuples with
  | nil => simp at hLen
  | cons t ts =>
    simp only [List.length_cons, add_eq_right] at hLen
    have hts : ts = [] := List.length_eq_zero_iff.mp hLen
    subst hts
    use t
    constructor
    · rfl
    · simp only [List.foldl_cons, List.foldl_nil] at hSingleton
      have hFst := diamondStep_nil_fst_eq b learners φ w t st
      simp only [hFst, List.cons.injEq, and_true] at hSingleton
      exact hSingleton.symm

/-- The witness fold preserves offset. -/
lemma diamondWitnessFold_offset (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants)
    (st st' : EncState b) (offset : Nat) (hOffset : st'.nextFresh = st.nextFresh + offset)
    (ih : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w' st1').2.nextFresh =
        (encodeFormula b φ w' st1).2.nextFresh + off) :
    (diamondWitnessFold b φ w intersection st').2.nextFresh =
    (diamondWitnessFold b φ w intersection st).2.nextFresh + offset := by
  simp only [diamondWitnessFold]
  exact diamond_inner_fold_offset b φ w intersection st st' offset hOffset ih

/-- When we have explicit elements u0 and u0' from the fold, and know they equal the
    encodeTupleControl results, their ids shift by offset. -/
lemma diamondStep_foldl_singleton_id_shift (b : Bounds S) (learners : List S.Value)
    (φ : Formula S) (w : WId b) (tuple : List (Finset b.participants))
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (ih : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w' st1').2.nextFresh = (encodeFormula b φ w' st1).2.nextFresh + off) :
    let intersection := tuple.foldl (· ∩ ·) Finset.univ
    let wf := diamondWitnessFold b φ w intersection st
    let wf' := diamondWitnessFold b φ w intersection st'
    let wvs := wf.1.map fun u => FVar.toVar b u.1
    let wvs' := wf'.1.map fun u => FVar.toVar b u.1
    (encodeTupleControl b learners tuple wvs' wf'.2).1.id =
    (encodeTupleControl b learners tuple wvs wf.2).1.id + offset := by
  intro intersection wf wf' wvs wvs'
  rw [encodeTupleControl_fst_id, encodeTupleControl_fst_id]
  exact diamondWitnessFold_offset b φ w intersection st st' offset hOffset ih

/-- One step of the diamond fold preserves offset (using diamondStep). -/
lemma diamondStep_offset (b : Bounds S) (learners : List S.Value) (φ : Formula S)
    (w : WId b) (tuple : List (Finset b.participants))
    (acc acc' : List (FVar b) × EncState b) (offset : Nat)
    (hOffset : acc'.2.nextFresh = acc.2.nextFresh + offset)
    (ih : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w' st1').2.nextFresh =
        (encodeFormula b φ w' st1).2.nextFresh + off) :
    (diamondStep b learners φ w acc' tuple).2.nextFresh =
    (diamondStep b learners φ w acc tuple).2.nextFresh + offset := by
  simp only [diamondStep]
  let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
  have hWitOffset := diamondWitnessFold_offset b φ w intersection acc.2 acc'.2 offset hOffset ih
  have h1 := encodeTupleControl_nextFresh' b learners tuple
    ((diamondWitnessFold b φ w intersection acc.2).1.map (fun u => FVar.toVar b u.1))
    (diamondWitnessFold b φ w intersection acc.2).2
  have h2 := encodeTupleControl_nextFresh' b learners tuple
    ((diamondWitnessFold b φ w intersection acc'.2).1.map (fun u => FVar.toVar b u.1))
    (diamondWitnessFold b φ w intersection acc'.2).2
  simp only [intersection] at hWitOffset h1 h2
  omega

/-- The outer fold in diamond encoding using diamondStep preserves offset. -/
lemma diamondStep_foldl_offset (b : Bounds S) (learners : List S.Value) (φ : Formula S)
    (w : WId b) (tuples : List (List (Finset b.participants)))
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (ih : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w' st1').2.nextFresh =
        (encodeFormula b φ w' st1).2.nextFresh + off) :
    (tuples.foldl (diamondStep b learners φ w) ([], st')).2.nextFresh =
    (tuples.foldl (diamondStep b learners φ w) ([], st)).2.nextFresh + offset := by
  induction tuples generalizing st st' with
  | nil => simp [hOffset]
  | cons tuple tuples' ih_tuples =>
    simp only [List.foldl_cons]
    let res := diamondStep b learners φ w ([], st) tuple
    let res' := diamondStep b learners φ w ([], st') tuple
    have hStepOffset : res'.2.nextFresh = res.2.nextFresh + offset :=
      diamondStep_offset b learners φ w tuple ([], st) ([], st') offset hOffset ih
    have hIndep : ∀ (ts : List (List (Finset b.participants)))
        (acc1 acc2 : List (FVar b) × EncState b),
        acc1.2 = acc2.2 →
        (ts.foldl (diamondStep b learners φ w) acc1).2.nextFresh =
        (ts.foldl (diamondStep b learners φ w) acc2).2.nextFresh := by
      intro ts acc1 acc2 hEq
      induction ts generalizing acc1 acc2 with
      | nil => simp [hEq]
      | cons t ts' ih' =>
        simp only [List.foldl_cons]
        apply ih'
        simp only [diamondStep, hEq]
    have hIh := ih_tuples res.2 res'.2 hStepOffset
    have hIndep1 := hIndep tuples' res ([], res.2) rfl
    have hIndep2 := hIndep tuples' res' ([], res'.2) rfl
    simp only [res, res'] at hIndep1 hIndep2 hIh
    rw [hIndep1, hIndep2]
    exact hIh

/-- The fold length is independent of the starting state. -/
lemma diamondStep_foldl_length_eq (b : Bounds S) (learners : List S.Value) (φ : Formula S)
    (w : WId b) (tuples : List (List (Finset b.participants)))
    (st st' : EncState b) :
    (tuples.foldl (diamondStep b learners φ w) ([], st')).1.length =
    (tuples.foldl (diamondStep b learners φ w) ([], st)).1.length := by
  -- Each step appends exactly one element
  have hGeneral : ∀ (ts : List (List (Finset b.participants)))
      (acc : List (FVar b) × EncState b),
      (ts.foldl (diamondStep b learners φ w) acc).1.length = acc.1.length + ts.length := by
    intro ts acc
    induction ts generalizing acc with
    | nil => simp
    | cons t ts' ih' =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih']
      simp only [diamondStep, List.length_append, List.length_singleton]
      ring
  simp only [hGeneral, List.length_nil, zero_add]

/-- Helper: One step of the diamond outer fold preserves offset.
    Each step does inner fold (preserves offset) + encodeTupleControl (adds exactly 1). -/
private lemma diamond_step_offset (b : Bounds S) (φ : Formula S) (w : WId b)
    (learners : List S.Value) (tuple : List (Finset b.participants))
    (_accVars : List (FVar b)) (stCur stCur' : EncState b) (offset : Nat)
    (hOffset : stCur'.nextFresh = stCur.nextFresh + offset)
    (ih : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w' st1').2.nextFresh =
        (encodeFormula b φ w' st1).2.nextFresh + off) :
    let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
    let innerFold := fun (acc : List (FVar b × b.participants) × EncState b) (p : b.participants) =>
      if _ : p ∈ intersection then
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let (uWit, stNew) := encodeFormula b φ wEnd acc.2
        (acc.1 ++ [(uWit, p)], stNew)
      else acc
    let witnessFold := (Bounds.partsL b).foldl innerFold ([], stCur)
    let witnessFold' := (Bounds.partsL b).foldl innerFold ([], stCur')
    let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
    let witnessVars' := witnessFold'.1.map (fun u => FVar.toVar b u.1)
    let stFinal := (encodeTupleControl b learners tuple witnessVars witnessFold.2).2
    let stFinal' := (encodeTupleControl b learners tuple witnessVars' witnessFold'.2).2
    stFinal'.nextFresh = stFinal.nextFresh + offset := by
  intro intersection innerFold witnessFold witnessFold' witnessVars witnessVars' stFinal stFinal'
  -- Inner fold preserves offset
  have hInnerOffset : witnessFold'.2.nextFresh = witnessFold.2.nextFresh + offset := by
    simp only [witnessFold, witnessFold']
    exact diamond_inner_fold_offset b φ w intersection stCur stCur' offset hOffset ih
  -- encodeTupleControl adds exactly 1 to both
  have hEnc : stFinal.nextFresh = witnessFold.2.nextFresh + 1 := by
    simp only [stFinal, witnessVars]
    exact encodeTupleControl_nextFresh' b learners tuple _ witnessFold.2
  have hEnc' : stFinal'.nextFresh = witnessFold'.2.nextFresh + 1 := by
    simp only [stFinal', witnessVars']
    exact encodeTupleControl_nextFresh' b learners tuple _ witnessFold'.2
  rw [hEnc, hEnc', hInnerOffset]; ring

set_option linter.style.longLine false in
/-- Helper: The outer fold in diamond encoding preserves offset.
    CRITICAL: The step function is INLINED in the type to match `simp only [encodeFormula]` exactly. -/
lemma diamond_outer_fold_offset (b : Bounds S) (φ : Formula S) (w : WId b)
    (learners : List S.Value)
    (tuples : List (List (Finset b.participants)))
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (ih : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w' st1').2.nextFresh =
        (encodeFormula b φ w' st1).2.nextFresh + off) :
    -- Step function INLINED (no let binding) to match goal syntax exactly
    (tuples.foldl (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      (x.1 ++ [(encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).1],
        (encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).2)) ([], st')).2.nextFresh =
    (tuples.foldl (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      (x.1 ++ [(encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).1],
        (encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).2)) ([], st)).2.nextFresh + offset := by
  -- Define step locally for the proof
  let step := fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
    (x.1 ++ [(encodeTupleControl b learners tuple
        (List.map (fun u => FVar.toVar b u.1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).1)
        (List.foldl
          (fun acc p =>
            if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
              (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
            else acc)
          ([], x.2) b.partsL).2).1],
      (encodeTupleControl b learners tuple
        (List.map (fun u => FVar.toVar b u.1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).1)
        (List.foldl
          (fun acc p =>
            if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
              (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
            else acc)
          ([], x.2) b.partsL).2).2)
  induction tuples generalizing st st' with
  | nil => simp [hOffset]
  | cons tuple tuples' ih_tuples =>
    simp only [List.foldl_cons]
    -- Results after one step
    let res := step ([], st) tuple
    let res' := step ([], st') tuple
    -- One step preserves offset
    have hStepOffset : res'.2.nextFresh = res.2.nextFresh + offset := by
      simp only [res, res', step]
      exact diamond_step_offset b φ w learners tuple [] st st' offset hOffset ih
    -- Fold depends only on .2, not on .1
    have hIndep : ∀ (ts : List (List (Finset b.participants)))
        (acc1 acc2 : List (FVar b) × EncState b),
        acc1.2 = acc2.2 →
        (ts.foldl step acc1).2.nextFresh = (ts.foldl step acc2).2.nextFresh := by
      intro ts acc1 acc2 hEq
      induction ts generalizing acc1 acc2 with
      | nil => simp only [List.foldl_nil]; exact congrArg (·.nextFresh) hEq
      | cons t ts' ih' =>
        simp only [List.foldl_cons]
        apply ih'
        simp only [step]
        have : acc1.2 = acc2.2 := hEq
        congr 1
        -- The witnessFold only depends on stCur = acc.2
        simp only [this]
    have hIh := ih_tuples res.2 res'.2 hStepOffset
    have hIndep1 := hIndep tuples' (step ([], st) tuple) ([], (step ([], st) tuple).2) rfl
    have hIndep2 := hIndep tuples' (step ([], st') tuple) ([], (step ([], st') tuple).2) rfl
    simp only [res, res'] at hIndep1 hIndep2 hIh
    rw [hIndep1, hIndep2]
    exact hIh

set_option linter.style.longLine false in
/-- Helper: The outer fold in diamond encoding produces lists of the same length.
    CRITICAL: The step function is INLINED in the type to match `simp only [encodeFormula]` exactly. -/
lemma diamond_outer_fold_length_eq (b : Bounds S) (φ : Formula S) (w : WId b)
    (learners : List S.Value)
    (tuples : List (List (Finset b.participants)))
    (st st' : EncState b) :
    -- Step function INLINED (no let binding) to match goal syntax exactly
    (tuples.foldl (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      (x.1 ++ [(encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).1],
        (encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).2)) ([], st')).1.length =
    (tuples.foldl (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      (x.1 ++ [(encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).1],
        (encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).2)) ([], st)).1.length := by
  -- Define step locally for the proof
  let step := fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
    (x.1 ++ [(encodeTupleControl b learners tuple
        (List.map (fun u => FVar.toVar b u.1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).1)
        (List.foldl
          (fun acc p =>
            if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
              (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
            else acc)
          ([], x.2) b.partsL).2).1],
      (encodeTupleControl b learners tuple
        (List.map (fun u => FVar.toVar b u.1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).1)
        (List.foldl
          (fun acc p =>
            if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
              (acc.1 ++ [((encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                (encodeFormula b φ { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
            else acc)
          ([], x.2) b.partsL).2).2)
  change (tuples.foldl step ([], st')).1.length = (tuples.foldl step ([], st)).1.length
  -- Both produce lists of length = tuples.length
  have hLen : ∀ (ts : List (List (Finset b.participants)))
      (acc : List (FVar b) × EncState b),
      (ts.foldl step acc).1.length = acc.1.length + ts.length := by
    intro ts acc
    induction ts generalizing acc with
    | nil => simp
    | cons t ts' ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [step, List.length_append, List.length_singleton]
      ring
  simp only [hLen, List.length_nil, zero_add]

end Encoding
