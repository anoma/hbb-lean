import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Lemmas.DiamondHelpers
import ModalDistribution.Logic.SATEncoding.Lemmas.PredicateHelpers

/-!
# Structural Determinism Lemmas

This file contains the main structural determinism lemmas for formula encoding:

- `encodeFormula_nextFresh_offset`: The encoding adds a deterministic delta to nextFresh
- `encodeFormula_controlVar_shift`: Control variable IDs shift by exactly the state offset
- `encodeFormula_allClauses_true`: Clause satisfaction propagates to prior state

These lemmas are critical for completeness proofs - they show that the encoding is
"structurally deterministic" in that it produces equivalent results from different states.

## Helper Lemmas

This file also contains helper lemmas for event, forall, and past cases:
- Event witness step properties
- Forall fold properties
- Past auxiliary variable fold properties
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}

/-! ## Event Encoding Helpers -/

/-- eventWitnessStep adds exactly 1 to nextFresh.
    This is used for offset preservation proofs. -/
private lemma eventWitnessStep_nextFresh_eq' (b : Bounds S) (acc : List (Var b) × EncState b)
    (pair : Var b × Var b) :
    (eventWitnessStep b acc pair).2.nextFresh = acc.2.nextFresh + 1 := by
  simp only [eventWitnessStep]
  simp only [EncState.addClause, EncState.allocFresh_nextFresh]

/-- The fold of eventWitnessStep adds exactly pairs.length to nextFresh.
    This is the key determinism property for event encoding. -/
lemma foldl_eventWitnessStep_nextFresh_eq' (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b) :
    (pairs.foldl (eventWitnessStep b) acc).2.nextFresh = acc.2.nextFresh + pairs.length := by
  induction pairs generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, eventWitnessStep_nextFresh_eq']
    ring

variable [DecidableEq S.EventType]

/-- encodeFormulaEvent preserves offset: if we start at states differing by offset,
    we end at states also differing by offset.

    This helper lemma is used in the event case of encodeFormula_nextFresh_offset.
    It shows that eventWitnessStep fold + mkBigOrIff add deterministic amounts to nextFresh. -/
lemma encodeFormulaEvent_nextFresh_offset (b : Bounds S) (w : WId b)
    (evt : Signature.EventType S) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (encodeFormulaEvent b w evt st').2.nextFresh =
    (encodeFormulaEvent b w evt st).2.nextFresh + offset := by
  simp only [encodeFormulaEvent]
  -- eventWitnessStep adds exactly 1 per step, so fold adds pairs.length
  have hFoldEq1 : ((eventWitnessPairs b w evt).foldl (eventWitnessStep b) ([], st)).2.nextFresh =
      st.nextFresh + (eventWitnessPairs b w evt).length :=
    foldl_eventWitnessStep_nextFresh_eq' b (eventWitnessPairs b w evt) ([], st)
  have hFoldEq2 : ((eventWitnessPairs b w evt).foldl (eventWitnessStep b) ([], st')).2.nextFresh =
      st'.nextFresh + (eventWitnessPairs b w evt).length :=
    foldl_eventWitnessStep_nextFresh_eq' b (eventWitnessPairs b w evt) ([], st')
  -- mkBigOrIff adds exactly 1
  rw [mkBigOrIff_nextFresh, mkBigOrIff_nextFresh, hFoldEq1, hFoldEq2, hOffset]
  ring

/-! ## Forall Encoding Helpers -/

variable [DecidableEq S.AtomicPredType]
variable [DecidableEq S.Value]

/-- Helper: for a fold with encodeFormula, the .2.nextFresh only depends on acc.2, not acc.1.
    This is because encodeFormula only uses the EncState (acc.2), not the accumulated list. -/
private lemma foldl_encodeFormula_snd_nextFresh_indep
    (b : Bounds S) (body : S.Value → Formula S) (w : WId b)
    (valIndices : List (Fin b.nVals))
    (acc1 acc2 : List (FVar b) × EncState b) (hSnd : acc1.2 = acc2.2) :
    let fold := fun (acc : List (FVar b) × EncState b) (vIdx : Fin b.nVals) =>
      let v := b.values.get vIdx
      let (uBody, stNext) := encodeFormula b (body v) w acc.2
      (acc.1 ++ [uBody], stNext)
    (valIndices.foldl fold acc1).2.nextFresh = (valIndices.foldl fold acc2).2.nextFresh := by
  intro fold
  induction valIndices generalizing acc1 acc2 with
  | nil => simp [hSnd]
  | cons vIdx rest ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [fold, hSnd]

/-- Helper: the encodeFormula fold (as used in forall case) preserves offset.
    If we start at states differing by offset, after the fold they still differ by offset.
    This requires an IH saying encodeFormula on (body v) preserves offset for all v. -/
lemma foldl_encodeFormula_offset
    (b : Bounds S) (body : S.Value → Formula S) (w : WId b)
    (valIndices : List (Fin b.nVals))
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (ih : ∀ (v : S.Value) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b (body v) w st1').2.nextFresh =
        (encodeFormula b (body v) w st1).2.nextFresh + off) :
    let fold := fun (acc : List (FVar b) × EncState b) (vIdx : Fin b.nVals) =>
      let v := b.values.get vIdx
      let (uBody, stNext) := encodeFormula b (body v) w acc.2
      (acc.1 ++ [uBody], stNext)
    (valIndices.foldl fold ([], st')).2.nextFresh =
    (valIndices.foldl fold ([], st)).2.nextFresh + offset := by
  intro fold
  induction valIndices generalizing st st' with
  | nil => simp [hOffset]
  | cons vIdx rest ihFold =>
    simp only [List.foldl_cons]
    have hStep : (fold ([], st') vIdx).2.nextFresh = (fold ([], st) vIdx).2.nextFresh + offset := by
      simp only [fold]
      exact ih (b.values.get vIdx) st st' offset hOffset
    have hIndep1 : (rest.foldl fold (fold ([], st) vIdx)).2.nextFresh =
        (rest.foldl fold ([], (fold ([], st) vIdx).2)).2.nextFresh :=
      foldl_encodeFormula_snd_nextFresh_indep b body w rest
        (fold ([], st) vIdx) ([], (fold ([], st) vIdx).2) rfl
    have hIndep2 : (rest.foldl fold (fold ([], st') vIdx)).2.nextFresh =
        (rest.foldl fold ([], (fold ([], st') vIdx).2)).2.nextFresh :=
      foldl_encodeFormula_snd_nextFresh_indep b body w rest
        (fold ([], st') vIdx) ([], (fold ([], st') vIdx).2) rfl
    rw [hIndep1, hIndep2]
    exact ihFold (fold ([], st) vIdx).2 (fold ([], st') vIdx).2 hStep

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: the outer fold in forall encoding (adding implication clauses) preserves nextFresh.
    This fold only modifies the clauses list, not nextFresh. -/
lemma forall_outer_fold_preserves_nextFresh (b : Bounds S) (u : FVar b)
    (vars : List (FVar b)) (st : EncState b) :
    (vars.foldl (fun stCur uBody =>
      { stCur with clauses :=
        [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)] :: stCur.clauses })
      st).nextFresh = st.nextFresh := by
  induction vars generalizing st with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; exact ih _

/-! ## Past Encoding Helpers -/

/-- Helper: for a fold with encodeFormula over worlds, the .2.nextFresh only depends on acc.2.
    Used in past case to show fold result independence from accumulator's list component. -/
private lemma foldl_encodeFormula_worlds_snd_indep
    (b : Bounds S) (φ : Formula S)
    (worlds : List (WId b))
    (acc1 acc2 : List (FVar b) × EncState b) (hSnd : acc1.2 = acc2.2) :
    let fold := fun (acc : List (FVar b) × EncState b) (w' : WId b) =>
      let (u', stNext) := encodeFormula b φ w' acc.2
      (acc.1 ++ [u'], stNext)
    (worlds.foldl fold acc1).2.nextFresh = (worlds.foldl fold acc2).2.nextFresh := by
  intro fold
  induction worlds generalizing acc1 acc2 with
  | nil => simp [hSnd]
  | cons w' rest ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [fold, hSnd]

/-- Helper: the encodeFormula fold over worlds (as used in past case) preserves offset.
    If we start at states differing by offset, after the fold they still differ by offset.
    This requires an IH saying encodeFormula on φ preserves offset for all worlds. -/
lemma foldl_encodeFormula_worlds_offset
    (b : Bounds S) (φ : Formula S)
    (worlds : List (WId b))
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (ih : ∀ (w : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w st1').2.nextFresh =
        (encodeFormula b φ w st1).2.nextFresh + off) :
    let fold := fun (acc : List (FVar b) × EncState b) (w' : WId b) =>
      let (u', stNext) := encodeFormula b φ w' acc.2
      (acc.1 ++ [u'], stNext)
    (worlds.foldl fold ([], st')).2.nextFresh =
    (worlds.foldl fold ([], st)).2.nextFresh + offset := by
  intro fold
  induction worlds generalizing st st' with
  | nil => simp [hOffset]
  | cons w' rest ihFold =>
    simp only [List.foldl_cons]
    have hStep : (fold ([], st') w').2.nextFresh = (fold ([], st) w').2.nextFresh + offset := by
      simp only [fold]
      exact ih w' st st' offset hOffset
    have hIndep1 : (rest.foldl fold (fold ([], st) w')).2.nextFresh =
        (rest.foldl fold ([], (fold ([], st) w').2)).2.nextFresh :=
      foldl_encodeFormula_worlds_snd_indep b φ rest
        (fold ([], st) w') ([], (fold ([], st) w').2) rfl
    have hIndep2 : (rest.foldl fold (fold ([], st') w')).2.nextFresh =
        (rest.foldl fold ([], (fold ([], st') w').2)).2.nextFresh :=
      foldl_encodeFormula_worlds_snd_indep b φ rest
        (fold ([], st') w') ([], (fold ([], st') w').2) rfl
    rw [hIndep1, hIndep2]
    exact ihFold (fold ([], st) w').2 (fold ([], st') w').2 hStep

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: auxVars fold (in past case) only depends on acc.2 for its .2 output. -/
private lemma past_auxVars_fold_snd_indep (b : Bounds S) (u : FVar b) (ti : b.times)
    (pairs : List (FVar b × WId b))
    (acc1 acc2 : List (FVar b) × EncState b) (hSnd : acc1.2 = acc2.2) :
    let auxStep := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (u', w') := pair
      let memVar := Var.Mem ti w'
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
          SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
          SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
      (acc.1 ++ [aux], stCur)
    (pairs.foldl auxStep acc1).2.nextFresh = (pairs.foldl auxStep acc2).2.nextFresh := by
  intro auxStep
  induction pairs generalizing acc1 acc2 with
  | nil => simp [hSnd]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [auxStep, hSnd]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: auxVars fold (in past case) adds exactly pairs.length to nextFresh. -/
private lemma past_auxVars_fold_nextFresh_eq (b : Bounds S) (u : FVar b) (ti : b.times)
    (pairs : List (FVar b × WId b)) (st : EncState b) :
    let auxStep := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (u', w') := pair
      let memVar := Var.Mem ti w'
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
          SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
          SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
      (acc.1 ++ [aux], stCur)
    (pairs.foldl auxStep ([], st)).2.nextFresh = st.nextFresh + pairs.length := by
  intro auxStep
  induction pairs generalizing st with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hStepEq : (auxStep ([], st) hd).2.nextFresh = st.nextFresh + 1 := by
      simp only [auxStep, EncState.allocFresh, EncState.addClause]
    have hIndep : (tl.foldl auxStep (auxStep ([], st) hd)).2.nextFresh =
        (tl.foldl auxStep ([], (auxStep ([], st) hd).2)).2.nextFresh :=
      past_auxVars_fold_snd_indep b u ti tl (auxStep ([], st) hd) ([], (auxStep ([], st) hd).2) rfl
    rw [hIndep]
    have hIh := ih (auxStep ([], st) hd).2
    rw [hIh, hStepEq]
    ring

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: auxVars fold (in past case) preserves offset. -/
private lemma past_auxVars_fold_offset (b : Bounds S) (u : FVar b) (ti : b.times)
    (pairs : List (FVar b × WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    let auxStep := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (u', w') := pair
      let memVar := Var.Mem ti w'
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
          SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
          SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
      (acc.1 ++ [aux], stCur)
    (pairs.foldl auxStep ([], st')).2.nextFresh =
    (pairs.foldl auxStep ([], st)).2.nextFresh + offset := by
  intro auxStep
  rw [past_auxVars_fold_nextFresh_eq, past_auxVars_fold_nextFresh_eq, hOffset]
  ring

/-- Helper: the encodeWitnesses fold produces a list of the same length as input.
    Since each step appends exactly one element, output length equals input length. -/
lemma encodeWitnesses_length (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (st : EncState b) :
    let fold := fun (acc : List (FVar b) × EncState b) (w' : WId b) =>
      let (u', stNext) := encodeFormula b φ w' acc.2
      (acc.1 ++ [u'], stNext)
    (witnesses.foldl fold ([], st)).1.length = witnesses.length := by
  intro fold
  have hGeneral : ∀ (acc : List (FVar b) × EncState b),
      (witnesses.foldl fold acc).1.length = acc.1.length + witnesses.length := by
    intro acc
    induction witnesses generalizing acc with
    | nil => simp
    | cons w' rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [fold, List.length_append, List.length_singleton]
      ring
  simp only [hGeneral, List.length_nil, zero_add]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: auxVars fold with different u values and different pairs lists of the same length
    still preserves offset, because only list length matters for nextFresh calculation. -/
lemma past_auxVars_fold_offset_general (b : Bounds S)
    (u u' : FVar b) (ti : b.times)
    (pairs pairs' : List (FVar b × WId b))
    (st st' : EncState b) (offset : Nat)
    (hLen : pairs.length = pairs'.length)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    let auxStepU := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (u_wit, w') := pair
      let memVar := Var.Mem ti w'
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u_wit),
          SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u_wit),
          SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u_wit)]
      (acc.1 ++ [aux], stCur)
    let auxStepU' := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (u_wit, w') := pair
      let memVar := Var.Mem ti w'
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u_wit),
          SAT.Lit.pos (FVar.toVar b u')]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u_wit),
          SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u_wit)]
      (acc.1 ++ [aux], stCur)
    (pairs'.foldl auxStepU' ([], st')).2.nextFresh =
    (pairs.foldl auxStepU ([], st)).2.nextFresh + offset := by
  intro auxStepU auxStepU'
  -- Each fold adds exactly its list length to nextFresh
  have h1 : (pairs.foldl auxStepU ([], st)).2.nextFresh = st.nextFresh + pairs.length := by
    have := past_auxVars_fold_nextFresh_eq b u ti pairs st
    simp only [auxStepU] at this ⊢
    exact this
  have h2 : (pairs'.foldl auxStepU' ([], st')).2.nextFresh = st'.nextFresh + pairs'.length := by
    have := past_auxVars_fold_nextFresh_eq b u' ti pairs' st'
    simp only [auxStepU'] at this ⊢
    exact this
  rw [h1, h2, hOffset, hLen]
  ring

/-! ## Main Structural Determinism Theorems -/

/-- The encoding adds a deterministic delta to nextFresh that depends only on the formula
    structure, not on the starting state.

    This is the key property for structural determinism: if we encode φ at st and st' where
    st'.nextFresh = st.nextFresh + offset, then:
    (encodeFormula b φ w st').2.nextFresh = (encodeFormula b φ w st).2.nextFresh + offset

    Equivalently: the "delta" added is the same regardless of starting state. -/
lemma encodeFormula_nextFresh_offset (b : Bounds S) (φ : Formula S) (w : WId b)
    (st st' : EncState b) (offset : Nat) (hOffset : st'.nextFresh = st.nextFresh + offset) :
    (encodeFormula b φ w st').2.nextFresh = (encodeFormula b φ w st).2.nextFresh + offset := by
  induction φ generalizing w st st' offset with
  | bot =>
    simp only [encodeFormula, EncState.allocFresh, EncState.addClause]
    omega
  | eq v1 v2 =>
    simp only [encodeFormula, EncState.allocFresh, EncState.addClause]
    split <;> simp only [hOffset] <;> ring
  | seq =>
    simp only [encodeFormula, EncState.allocFresh, EncState.addClause]
    omega
  | predicate atom =>
    -- predicate case: mkBigOrIff followed by optional addPreEq + folds
    simp only [encodeFormula]
    -- Work directly with split to handle the dite
    split
    · -- Empty case
      rw [mkBigOrIff_nextFresh, mkBigOrIff_nextFresh, hOffset]; ring
    · -- Non-empty case
      rename_i hNonEmpty
      -- The structure is: mkBigOrIff → addPreEqFrom → addPreEqReflAll → fold1 → fold2
      let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
      let idxs := predIxList b pred
      let literals := idxs.map (fun k => Var.Pred w.p w.ti k)
      -- mkBigOrIff preserves offset
      have hMkBigOrIff : (mkBigOrIff b literals st').2.nextFresh =
          (mkBigOrIff b literals st).2.nextFresh + offset := by
        rw [mkBigOrIff_nextFresh, mkBigOrIff_nextFresh, hOffset]; ring
      -- addPreEqFrom preserves offset
      have hPreEq : (addPreEqFrom b w.ti (mkBigOrIff b literals st').2).nextFresh =
          (addPreEqFrom b w.ti (mkBigOrIff b literals st).2).nextFresh + offset :=
        addPreEqFrom_offset b w.ti _ _ offset hMkBigOrIff
      -- addPreEqReflAll preserves nextFresh
      have hRefl : (addPreEqReflAll b
          (addPreEqFrom b w.ti (mkBigOrIff b literals st').2)).nextFresh =
          (addPreEqReflAll b
            (addPreEqFrom b w.ti (mkBigOrIff b literals st).2)).nextFresh + offset := by
        rw [addPreEqReflAll_nextFresh', addPreEqReflAll_nextFresh']
        exact hPreEq
      -- The nested fold adds backward+forward clauses per iteration
      exact nested_addClause_fold2_offset b idxs w _ _ offset hRefl
  | event atom =>
    simp only [encodeFormula]
    let evt : Signature.EventType S := ⟨atom.sym, atom.args⟩
    -- Split on the match for decodeMaybeEvent
    cases hDecode : b.decodeMaybeEvent w.ei with
    | some e =>
      simp only []
      split
      · -- e = evt case: use encodeFormulaEvent
        exact encodeFormulaEvent_nextFresh_offset b w evt st st' offset hOffset
      · -- e ≠ evt case: allocFresh + addClause
        simp only [EncState.allocFresh, EncState.addClause, hOffset]; ring
    | none =>
      simp only [EncState.allocFresh, EncState.addClause, hOffset]; ring
  | imp φ1 φ2 ih1 ih2 =>
    simp only [encodeFormula]
    -- imp: encode φ1, then φ2, then allocFresh, then addClauses
    -- After encoding φ1 at st: st1.nextFresh = st.nextFresh + delta1
    -- After encoding φ1 at st': st1'.nextFresh = st'.nextFresh + delta1
    --   = st.nextFresh + offset + delta1
    -- So st1'.nextFresh = st1.nextFresh + offset (offset preserved!)
    have hOffset1 : (encodeFormula b φ1 w st').2.nextFresh =
        (encodeFormula b φ1 w st).2.nextFresh + offset := ih1 w st st' offset hOffset
    have hOffset2 : (encodeFormula b φ2 w (encodeFormula b φ1 w st').2).2.nextFresh =
        (encodeFormula b φ2 w (encodeFormula b φ1 w st).2).2.nextFresh + offset :=
      ih2 w (encodeFormula b φ1 w st).2 (encodeFormula b φ1 w st').2 offset hOffset1
    -- allocFresh adds 1 to both, addClause preserves nextFresh
    simp only [EncState.allocFresh, EncState.addClause, hOffset2]
    ring
  | atEnd φ ih =>
    simp only [encodeFormula]
    have hOffset1 : (encodeFormula b φ ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st').2.nextFresh =
        (encodeFormula b φ ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st).2.nextFresh + offset :=
      ih ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st st' offset hOffset
    simp only [EncState.allocFresh, EncState.addClause, hOffset1]
    ring
  | past φ ih =>
    -- past: allocFresh, then fold encodeFormula over witnesses, then fold for aux vars
    -- The proof uses that both sides have the same structural shape:
    -- Each encodes at the same witness worlds, each aux fold runs over same number of pairs
    simp only [encodeFormula, EncState.addClause]
    -- Define witnesses (same for both st and st')
    let witnesses := (WId.allWorlds b).filterMap fun w' => if w'.p = w.p then some w' else none
    -- Define the encode fold function
    let encodeFold := fun (acc : List (FVar b) × EncState b) (w' : WId b) =>
      let (u', stNext) := encodeFormula b φ w' acc.2
      (acc.1 ++ [u'], stNext)
    -- Control variables from allocFresh
    let u := (EncState.allocFresh b st).1
    let u' := (EncState.allocFresh b st').1
    let st1 := (EncState.allocFresh b st).2
    let st1' := (EncState.allocFresh b st').2
    -- After allocFresh
    have hOffset1 : st1'.nextFresh = st1.nextFresh + offset := by
      simp only [st1, st1', EncState.allocFresh_nextFresh, hOffset]; ring
    -- The encodeWitnesses fold preserves offset
    have ihPast : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w' st1').2.nextFresh =
        (encodeFormula b φ w' st1).2.nextFresh + off := fun w' st1 st1' off hOff =>
      ih w' st1 st1' off hOff
    -- Results after encodeWitnesses fold
    let encResult := witnesses.foldl encodeFold ([], st1)
    let encResult' := witnesses.foldl encodeFold ([], st1')
    let witnessVars := encResult.1
    let witnessVars' := encResult'.1
    let st2 := encResult.2
    let st2' := encResult'.2
    have hOffset2 : st2'.nextFresh = st2.nextFresh + offset := by
      simp only [st2, st2', encResult, encResult', encodeFold]
      exact foldl_encodeFormula_worlds_offset b φ witnesses st1 st1' offset hOffset1 ihPast
    -- Both witness lists have the same length as witnesses
    have hWitnessLen : witnessVars.length = witnesses.length := by
      simp only [witnessVars, encResult, encodeFold]
      exact encodeWitnesses_length b φ witnesses st1
    have hWitnessLen' : witnessVars'.length = witnesses.length := by
      simp only [witnessVars', encResult', encodeFold]
      exact encodeWitnesses_length b φ witnesses st1'
    -- Define pairs
    let pairs := witnessVars.zip witnesses
    let pairs' := witnessVars'.zip witnesses
    -- Pairs have the same length
    have hPairsLen : pairs.length = witnesses.length := by
      simp only [pairs, List.length_zip, hWitnessLen, Nat.min_self]
    have hPairsLen' : pairs'.length = witnesses.length := by
      simp only [pairs', List.length_zip, hWitnessLen', Nat.min_self]
    have hPairsEq : pairs.length = pairs'.length := by rw [hPairsLen, hPairsLen']
    -- Use the general auxVars offset lemma
    have hOffset3 := past_auxVars_fold_offset_general b u u' w.ti pairs pairs'
      st2 st2' offset hPairsEq hOffset2
    -- The final addClause preserves nextFresh
    simp only [st2', st2, encResult', encResult, st1', st1, u', u, encodeFold, pairs', pairs,
      witnessVars', witnessVars, witnesses] at hOffset3
    exact hOffset3
  | «forall» body ih =>
    -- forall: allocFresh, then fold encodeFormula over values, then addClause folds
    simp only [encodeFormula, EncState.addClause]
    -- Define the inner fold result for clearer naming
    let inner := (List.finRange b.nVals).foldl (fun x vIdx =>
      (x.1 ++ [(encodeFormula b (body (b.values.get vIdx)) w x.2).1],
        (encodeFormula b (body (b.values.get vIdx)) w x.2).2))
      ([], (EncState.allocFresh b st).2)
    let inner' := (List.finRange b.nVals).foldl (fun x vIdx =>
      (x.1 ++ [(encodeFormula b (body (b.values.get vIdx)) w x.2).1],
        (encodeFormula b (body (b.values.get vIdx)) w x.2).2))
      ([], (EncState.allocFresh b st').2)
    -- The outer fold preserves nextFresh
    have hOuter1 := forall_outer_fold_preserves_nextFresh b
      (EncState.allocFresh b st').1 inner'.1 inner'.2
    have hOuter2 := forall_outer_fold_preserves_nextFresh b
      (EncState.allocFresh b st).1 inner.1 inner.2
    simp only [inner', inner] at hOuter1 hOuter2
    rw [hOuter1, hOuter2]
    -- Now the goal is: inner'.2.nextFresh = inner.2.nextFresh + offset
    have hOffset1 : (EncState.allocFresh b st').2.nextFresh =
        (EncState.allocFresh b st).2.nextFresh + offset := by
      simp only [EncState.allocFresh_nextFresh, hOffset]; ring
    have ihForall : ∀ (v : S.Value) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b (body v) w st1').2.nextFresh =
        (encodeFormula b (body v) w st1).2.nextFresh + off := fun v st1 st1' off hOff =>
      ih v w st1 st1' off hOff
    exact foldl_encodeFormula_offset b body w (List.finRange b.nVals)
      (EncState.allocFresh b st).2 (EncState.allocFresh b st').2 offset hOffset1 ihForall
  | diamond learners φ ih =>
    -- Unfold encodeFormula first
    simp only [encodeFormula]
    -- Define step and tuples AFTER simp to match the goal exactly
    let step := (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      (x.1 ++ [(encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ
                      { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ
                  { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).1],
        (encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ
                      { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ
                  { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
            else acc)
            ([], x.2) b.partsL).2).2))
    let tuples := cartesianProduct (List.map
      (fun ℓ => List.filterMap
        (fun v => match v with
          | Var.MinQ a Q => some Q
          | x => none)
        (Var.allMinQ b (b.findValueIndex ℓ)))
      learners)
    let fold := List.foldl step ([], st) tuples
    let fold' := List.foldl step ([], st') tuples
    -- Use change to convert the goal to use fold and fold'
    change (match fold'.1 with
          | [] =>
            let (u', st'') := EncState.allocFresh b fold'.2
            let st''' := EncState.addClause b st'' [SAT.Lit.pos (FVar.toVar b u')]
            (u', st''')
          | u0 :: us =>
            let res := us.foldl (fun (acc : FVar b × EncState b) u' =>
              let (uAcc, stAcc) := acc
              mkAndIff b uAcc u' stAcc) (u0, fold'.2)
            (res.1, res.2)).2.nextFresh =
         (match fold.1 with
          | [] =>
            let (u', st'') := EncState.allocFresh b fold.2
            let st''' := EncState.addClause b st'' [SAT.Lit.pos (FVar.toVar b u')]
            (u', st''')
          | u0 :: us =>
            let res := us.foldl (fun (acc : FVar b × EncState b) u' =>
              let (uAcc, stAcc) := acc
              mkAndIff b uAcc u' stAcc) (u0, fold.2)
            (res.1, res.2)).2.nextFresh + offset
    -- Get the offset and length properties
    have hOff : fold'.2.nextFresh = fold.2.nextFresh + offset :=
      diamond_outer_fold_offset b φ w learners tuples st st' offset hOffset ih
    have hLen : fold'.1.length = fold.1.length :=
      diamond_outer_fold_length_eq b φ w learners tuples st st'
    -- Use cases to split on the fold results
    cases hf : fold.1 with
    | nil =>
      cases hf' : fold'.1 with
      | nil =>
        simp only [EncState.allocFresh_nextFresh, EncState.addClause]
        omega
      | cons u0' us' =>
        exfalso
        have hContra : ([] : List (FVar b)).length = (u0' :: us').length := by
          calc ([] : List (FVar b)).length
            _ = fold.1.length := by rw [hf]
            _ = fold'.1.length := hLen.symm
            _ = (u0' :: us').length := by rw [hf']
        simp only [List.length_nil, List.length_cons] at hContra
        omega
    | cons u0 us =>
      cases hf' : fold'.1 with
      | nil =>
        exfalso
        have hContra : (u0 :: us).length = ([] : List (FVar b)).length := by
          calc (u0 :: us).length
            _ = fold.1.length := by rw [hf]
            _ = fold'.1.length := hLen.symm
            _ = ([] : List (FVar b)).length := by rw [hf']
        simp only [List.length_nil, List.length_cons] at hContra
        omega
      | cons u0' us' =>
        have hUsLen : us.length = us'.length := by
          have h1 : (u0 :: us).length = fold.1.length := by rw [hf]
          have h2 : fold'.1.length = (u0' :: us').length := by rw [hf']
          simp only [List.length_cons] at h1 h2
          omega
        exact mkAndIff_fold_offset b u0 u0' us us' _ _ offset hUsLen hOff

/-- Corollary: the control variable from encoding at st' is the shifted control var from st.

    This is a key lemma for structural determinism: it shows the control variable's id
    is shifted by exactly the offset between starting states. Combined with
    encodeFormula_nextFresh_offset, this allows us to track how Fresh variable indices
    shift through recursive encoding calls. -/
lemma encodeFormula_controlVar_shift (b : Bounds S) (φ : Formula S) (w : WId b)
    (st st' : EncState b) (hMono : st.nextFresh ≤ st'.nextFresh) :
    (encodeFormula b φ w st').1.id =
      (encodeFormula b φ w st).1.id + (st'.nextFresh - st.nextFresh) := by
  induction φ generalizing w st st' with
  | bot =>
    -- Control var comes from allocFresh at st.nextFresh (resp st'.nextFresh)
    simp only [encodeFormula, EncState.allocFresh]; omega
  | eq _ _ =>
    simp only [encodeFormula, EncState.allocFresh]; omega
  | seq =>
    simp only [encodeFormula, EncState.allocFresh]; omega
  | predicate atom =>
    -- Control var comes from mkBigOrIff which uses allocFresh at st.nextFresh
    simp only [encodeFormula]
    split <;> simp only [mkBigOrIff_fst] <;> omega
  | event atom =>
    simp only [encodeFormula]
    let evt : Signature.EventType S := ⟨atom.sym, atom.args⟩
    cases hDecode : b.decodeMaybeEvent w.ei with
    | some e =>
      simp only []
      split
      · -- encodeFormulaEvent case: control from mkBigOrIff after eventWitnessStep fold
        simp only [encodeFormulaEvent, mkBigOrIff_fst]
        -- Control var ID = fold result's nextFresh
        -- fold adds pairs.length to nextFresh
        have hFold1 : ((eventWitnessPairs b w evt).foldl
            (eventWitnessStep b) ([], st)).2.nextFresh =
            st.nextFresh + (eventWitnessPairs b w evt).length :=
          foldl_eventWitnessStep_nextFresh_eq' b (eventWitnessPairs b w evt) ([], st)
        have hFold2 : ((eventWitnessPairs b w evt).foldl
            (eventWitnessStep b) ([], st')).2.nextFresh =
            st'.nextFresh + (eventWitnessPairs b w evt).length :=
          foldl_eventWitnessStep_nextFresh_eq' b (eventWitnessPairs b w evt) ([], st')
        rw [hFold1, hFold2]; omega
      · simp only [EncState.allocFresh]; omega
    | none =>
      simp only [EncState.allocFresh]; omega
  | imp φ1 φ2 ih1 ih2 =>
    simp only [encodeFormula]
    -- Control var u is allocated after encoding φ1 and φ2
    -- u.id = (encodeFormula φ2 w (encodeFormula φ1 w st).2).2.nextFresh
    have hOffset1 := encodeFormula_nextFresh_offset b φ1 w st st'
        (st'.nextFresh - st.nextFresh) (by omega)
    have hOffset2 := encodeFormula_nextFresh_offset b φ2 w
        (encodeFormula b φ1 w st).2
        (encodeFormula b φ1 w st').2
        (st'.nextFresh - st.nextFresh) hOffset1
    simp only [EncState.allocFresh, hOffset2]
  | atEnd φ ih =>
    simp only [encodeFormula]
    have hOffset1 := encodeFormula_nextFresh_offset b φ
        ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ st st'
        (st'.nextFresh - st.nextFresh) (by omega)
    simp only [EncState.allocFresh, hOffset1]
  | past φ ih =>
    -- past: control var u allocated first at st.nextFresh
    simp only [encodeFormula, EncState.allocFresh]; omega
  | «forall» body ih =>
    -- forall: control var u allocated first at st.nextFresh
    simp only [encodeFormula, EncState.allocFresh]; omega
  | diamond learners φ ih =>
    -- Diamond case: control var comes from match on tupleVars
    -- Use the same pattern as encodeFormula_nextFresh_offset diamond case
    simp only [encodeFormula]
    -- Define step with the EXACT inline form from simp
    let step := (fun (x : List (FVar b) × EncState b) (tuple : List (Finset b.participants)) =>
      (x.1 ++ [(encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ
                      { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ
                  { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
              else acc)
            ([], x.2) b.partsL).2).1],
        (encodeTupleControl b learners tuple
          (List.map (fun u => FVar.toVar b u.1)
            (List.foldl
              (fun acc p =>
                if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                  (acc.1 ++ [((encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                    (encodeFormula b φ
                      { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
                else acc)
              ([], x.2) b.partsL).1)
          (List.foldl
            (fun acc p =>
              if _ : p ∈ List.foldl (fun x1 x2 => x1 ∩ x2) Finset.univ tuple then
                (acc.1 ++ [((encodeFormula b φ
                  { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).1, p)],
                  (encodeFormula b φ
                    { p := p, ei := ⟨0, Nat.zero_lt_succ _⟩, ti := w.ti } acc.2).2)
            else acc)
            ([], x.2) b.partsL).2).2))
    let tuples := cartesianProduct (List.map
      (fun ℓ => List.filterMap
        (fun v => match v with
          | Var.MinQ a Q => some Q
          | x => none)
        (Var.allMinQ b (b.findValueIndex ℓ)))
      learners)
    let fold := List.foldl step ([], st) tuples
    let fold' := List.foldl step ([], st') tuples
    let offset := st'.nextFresh - st.nextFresh
    -- Use change to convert goal to use fold and fold'
    change (match fold'.1 with
          | [] =>
            let (u', st'') := EncState.allocFresh b fold'.2
            let st''' := EncState.addClause b st'' [SAT.Lit.pos (FVar.toVar b u')]
            (u', st''')
          | u0 :: us =>
            let res := us.foldl (fun (acc : FVar b × EncState b) u' =>
              let (uAcc, stAcc) := acc
              mkAndIff b uAcc u' stAcc) (u0, fold'.2)
            (res.1, res.2)).1.id =
         (match fold.1 with
          | [] =>
            let (u', st'') := EncState.allocFresh b fold.2
            let st''' := EncState.addClause b st'' [SAT.Lit.pos (FVar.toVar b u')]
            (u', st''')
          | u0 :: us =>
            let res := us.foldl (fun (acc : FVar b × EncState b) u' =>
              let (uAcc, stAcc) := acc
              mkAndIff b uAcc u' stAcc) (u0, fold.2)
            (res.1, res.2)).1.id + offset
    -- Key facts
    -- Note: diamond_outer_fold_offset needs ih about nextFresh, not controlVar
    have ih_offset : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
        st1'.nextFresh = st1.nextFresh + off →
        (encodeFormula b φ w' st1').2.nextFresh =
        (encodeFormula b φ w' st1).2.nextFresh + off := by
      intro w' st1 st1' off hOff'
      exact encodeFormula_nextFresh_offset b φ w' st1 st1' off hOff'
    have hOff : fold'.2.nextFresh = fold.2.nextFresh + offset :=
      diamond_outer_fold_offset b φ w learners tuples st st' offset (by omega) ih_offset
    have hLen : fold'.1.length = fold.1.length :=
      diamond_outer_fold_length_eq b φ w learners tuples st st'
    -- Case split on fold.1
    cases hf : fold.1 with
    | nil =>
      cases hf' : fold'.1 with
      | nil =>
        simp only [EncState.allocFresh, hOff]
      | cons u0' us' =>
        -- Contradiction: lengths don't match
        have : (u0' :: us').length = ([] : List (FVar b)).length := by
          calc (u0' :: us').length = fold'.1.length := by rw [hf']
            _ = fold.1.length := hLen
            _ = ([] : List (FVar b)).length := by rw [hf]
        simp at this
    | cons u0 us =>
      cases hf' : fold'.1 with
      | nil =>
        -- Contradiction: lengths don't match
        have : ([] : List (FVar b)).length = (u0 :: us).length := by
          calc ([] : List (FVar b)).length = fold'.1.length := by rw [hf']
            _ = fold.1.length := hLen
            _ = (u0 :: us).length := by rw [hf]
        simp at this
      | cons u0' us' =>
        -- Both non-empty: control from mkAndIff fold
        have hUsLen : us'.length = us.length := by
          have h1 : (u0' :: us').length = fold'.1.length := by rw [hf']
          have h2 : fold'.1.length = fold.1.length := hLen
          have h3 : fold.1.length = (u0 :: us).length := by rw [hf]
          simp only [List.length_cons] at h1 h3
          omega
        cases hus : us with
        | nil =>
          -- Singleton case: control is u0 (resp u0')
          have hus' : us' = [] := List.length_eq_zero_iff.mp (by rw [hUsLen, hus]; simp)
          simp only [hus', List.foldl_nil]
          -- Connect step to diamondStep
          have hStepEq : step = diamondStep b learners φ w :=
            encodeFormula_diamond_step_unfolded_eq b learners φ w
          have hFoldEq : fold = tuples.foldl (diamondStep b learners φ w) ([], st) := by
            simp only [fold, hStepEq]
          have hFold'Eq : fold' = tuples.foldl (diamondStep b learners φ w) ([], st') := by
            simp only [fold', hStepEq]
          -- Get characterization of u0
          have hfSingleton : fold.1 = [u0] := by simp only [hf, hus]
          have hSingleton : (tuples.foldl (diamondStep b learners φ w) ([], st)).1 = [u0] := by
            rw [← hFoldEq]; exact hfSingleton
          obtain ⟨tuple, hTuples, hu0⟩ :=
            diamondStep_foldl_singleton_characterization b learners φ w tuples st u0 hSingleton
          -- Get characterization of u0'
          have hf'Singleton : fold'.1 = [u0'] := by simp only [hf', hus']
          have hSingleton' : (tuples.foldl (diamondStep b learners φ w) ([], st')).1 = [u0'] := by
            rw [← hFold'Eq]; exact hf'Singleton
          rw [hTuples] at hSingleton'
          simp only [List.foldl_cons, List.foldl_nil] at hSingleton'
          have hu0'_form := diamondStep_nil_fst_eq b learners φ w tuple st'
          rw [hu0'_form] at hSingleton'
          simp only [List.cons.injEq, and_true] at hSingleton'
          -- Now u0 = encodeTupleControl... and hSingleton' : encodeTupleControl... = u0'
          rw [hu0, ← hSingleton']
          -- Apply diamondStep_foldl_singleton_id_shift
          have ih_offset : ∀ (w' : WId b) (st1 st1' : EncState b) (off : Nat),
              st1'.nextFresh = st1.nextFresh + off →
              (encodeFormula b φ w' st1').2.nextFresh =
              (encodeFormula b φ w' st1).2.nextFresh + off := by
            intro w' st1 st1' off hOff'
            exact encodeFormula_nextFresh_offset b φ w' st1 st1' off hOff'
          exact diamondStep_foldl_singleton_id_shift b learners φ w tuple st st' offset
            (by omega) ih_offset
        | cons v vs =>
          -- Multiple elements: control from mkAndIff fold
          have hPos : 0 < (v :: vs).length := by simp
          have hus' : ∃ v' vs', us' = v' :: vs' ∧ vs'.length = vs.length := by
            have h : us'.length = (v :: vs).length := by rw [hUsLen, hus]
            cases hus'' : us' with
            | nil =>
              rw [hus''] at h
              simp only [List.length_nil, List.length_cons] at h
              exact absurd h (by omega)
            | cons v' vs' =>
              rw [hus''] at h
              simp only [List.length_cons] at h
              exact ⟨v', vs', rfl, by omega⟩
          obtain ⟨v', vs', hus'', hVsLen⟩ := hus'
          simp only [hus'']
          exact mkAndIff_fold_fst_id_shift_pos b u0 u0' (v :: vs) (v' :: vs') fold.2 fold'.2
            offset (by simp [hVsLen]) hPos hOff

/-- If the encoded state's clauses all evaluate to true, so do the prior state's clauses. -/
lemma encodeFormula_allClauses_true (b : Bounds S)
    (φ : Formula S) (w : WId b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hAll : (encodeFormula b φ w st).2.clauses.all (SAT.Clause.eval σ) = true) :
    st.clauses.all (SAT.Clause.eval σ) = true :=
  all_true_of_subset (encodeFormula_clauses_subset b φ w st) hAll

end Encoding
