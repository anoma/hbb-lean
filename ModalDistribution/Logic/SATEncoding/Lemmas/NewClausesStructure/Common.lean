import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.ClausePreservation
import ModalDistribution.Logic.SATEncoding.Lemmas.Basic
import ModalDistribution.Logic.SATEncoding.Lemmas.WellFormedness
import ModalDistribution.Logic.SATEncoding.Lemmas.FreshVarBounds
import ModalDistribution.Logic.SATEncoding.Lemmas.EventWitnessStep
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinPred

/-!
# Common Helpers for New Clauses Structural Lemmas

This file contains shared helper lemmas used by the structural determinism
proofs for individual formula constructors.

## Main Content

- `nonFreshClausesCompat` preservation lemmas for encoding folds
- Fresh variable presence lemmas for new clauses
- Clause set independence lemmas
- `encodeFormula_preserves_nonFreshCompat`: Main compatibility theorem

These helpers are used by per-constructor structural determinism files.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}

/-! ## Generic List Lemmas -/

/-- Two lists with the same length and pointwise equal evaluations have equal `any` results. -/
lemma List.any_eq_of_get_eq {α β : Type*} (l1 : List α) (l2 : List β) (p : α → Bool) (q : β → Bool)
    (hLen : l1.length = l2.length)
    (h : ∀ i (hi1 : i < l1.length) (hi2 : i < l2.length), p (l1.get ⟨i, hi1⟩) = q (l2.get ⟨i, hi2⟩)) :
    l1.any p = l2.any q := by
  induction l1 generalizing l2 with
  | nil =>
    simp only [List.length_nil] at hLen
    simp [List.length_eq_zero_iff.mp hLen.symm]
  | cons a as ih =>
    match l2 with
    | [] => simp at hLen
    | b :: bs =>
      simp only [List.any_cons]
      have hLenAs : as.length = bs.length := by simp at hLen; omega
      have hHead := h 0 (by simp) (by simp)
      simp at hHead
      have hTail : ∀ i (hi1 : i < as.length) (hi2 : i < bs.length),
          p (as.get ⟨i, hi1⟩) = q (bs.get ⟨i, hi2⟩) := by
        intro i hi1 hi2
        have := h (i+1) (by simp; omega) (by simp; omega)
        simp at this
        exact this
      rw [hHead, ih bs hLenAs hTail]

/-! ## Helper lemmas for nonFreshClausesCompat preservation -/


/-- Helper: all vars in eventWitnessStep fold result starting from init are Fresh
    or in init. -/
lemma foldl_eventWitnessStep_witnessVars_are_fresh_aux (b : Bounds S)
    (pairs : List (Var b × Var b)) (init : List (Var b)) (st : EncState b)
    (v : Var b) (hv : v ∈ (pairs.foldl (eventWitnessStep b) (init, st)).1) :
    v ∈ init ∨ ∃ n, v = Var.Fresh n := by
  induction pairs generalizing init st v with
  | nil => simp only [List.foldl_nil] at hv; exact Or.inl hv
  | cons hd tl ih =>
      simp only [List.foldl_cons] at hv
      have hStep : (eventWitnessStep b (init, st) hd).1 = init ++ [Var.Fresh st.nextFresh] := by
        simp only [eventWitnessStep, FVar.toVar, EncState.allocFresh]
      have hFromTail := ih (init ++ [Var.Fresh st.nextFresh])
        (eventWitnessStep b (init, st) hd).2 v
        (by rw [← hStep]; exact hv)
      rcases hFromTail with hIn | hEx
      · simp only [List.mem_append, List.mem_singleton] at hIn
        rcases hIn with hInit | hNew
        · exact Or.inl hInit
        · exact Or.inr ⟨st.nextFresh, hNew⟩
      · exact Or.inr hEx

/-- All vars produced by eventWitnessStep fold (starting from []) are Fresh. -/
lemma foldl_eventWitnessStep_witnessVars_are_fresh (b : Bounds S)
    (pairs : List (Var b × Var b)) (st : EncState b)
    (v : Var b) (hv : v ∈ (pairs.foldl (eventWitnessStep b) ([], st)).1) :
    ∃ n, v = Var.Fresh n := by
  have h := foldl_eventWitnessStep_witnessVars_are_fresh_aux b pairs [] st v hv
  simp at h
  exact h

/-- Every new clause from eventWitnessStep contains Fresh z.
    The 3 clauses are [neg z, pos preEq], [neg z, pos mem], [neg preEq, neg mem, pos z]. -/
lemma eventWitnessStep_newClause_contains_fresh (b : Bounds S) (acc : List (Var b) × EncState b)
    (pair : Var b × Var b) (c : SAT.Clause (Var b))
    (hcNew : c ∈ (eventWitnessStep b acc pair).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  simp only [eventWitnessStep, EncState.addClause, List.mem_cons] at hcNew
  -- After simp, hcNew is a disjunction of 4 cases
  let z := (EncState.allocFresh b acc.2).1
  have hAllocEq : (EncState.allocFresh b acc.2).2.clauses = acc.2.clauses :=
    EncState.allocFresh_clauses_eq (b := b) acc.2
  rcases hcNew with hc3 | hc2 | hc1 | hcOld
  · -- c = [neg preEq, neg mem, pos z]
    subst hc3
    exact ⟨SAT.Lit.pos (FVar.toVar b z), List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
           z.id, by simp [FVar.toVar, SAT.Lit.getVar]⟩
  · -- c = [neg z, pos mem]
    subst hc2
    exact ⟨SAT.Lit.neg (FVar.toVar b z), List.Mem.head _,
           z.id, by simp [FVar.toVar, SAT.Lit.getVar]⟩
  · -- c = [neg z, pos preEq]
    subst hc1
    exact ⟨SAT.Lit.neg (FVar.toVar b z), List.Mem.head _,
           z.id, by simp [FVar.toVar, SAT.Lit.getVar]⟩
  · -- c ∈ acc.2.clauses - contradicts hcNotOld
    rw [hAllocEq] at hcOld
    exact absurd hcOld hcNotOld

/-- New clauses from eventWitnessStep fold all contain Fresh vars. -/
lemma foldl_eventWitnessStep_newClause_contains_fresh (b : Bounds S)
    (pairs : List (Var b × Var b)) (acc : List (Var b) × EncState b)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (pairs.foldl (eventWitnessStep b) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  induction pairs generalizing acc c with
  | nil => simp only [List.foldl_nil] at hcNew; exact absurd hcNew hcNotOld
  | cons hd tl ih =>
      simp only [List.foldl_cons] at hcNew
      by_cases hcStep : c ∈ (eventWitnessStep b acc hd).2.clauses
      · by_cases hcAcc : c ∈ acc.2.clauses
        · exact absurd hcAcc hcNotOld
        · exact eventWitnessStep_newClause_contains_fresh b acc hd c hcStep hcAcc
      · exact ih (eventWitnessStep b acc hd) c hcNew hcStep

/-- Helper: auxStep adds 4 clauses, each containing Fresh aux. -/
lemma auxVars_step_newClause_has_fresh (b : Bounds S) (w : WId b) (u : FVar b)
    (acc : List (FVar b) × EncState b) (uv : FVar b) (wv : WId b)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (let memVar := Var.Mem w.ti wv
                  let (aux, stCur) := EncState.allocFresh b acc.2
                  let stCur := EncState.addClause b stCur
                    [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv),
                      SAT.Lit.pos (FVar.toVar b u)]
                  let stCur := EncState.addClause b stCur
                    [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv),
                      SAT.Lit.pos (FVar.toVar b aux)]
                  let stCur := EncState.addClause b stCur
                    [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
                  let stCur := EncState.addClause b stCur
                    [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
                  (acc.1 ++ [aux], stCur)).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  let aux := (EncState.allocFresh b acc.2).1
  have hAllocEq : (EncState.allocFresh b acc.2).2.clauses = acc.2.clauses :=
    EncState.allocFresh_clauses_eq (b := b) acc.2
  simp only [EncState.addClause, List.mem_cons] at hcNew
  rcases hcNew with hc4 | hc3 | hc2 | hc1 | hcOld
  · -- c = [neg aux, pos uv] (4th clause) - has aux Fresh
    subst hc4
    exact ⟨SAT.Lit.neg (FVar.toVar b aux), List.Mem.head _,
           aux.id, by simp [FVar.toVar, SAT.Lit.getVar]⟩
  · -- c = [neg aux, pos Mem] (3rd clause) - has aux Fresh
    subst hc3
    exact ⟨SAT.Lit.neg (FVar.toVar b aux), List.Mem.head _,
           aux.id, by simp [FVar.toVar, SAT.Lit.getVar]⟩
  · -- c = [neg Mem, neg uv, pos aux] (2nd clause) - has aux Fresh
    subst hc2
    exact ⟨SAT.Lit.pos (FVar.toVar b aux), List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
           aux.id, by simp [FVar.toVar, SAT.Lit.getVar]⟩
  · -- c = [neg Mem, neg uv, pos u] (1st clause) - has u Fresh
    subst hc1
    exact ⟨SAT.Lit.pos (FVar.toVar b u), List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
           u.id, by simp [FVar.toVar, SAT.Lit.getVar]⟩
  · -- c ∈ acc.2.clauses - contradicts hcNotOld
    rw [hAllocEq] at hcOld
    exact absurd hcOld hcNotOld

/-- New clauses from auxVars fold (used in past encoding) contain Fresh vars. -/
lemma foldl_auxVars_step_newClause_has_fresh (b : Bounds S) (w : WId b) (u : FVar b)
    (pairs : List (FVar b × WId b)) (acc : List (FVar b) × EncState b)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (pairs.foldl (fun (accL, stCur) (uv, wv) =>
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b stCur
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv),
          SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv),
          SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (accL ++ [aux], stCur)) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  induction pairs generalizing acc c with
  | nil => simp only [List.foldl_nil] at hcNew; exact absurd hcNew hcNotOld
  | cons hd tl ih =>
      simp only [List.foldl_cons] at hcNew
      let step := fun (accPair : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
        let accL := accPair.1
        let stCur := accPair.2
        let uv := pair.1
        let wv := pair.2
        let memVar := Var.Mem w.ti wv
        let (aux, stCur') := EncState.allocFresh b stCur
        let stCur' := EncState.addClause b stCur'
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
        let stCur' := EncState.addClause b stCur'
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
        let stCur' := EncState.addClause b stCur'
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
        let stCur' := EncState.addClause b stCur'
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
        (accL ++ [aux], stCur')
      by_cases hcStep : c ∈ (step acc hd).2.clauses
      · by_cases hcAcc : c ∈ acc.2.clauses
        · exact absurd hcAcc hcNotOld
        · exact auxVars_step_newClause_has_fresh b w u acc hd.1 hd.2 c hcStep hcAcc
      · exact ih (step acc hd) c hcNew hcStep

/-- Helper: new clauses from bodyVars.foldl in forall encoding have Fresh u. -/
lemma forall_bodyVars_foldl_newClause_has_fresh (b : Bounds S) (u : FVar b)
    (bodyVars : List (FVar b)) (st : EncState b) (c : SAT.Clause (Var b))
    (hcNew : c ∈ (bodyVars.foldl (fun stCur uBody =>
        EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]) st).clauses)
    (hcNotOld : c ∉ st.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  induction bodyVars generalizing st with
  | nil => simp only [List.foldl_nil] at hcNew; exact absurd hcNew hcNotOld
  | cons bhd btl ih =>
      simp only [List.foldl_cons] at hcNew
      let stStep := EncState.addClause b st
        [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b bhd)]
      by_cases hcStep : c ∈ stStep.clauses
      · simp only [] at hcStep
        cases hcStep with
        | head =>
            -- c = [neg u, pos bhd] - has Fresh u
            exact ⟨SAT.Lit.neg (FVar.toVar b u), List.Mem.head _,
                   u.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
        | tail _ hcInOld => exact absurd hcInOld hcNotOld
      · exact ih stStep hcNew hcStep

/-! ## Diamond Case Helper Lemmas -/

/-- mkAndIff new clauses contain Fresh vars.
    mkAndIff adds 3 clauses: [neg u, pos x], [neg u, pos y], [neg x, neg y, pos u]
    where u is the newly allocated Fresh var (id = st.nextFresh). -/
lemma mkAndIff_newClause_has_fresh (b : Bounds S) (x y : FVar b) (st : EncState b)
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (mkAndIff b x y st).2.clauses)
    (hcNotOld : c ∉ st.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  simp only [mkAndIff] at hcNew
  rcases hAlloc : EncState.allocFresh b st with ⟨u, stU⟩
  simp only [hAlloc] at hcNew
  have hStUEq : stU.clauses = st.clauses := by
    have h := EncState.allocFresh_clauses_eq (b := b) st
    simp only [hAlloc] at h; exact h
  simp only [EncState.addClause, List.mem_cons] at hcNew
  rcases hcNew with hc3 | hc2 | hc1 | hcOld
  · -- c = [neg x, neg y, pos u] - has Fresh u
    subst hc3
    exact ⟨SAT.Lit.pos (FVar.toVar b u), List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
           u.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
  · -- c = [neg u, pos y] - has Fresh u
    subst hc2
    exact ⟨SAT.Lit.neg (FVar.toVar b u), List.Mem.head _,
           u.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
  · -- c = [neg u, pos x] - has Fresh u
    subst hc1
    exact ⟨SAT.Lit.neg (FVar.toVar b u), List.Mem.head _,
           u.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
  · -- c ∈ st.clauses - contradicts hcNotOld
    rw [hStUEq] at hcOld
    exact absurd hcOld hcNotOld

/-- mkAndIff fold new clauses contain Fresh vars.
    Each mkAndIff in the fold allocates a Fresh var and adds clauses containing it. -/
lemma mkAndIff_foldl_newClause_has_fresh (b : Bounds S) (us : List (FVar b))
    (acc : FVar b × EncState b) (c : SAT.Clause (Var b))
    (hcNew : c ∈ (us.foldl (fun acc' u' => mkAndIff b acc'.1 u' acc'.2) acc).2.clauses)
    (hcNotOld : c ∉ acc.2.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  induction us generalizing acc with
  | nil => simp only [List.foldl_nil] at hcNew; exact absurd hcNew hcNotOld
  | cons u' us' ih =>
      simp only [List.foldl_cons] at hcNew
      let step := mkAndIff b acc.1 u' acc.2
      by_cases hcStep : c ∈ step.2.clauses
      · by_cases hcAcc : c ∈ acc.2.clauses
        · exact absurd hcAcc hcNotOld
        · exact mkAndIff_newClause_has_fresh b acc.1 u' acc.2 c hcStep hcAcc
      · exact ih step hcNew hcStep

/-! ### Helper lemmas for individual formula cases -/

/-! ## Clause Shift Compatibility -/

/-- Shift Fresh variable indices in a literal by offset. Non-Fresh vars unchanged. -/
def shiftLitFresh (b : Bounds S) (offset : Nat) (lit : SAT.Lit (Var b)) : SAT.Lit (Var b) :=
  match lit with
  | SAT.Lit.pos (Var.Fresh n) => SAT.Lit.pos (Var.Fresh (n + offset))
  | SAT.Lit.neg (Var.Fresh n) => SAT.Lit.neg (Var.Fresh (n + offset))
  | other => other

/-- shiftLitFresh preserves non-Fresh literals. -/
lemma shiftLitFresh_non_fresh (b : Bounds S) (offset : Nat) (lit : SAT.Lit (Var b))
    (hNotFresh : ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n) :
    shiftLitFresh b offset lit = lit := by
  cases lit with
  | pos v =>
      cases v with
      | Fresh n => exact absurd rfl (hNotFresh n)
      | _ => simp [shiftLitFresh]
  | neg v =>
      cases v with
      | Fresh n => exact absurd rfl (hNotFresh n)
      | _ => simp [shiftLitFresh]

/-- shiftLitFresh on pos Fresh adds offset. -/
@[simp]
lemma shiftLitFresh_pos_fresh (b : Bounds S) (offset n : Nat) :
    shiftLitFresh b offset (SAT.Lit.pos (Var.Fresh n)) = SAT.Lit.pos (Var.Fresh (n + offset)) :=
  rfl

/-- shiftLitFresh on neg Fresh adds offset. -/
@[simp]
lemma shiftLitFresh_neg_fresh (b : Bounds S) (offset n : Nat) :
    shiftLitFresh b offset (SAT.Lit.neg (Var.Fresh n)) = SAT.Lit.neg (Var.Fresh (n + offset)) :=
  rfl

/-- Clause shift compatibility: all clauses in st map to clauses in st'. -/
def clauseShiftCompat (b : Bounds S) (st st' : EncState b) (offset : Nat) : Prop :=
  ∀ c ∈ st.clauses, c.map (shiftLitFresh b offset) ∈ st'.clauses

/-- Clause with no Fresh vars maps to itself under shiftLitFresh. -/
lemma shiftClause_nonFresh (b : Bounds S) (offset : Nat) (c : SAT.Clause (Var b))
    (hNoFresh : ∀ lit ∈ c, ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n) :
    c.map (shiftLitFresh b offset) = c := by
  induction c with
  | nil => simp [List.map]
  | cons hd tl ih =>
      have hHd : ∀ n, SAT.Lit.getVar hd ≠ Var.Fresh n := fun n =>
        hNoFresh hd (List.Mem.head tl) n
      have hTl : ∀ lit ∈ tl, ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n := fun lit hLit n =>
        hNoFresh lit (List.Mem.tail hd hLit) n
      simp only [List.map]
      rw [shiftLitFresh_non_fresh b offset hd hHd, ih hTl]

/-- Helper: auxVars fold preserves clause shift compatibility.

    The auxVars fold adds gadget clauses for each (witnessVar, witness) pair.
    If the input states have clause shift compat, and the pairs/u vars have
    the correct offset relationship, then the output states have clause shift compat.

    Key preconditions:
    - u'.id = u.id + offset (control vars are offset)
    - pairs and pairs' have same length
    - For each i: pairs'[i].1.id = pairs[i].1.id + offset and pairs'[i].2 = pairs[i].2
-/
lemma auxVars_foldl_preserves_clauseShiftCompat (b : Bounds S) (w : WId b)
    (u u' : FVar b) (pairs pairs' : List (FVar b × WId b))
    (stAcc stAcc' : EncState b) (offset : Nat)
    (hOffset : stAcc'.nextFresh = stAcc.nextFresh + offset)
    (hCompat : clauseShiftCompat b stAcc stAcc' offset)
    (hUOff : u'.id = u.id + offset)
    (hLen : pairs.length = pairs'.length)
    (hPairsOff : ∀ i (hi : i < pairs.length) (hi' : i < pairs'.length),
        (pairs.get ⟨i, hi⟩).1.id + offset = (pairs'.get ⟨i, hi'⟩).1.id ∧
        (pairs.get ⟨i, hi⟩).2 = (pairs'.get ⟨i, hi'⟩).2) :
    let auxStep := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (uv, wv) := pair
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (acc.1 ++ [aux], stCur)
    let auxStep' := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (uv, wv) := pair
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u')]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (acc.1 ++ [aux], stCur)
    clauseShiftCompat b
      (pairs.foldl auxStep ([], stAcc)).2 (pairs'.foldl auxStep' ([], stAcc')).2 offset := by
  intro auxStep auxStep' c hc
  -- Induction on pairs/pairs' with parallel structure
  suffices hSuff : ∀ (ps : List (FVar b × WId b)) (ps' : List (FVar b × WId b))
      (acc : List (FVar b) × EncState b) (acc' : List (FVar b) × EncState b),
      ps.length = ps'.length →
      acc'.2.nextFresh = acc.2.nextFresh + offset →
      clauseShiftCompat b acc.2 acc'.2 offset →
      (∀ i (hi : i < ps.length) (hi' : i < ps'.length),
          (ps.get ⟨i, hi⟩).1.id + offset = (ps'.get ⟨i, hi'⟩).1.id ∧
          (ps.get ⟨i, hi⟩).2 = (ps'.get ⟨i, hi'⟩).2) →
      clauseShiftCompat b (ps.foldl auxStep acc).2 (ps'.foldl auxStep' acc').2 offset by
    exact hSuff pairs pairs' ([], stAcc) ([], stAcc') hLen hOffset hCompat hPairsOff c hc

  intro ps
  induction ps with
  | nil =>
    intro ps' acc acc' hLenEq _ hAccCompat _ c' hc'
    have hPs'Nil : ps' = [] := List.length_eq_zero_iff.mp (hLenEq.symm ▸ rfl)
    simp only [hPs'Nil, List.foldl_nil] at hc' ⊢
    exact hAccCompat c' hc'
  | cons p pTail ihTail =>
    intro ps' acc acc' hLenEq hAccOff hAccCompat hPsOff c' hc'
    match ps' with
    | [] => simp only [List.length_nil, List.length_cons, Nat.succ_ne_zero] at hLenEq
    | p' :: p'Tail =>
      simp only [List.length_cons, Nat.succ.injEq] at hLenEq
      simp only [List.foldl_cons] at hc'

      -- Get correspondence for first element
      have hP0 := hPsOff 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      have hUvOff : p.1.id + offset = p'.1.id := hP0.1
      have hWvEq : p.2 = p'.2 := hP0.2

      -- Compute one step
      let accNext := auxStep acc p
      let accNext' := auxStep' acc' p'

      -- aux vars have offset relationship
      have hAuxOff : (EncState.allocFresh b acc.2).1.id + offset =
          (EncState.allocFresh b acc'.2).1.id := by
        simp only [EncState.allocFresh, hAccOff]

      -- Step preserves offset
      have hStepOff : accNext'.2.nextFresh = accNext.2.nextFresh + offset := by
        simp only [accNext, accNext', auxStep, auxStep', EncState.addClause, EncState.allocFresh,
                   hAccOff]
        ring

      -- Step preserves clause shift compat
      have hStepCompat : clauseShiftCompat b accNext.2 accNext'.2 offset := by
        intro c'' hc''
        simp only [accNext, accNext', auxStep, auxStep', EncState.addClause,
          List.mem_cons] at hc'' ⊢
        -- c'' is one of the 4 gadget clauses or from acc.2
        rcases hc'' with hC4 | hC3 | hC2 | hC1 | hOld
        · -- c'' = [neg aux, pos uv] (4th clause)
          left
          subst hC4
          simp only [List.map_cons, List.map_nil, shiftLitFresh, FVar.toVar, EncState.allocFresh,
                     hAccOff.symm, hUvOff]
        · -- c'' = [neg aux, pos Mem] (3rd clause)
          right; left
          subst hC3
          simp only [List.map_cons, List.map_nil, shiftLitFresh, FVar.toVar, EncState.allocFresh,
                     hAccOff.symm, hWvEq]
        · -- c'' = [neg Mem, neg uv, pos aux] (2nd clause)
          right; right; left
          subst hC2
          simp only [List.map_cons, List.map_nil, shiftLitFresh, FVar.toVar, EncState.allocFresh,
                     hAccOff.symm, hUvOff, hWvEq]
        · -- c'' = [neg Mem, neg uv, pos u] (1st clause)
          right; right; right; left
          subst hC1
          simp only [List.map_cons, List.map_nil, shiftLitFresh, FVar.toVar,
                     hUOff, hUvOff, hWvEq]
        · -- c'' ∈ acc.2.clauses
          right; right; right; right
          simp only [EncState.allocFresh] at hOld
          exact hAccCompat c'' hOld

      -- Tail pairs offset
      have hTailOff : ∀ i (hi : i < pTail.length) (hi' : i < p'Tail.length),
          (pTail.get ⟨i, hi⟩).1.id + offset = (p'Tail.get ⟨i, hi'⟩).1.id ∧
          (pTail.get ⟨i, hi⟩).2 = (p'Tail.get ⟨i, hi'⟩).2 := by
        intro i hi hi'
        have := hPsOff (i + 1) (Nat.add_lt_add_right hi 1) (Nat.add_lt_add_right hi' 1)
        simp only [List.get_cons_succ] at this
        exact this

      exact ihTail p'Tail accNext accNext' hLenEq hStepOff hStepCompat hTailOff c' hc'


/-- mkBigOrIff preserves clause shift compat when input vars are all non-Fresh.
    This is used for the predicate encoding where vs are all Pred vars. -/
lemma mkBigOrIff_preserves_clauseShiftCompat (b : Bounds S)
    (vs : List (Var b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset)
    (hNonFresh : ∀ v ∈ vs, ∀ n, v ≠ Var.Fresh n) :
    clauseShiftCompat b (mkBigOrIff b vs st).2 (mkBigOrIff b vs st').2 offset := by
  intro c hc
  -- Use mkBigOrIff_clause_mem_iff to characterize c
  rw [mkBigOrIff_clause_mem_iff] at hc
  rcases hc with hBase | ⟨v, hv, hEq⟩ | hLong
  · -- c from base state st
    have hShifted := hCompat c hBase
    rw [mkBigOrIff_clause_mem_iff]
    left
    exact hShifted
  · -- c = [neg v, pos u] for some v ∈ vs (forward clause)
    subst hEq
    rw [mkBigOrIff_clause_mem_iff]
    right; left
    use v, hv
    -- Show shifted clause equals expected
    simp only [List.map_cons, List.map_nil]
    have hVNotFresh := hNonFresh v hv
    -- For non-Fresh vars, shiftLitFresh is identity on neg
    have hShiftNeg : shiftLitFresh b offset (SAT.Lit.neg v) = SAT.Lit.neg v := by
      cases v <;> first | (exfalso; exact hVNotFresh _ rfl) | rfl
    -- The Fresh var in allocFresh shifts
    have hShiftPos : shiftLitFresh b offset (SAT.Lit.pos (FVar.toVar b (mkBigOrIff b vs st).1)) =
        SAT.Lit.pos (FVar.toVar b (mkBigOrIff b vs st').1) := by
      have hFst := mkBigOrIff_fst b vs st
      have hFst' := mkBigOrIff_fst b vs st'
      simp only [FVar.toVar, hFst, hFst', shiftLitFresh, hOffset]
    rw [hShiftNeg, hShiftPos]
  · -- c = [neg u, pos v₁, ..., pos vₙ] (backward/long clause)
    subst hLong
    rw [mkBigOrIff_clause_mem_iff]
    right; right
    simp only [List.map_cons, List.cons.injEq]
    have hFst := mkBigOrIff_fst b vs st
    have hFst' := mkBigOrIff_fst b vs st'
    constructor
    · -- neg u shifts to neg u'
      simp only [FVar.toVar, hFst, hFst', shiftLitFresh, hOffset]
    · -- vs.map pos is unchanged
      rw [List.map_map]
      apply List.map_congr_left
      intro v hvMem
      have hVNotFresh := hNonFresh v hvMem
      cases v <;> first | (exfalso; exact hVNotFresh _ rfl) | rfl

/-- Helper: addClause with non-Fresh clause preserves clauseShiftCompat. -/
lemma addClause_nonFresh_preserves_clauseShiftCompat (b : Bounds S)
    (c : SAT.Clause (Var b)) (st st' : EncState b) (offset : Nat)
    (hCompat : clauseShiftCompat b st st' offset)
    (hNonFresh : ∀ lit ∈ c, ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n) :
    clauseShiftCompat b (EncState.addClause b st c) (EncState.addClause b st' c) offset := by
  intro c' hc'
  simp only [EncState.addClause, List.mem_cons] at hc' ⊢
  cases hc' with
  | inl hEq =>
      left
      rw [hEq, shiftClause_nonFresh b offset c hNonFresh]
  | inr hOld =>
      right
      exact hCompat c' hOld

/-- Shift Fresh variable indices in a variable by offset. Non-Fresh vars unchanged. -/
def shiftVarFresh (b : Bounds S) (offset : Nat) (v : Var b) : Var b :=
  match v with
  | Var.Fresh n => Var.Fresh (n + offset)
  | other => other

/-- shiftLitFresh relates to shiftVarFresh: shift of pos v = pos (shift v). -/
@[simp]
lemma shiftLitFresh_pos (b : Bounds S) (offset : Nat) (v : Var b) :
    shiftLitFresh b offset (SAT.Lit.pos v) = SAT.Lit.pos (shiftVarFresh b offset v) := by
  cases v <;> simp [shiftLitFresh, shiftVarFresh]

/-- shiftLitFresh relates to shiftVarFresh: shift of neg v = neg (shift v). -/
@[simp]
lemma shiftLitFresh_neg (b : Bounds S) (offset : Nat) (v : Var b) :
    shiftLitFresh b offset (SAT.Lit.neg v) = SAT.Lit.neg (shiftVarFresh b offset v) := by
  cases v <;> simp [shiftLitFresh, shiftVarFresh]

/-- Helper: mkY fold nextFresh offset is preserved. -/
lemma mkY_foldl_nextFresh_offset (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    let step := fun (acc : List (Var b) × EncState b) w' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w' st''
      (FVar.toVar b y :: vs, st''')
    (cands.foldl step ([], st')).2.nextFresh =
      (cands.foldl step ([], st)).2.nextFresh + offset := by
  intro step
  -- Use a generalized induction
  suffices h : ∀ (initVs initVs' : List (Var b)) (initSt initSt' : EncState b),
      initSt'.nextFresh = initSt.nextFresh + offset →
      (cands.foldl step (initVs', initSt')).2.nextFresh =
        (cands.foldl step (initVs, initSt)).2.nextFresh + offset by
    exact h [] [] st st' hOffset
  intro initVs initVs' initSt initSt' hInitOff
  induction cands generalizing initVs initVs' initSt initSt' with
  | nil => simp only [List.foldl_nil, hInitOff]
  | cons w' wTail ih =>
    simp only [List.foldl_cons, step]
    have hMkYOff : (mkY b t' w w' initSt').2.nextFresh =
        (mkY b t' w w' initSt).2.nextFresh + offset := by
      have hN := mkY_nextFresh b t' w w' initSt
      have hN' := mkY_nextFresh b t' w w' initSt'
      omega
    exact ih _ _ _ _ hMkYOff

/-- Helper: mkY fold fst list lengths are equal. -/
lemma mkY_foldl_fst_length_eq (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st st' : EncState b) :
    let step := fun (acc : List (Var b) × EncState b) w' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w' st''
      (FVar.toVar b y :: vs, st''')
    (cands.foldl step ([], st)).1.length = (cands.foldl step ([], st')).1.length :=
  mkDw_fold_length_eq b t' w cands st st'

/-- Helper: all vars in mkY fold result are Fresh (i.e., exist as FVar.toVar). -/
lemma mkY_foldl_all_fresh (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st : EncState b) :
    let step := fun (acc : List (Var b) × EncState b) w' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w' st''
      (FVar.toVar b y :: vs, st''')
    ∀ (i : Nat) (hi : i < (cands.foldl step ([], st)).1.length),
      ∃ y : FVar b, (cands.foldl step ([], st)).1.get ⟨i, hi⟩ = FVar.toVar b y := by
  intro step
  -- By induction, all elements of the fst are FVar.toVar
  suffices h : ∀ init : List (Var b) × EncState b,
      (∀ j (hj : j < init.1.length), ∃ y, init.1.get ⟨j, hj⟩ = FVar.toVar b y) →
      ∀ j (hj : j < (cands.foldl step init).1.length),
        ∃ y, (cands.foldl step init).1.get ⟨j, hj⟩ = FVar.toVar b y by
    exact h ([], st) (fun j hj => by simp only [List.length_nil] at hj; omega)
  intro init hInit j hj
  induction cands generalizing init with
  | nil => exact hInit j hj
  | cons w' wTail ih =>
    simp only [List.foldl_cons, step] at hj ⊢
    apply ih
    intro k hk
    simp only [List.length_cons] at hk
    match k with
    | 0 =>
      exact ⟨(mkY b t' w w' init.2).1, rfl⟩
    | k' + 1 =>
      simp only [List.get_cons_succ]
      have hk' : k' < init.1.length := by omega
      exact hInit k' hk'

/-- Helper: mkY preserves clauseShiftCompat.
    mkY allocates y and adds 3 clauses with Fresh var y at st.nextFresh. -/
lemma mkY_preserves_clauseShiftCompat (b : Bounds S) (t' : b.times) (w w' : WId b)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset) :
    clauseShiftCompat b (mkY b t' w w' st).2 (mkY b t' w w' st').2 offset := by
  intro c hc
  have hYOff : (mkY b t' w w' st').1.id = (mkY b t' w w' st).1.id + offset := by
    have hY := mkY_fst_id b t' w w' st
    have hY' := mkY_fst_id b t' w w' st'
    simp only [hY, hY', hOffset]
  -- Unfold mkY to get at the clause structure directly
  simp only [mkY, EncState.allocFresh, EncState.addClause, List.mem_cons] at hc ⊢
  -- hc : c = c1 ∨ c = c2 ∨ c = c3 ∨ c ∈ st.clauses
  rcases hc with h1 | h2 | h3 | hOld
  · -- Clause 1: [neg (Mem t' w'), neg (PreEq w.ti w'.ti), pos y]
    left
    rw [h1]
    simp only [FVar.toVar, shiftLitFresh_neg, shiftLitFresh_pos, shiftVarFresh,
      List.map_cons, List.map_nil, ← hOffset]
  · -- Clause 2: [neg y, pos (PreEq w.ti w'.ti)]
    right; left
    rw [h2]
    simp only [FVar.toVar, shiftLitFresh_neg, shiftLitFresh_pos, shiftVarFresh,
      List.map_cons, List.map_nil, ← hOffset]
  · -- Clause 3: [neg y, pos (Mem t' w')]
    right; right; left
    rw [h3]
    simp only [FVar.toVar, shiftLitFresh_neg, shiftLitFresh_pos, shiftVarFresh,
      List.map_cons, List.map_nil, ← hOffset]
  · -- Inherited from st
    right; right; right
    exact hCompat c hOld


/-- Helper: mkY fold preserves clauseShiftCompat with shifted ys list. -/
lemma mkY_foldl_preserves_clauseShiftCompat (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset) :
    let step := fun (acc : List (Var b) × EncState b) w' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w' st''
      (FVar.toVar b y :: vs, st''')
    clauseShiftCompat b
      (cands.foldl step ([], st)).2
      (cands.foldl step ([], st')).2 offset := by
  intro step
  -- Use generalized induction to handle arbitrary accumulators
  suffices h : ∀ (initVs initVs' : List (Var b)) (initSt initSt' : EncState b),
      initSt'.nextFresh = initSt.nextFresh + offset →
      clauseShiftCompat b initSt initSt' offset →
      clauseShiftCompat b
        (cands.foldl step (initVs, initSt)).2
        (cands.foldl step (initVs', initSt')).2 offset by
    exact h [] [] st st' hOffset hCompat
  intro initVs initVs' initSt initSt' hInitOff hInitCompat
  induction cands generalizing initVs initVs' initSt initSt' with
  | nil =>
    simp only [List.foldl_nil]
    exact hInitCompat
  | cons w' wTail ih =>
    simp only [List.foldl_cons, step]
    have hMkYOff : (mkY b t' w w' initSt').2.nextFresh =
        (mkY b t' w w' initSt).2.nextFresh + offset := by
      have hN := mkY_nextFresh b t' w w' initSt
      have hN' := mkY_nextFresh b t' w w' initSt'
      omega
    have hMkYCompat := mkY_preserves_clauseShiftCompat b t' w w' initSt initSt' offset
      hInitOff hInitCompat
    exact ih _ _ _ _ hMkYOff hMkYCompat

/-- Helper: mkBigOrIff preserves clauseShiftCompat with shifted vs list.
    Unlike mkBigOrIff_preserves_clauseShiftCompat, this handles Fresh vars in vs. -/
lemma mkBigOrIff_preserves_clauseShiftCompat_shifted (b : Bounds S)
    (vs vs' : List (Var b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset)
    (hLen : vs.length = vs'.length)
    (hVsShift : ∀ i (hi : i < vs.length),
        shiftVarFresh b offset (vs.get ⟨i, hi⟩) = vs'.get ⟨i, hLen ▸ hi⟩) :
    clauseShiftCompat b (mkBigOrIff b vs st).2 (mkBigOrIff b vs' st').2 offset := by
  intro c hc
  rw [mkBigOrIff_clause_mem_iff] at hc ⊢
  have hUOff : (mkBigOrIff b vs' st').1.id = (mkBigOrIff b vs st).1.id + offset := by
    have hFst := mkBigOrIff_fst b vs st
    have hFst' := mkBigOrIff_fst b vs' st'
    simp only [hFst, hFst', hOffset]
  obtain hBase | ⟨v, hv, hEq⟩ | hLong := hc
  · -- c from base state st
    left
    exact hCompat c hBase
  · -- c = [neg v, pos u] for some v ∈ vs (forward clause)
    right; left
    rw [hEq]
    -- Find the shifted v in vs'
    rcases List.mem_iff_getElem?.mp hv with ⟨i, hi⟩
    have hiLen : i < vs.length := List.getElem?_eq_some_iff.mp hi |>.1
    have hGetV : vs[i] = v := List.getElem?_eq_some_iff.mp hi |>.2
    use vs'.get ⟨i, hLen ▸ hiLen⟩
    constructor
    · exact List.get_mem vs' ⟨i, hLen ▸ hiLen⟩
    · simp only [List.map_cons, List.map_nil]
      have hShiftV := hVsShift i hiLen
      simp only [List.get_eq_getElem, hGetV] at hShiftV
      simp only [List.get_eq_getElem, shiftLitFresh_neg, shiftLitFresh_pos_fresh,
        hShiftV, FVar.toVar, hUOff]
  · -- c = [neg u, pos v₁, ..., pos vₙ] (backward/long clause)
    right; right
    rw [hLong]
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · simp only [FVar.toVar, shiftLitFresh_neg_fresh, hUOff]
    · -- Show shifted vs.map pos = vs'.map pos
      rw [List.map_map]
      apply List.ext_getElem
      · simp only [List.length_map, hLen]
      · intro i hi hi'
        simp only [List.length_map] at hi
        simp only [List.getElem_map, Function.comp_apply]
        have hShiftV := hVsShift i hi
        simp only [List.get_eq_getElem] at hShiftV
        simp only [shiftLitFresh_pos, hShiftV]


/-- Helper: mkOw preserves clauseShiftCompat.
    mkOw allocates o and adds 3 clauses with Fresh vars o and d. -/
lemma mkOw_preserves_clauseShiftCompat (b : Bounds S) (t : b.times) (w : WId b)
    (d d' : FVar b) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset)
    (hDOff : d'.id = d.id + offset) :
    clauseShiftCompat b (mkOw b t w d st).2 (mkOw b t w d' st').2 offset := by
  intro c hc
  -- mkOw adds 3 clauses, then we have inherited clauses
  simp only [mkOw, EncState.allocFresh, EncState.addClause, List.mem_cons] at hc ⊢
  -- o.id = st.nextFresh, o'.id = st'.nextFresh = st.nextFresh + offset
  have hOOff : st'.nextFresh = st.nextFresh + offset := hOffset
  rcases hc with hC3 | hC2 | hC1 | hOld
  · -- c = [pos o, neg d] (third clause)
    left
    subst hC3
    simp only [List.map_cons, List.map_nil, FVar.toVar,
      shiftLitFresh_pos_fresh, shiftLitFresh_neg_fresh, hOOff, hDOff]
  · -- c = [pos o, pos (Mem t w)] (second clause)
    right; left
    subst hC2
    simp only [List.map_cons, List.map_nil, FVar.toVar,
      shiftLitFresh_pos_fresh, hOOff]
    -- Mem t w is non-Fresh
    rfl
  · -- c = [neg o, neg (Mem t w), pos d] (first clause)
    right; right; left
    subst hC1
    simp only [List.map_cons, List.map_nil, FVar.toVar,
      shiftLitFresh_neg_fresh, shiftLitFresh_pos_fresh, hOOff, hDOff]
    -- Mem t w is non-Fresh
    rfl
  · -- c from st.clauses (inherited)
    right; right; right
    exact hCompat c hOld

/-- Helper: The state (.2) of eventWitnessStep fold is independent of the list accumulator (.1). -/
lemma eventWitnessStep_foldl_state_indep (b : Bounds S)
    (pairs : List (Var b × Var b)) (lst : List (Var b)) (stIn : EncState b) :
    (pairs.foldl (eventWitnessStep b) (lst, stIn)).2 =
    (pairs.foldl (eventWitnessStep b) ([], stIn)).2 := by
  induction pairs generalizing lst stIn with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hStepEq : (eventWitnessStep b (lst, stIn) p).2 =
        (eventWitnessStep b ([], stIn) p).2 := by
      simp only [eventWitnessStep, EncState.allocFresh, EncState.addClause]
    let stNext := (eventWitnessStep b ([], stIn) p).2
    calc (ps.foldl (eventWitnessStep b) (eventWitnessStep b (lst, stIn) p)).2
        = (ps.foldl (eventWitnessStep b) ([], (eventWitnessStep b (lst, stIn) p).2)).2 := ih _ _
      _ = (ps.foldl (eventWitnessStep b) ([], stNext)).2 := by rw [hStepEq]
      _ = (ps.foldl (eventWitnessStep b) (eventWitnessStep b ([], stIn) p)).2 := (ih _ _).symm


/-- Helper: eventWitnessStep fold preserves clauseShiftCompat. -/
lemma eventWitnessStep_foldl_preserves_clauseShiftCompat (b : Bounds S)
    (pairs : List (Var b × Var b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset)
    (hNonFresh : ∀ p ∈ pairs, ∀ n, p.1 ≠ Var.Fresh n ∧ p.2 ≠ Var.Fresh n) :
    clauseShiftCompat b
      (pairs.foldl (eventWitnessStep b) ([], st)).2
      (pairs.foldl (eventWitnessStep b) ([], st')).2 offset := by
  revert st st' hOffset hCompat
  induction pairs with
  | nil =>
    intro st st' hOffset hCompat
    simp only [List.foldl_nil]
    exact hCompat
  | cons pair pairsTail ih =>
    intro st st' hOffset hCompat
    simp only [List.foldl_cons]
    -- eventWitnessStep adds 3 clauses with Fresh z
    have hPairMem : pair ∈ (pair :: pairsTail) := List.mem_cons_self
    have hPairNF : ∀ n, pair.1 ≠ Var.Fresh n ∧ pair.2 ≠ Var.Fresh n := fun n =>
      hNonFresh pair hPairMem n
    have hTailNF : ∀ p ∈ pairsTail, ∀ n, p.1 ≠ Var.Fresh n ∧ p.2 ≠ Var.Fresh n :=
      fun p hp n => hNonFresh p (List.mem_cons_of_mem _ hp) n
    -- Define intermediate states after one step
    let step := eventWitnessStep b ([], st) pair
    let step' := eventWitnessStep b ([], st') pair
    -- Offset is preserved after one step
    have hOff1 : step'.2.nextFresh = step.2.nextFresh + offset := by
      simp only [step, step', eventWitnessStep, EncState.allocFresh, EncState.addClause, hOffset]
      ring
    -- Show clauseShiftCompat after one step
    have hComp1 : clauseShiftCompat b step.2 step'.2 offset := by
      intro c hc
      simp only [step, step', eventWitnessStep, EncState.allocFresh, EncState.addClause,
        List.mem_cons] at hc ⊢
      -- z.id = st.nextFresh, z'.id = st'.nextFresh = st.nextFresh + offset
      have hZOff : st'.nextFresh = st.nextFresh + offset := hOffset
      -- Helper: non-Fresh literals shift to themselves
      have hShiftNeg1 : shiftLitFresh b offset (SAT.Lit.neg pair.1) = SAT.Lit.neg pair.1 :=
        shiftLitFresh_non_fresh b offset (SAT.Lit.neg pair.1)
          (fun m => by simp only [SAT.Lit.getVar]; exact (hPairNF m).1)
      have hShiftNeg2 : shiftLitFresh b offset (SAT.Lit.neg pair.2) = SAT.Lit.neg pair.2 :=
        shiftLitFresh_non_fresh b offset (SAT.Lit.neg pair.2)
          (fun m => by simp only [SAT.Lit.getVar]; exact (hPairNF m).2)
      have hShiftPos1 : shiftLitFresh b offset (SAT.Lit.pos pair.1) = SAT.Lit.pos pair.1 :=
        shiftLitFresh_non_fresh b offset (SAT.Lit.pos pair.1)
          (fun m => by simp only [SAT.Lit.getVar]; exact (hPairNF m).1)
      have hShiftPos2 : shiftLitFresh b offset (SAT.Lit.pos pair.2) = SAT.Lit.pos pair.2 :=
        shiftLitFresh_non_fresh b offset (SAT.Lit.pos pair.2)
          (fun m => by simp only [SAT.Lit.getVar]; exact (hPairNF m).2)
      rcases hc with hC3 | hC2 | hC1 | hOld
      · -- c = [neg preEq, neg mem, pos z] (third clause)
        left
        subst hC3
        simp only [List.map_cons, List.map_nil, FVar.toVar,
          shiftLitFresh_pos_fresh, hZOff, hShiftNeg1, hShiftNeg2]
      · -- c = [neg z, pos mem] (second clause)
        right; left
        subst hC2
        simp only [List.map_cons, List.map_nil, FVar.toVar,
          shiftLitFresh_neg_fresh, hZOff, hShiftPos2]
      · -- c = [neg z, pos preEq] (first clause)
        right; right; left
        subst hC1
        simp only [List.map_cons, List.map_nil, FVar.toVar,
          shiftLitFresh_neg_fresh, hZOff, hShiftPos1]
      · -- c from st.clauses (inherited)
        right; right; right
        exact hCompat c hOld
    -- Apply IH - use the state independence lemma
    have hGoal1 : (pairsTail.foldl (eventWitnessStep b) step).2 =
        (pairsTail.foldl (eventWitnessStep b) ([], step.2)).2 :=
      eventWitnessStep_foldl_state_indep b pairsTail step.1 step.2
    have hGoal2 : (pairsTail.foldl (eventWitnessStep b) step').2 =
        (pairsTail.foldl (eventWitnessStep b) ([], step'.2)).2 :=
      eventWitnessStep_foldl_state_indep b pairsTail step'.1 step'.2
    rw [hGoal1, hGoal2]
    exact ih hTailNF step.2 step'.2 hOff1 hComp1

variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]
variable [DecidableEq S.Value]

/-- New clauses from event encoding have at least one Fresh literal.
    eventWitnessStep adds clauses containing Fresh z, mkBigOrIff adds clauses with Fresh u. -/
lemma encodeFormula_event_newClause_has_fresh (b : Bounds S) (atom : EventAtom S) (w : WId b)
    (st : EncState b) (c : SAT.Clause (Var b))
    (hcNew : c ∈ (encodeFormula b (Formula.event atom) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  simp only [encodeFormula] at hcNew
  split at hcNew
  · -- MaybeEvent.some e
    rename_i e hDecode
    split at hcNew
    · -- e = evt: encodeFormulaEvent case
      simp only [encodeFormulaEvent] at hcNew
      let witnessPairs := eventWitnessPairs b w ⟨atom.sym, atom.args⟩
      let stFold := (witnessPairs.foldl (eventWitnessStep b) ([], st)).2
      let witnessVars := (witnessPairs.foldl (eventWitnessStep b) ([], st)).1
      -- Check if c is from eventWitnessStep fold or from mkBigOrIff
      by_cases hcFold : c ∈ stFold.clauses
      · -- c from eventWitnessStep fold
        by_cases hcSt : c ∈ st.clauses
        · exact absurd hcSt hcNotOld
        · exact foldl_eventWitnessStep_newClause_contains_fresh b witnessPairs
            ([], st) c hcFold hcSt
      · -- c from mkBigOrIff - uses witnessVars (Fresh) or u (Fresh)
        have hVars := mkBigOrIff_newClause_vars b witnessVars stFold c hcNew hcFold
        -- Get any lit from c (c must be non-empty since it's from mkBigOrIff)
        have hNE : c ≠ [] := by
          intro hEmpty; subst hEmpty
          -- mkBigOrIff doesn't add empty clauses
          simp only [mkBigOrIff, EncState.addClause, EncState.allocFresh, List.mem_cons] at hcNew
          rcases hcNew with hLong | hInFold
          · exact List.cons_ne_nil _ _ hLong.symm
          · -- fold only adds non-empty clauses [neg v, pos u]
            -- Helper: characterize clauses in any foldl result
            let u := FVar.toVar b (EncState.allocFresh b stFold).1
            let f : EncState b → Var b → EncState b :=
              fun acc v => EncState.addClause b acc [SAT.Lit.neg v, SAT.Lit.pos u]
            have hCharacterize : ∀ (vs : List (Var b)) (st' : EncState b) c,
                c ∈ (vs.foldl f st').clauses →
                c ∈ st'.clauses ∨ ∃ v ∈ vs, c = [SAT.Lit.neg v, SAT.Lit.pos u] := by
              intro vs
              induction vs with
              | nil => intro st' c hc; left; exact hc
              | cons hd tl ih =>
                  intro st' c hc
                  simp only [List.foldl_cons, f, EncState.addClause] at hc
                  rcases ih _ c hc with hBase | ⟨v, hv, hEq⟩
                  · simp only [List.mem_cons] at hBase
                    rcases hBase with hNew | hOld
                    · right; exact ⟨hd, List.Mem.head _, hNew⟩
                    · left; exact hOld
                  · right; exact ⟨v, List.Mem.tail _ hv, hEq⟩
            have hResult := hCharacterize witnessVars (EncState.allocFresh b stFold).2 [] hInFold
            rcases hResult with hBase | ⟨_, _, hEq⟩
            · -- [] ∈ (allocFresh stFold).clauses = stFold.clauses
              have hAllocClauses : (EncState.allocFresh b stFold).2.clauses = stFold.clauses :=
                EncState.allocFresh_clauses_eq (b := b) stFold
              rw [hAllocClauses] at hBase
              exact hcFold hBase
            · -- [] = [neg v, pos u] - contradiction
              exact List.cons_ne_nil _ _ hEq.symm
        obtain ⟨lit, hLit⟩ := List.exists_mem_of_ne_nil c hNE
        rcases hVars lit hLit with hIsU | hInWitness
        · -- lit.getVar = u (Fresh)
          have hUId : (mkBigOrIff b witnessVars stFold).1.id = stFold.nextFresh :=
            by simp [mkBigOrIff_fst]
          refine ⟨lit, hLit, stFold.nextFresh, ?_⟩
          simp only [FVar.toVar] at hIsU
          rw [← hUId]; exact hIsU
        · -- lit.getVar ∈ witnessVars (all Fresh)
          obtain ⟨n, hEqFresh⟩ := foldl_eventWitnessStep_witnessVars_are_fresh b
            witnessPairs st lit.getVar hInWitness
          exact ⟨lit, hLit, n, hEqFresh⟩
    · -- e ≠ evt: guard fails, adds [neg u] where u = Fresh
      simp only [EncState.addClause, EncState.allocFresh, List.mem_cons] at hcNew
      rcases hcNew with hEq | hTail
      · -- c = [neg (Fresh st.nextFresh)]
        subst hEq
        exact ⟨SAT.Lit.neg (Var.Fresh st.nextFresh), List.Mem.head _, st.nextFresh, rfl⟩
      · exact absurd hTail hcNotOld
  · -- MaybeEvent.none: guard fails, adds [neg u] where u = Fresh
    simp only [EncState.addClause, EncState.allocFresh, List.mem_cons] at hcNew
    rcases hcNew with hEq | hTail
    · -- c = [neg (Fresh st.nextFresh)]
      subst hEq
      exact ⟨SAT.Lit.neg (Var.Fresh st.nextFresh), List.Mem.head _, st.nextFresh, rfl⟩
    · exact absurd hTail hcNotOld

/-- Helper: witnessVars from encodeWitnesses fold are Fresh.
    This is trivially true since encodeFormula always returns a Fresh variable. -/
lemma encodeWitnesses_foldl_witnessVars_are_fresh (b : Bounds S) (φ : Formula S)
    (ws : List (WId b)) (st : EncState b) (v : FVar b)
    (_ : v ∈ (ws.foldl (fun (uvars, stCur) w' =>
      let res := encodeFormula b φ w' stCur
      (uvars ++ [res.1], res.2)) ([], st)).1) :
    ∃ n, FVar.toVar b v = Var.Fresh n := by
  -- Every encodeFormula result is Fresh, so any v in the fold is Fresh
  exact ⟨v.id, by simp [FVar.toVar]⟩



/-- Helper: The clause set from encodeWitnesses fold only depends on the state, not
    the accumulator's first component (the list of control vars). -/
lemma encodeWitnesses_foldl_clauses_indep (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (acc1 acc2 : List (FVar b) × EncState b)
    (hSnd : acc1.2 = acc2.2) :
    (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) acc1).2.clauses =
    (witnesses.foldl (fun (uvars, stCur) w' =>
        let (u', stNext) := encodeFormula b φ w' stCur
        (uvars ++ [u'], stNext)) acc2).2.clauses := by
  induction witnesses generalizing acc1 acc2 with
  | nil => simp only [List.foldl_nil, hSnd]
  | cons w' ws ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [hSnd]

/-- Helper: track clause source in encodeWitnesses fold (generalized over initial list). -/
lemma encodeWitnesses_foldl_newClause_from_recursive_aux (b : Bounds S) (φ : Formula S)
    (ws : List (WId b)) (init : List (FVar b)) (st : EncState b) (c : SAT.Clause (Var b))
    (hcNew : c ∈ (ws.foldl (fun (uvars, stCur) w' =>
      let res := encodeFormula b φ w' stCur
      (uvars ++ [res.1], res.2)) (init, st)).2.clauses)
    (hcNotOld : c ∉ st.clauses) :
    ∃ w' ∈ ws, ∃ stPrev, c ∈ (encodeFormula b φ w' stPrev).2.clauses ∧ c ∉ stPrev.clauses := by
  induction ws generalizing init st with
  | nil => simp only [List.foldl_nil] at hcNew; exact absurd hcNew hcNotOld
  | cons whd wtl wih =>
      simp only [List.foldl_cons] at hcNew
      let res := encodeFormula b φ whd st
      by_cases hcRes : c ∈ res.2.clauses
      · by_cases hcSt : c ∈ st.clauses
        · exact absurd hcSt hcNotOld
        · exact ⟨whd, List.Mem.head _, st, hcRes, hcSt⟩
      · have hFromTail := wih (init ++ [res.1]) res.2 hcNew hcRes
        obtain ⟨w', hw', stPrev, hcEnc, hcNotPrev⟩ := hFromTail
        exact ⟨w', List.Mem.tail _ hw', stPrev, hcEnc, hcNotPrev⟩

/-- Helper: track clause source in encodeWitnesses fold. -/
lemma encodeWitnesses_foldl_newClause_from_recursive (b : Bounds S) (φ : Formula S)
    (ws : List (WId b)) (st : EncState b) (c : SAT.Clause (Var b))
    (hcNew : c ∈ (ws.foldl (fun (uvars, stCur) w' =>
      let res := encodeFormula b φ w' stCur
      (uvars ++ [res.1], res.2)) ([], st)).2.clauses)
    (hcNotOld : c ∉ st.clauses) :
    ∃ w' ∈ ws, ∃ stPrev, c ∈ (encodeFormula b φ w' stPrev).2.clauses ∧ c ∉ stPrev.clauses :=
  encodeWitnesses_foldl_newClause_from_recursive_aux b φ ws [] st c hcNew hcNotOld

/-- Helper: nonFreshClausesCompat is preserved through encodeWitnesses fold.
    If non-Fresh clauses from stAcc are in stAcc', and we apply the fold,
    then non-Fresh clauses in the result from stAcc are in the result from stAcc'. -/
lemma encodeWitnesses_foldl_preserves_nonFreshCompat (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (stAcc stAcc' : EncState b)
    (hCompat : nonFreshClausesCompat stAcc stAcc')
    (hIH : ∀ w' st st', nonFreshClausesCompat st st' →
           nonFreshClausesCompat (encodeFormula b φ w' st).2 (encodeFormula b φ w' st').2) :
    nonFreshClausesCompat
      (witnesses.foldl (fun (uvars, stCur) w' =>
        let res := encodeFormula b φ w' stCur
        (uvars ++ [res.1], res.2)) ([], stAcc)).2
      (witnesses.foldl (fun (uvars, stCur) w' =>
        let res := encodeFormula b φ w' stCur
        (uvars ++ [res.1], res.2)) ([], stAcc')).2 := by
  -- Use clause set independence: fold result clauses depend only on the EncState
  -- Transform using encodeWitnesses_foldl_clauses_indep to work with ([], stAcc) form
  intro c hc hNoFresh
  induction witnesses generalizing stAcc stAcc' c with
  | nil =>
      simp only [List.foldl_nil] at hc ⊢
      exact hCompat c hc hNoFresh
  | cons whd wtl wih =>
      simp only [List.foldl_cons] at hc ⊢
      let st1 := (encodeFormula b φ whd stAcc).2
      let st1' := (encodeFormula b φ whd stAcc').2
      have hCompat1 : nonFreshClausesCompat st1 st1' := hIH whd stAcc stAcc' hCompat
      -- Use clause independence to relate different accumulator lists
      have hIndep1 := encodeWitnesses_foldl_clauses_indep b φ wtl
        ([(encodeFormula b φ whd stAcc).1], st1) ([], st1) rfl
      have hIndep2 := encodeWitnesses_foldl_clauses_indep b φ wtl
        ([(encodeFormula b φ whd stAcc').1], st1') ([], st1') rfl
      -- c is in the fold result starting from ([(...)], st1)
      -- By independence, same clauses as fold starting from ([], st1)
      have hcInEmptyStart : c ∈ (wtl.foldl (fun (uvars, stCur) w' =>
          let res := encodeFormula b φ w' stCur
          (uvars ++ [res.1], res.2)) ([], st1)).2.clauses := hIndep1 ▸ hc
      -- Apply IH
      have hRes := wih st1 st1' hCompat1 c hcInEmptyStart hNoFresh
      -- Transform back using membership equality
      exact hIndep2 ▸ hRes

/-- Helper: clause set from encodeConj fold only depends on EncState, not list accumulator. -/
lemma encodeConj_foldl_clauses_indep (b : Bounds S) (body : S.Value → Formula S)
    (w : WId b) (valIndices : List b.valIx) (acc1 acc2 : List (FVar b) × EncState b)
    (hSnd : acc1.2 = acc2.2) :
    (valIndices.foldl (fun (vars, stCur) vIdx =>
        let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
        (vars ++ [uBody], stNext)) acc1).2.clauses =
    (valIndices.foldl (fun (vars, stCur) vIdx =>
        let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
        (vars ++ [uBody], stNext)) acc2).2.clauses := by
  induction valIndices generalizing acc1 acc2 with
  | nil => simp only [List.foldl_nil, hSnd]
  | cons vhd vtl ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [hSnd]

/-- Helper: nonFreshClausesCompat is preserved through encodeConj fold (forall encoding).
    Similar to encodeWitnesses_foldl_preserves_nonFreshCompat. -/
lemma encodeConj_foldl_preserves_nonFreshCompat (b : Bounds S) (body : S.Value → Formula S)
    (w : WId b) (valIndices : List b.valIx) (stAcc stAcc' : EncState b)
    (hCompat : nonFreshClausesCompat stAcc stAcc')
    (hIH : ∀ v stX stX', nonFreshClausesCompat stX stX' →
           nonFreshClausesCompat (encodeFormula b (body v) w stX).2
             (encodeFormula b (body v) w stX').2) :
    nonFreshClausesCompat
      (valIndices.foldl (fun (vars, stCur) vIdx =>
        let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
        (vars ++ [uBody], stNext)) ([], stAcc)).2
      (valIndices.foldl (fun (vars, stCur) vIdx =>
        let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
        (vars ++ [uBody], stNext)) ([], stAcc')).2 := by
  intro c hc hNoFresh
  induction valIndices generalizing stAcc stAcc' c with
  | nil =>
      simp only [List.foldl_nil] at hc ⊢
      exact hCompat c hc hNoFresh
  | cons vhd vtl vih =>
      simp only [List.foldl_cons] at hc ⊢
      let v := b.values.get vhd
      let st1 := (encodeFormula b (body v) w stAcc).2
      let st1' := (encodeFormula b (body v) w stAcc').2
      have hCompat1 : nonFreshClausesCompat st1 st1' := hIH v stAcc stAcc' hCompat
      -- Use clause independence
      have hIndep1 := encodeConj_foldl_clauses_indep b body w vtl
        ([(encodeFormula b (body v) w stAcc).1], st1) ([], st1) rfl
      have hIndep2 := encodeConj_foldl_clauses_indep b body w vtl
        ([(encodeFormula b (body v) w stAcc').1], st1') ([], st1') rfl
      have hcInEmptyStart : c ∈ (vtl.foldl (fun (vars, stCur) vIdx =>
          let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
          (vars ++ [uBody], stNext)) ([], st1)).2.clauses := hIndep1 ▸ hc
      have hRes := vih st1 st1' hCompat1 c hcInEmptyStart hNoFresh
      exact hIndep2 ▸ hRes


omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- encodeTupleControl new clauses contain Fresh vars.
    encodeTupleControl allocates uTuple (Fresh, id = st.nextFresh) and adds clauses
    containing it. All new clauses have neg uTuple or pos uTuple. -/
lemma encodeTupleControl_newClause_has_fresh (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars : List (Var b)) (st : EncState b) (c : SAT.Clause (Var b))
    (hcNew : c ∈ (encodeTupleControl b learners tuple witnessVars st).2.clauses)
    (hcNotOld : c ∉ st.clauses) :
    ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
  simp only [encodeTupleControl] at hcNew
  -- encodeTupleControl does:
  --   allocFresh → addClause (forward) → foldl guards → foldl witnesses
  -- All clauses contain pos/neg uTuple (Fresh)
  rcases hAlloc : EncState.allocFresh b st with ⟨uTuple, stAlloc⟩
  simp only [hAlloc] at hcNew
  have hAllocEq : stAlloc.clauses = st.clauses := by
    have h := EncState.allocFresh_clauses_eq (b := b) st
    simp only [hAlloc] at h; exact h

  let guards := (learners.zip tuple).map fun (ℓ, Q) =>
    SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)

  let st1 := EncState.addClause b stAlloc
    ([SAT.Lit.neg (FVar.toVar b uTuple)] ++ guards ++ witnessVars.map SAT.Lit.pos)

  -- Helper for phase 2 induction
  have hPhase2 : ∀ (pairs : List (S.Value × Finset b.participants)) (stAcc : EncState b),
      c ∉ stAcc.clauses →
      c ∈ (pairs.foldl (fun st' pr =>
        EncState.addClause b st' [SAT.Lit.pos (Var.MinQ (b.findValueIndex pr.1) pr.2),
           SAT.Lit.pos (FVar.toVar b uTuple)]) stAcc).clauses →
      ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
    intro pairs
    induction pairs with
    | nil => intro stAcc hNot hIn; exact absurd hIn hNot
    | cons pr prs ih =>
        intro stAcc hNotAcc hIn
        let stStep := EncState.addClause b stAcc
          [SAT.Lit.pos (Var.MinQ (b.findValueIndex pr.1) pr.2),
           SAT.Lit.pos (FVar.toVar b uTuple)]
        by_cases hcStep : c ∈ stStep.clauses
        · simp only [] at hcStep
          cases hcStep with
          | head =>
              exact ⟨SAT.Lit.pos (FVar.toVar b uTuple), List.Mem.tail _ (List.Mem.head _),
                     uTuple.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
          | tail _ hOld => exact absurd hOld hNotAcc
        · exact ih stStep hcStep hIn

  -- Helper for phase 3 induction
  have hPhase3 : ∀ (vars : List (Var b)) (stAcc : EncState b),
      c ∉ stAcc.clauses →
      c ∈ (vars.foldl (fun st' v =>
        EncState.addClause b st'
          [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)]) stAcc).clauses →
      ∃ lit ∈ c, ∃ n, SAT.Lit.getVar lit = Var.Fresh n := by
    intro vars
    induction vars with
    | nil => intro stAcc hNot hIn; exact absurd hIn hNot
    | cons v vs ih =>
        intro stAcc hNotAcc hIn
        let stStep := EncState.addClause b stAcc [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)]
        by_cases hcStep : c ∈ stStep.clauses
        · simp only [] at hcStep
          cases hcStep with
          | head =>
              exact ⟨SAT.Lit.pos (FVar.toVar b uTuple), List.Mem.tail _ (List.Mem.head _),
                     uTuple.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
          | tail _ hOld => exact absurd hOld hNotAcc
        · exact ih stStep hcStep hIn

  let st2 := (learners.zip tuple).foldl (fun stAcc pr =>
    EncState.addClause b stAcc [SAT.Lit.pos (Var.MinQ (b.findValueIndex pr.1) pr.2),
       SAT.Lit.pos (FVar.toVar b uTuple)]) st1

  -- Track backwards through phases
  by_cases hcSt2 : c ∈ st2.clauses
  · -- c was in st2, check phases 1-2
    by_cases hcSt1 : c ∈ st1.clauses
    · -- c was in st1, check phase 1 / stAlloc
      simp only [] at hcSt1
      cases hcSt1 with
      | head =>
          exact ⟨SAT.Lit.neg (FVar.toVar b uTuple), List.Mem.head _,
                 uTuple.id, by simp [SAT.Lit.getVar, FVar.toVar]⟩
      | tail _ hcAlloc =>
          rw [hAllocEq] at hcAlloc
          exact absurd hcAlloc hcNotOld
    · -- c was added in phase 2
      exact hPhase2 (learners.zip tuple) st1 hcSt1 hcSt2
  · -- c was added in phase 3
    exact hPhase3 witnessVars st2 hcSt2 hcNew

/-- diamond witnessFold clause set independence (auxiliary). -/
lemma diamond_witnessFold_clauses_indep_aux (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants)
    (parts : List b.participants)
    (acc1 acc2 : List (FVar b × b.participants) × EncState b)
    (hSnd : acc1.2 = acc2.2) :
    (parts.foldl (fun acc p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc.2
          (acc.1 ++ [(uWit, p)], stNew)
        else acc) acc1).2.clauses =
    (parts.foldl (fun acc p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc.2
          (acc.1 ++ [(uWit, p)], stNew)
        else acc) acc2).2.clauses := by
  induction parts generalizing acc1 acc2 with
  | nil => simp only [List.foldl_nil, hSnd]
  | cons p ps ih =>
      simp only [List.foldl_cons]
      split
      · -- p ∈ intersection: encode and continue
        apply ih
        simp only [hSnd]
      · -- p ∉ intersection: skip
        exact ih acc1 acc2 hSnd

/-- diamond witnessFold clause set independence. -/
lemma diamond_witnessFold_clauses_indep (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants)
    (stAcc stAcc' : EncState b)
    (hEq : stAcc = stAcc') :
    let witnessFold := fun st =>
      (Bounds.partsL b).foldl (fun acc p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc.2
          (acc.1 ++ [(uWit, p)], stNew)
        else acc) ([], st)
    (witnessFold stAcc).2.clauses = (witnessFold stAcc').2.clauses := by
  intro witnessFold
  subst hEq
  rfl

/-- Helper: nonFreshClausesCompat is preserved through diamond witnessFold (auxiliary). -/
lemma diamond_witnessFold_preserves_nonFreshCompat_aux (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants)
    (parts : List b.participants)
    (acc acc' : List (FVar b × b.participants) × EncState b)
    (hCompat : nonFreshClausesCompat acc.2 acc'.2)
    (hIH : ∀ w' st st', nonFreshClausesCompat st st' →
           nonFreshClausesCompat (encodeFormula b φ w' st).2 (encodeFormula b φ w' st').2) :
    nonFreshClausesCompat
      (parts.foldl (fun acc p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc.2
          (acc.1 ++ [(uWit, p)], stNew)
        else acc) acc).2
      (parts.foldl (fun acc p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc.2
          (acc.1 ++ [(uWit, p)], stNew)
        else acc) acc').2 := by
  intro c hc hNoFresh
  induction parts generalizing acc acc' c with
  | nil =>
      simp only [List.foldl_nil] at hc ⊢
      exact hCompat c hc hNoFresh
  | cons p ps ih =>
      simp only [List.foldl_cons] at hc ⊢
      by_cases hp : p ∈ intersection
      · -- p ∈ intersection
        simp only [hp, dite_true] at hc ⊢
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        let st1 := (encodeFormula b φ wEnd acc.2).2
        let st1' := (encodeFormula b φ wEnd acc'.2).2
        have hCompat1 : nonFreshClausesCompat st1 st1' := hIH wEnd acc.2 acc'.2 hCompat
        -- Use clause independence to relate different list accumulators
        have hIndep1 := diamond_witnessFold_clauses_indep_aux b φ w intersection ps
          (acc.1 ++ [((encodeFormula b φ wEnd acc.2).1, p)], st1) ([], st1) rfl
        have hIndep2 := diamond_witnessFold_clauses_indep_aux b φ w intersection ps
          (acc'.1 ++ [((encodeFormula b φ wEnd acc'.2).1, p)], st1') ([], st1') rfl
        have hcEmptyStart : c ∈ (ps.foldl (fun acc'' p' =>
            if hp' : p' ∈ intersection then
              let wEnd' : WId b := ⟨p', ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
              let (uWit, stNew) := encodeFormula b φ wEnd' acc''.2
              (acc''.1 ++ [(uWit, p')], stNew)
            else acc'') ([], st1)).2.clauses := hIndep1 ▸ hc
        have hRes := ih ([], st1) ([], st1') hCompat1 c hcEmptyStart hNoFresh
        exact hIndep2 ▸ hRes
      · -- p ∉ intersection: skip
        simp only [hp, dite_false] at hc ⊢
        exact ih acc acc' hCompat c hc hNoFresh

/-- nonFreshClausesCompat is preserved through diamond witnessFold. -/
lemma diamond_witnessFold_preserves_nonFreshCompat (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants)
    (stAcc stAcc' : EncState b)
    (hCompat : nonFreshClausesCompat stAcc stAcc')
    (hIH : ∀ w' st st', nonFreshClausesCompat st st' →
           nonFreshClausesCompat (encodeFormula b φ w' st).2 (encodeFormula b φ w' st').2) :
    let witnessFold := fun st =>
      (Bounds.partsL b).foldl (fun acc p =>
        if _ : p ∈ intersection then
          let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
          let (uWit, stNew) := encodeFormula b φ wEnd acc.2
          (acc.1 ++ [(uWit, p)], stNew)
        else acc) ([], st)
    nonFreshClausesCompat (witnessFold stAcc).2 (witnessFold stAcc').2 :=
  diamond_witnessFold_preserves_nonFreshCompat_aux b φ w intersection (Bounds.partsL b)
    ([], stAcc) ([], stAcc') hCompat hIH

/-- Helper: diamond step preserves nonFreshClausesCompat.
    The step consists of witnessFold (recursive encoding) + encodeTupleControl (Fresh vars).
    Non-Fresh clauses only come from witnessFold, which preserves nonFreshClausesCompat by IH. -/
lemma diamond_step_preserves_nonFreshCompat (b : Bounds S) (φ : Formula S) (w : WId b)
    (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (accVars : List (FVar b)) (stCur stCur' : EncState b)
    (hCompat : nonFreshClausesCompat stCur stCur')
    (hIH : ∀ w' st st', nonFreshClausesCompat st st' →
           nonFreshClausesCompat (encodeFormula b φ w' st).2 (encodeFormula b φ w' st').2) :
    let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
    let witnessFold := fun stIn =>
      (Bounds.partsL b).foldl
        (fun (acc : List (FVar b × b.participants) × EncState b) p =>
          if _ : p ∈ intersection then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd acc.2
            (acc.1 ++ [(uWit, p)], stNew)
          else acc) ([], stIn)
    let witnessVars := fun stIn => (witnessFold stIn).1.map (fun u => FVar.toVar b u.1)
    let step := fun stIn =>
      let wf := witnessFold stIn
      let (uTuple, stFinal) := encodeTupleControl b learners tuple (witnessVars stIn) wf.2
      (accVars ++ [uTuple], stFinal)
    nonFreshClausesCompat (step stCur).2 (step stCur').2 := by
  intro intersection witnessFold witnessVars step c hc hNoFresh
  -- The step consists of witnessFold + encodeTupleControl
  -- encodeTupleControl only adds clauses with Fresh vars
  -- Non-Fresh clauses come from witnessFold (recursive encoding)

  -- Track c from (step stCur): c ∈ (step stCur).2.clauses
  -- (step stCur).2 = (encodeTupleControl b learners tuple (witnessVars stCur) wf.2).2
  -- where wf = witnessFold stCur

  let wf := witnessFold stCur
  let wf' := witnessFold stCur'
  have hWfCompat : nonFreshClausesCompat wf.2 wf'.2 :=
    diamond_witnessFold_preserves_nonFreshCompat b φ w intersection stCur stCur' hCompat hIH

  -- (step stCur).2 = (encodeTupleControl ...).2
  have hStepEq : (step stCur).2 =
      (encodeTupleControl b learners tuple (witnessVars stCur) wf.2).2 := rfl

  -- c ∈ (encodeTupleControl ...).2.clauses
  rw [hStepEq] at hc

  -- Check if c was in wf.2.clauses (from witnessFold at stCur)
  by_cases hcWf : c ∈ wf.2.clauses
  · -- c was in witnessFold result at stCur
    -- By hWfCompat, c ∈ wf'.2.clauses
    have hcWf' := hWfCompat c hcWf hNoFresh
    -- By encodeTupleControl_clauses_subset, c ∈ (step stCur').2.clauses
    exact encodeTupleControl_clauses_subset b learners tuple (witnessVars stCur') wf'.2 hcWf'
  · -- c was added by encodeTupleControl at stCur (new clause)
    -- encodeTupleControl new clauses have Fresh vars - contradiction with hNoFresh
    have hcNew := encodeTupleControl_newClause_has_fresh b learners tuple (witnessVars stCur)
      wf.2 c hc hcWf
    obtain ⟨lit, hLit, n, hFresh⟩ := hcNew
    exact absurd hFresh (hNoFresh lit hLit n)

/-- Helper: diamond tuples.foldl preserves nonFreshClausesCompat.
    Each step preserves nonFreshClausesCompat, so the full fold does too. -/
lemma diamond_tuples_foldl_preserves_nonFreshCompat (b : Bounds S) (φ : Formula S) (w : WId b)
    (learners : List S.Value)
    (tuples : List (List (Finset b.participants)))
    (acc acc' : List (FVar b) × EncState b)
    (hCompat : nonFreshClausesCompat acc.2 acc'.2)
    (hIH : ∀ w' st st', nonFreshClausesCompat st st' →
           nonFreshClausesCompat (encodeFormula b φ w' st).2 (encodeFormula b φ w' st').2) :
    let step :
        (List (FVar b) × EncState b) → List (Finset b.participants) →
        List (FVar b) × EncState b :=
      fun (accVars, stCur) tuple =>
        let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
        let witnessFold :=
          (Bounds.partsL b).foldl
            (fun (acc : List (FVar b × b.participants) × EncState b) p =>
              if _ : p ∈ intersection then
                let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
                let (uWit, stNew) := encodeFormula b φ wEnd acc.2
                (acc.1 ++ [(uWit, p)], stNew)
              else acc)
            ([], stCur)
        let witnessVars := witnessFold.1.map (fun u => FVar.toVar b u.1)
        let (uTuple, stFinal) := encodeTupleControl b learners tuple witnessVars witnessFold.2
        (accVars ++ [uTuple], stFinal)
    nonFreshClausesCompat (tuples.foldl step acc).2 (tuples.foldl step acc').2 := by
  intro step c hc hNoFresh
  induction tuples generalizing acc acc' c with
  | nil =>
      simp only [List.foldl_nil] at hc ⊢
      exact hCompat c hc hNoFresh
  | cons tuple rest ih =>
      simp only [List.foldl_cons] at hc ⊢
      have hStepCompat := diamond_step_preserves_nonFreshCompat b φ w learners tuple
        acc.1 acc.2 acc'.2 hCompat hIH
      exact ih (step acc tuple) (step acc' tuple) hStepCompat c hc hNoFresh


/-- Non-Fresh new clauses from predicate encoding are deterministic.
    If c is a new clause with no Fresh vars at st, the same clause c is added at st'.
    This is because non-Fresh clauses come from addPreEqReflAll ([pos (PreEq t t)])
    or predicateFold ([neg PreEq, neg Pred, pos Pred]) - both state-independent.

    Proof structure (when idxs ≠ []):
    1. mkBigOrIff new clauses have Fresh control var → contradiction with hNoFresh
    2. addPreEqFrom: non-Fresh new clauses are [pos (PreEq ti ti)]
       (via addPreEqFrom_newClause_nonFresh_eq_refl) → deterministic (addPreEqFrom_refl_unit_mem)
    3. addPreEqReflAll: new clauses are [pos (PreEq t t)]
       → deterministic (foldl_addClause_elem_mem)
    4. predicateFold: new clauses are guard clauses
       → deterministic (nested_foldl_addClause2_elem_mem)

    TODO: Complete this proof once addPreEqFrom_newClause_nonFresh_eq_refl is proven.
    The key dependency is addPreEqPair_core_newClause_has_fresh which shows that
    addPreEqPair_core only adds clauses with Fresh vars. -/
lemma encodeFormula_predicate_nonFresh_deterministic (b : Bounds S) (atom : PredicateAtom S)
    (w : WId b) (st st' : EncState b) (c : SAT.Clause (Var b))
    (hcNew : c ∈ (encodeFormula b (Formula.predicate atom) w st).2.clauses)
    (hcNotOld : c ∉ st.clauses)
    (hNoFresh : clauseHasNoFresh c) :
    c ∈ (encodeFormula b (Formula.predicate atom) w st').2.clauses := by
  classical
  -- Define intermediate states
  let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
  let idxs := predIxList b pred
  let literals := idxs.map (fun k => Var.Pred w.p w.ti k)
  let st1 := (mkBigOrIff b literals st).2
  let st1' := (mkBigOrIff b literals st').2
  simp only [encodeFormula] at hcNew ⊢
  split at hcNew
  · -- idxs = []: only mkBigOrIff runs
    rename_i hEmpty
    simp only [hEmpty]
    -- New clauses from mkBigOrIff have control var (Fresh) → contradiction
    have ⟨lit, hLit, hIsCtrl⟩ :=
      mkBigOrIff_newClause_contains_control_var b literals st c hcNew hcNotOld
    have hCtrlFresh : (mkBigOrIff b literals st).1 = ⟨st.nextFresh⟩ := mkBigOrIff_fst b literals st
    simp only [FVar.toVar, hCtrlFresh] at hIsCtrl
    exact absurd hIsCtrl (hNoFresh lit hLit st.nextFresh)
  · -- idxs ≠ []: full predicate encoding
    rename_i hNonEmpty
    simp only [hNonEmpty]
    let st2 := addPreEqFrom b w.ti st1
    let st3 := addPreEqReflAll b st2
    let st2' := addPreEqFrom b w.ti st1'
    let st3' := addPreEqReflAll b st2'
    -- Clause subsets through pipeline
    have hSt1St2 : st1.clauses ⊆ st2.clauses := addPreEqFrom_clauses_subset b w.ti st1
    have hSt2St3 : st2.clauses ⊆ st3.clauses := addPreEqReflAll_clauses_subset b st2
    have hSt1'St2' : st1'.clauses ⊆ st2'.clauses := addPreEqFrom_clauses_subset b w.ti st1'
    have hSt2'St3' : st2'.clauses ⊆ st3'.clauses := addPreEqReflAll_clauses_subset b st2'
    -- Track which stage c came from
    by_cases hcSt1 : c ∈ st1.clauses
    · -- c from mkBigOrIff
      by_cases hcStOld : c ∈ st.clauses
      · exact absurd hcStOld hcNotOld
      · -- c is new from mkBigOrIff, has control var → contradiction
        have ⟨lit, hLit, hIsCtrl⟩ :=
          mkBigOrIff_newClause_contains_control_var b literals st c hcSt1 hcStOld
        have hCtrlFresh : (mkBigOrIff b literals st).1 = ⟨st.nextFresh⟩ :=
          mkBigOrIff_fst b literals st
        simp only [FVar.toVar, hCtrlFresh] at hIsCtrl
        exact absurd hIsCtrl (hNoFresh lit hLit st.nextFresh)
    · by_cases hcSt2 : c ∈ st2.clauses
      · -- c is from addPreEqFrom
        -- Non-Fresh new clause = [pos (PreEq w.ti w.ti)]
        have hcEq := addPreEqFrom_newClause_nonFresh_eq_refl b w.ti st1 c hcSt2 hcSt1 hNoFresh
        -- Same clause is added at st2' and preserved through pipeline
        have hInSt2' : c ∈ st2'.clauses := by
          rw [hcEq]; exact addPreEqFrom_refl_unit_mem b w.ti st1'
        have hInSt3' : c ∈ st3'.clauses := hSt2'St3' hInSt2'
        -- Need st3' ⊆ final (predicateFold preserves clauses)
        let predicateFoldStep := fun stCur (H' : b.times) =>
          idxs.foldl (fun stAcc k =>
            let backward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                             SAT.Lit.neg (Var.Pred w.p H' k),
                             SAT.Lit.pos (Var.Pred w.p w.ti k)]
            let forward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                            SAT.Lit.neg (Var.Pred w.p w.ti k),
                            SAT.Lit.pos (Var.Pred w.p H' k)]
            EncState.addClause b (EncState.addClause b stAcc backward) forward) stCur
        have hSt3'Final : st3'.clauses ⊆ ((Bounds.timesL b).foldl predicateFoldStep st3').clauses :=
          foldl_subset_state (b := b) (f := predicateFoldStep)
            (hStep := fun stCur _ => by
              simp only [predicateFoldStep]
              exact foldl_subset_state (b := b) (f := fun stAcc k =>
                let backward := [SAT.Lit.neg (Var.PreEq w.ti _),
                                 SAT.Lit.neg (Var.Pred w.p _ k),
                                 SAT.Lit.pos (Var.Pred w.p w.ti k)]
                let forward := [SAT.Lit.neg (Var.PreEq w.ti _),
                                SAT.Lit.neg (Var.Pred w.p w.ti k),
                                SAT.Lit.pos (Var.Pred w.p _ k)]
                EncState.addClause b (EncState.addClause b stAcc backward) forward)
                (hStep := fun stAcc' _ =>
                  List.Subset.trans (EncState.addClause_subset_clauses (b := b) stAcc' _)
                    (EncState.addClause_subset_clauses (b := b) _ _))
                (xs := idxs) (init := stCur))
            (xs := Bounds.timesL b) (init := st3')
        exact hSt3'Final hInSt3'
      · by_cases hcSt3 : c ∈ st3.clauses
        · -- c is from addPreEqReflAll: [pos (PreEq t t)] for some t
          -- Use foldl_addClause_mem to identify which t
          simp only [st3, addPreEqReflAll] at hcSt3
          rcases foldl_addClause_mem b (Bounds.timesL b) st2
              (fun t => [SAT.Lit.pos (Var.PreEq t t)]) c hcSt3 with hBase | ⟨t, hT, hEq⟩
          · -- c ∈ st2.clauses contradicts hcSt2
            exact absurd hBase hcSt2
          · -- c = [pos (PreEq t t)], same clause added at st3'
            have hInSt3' : c ∈ st3'.clauses := by
              rw [hEq]
              simp only [st3', addPreEqReflAll]
              exact foldl_addClause_elem_mem b (Bounds.timesL b) st2'
                  (fun t => [SAT.Lit.pos (Var.PreEq t t)]) t hT
            -- st3' ⊆ final (same predicateFoldStep definition as above)
            let predicateFoldStep := fun stCur (H' : b.times) =>
              idxs.foldl (fun stAcc k =>
                let backward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                 SAT.Lit.neg (Var.Pred w.p H' k),
                                 SAT.Lit.pos (Var.Pred w.p w.ti k)]
                let forward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                SAT.Lit.neg (Var.Pred w.p w.ti k),
                                SAT.Lit.pos (Var.Pred w.p H' k)]
                EncState.addClause b (EncState.addClause b stAcc backward) forward) stCur
            have hSt3'Final : st3'.clauses ⊆
                ((Bounds.timesL b).foldl predicateFoldStep st3').clauses :=
              foldl_subset_state (b := b) (f := predicateFoldStep)
                (hStep := fun stCur _ => by
                  simp only [predicateFoldStep]
                  exact foldl_subset_state (b := b) (f := fun stAcc k =>
                    let backward := [SAT.Lit.neg (Var.PreEq w.ti _),
                                     SAT.Lit.neg (Var.Pred w.p _ k),
                                     SAT.Lit.pos (Var.Pred w.p w.ti k)]
                    let forward := [SAT.Lit.neg (Var.PreEq w.ti _),
                                    SAT.Lit.neg (Var.Pred w.p w.ti k),
                                    SAT.Lit.pos (Var.Pred w.p _ k)]
                    EncState.addClause b (EncState.addClause b stAcc backward) forward)
                    (hStep := fun stAcc' _ =>
                      List.Subset.trans (EncState.addClause_subset_clauses (b := b) stAcc' _)
                        (EncState.addClause_subset_clauses (b := b) _ _))
                    (xs := idxs) (init := stCur))
                (xs := Bounds.timesL b) (init := st3')
            exact hSt3'Final hInSt3'
        · -- c is from predicateFold
          -- Use nested_foldl_addClause2_mem to identify which (H', k) produced c
          let mkBackward := fun (H' : b.times) (k : b.predIx) =>
            [SAT.Lit.neg (Var.PreEq w.ti H'),
             SAT.Lit.neg (Var.Pred w.p H' k),
             SAT.Lit.pos (Var.Pred w.p w.ti k)]
          let mkForward := fun (H' : b.times) (k : b.predIx) =>
            [SAT.Lit.neg (Var.PreEq w.ti H'),
             SAT.Lit.neg (Var.Pred w.p w.ti k),
             SAT.Lit.pos (Var.Pred w.p H' k)]
          let predicateFoldStep := fun stCur (H' : b.times) =>
            idxs.foldl (fun stAcc k =>
              EncState.addClause b (EncState.addClause b stAcc (mkBackward H' k))
                (mkForward H' k)) stCur
          -- hcNew is in the unfolded form; extract the relevant part
          have hcInFold : c ∈ ((Bounds.timesL b).foldl predicateFoldStep st3).clauses := by
            simp only [predicateFoldStep, mkBackward, mkForward, st3, st2, st1]
            exact hcNew
          rcases nested_foldl_addClause2_mem b (Bounds.timesL b) idxs st3
              mkBackward mkForward c hcInFold with hBase | ⟨H', hH', k, hk, hEq⟩
          · -- c ∈ st3.clauses contradicts hcSt3
            exact absurd hBase hcSt3
          · -- c = mkBackward H' k or c = mkForward H' k
            -- Same clause is added at st' (clauses are state-independent)
            have hcInSt' : c ∈ ((Bounds.timesL b).foldl predicateFoldStep st3').clauses := by
              rcases hEq with hBack | hFwd
              · rw [hBack]
                exact nested_foldl_addClause2_elem_mem1 b (Bounds.timesL b) idxs st3'
                    mkBackward mkForward H' hH' k hk
              · rw [hFwd]
                exact nested_foldl_addClause2_elem_mem2 b (Bounds.timesL b) idxs st3'
                    mkBackward mkForward H' hH' k hk
            -- Convert back to goal form
            simp only [predicateFoldStep, mkBackward, mkForward, st3', st2', st1'] at hcInSt'
            exact hcInSt'

/-! ## NonFreshClausesCompat Preservation -/

/-- nonFreshClausesCompat is preserved through encodeFormula.

    If non-Fresh clauses in st are in st', and we encode φ from both states,
    then non-Fresh clauses in the result from st are in the result from st'.

    Key insight: encoding adds two kinds of clauses:
    1. Non-Fresh clauses (deterministic - same regardless of starting state)
    2. Fresh clauses (different indices at st vs st')

    For non-Fresh clauses c in result from st:
    - If c was in st: c is non-Fresh, so c ∈ st' (by hypothesis), so c ∈ st1'
    - If c was added by encoding: c is deterministic, same clause added at st' -/
lemma encodeFormula_preserves_nonFreshCompat
    (b : Bounds S) (φ : Formula S) (w : WId b)
    (st st' : EncState b)
    (hCompat : nonFreshClausesCompat st st') :
    nonFreshClausesCompat (encodeFormula b φ w st).2 (encodeFormula b φ w st').2 := by
  -- Proof by induction on φ
  induction φ generalizing w st st' with
  | bot =>
      intro c hc hNoFresh
      -- bot encoding adds [neg u] where u is Fresh
      unfold encodeFormula at hc
      simp only [EncState.addClause, List.mem_cons] at hc
      cases hc with
      | inl hEq =>
          -- c = [neg (Fresh st.nextFresh)] - has Fresh var, contradiction
          exfalso
          simp only [FVar.toVar, EncState.allocFresh] at hEq
          subst hEq
          have hLit : SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh) ∈
              [SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] := List.Mem.head _
          exact hNoFresh _ hLit st.nextFresh rfl
      | inr hTail =>
          simp only [EncState.allocFresh] at hTail
          have hInSt' := hCompat c hTail hNoFresh
          exact encodeFormula_clauses_subset b Formula.bot w st' hInSt'
  | eq v1 v2 =>
      intro c hc hNoFresh
      simp only [encodeFormula] at hc
      -- eq encoding branches on v1 == v2, both add [pos/neg Fresh]
      by_cases hEq : (v1 == v2) = true
      · simp only [hEq, ↓reduceIte, EncState.addClause, EncState.allocFresh] at hc
        rw [List.mem_cons] at hc
        cases hc with
        | inl hEq' =>
            subst hEq'
            exfalso
            have hLit : SAT.Lit.pos (Var.Fresh (b := b) st.nextFresh) ∈
                [SAT.Lit.pos (Var.Fresh (b := b) st.nextFresh)] := List.Mem.head _
            exact hNoFresh _ hLit st.nextFresh rfl
        | inr hTail =>
            have hInSt' := hCompat c hTail hNoFresh
            exact encodeFormula_clauses_subset b (Formula.eq v1 v2) w st' hInSt'
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte, EncState.addClause,
          EncState.allocFresh] at hc
        rw [List.mem_cons] at hc
        cases hc with
        | inl hEq' =>
            subst hEq'
            exfalso
            have hLit : SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh) ∈
                [SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)] := List.Mem.head _
            exact hNoFresh _ hLit st.nextFresh rfl
        | inr hTail =>
            have hInSt' := hCompat c hTail hNoFresh
            exact encodeFormula_clauses_subset b (Formula.eq v1 v2) w st' hInSt'
  | seq =>
      intro c hc hNoFresh
      -- seq encoding adds [neg Fresh, pos Seq] and [neg Seq, pos Fresh] - both have Fresh var
      by_cases hOld : c ∈ st.clauses
      · have hInSt' := hCompat c hOld hNoFresh
        exact encodeFormula_clauses_subset b Formula.seq w st' hInSt'
      · -- c is new - must be one of the two clauses with Fresh var
        exfalso
        unfold encodeFormula at hc
        simp only [EncState.addClause, EncState.allocFresh, List.mem_cons] at hc
        -- hc : c = clause1 ∨ c = clause2 ∨ c ∈ st.clauses
        -- Since hOld says c ∉ st.clauses, c must be clause1 or clause2
        rcases hc with hEq1 | hEq2 | hInSt
        · -- c = [neg Seq, pos Fresh] (second clause added)
          simp only [FVar.toVar] at hEq1
          subst hEq1
          have hLit : SAT.Lit.pos (Var.Fresh (b := b) st.nextFresh) ∈
              [SAT.Lit.neg (Var.Seq w.ti w.p),
               SAT.Lit.pos (Var.Fresh (b := b) st.nextFresh)] := by simp
          have hGetVar : SAT.Lit.getVar (SAT.Lit.pos (Var.Fresh (b := b) st.nextFresh)) =
              Var.Fresh st.nextFresh := by simp [SAT.Lit.getVar]
          exact hNoFresh _ hLit st.nextFresh hGetVar
        · -- c = [neg Fresh, pos Seq] (first clause added)
          simp only [FVar.toVar] at hEq2
          subst hEq2
          have hLit : SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh) ∈
              [SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh),
               SAT.Lit.pos (Var.Seq w.ti w.p)] := by simp
          have hGetVar : SAT.Lit.getVar (SAT.Lit.neg (Var.Fresh (b := b) st.nextFresh)) =
              Var.Fresh st.nextFresh := by simp [SAT.Lit.getVar]
          exact hNoFresh _ hLit st.nextFresh hGetVar
        · exact hOld hInSt
  | imp φ1 φ2 ih1 ih2 =>
      intro c hc hNoFresh
      -- Define intermediate states
      let st1 := (encodeFormula b φ1 w st).2
      let st1' := (encodeFormula b φ1 w st').2
      -- Helper: φ2 encoding result clauses are subset of imp encoding result clauses
      have hImpSub : (encodeFormula b φ2 w st1').2.clauses ⊆
          (encodeFormula b (Formula.imp φ1 φ2) w st').2.clauses := by
        simp only [encodeFormula]
        intro x hx
        simp only [EncState.addClause, EncState.allocFresh, List.mem_cons]
        right; right; right
        exact hx
      -- imp adds clauses with Fresh vars, plus nested encoding
      by_cases hInSt1 : c ∈ st1.clauses
      · -- c from φ1 encoding
        have hComp1 : nonFreshClausesCompat st1 st1' := ih1 w st st' hCompat
        have hInSt1' := hComp1 c hInSt1 hNoFresh
        have hInEnc2' := encodeFormula_clauses_subset b φ2 w st1' hInSt1'
        exact hImpSub hInEnc2'
      · by_cases hInEnc2 : c ∈ (encodeFormula b φ2 w st1).2.clauses
        · -- c from φ2 encoding
          have hComp1 : nonFreshClausesCompat st1 st1' := ih1 w st st' hCompat
          have hComp2 : nonFreshClausesCompat (encodeFormula b φ2 w st1).2
              (encodeFormula b φ2 w st1').2 := ih2 w st1 st1' hComp1
          have hInEnc2' := hComp2 c hInEnc2 hNoFresh
          exact hImpSub hInEnc2'
        · -- c is new from imp itself - has Fresh var
          exfalso
          -- Unfold imp encoding to see the three clauses
          unfold encodeFormula at hc
          simp only [EncState.addClause, EncState.allocFresh, List.mem_cons] at hc
          -- hc : c = clause1 ∨ c = clause2 ∨ c = clause3 ∨ c ∈ st2.clauses
          -- where st2 = (encodeFormula b φ2 w st1).2
          let freshN := (encodeFormula b φ2 w st1).snd.nextFresh
          rcases hc with hEq1 | hEq2 | hEq3 | hInSt2
          · -- c = [neg u, neg u1, pos u2]
            simp only [FVar.toVar] at hEq1
            subst hEq1
            have hLit : SAT.Lit.neg (Var.Fresh (b := b) freshN) ∈
                [SAT.Lit.neg (Var.Fresh (b := b) freshN),
                 SAT.Lit.neg (Var.Fresh (b := b) (encodeFormula b φ1 w st).fst.id),
                 SAT.Lit.pos (Var.Fresh (b := b) (encodeFormula b φ2 w st1).fst.id)] := by simp
            have hGetVar : SAT.Lit.getVar (SAT.Lit.neg (Var.Fresh (b := b) freshN)) =
                Var.Fresh freshN := by simp [SAT.Lit.getVar]
            exact hNoFresh _ hLit freshN hGetVar
          · -- c = [neg u2, pos u]
            simp only [FVar.toVar] at hEq2
            subst hEq2
            have hLit : SAT.Lit.pos (Var.Fresh (b := b) freshN) ∈
                [SAT.Lit.neg (Var.Fresh (b := b) (encodeFormula b φ2 w st1).fst.id),
                 SAT.Lit.pos (Var.Fresh (b := b) freshN)] := by simp
            have hGetVar : SAT.Lit.getVar (SAT.Lit.pos (Var.Fresh (b := b) freshN)) =
                Var.Fresh freshN := by simp [SAT.Lit.getVar]
            exact hNoFresh _ hLit freshN hGetVar
          · -- c = [pos u1, pos u]
            simp only [FVar.toVar] at hEq3
            subst hEq3
            have hLit : SAT.Lit.pos (Var.Fresh (b := b) freshN) ∈
                [SAT.Lit.pos (Var.Fresh (b := b) (encodeFormula b φ1 w st).fst.id),
                 SAT.Lit.pos (Var.Fresh (b := b) freshN)] := by simp
            have hGetVar : SAT.Lit.getVar (SAT.Lit.pos (Var.Fresh (b := b) freshN)) =
                Var.Fresh freshN := by simp [SAT.Lit.getVar]
            exact hNoFresh _ hLit freshN hGetVar
          · exact hInEnc2 hInSt2
  | atEnd φ ih =>
      intro c hc hNoFresh
      let wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
      let freshN := (encodeFormula b φ wEnd st).2.nextFresh
      -- Helper: φ encoding result clauses are subset of atEnd encoding result clauses
      have hAtEndSub : (encodeFormula b φ wEnd st').2.clauses ⊆
          (encodeFormula b (Formula.atEnd φ) w st').2.clauses := by
        simp only [encodeFormula]
        intro x hx
        simp only [EncState.addClause, EncState.allocFresh, List.mem_cons]
        right; right
        exact hx
      unfold encodeFormula at hc
      simp only [EncState.addClause, EncState.allocFresh, List.mem_cons] at hc
      rcases hc with hEq1 | hEq2 | hTail
      · -- c = first clause - has Fresh var
        simp only [FVar.toVar] at hEq1
        subst hEq1
        exfalso
        have hLit : SAT.Lit.pos (Var.Fresh (b := b) freshN) ∈
            [SAT.Lit.neg (Var.Fresh (b := b) (encodeFormula b φ wEnd st).1.id),
             SAT.Lit.pos (Var.Fresh (b := b) freshN)] := by simp
        have hGetVar : SAT.Lit.getVar (SAT.Lit.pos (Var.Fresh (b := b) freshN)) =
            Var.Fresh freshN := by simp [SAT.Lit.getVar]
        exact hNoFresh _ hLit freshN hGetVar
      · -- c = second clause - has Fresh var
        simp only [FVar.toVar] at hEq2
        subst hEq2
        exfalso
        have hLit : SAT.Lit.neg (Var.Fresh (b := b) freshN) ∈
            [SAT.Lit.neg (Var.Fresh (b := b) freshN),
             SAT.Lit.pos (Var.Fresh (b := b) (encodeFormula b φ wEnd st).1.id)] := by simp
        have hGetVar : SAT.Lit.getVar (SAT.Lit.neg (Var.Fresh (b := b) freshN)) =
            Var.Fresh freshN := by simp [SAT.Lit.getVar]
        exact hNoFresh _ hLit freshN hGetVar
      · -- c from recursive encoding
        have hComp := ih wEnd st st' hCompat
        have hInEnc' := hComp c hTail hNoFresh
        exact hAtEndSub hInEnc'
  | predicate atom =>
      intro c hc hNoFresh
      -- Predicate encoding: mkBigOrIff → addPreEqFrom → addPreEqReflAll → predicateFold
      -- Non-Fresh new clauses are structurally determined (same at st and st')
      by_cases hOld : c ∈ st.clauses
      · have hInSt' := hCompat c hOld hNoFresh
        exact encodeFormula_clauses_subset b (Formula.predicate atom) w st' hInSt'
      · -- c is new, non-Fresh clause - use determinism lemma
        exact encodeFormula_predicate_nonFresh_deterministic b atom w st st' c hc hOld hNoFresh
  | event atom =>
      intro c hc hNoFresh
      -- Event encoding: eventWitnessStep fold → mkBigOrIff
      -- ALL new clauses have Fresh vars (z from eventWitnessStep, u from mkBigOrIff)
      by_cases hOld : c ∈ st.clauses
      · have hInSt' := hCompat c hOld hNoFresh
        exact encodeFormula_clauses_subset b (Formula.event atom) w st' hInSt'
      · -- c is new, but hNoFresh says c has no Fresh vars - contradiction
        exfalso
        obtain ⟨lit, hLit, n, hFresh⟩ :=
          encodeFormula_event_newClause_has_fresh b atom w st c hc hOld
        exact hNoFresh lit hLit n hFresh
  | past φ ih =>
      intro c hc hNoFresh
      -- Past encoding structure:
      --   st1 = allocFresh st (adds u)
      --   st2 = encodeWitnesses fold from st1 (recursive encoding at each witness)
      --   st3 = auxVars fold from st2 (adds 4 clauses per witness, all with Fresh aux)
      --   st4 = addClause st3 [neg u, aux1, ..., auxn] (final clause)
      --
      -- For non-Fresh clause c:
      --   If c ∈ st: use hCompat
      --   If c ∈ st2 \ st: c came from recursive encoding → use IH through fold
      --   If c ∈ st4 \ st2: c came from auxVars/final clause → has Fresh → contradiction
      by_cases hOld : c ∈ st.clauses
      · have hInSt' := hCompat c hOld hNoFresh
        exact encodeFormula_clauses_subset b (Formula.past φ) w st' hInSt'
      · -- c is new (not in st.clauses) and non-Fresh
        -- Define intermediate states
        let u := (EncState.allocFresh b st).1
        let st1 := (EncState.allocFresh b st).2
        let st1' := (EncState.allocFresh b st').2
        let witnesses := (WId.allWorlds b).filterMap fun w' =>
          if w'.p = w.p then some w' else none
        let st2 := (witnesses.foldl (fun (uvars, stCur) w' =>
          let res := encodeFormula b φ w' stCur
          (uvars ++ [res.1], res.2)) ([], st1)).2
        let st2' := (witnesses.foldl (fun (uvars, stCur) w' =>
          let res := encodeFormula b φ w' stCur
          (uvars ++ [res.1], res.2)) ([], st1')).2
        -- Helper: st1 has same clauses as st
        have hSt1Eq : st1.clauses = st.clauses := EncState.allocFresh_clauses_eq (b := b) st
        have hSt1'Eq : st1'.clauses = st'.clauses := EncState.allocFresh_clauses_eq (b := b) st'
        -- Helper: IH wrapped for use with encodeWitnesses fold
        have hIH : ∀ w' stX stX', nonFreshClausesCompat stX stX' →
            nonFreshClausesCompat (encodeFormula b φ w' stX).2 (encodeFormula b φ w' stX').2 :=
          fun w' s s' hC => ih w' s s' hC
        -- nonFreshClausesCompat st1 st1'
        have hCompat1 : nonFreshClausesCompat st1 st1' := by
          intro c' hc' hNoF
          have hc'St : c' ∈ st.clauses := hSt1Eq ▸ hc'
          have hIn' := hCompat c' hc'St hNoF
          exact hSt1'Eq ▸ hIn'
        -- nonFreshClausesCompat st2 st2'
        have hCompat2 : nonFreshClausesCompat st2 st2' :=
          encodeWitnesses_foldl_preserves_nonFreshCompat b φ witnesses st1 st1' hCompat1 hIH
        -- Check if c is in st2
        by_cases hcSt2 : c ∈ st2.clauses
        · -- c from encodeWitnesses fold (recursive encoding of φ)
          by_cases hcSt1 : c ∈ st1.clauses
          · -- c from st1 = st - contradicts hOld
            exact absurd (hSt1Eq ▸ hcSt1) hOld
          · -- c is new in st2 and non-Fresh → c ∈ st2' by nonFreshClausesCompat
            have hInSt2' := hCompat2 c hcSt2 hNoFresh
            -- st2'.clauses ⊆ (encodeFormula b (Formula.past φ) w st').2.clauses
            have hSub : st2'.clauses ⊆ (encodeFormula b (Formula.past φ) w st').2.clauses := by
              simp only [encodeFormula]
              intro x hx
              simp only [EncState.addClause, List.mem_cons]
              right
              -- auxVars fold preserves clauses from st2'
              have hAuxPreserve :
                  ∀ (pairs : List (FVar b × WId b)) (acc : List (FVar b) × EncState b),
                  acc.2.clauses ⊆ (pairs.foldl (fun (auxAcc, stCur) (u', w') =>
                    let memVar := Var.Mem w.ti w'
                    let (aux, stCur) := EncState.allocFresh b stCur
                    let stCur := EncState.addClause b stCur
                      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                        SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st').1)]
                    let stCur := EncState.addClause b stCur
                      [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b u'),
                        SAT.Lit.pos (FVar.toVar b aux)]
                    let stCur := EncState.addClause b stCur
                      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
                    let stCur := EncState.addClause b stCur
                      [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b u')]
                    (auxAcc ++ [aux], stCur)) acc).2.clauses := by
                intro pairs
                induction pairs with
                | nil => intro acc; exact fun x hx => hx
                | cons hd tl ihPairs =>
                    intro acc y hy
                    simp only [List.foldl_cons]
                    apply ihPairs
                    simp only [EncState.addClause, EncState.allocFresh, List.mem_cons]
                    right; right; right; right
                    exact hy
              let witnessVars' := (witnesses.foldl (fun (uvars, stCur) w' =>
                let res := encodeFormula b φ w' stCur
                (uvars ++ [res.1], res.2)) ([], st1')).1
              exact hAuxPreserve (witnessVars'.zip witnesses) ([], st2') hx
            exact hSub hInSt2'
        · -- c from auxVars fold or final clause → has Fresh → contradiction with hNoFresh
          exfalso
          -- c is new (not in st2) but in the final encoding result
          simp only [encodeFormula, EncState.addClause, List.mem_cons] at hc
          let witnessVars := (witnesses.foldl (fun (uvars, stCur) w' =>
            let res := encodeFormula b φ w' stCur
            (uvars ++ [res.1], res.2)) ([], st1)).1
          rcases hc with hFinal | hAux
          · -- c is final clause [neg u, aux1, ..., auxn] - has Fresh u
            subst hFinal
            -- The first literal is neg u which is Fresh
            have hGetVar : SAT.Lit.getVar (SAT.Lit.neg (FVar.toVar b u)) = Var.Fresh u.id := by
              simp [SAT.Lit.getVar, FVar.toVar]
            apply hNoFresh (SAT.Lit.neg (FVar.toVar b u)) _ u.id hGetVar
            -- Show neg u is in the clause (first element)
            exact List.Mem.head _
          · -- c from auxVars fold → has Fresh aux
            have hFresh := foldl_auxVars_step_newClause_has_fresh b w u
              (witnessVars.zip witnesses) ([], st2) c hAux hcSt2
            obtain ⟨lit, hLit, n, hGetVar⟩ := hFresh
            exact hNoFresh lit hLit n hGetVar
  | «forall» body ih =>
      intro c hc hNoFresh
      -- Forall encoding structure:
      --   st1 = allocFresh st (adds u)
      --   st2 = encodeConj fold from st1 (recursive encoding body v at each value)
      --   st3 = bodyVars.foldl adding [neg u, pos uBody] for each body
      --   st4 = addClause st3 [neg u1, ..., neg un, pos u]
      by_cases hOld : c ∈ st.clauses
      · have hInSt' := hCompat c hOld hNoFresh
        exact encodeFormula_clauses_subset b (Formula.forall body) w st' hInSt'
      · -- c is new (not in st.clauses) and non-Fresh
        -- Define intermediate states
        let u := (EncState.allocFresh b st).1
        let st1 := (EncState.allocFresh b st).2
        let st1' := (EncState.allocFresh b st').2
        let valIndices := List.finRange b.nVals
        let st2 := (valIndices.foldl (fun (vars, stCur) vIdx =>
          let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
          (vars ++ [uBody], stNext)) ([], st1)).2
        let st2' := (valIndices.foldl (fun (vars, stCur) vIdx =>
          let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
          (vars ++ [uBody], stNext)) ([], st1')).2
        -- Helper: st1 has same clauses as st
        have hSt1Eq : st1.clauses = st.clauses := EncState.allocFresh_clauses_eq (b := b) st
        have hSt1'Eq : st1'.clauses = st'.clauses := EncState.allocFresh_clauses_eq (b := b) st'
        -- Helper: IH for subformulas
        have hIH : ∀ v stX stX', nonFreshClausesCompat stX stX' →
            nonFreshClausesCompat (encodeFormula b (body v) w stX).2
              (encodeFormula b (body v) w stX').2 :=
          fun v s s' hC => ih v w s s' hC
        -- nonFreshClausesCompat st1 st1'
        have hCompat1 : nonFreshClausesCompat st1 st1' := by
          intro c' hc' hNoF
          have hc'St : c' ∈ st.clauses := hSt1Eq ▸ hc'
          have hIn' := hCompat c' hc'St hNoF
          exact hSt1'Eq ▸ hIn'
        -- nonFreshClausesCompat st2 st2'
        have hCompat2 : nonFreshClausesCompat st2 st2' :=
          encodeConj_foldl_preserves_nonFreshCompat b body w valIndices st1 st1' hCompat1 hIH
        -- Check if c is in st2
        by_cases hcSt2 : c ∈ st2.clauses
        · -- c from encodeConj fold (recursive encoding of body v)
          by_cases hcSt1 : c ∈ st1.clauses
          · exact absurd (hSt1Eq ▸ hcSt1) hOld
          · -- c is new in st2 and non-Fresh → c ∈ st2' by nonFreshClausesCompat
            have hInSt2' := hCompat2 c hcSt2 hNoFresh
            -- st2'.clauses ⊆ (encodeFormula b (Formula.forall body) w st').2.clauses
            have hSub : st2'.clauses ⊆ (encodeFormula b (Formula.forall body) w st').2.clauses := by
              simp only [encodeFormula]
              intro x hx
              simp only [EncState.addClause, List.mem_cons]
              right
              -- bodyVars fold preserves clauses, then final clause preserves
              let bodyVars' := (valIndices.foldl (fun (vars, stCur) vIdx =>
                let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
                (vars ++ [uBody], stNext)) ([], st1')).1
              have hBVPreserve : ∀ (bvs : List (FVar b)) (acc : EncState b),
                  acc.clauses ⊆ (bvs.foldl (fun stCur uBody =>
                    EncState.addClause b stCur
                      [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st').1),
                       SAT.Lit.pos (FVar.toVar b uBody)]) acc).clauses := by
                intro bvs
                induction bvs with
                | nil => intro acc; exact fun y hy => hy
                | cons bhd btl ihBV =>
                    intro acc y hy
                    simp only [List.foldl_cons]
                    apply ihBV
                    simp only [EncState.addClause, List.mem_cons]
                    right; exact hy
              exact hBVPreserve bodyVars' st2' hx
            exact hSub hInSt2'
        · -- c from bodyVars fold or final clause → has Fresh → contradiction
          exfalso
          simp only [encodeFormula, EncState.addClause, List.mem_cons] at hc
          let bodyVars := (valIndices.foldl (fun (vars, stCur) vIdx =>
            let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
            (vars ++ [uBody], stNext)) ([], st1)).1
          let st3 := bodyVars.foldl (fun stCur uBody =>
            EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]) st2
          by_cases hcSt3 : c ∈ st3.clauses
          · -- c from bodyVars fold → has Fresh u
            have hFresh := forall_bodyVars_foldl_newClause_has_fresh b u bodyVars st2 c hcSt3 hcSt2
            obtain ⟨lit, hLit, n, hGetVar⟩ := hFresh
            exact hNoFresh lit hLit n hGetVar
          · -- c is final clause [neg u1, ..., neg un, pos u] → has Fresh u
            rcases hc with hEq | hTail
            · -- c = final clause - has Fresh u at the end
              subst hEq
              have hGetVar : SAT.Lit.getVar (SAT.Lit.pos (FVar.toVar b u)) = Var.Fresh u.id := by
                simp [SAT.Lit.getVar, FVar.toVar]
              apply hNoFresh (SAT.Lit.pos (FVar.toVar b u)) _ u.id hGetVar
              -- Show pos u is in the clause (last element via List.mem_append)
              simp only [List.mem_append, List.mem_singleton, List.mem_map]
              right; rfl
            · exact absurd hTail hcSt3
  | diamond learners φ ih =>
      intro c hc hNoFresh
      by_cases hOld : c ∈ st.clauses
      · have hInSt' := hCompat c hOld hNoFresh
        exact encodeFormula_clauses_subset b (Formula.diamond learners φ) w st' hInSt'
      · -- c is new (not in st.clauses) and non-Fresh
        -- KEY: Use diamondStep from DiamondHelpers.lean, NOT a local definition
        let getMinQs (ℓ : S.Value) : List (Finset b.participants) :=
          let vIdx := b.findValueIndex ℓ
          let allVars := Var.allMinQ b vIdx
          allVars.filterMap fun v =>
            match v with
            | Var.MinQ _ Q => some Q
            | _ => none
        let quorumSets := learners.map getMinQs
        let tuples := cartesianProduct quorumSets

        -- Define in terms of diamondStep (NOT a local step!)
        let tupleVars := (tuples.foldl (diamondStep b learners φ w) ([], st)).1
        let stTuples := (tuples.foldl (diamondStep b learners φ w) ([], st)).2
        let tupleVars' := (tuples.foldl (diamondStep b learners φ w) ([], st')).1
        let stTuples' := (tuples.foldl (diamondStep b learners φ w) ([], st')).2

        -- IH for recursive calls
        have hIH' : ∀ w' st1 st1', nonFreshClausesCompat st1 st1' →
            nonFreshClausesCompat (encodeFormula b φ w' st1).2 (encodeFormula b φ w' st1').2 :=
          fun w' st1 st1' hC => ih w' st1 st1' hC

        -- Get nonFreshClausesCompat for stTuples/stTuples'
        have hTuplesCompat : nonFreshClausesCompat stTuples stTuples' :=
          diamond_tuples_foldl_preserves_nonFreshCompat b φ w learners
            tuples ([], st) ([], st') hCompat hIH'

        by_cases hcTuples : c ∈ stTuples.clauses
        · -- POSITIVE CASE: c ∈ stTuples.clauses
          have hcTuples' : c ∈ stTuples'.clauses := hTuplesCompat c hcTuples hNoFresh

          -- Unfold encodeFormula and rewrite to use diamondStep
          simp only [encodeFormula]
          rw [encodeFormula_diamond_step_unfolded_eq]

          -- Split on the match in the goal
          split
          next hEmpty =>
            -- Case: empty list - allocFresh + addClause preserves stTuples'.clauses
            simp only [EncState.addClause, List.mem_cons]
            right
            exact EncState.allocFresh_clauses_eq (b := b) stTuples' ▸ hcTuples'
          next u0 us hCons =>
            -- Case: cons - mkAndIff fold preserves stTuples'.clauses
            have hAndFold : stTuples'.clauses ⊆
                (us.foldl (fun (acc : FVar b × EncState b) u' =>
                  mkAndIff b acc.1 u' acc.2) (u0, stTuples')).2.clauses :=
              foldl_subset_snd
                (f := fun (acc : FVar b × EncState b) u' => mkAndIff b acc.1 u' acc.2)
                (hStep := fun acc u' => mkAndIff_clauses_subset b acc.1 u' acc.2)
                (xs := us) (init := (u0, stTuples'))
            exact hAndFold hcTuples'

        · -- NEGATIVE CASE: c ∉ stTuples.clauses → c is from final phase (has Fresh)
          exfalso
          simp only [encodeFormula] at hc
          rw [encodeFormula_diamond_step_unfolded_eq] at hc

          split at hc
          next hEmpty =>
            -- Case: empty list
            simp only [EncState.addClause, List.mem_cons] at hc
            rcases hc with hEq | hcAlloc
            · -- c = [pos u'] which has Fresh var - contradiction
              -- The singleton clause has a Fresh var, contradicting hNoFresh
              subst hEq
              have hLit : SAT.Lit.pos (FVar.toVar b
                  (EncState.allocFresh b stTuples).1) ∈
                  [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b stTuples).1)] := by
                simp only [List.mem_singleton]
              have hFresh : SAT.Lit.getVar (SAT.Lit.pos (FVar.toVar b
                  (EncState.allocFresh b stTuples).1)) =
                  Var.Fresh (EncState.allocFresh b stTuples).1.id := by
                simp [SAT.Lit.getVar, FVar.toVar]
              exact hNoFresh _ hLit _ hFresh
            · -- c ∈ (allocFresh stTuples).2.clauses = stTuples.clauses
              rw [EncState.allocFresh_clauses_eq] at hcAlloc
              exact hcTuples hcAlloc
          next u0 us hCons =>
            -- Case: cons
            by_cases hcStTuples : c ∈ stTuples.clauses
            · exact hcTuples hcStTuples
            · have hFresh := mkAndIff_foldl_newClause_has_fresh b us (u0, stTuples) c hc hcStTuples
              obtain ⟨lit, hLit, n, hFreshLit⟩ := hFresh
              exact hNoFresh lit hLit n hFreshLit

/-- Helper: encodeWitnesses fold preserves clause shift compatibility. -/
lemma encodeWitnesses_foldl_preserves_clauseShiftCompat (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (stAcc stAcc' : EncState b) (offset : Nat)
    (hOffset : stAcc'.nextFresh = stAcc.nextFresh + offset)
    (hCompat : clauseShiftCompat b stAcc stAcc' offset)
    (hIH : ∀ w' st st', st'.nextFresh = st.nextFresh + offset → clauseShiftCompat b st st' offset →
           clauseShiftCompat b (encodeFormula b φ w' st).2 (encodeFormula b φ w' st').2 offset) :
    clauseShiftCompat b
      (witnesses.foldl (fun (uvars, stCur) w' =>
        let res := encodeFormula b φ w' stCur
        (uvars ++ [res.1], res.2)) ([], stAcc)).2
      (witnesses.foldl (fun (uvars, stCur) w' =>
        let res := encodeFormula b φ w' stCur
        (uvars ++ [res.1], res.2)) ([], stAcc')).2 offset := by
  intro c hc
  induction witnesses generalizing stAcc stAcc' c with
  | nil =>
      simp only [List.foldl_nil] at hc ⊢
      exact hCompat c hc
  | cons whd wtl wih =>
      simp only [List.foldl_cons] at hc ⊢
      let st1 := (encodeFormula b φ whd stAcc).2
      let st1' := (encodeFormula b φ whd stAcc').2
      have hOffset1 : st1'.nextFresh = st1.nextFresh + offset := by
        simp only [st1, st1']
        exact encodeFormula_nextFresh_offset b φ whd stAcc stAcc' offset hOffset
      have hCompat1 : clauseShiftCompat b st1 st1' offset := hIH whd stAcc stAcc' hOffset hCompat
      -- Use clause independence
      have hIndep1 := encodeWitnesses_foldl_clauses_indep b φ wtl
        ([(encodeFormula b φ whd stAcc).1], st1) ([], st1) rfl
      have hIndep2 := encodeWitnesses_foldl_clauses_indep b φ wtl
        ([(encodeFormula b φ whd stAcc').1], st1') ([], st1') rfl
      have hcInEmptyStart : c ∈ (wtl.foldl (fun (uvars, stCur) w' =>
          let res := encodeFormula b φ w' stCur
          (uvars ++ [res.1], res.2)) ([], st1)).2.clauses := hIndep1 ▸ hc
      have hRes := wih st1 st1' hOffset1 hCompat1 c hcInEmptyStart
      exact hIndep2 ▸ hRes

/-- Helper: witnessVars from encodeWitnesses fold have offset relationship.

    If we run the encodeWitnesses fold at st and st' with st'.nextFresh = st.nextFresh + offset,
    then the resulting control variables have IDs that differ by offset. -/
lemma encodeWitnesses_foldl_vars_offset (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hIH : ∀ w stX stX', stX'.nextFresh = stX.nextFresh + offset →
           stX.nextFresh ≤ stX'.nextFresh →
           (encodeFormula b φ w stX').2.nextFresh =
             (encodeFormula b φ w stX).2.nextFresh + offset) :
    let step := fun (acc : List (FVar b) × EncState b) (w' : WId b) =>
        let (u', stNext) := encodeFormula b φ w' acc.2
        (acc.1 ++ [u'], stNext)
    let vars := (witnesses.foldl step ([], st)).1
    let vars' := (witnesses.foldl step ([], st')).1
    vars.length = vars'.length ∧
    ∀ i (hi : i < vars.length) (hi' : i < vars'.length),
        (vars.get ⟨i, hi⟩).id + offset = (vars'.get ⟨i, hi'⟩).id := by
  intro step vars vars'
  -- Prove by induction on witnesses, tracking offset through the fold
  suffices hSuff : ∀ (ws : List (WId b)) (accL accL' : List (FVar b)) (stCur stCur' : EncState b),
      stCur'.nextFresh = stCur.nextFresh + offset →
      stCur.nextFresh ≤ stCur'.nextFresh →
      accL.length = accL'.length →
      (∀ i (hi : i < accL.length) (hi' : i < accL'.length),
          (accL.get ⟨i, hi⟩).id + offset = (accL'.get ⟨i, hi'⟩).id) →
      let res := ws.foldl (fun (uvars, stC) w' =>
          let (u', stNext) := encodeFormula b φ w' stC
          (uvars ++ [u'], stNext)) (accL, stCur)
      let res' := ws.foldl (fun (uvars, stC) w' =>
          let (u', stNext) := encodeFormula b φ w' stC
          (uvars ++ [u'], stNext)) (accL', stCur')
      res.1.length = res'.1.length ∧
      ∀ i (hi : i < res.1.length) (hi' : i < res'.1.length),
          (res.1.get ⟨i, hi⟩).id + offset = (res'.1.get ⟨i, hi'⟩).id by
    have hInit := hSuff witnesses [] [] st st' hOffset hMono rfl
      (fun _ hi _ => (Nat.not_lt_zero _ hi).elim)
    simp only [vars, vars', step] at hInit ⊢
    exact hInit

  intro ws
  induction ws with
  | nil =>
    intro accL accL' stCur stCur' _ _ hLenEq hAccOff
    simp only [List.foldl_nil]
    exact ⟨hLenEq, hAccOff⟩
  | cons w' wtl wih =>
    intro accL accL' stCur stCur' hStOff hStMono hLenEq hAccOff
    simp only [List.foldl_cons]
    let u := (encodeFormula b φ w' stCur).1
    let u' := (encodeFormula b φ w' stCur').1
    let stNext := (encodeFormula b φ w' stCur).2
    let stNext' := (encodeFormula b φ w' stCur').2

    -- Control vars have offset (using encodeFormula_controlVar_shift)
    have hUOff : u.id + offset = u'.id := by
      simp only [u, u']
      have hShift := encodeFormula_controlVar_shift b φ w' stCur stCur' hStMono
      have hDiff : stCur'.nextFresh - stCur.nextFresh = offset := by omega
      omega

    -- Next states have offset
    have hNextOff : stNext'.nextFresh = stNext.nextFresh + offset :=
      hIH w' stCur stCur' hStOff hStMono
    have hNextMono : stNext.nextFresh ≤ stNext'.nextFresh := by omega

    -- New accumulators have offset relationship
    have hNewLenEq : (accL ++ [u]).length = (accL' ++ [u']).length := by
      simp only [List.length_append, List.length_singleton, hLenEq]

    have hNewAccOff : ∀ i (hi : i < (accL ++ [u]).length) (hi' : i < (accL' ++ [u']).length),
        ((accL ++ [u]).get ⟨i, hi⟩).id + offset = ((accL' ++ [u']).get ⟨i, hi'⟩).id := by
      intro i hi hi'
      simp only [List.length_append, List.length_singleton] at hi hi'
      by_cases hOld : i < accL.length
      · -- i is in original accumulator
        have hOld' : i < accL'.length := hLenEq ▸ hOld
        simp only [List.get_eq_getElem, List.getElem_append_left hOld,
          List.getElem_append_left hOld']
        exact hAccOff i hOld hOld'
      · -- i is the new element (i = accL.length)
        have hNew : i = accL.length := by omega
        subst hNew
        -- Need to show: (accL ++ [u])[accL.length] = u and (accL' ++ [u'])[accL.length] = u'
        -- Convert the bounds
        have hLt : accL.length < (accL ++ [u]).length := by simp
        have hLt' : accL.length < (accL' ++ [u']).length := by simp [hLenEq]
        have hGeL : accL.length ≤ accL.length := Nat.le_refl _
        have hGeL' : accL'.length ≤ accL.length := hLenEq ▸ Nat.le_refl accL'.length
        have hLHS : (accL ++ [u])[accL.length]'hLt = u := by
          simp only [List.getElem_append_right hGeL, Nat.sub_self, List.getElem_cons_zero]
        have hRHS : (accL' ++ [u'])[accL.length]'hLt' = u' := by
          have : accL.length - accL'.length = 0 := by omega
          simp only [List.getElem_append_right hGeL', this, List.getElem_cons_zero]
        simp only [List.get_eq_getElem]
        convert hUOff using 2; simp only [hLHS]

    exact wih (accL ++ [u]) (accL' ++ [u']) stNext stNext' hNextOff hNextMono hNewLenEq hNewAccOff

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Helper: mkDw preserves clauseShiftCompat.
    mkDw either allocates d with [neg d] (empty case) or does mkY fold + mkBigOrIff. -/
lemma mkDw_preserves_clauseShiftCompat (b : Bounds S) (t' : b.times) (w : WId b)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset) :
    clauseShiftCompat b (mkDw b t' w st).2 (mkDw b t' w st').2 offset := by
  unfold mkDw
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  cases hCands : cands with
  | nil =>
    -- Empty case: allocate d and add [neg d]
    intro c hc
    simp only [EncState.allocFresh, EncState.addClause, List.mem_cons] at hc ⊢
    have hDOff : st'.nextFresh = st.nextFresh + offset := hOffset
    obtain hNew | hOld := hc
    · -- c = [neg d]
      left
      rw [hNew]
      simp only [List.map_cons, List.map_nil, FVar.toVar, shiftLitFresh_neg_fresh, hDOff]
    · -- c from st.clauses
      right
      exact hCompat c hOld
  | cons cand candsTail =>
    -- Non-empty case: mkY fold + mkBigOrIff
    let step := fun (acc : List (Var b) × EncState b) w' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w' st''
      (FVar.toVar b y :: vs, st''')
    -- Get fold results
    let foldRes := (cand :: candsTail).foldl step ([], st)
    let foldRes' := (cand :: candsTail).foldl step ([], st')
    -- Offset preserved through fold
    have hFoldOff : foldRes'.2.nextFresh = foldRes.2.nextFresh + offset :=
      mkY_foldl_nextFresh_offset b t' w (cand :: candsTail) st st' offset hOffset
    -- clauseShiftCompat through fold
    have hFoldCompat : clauseShiftCompat b foldRes.2 foldRes'.2 offset :=
      mkY_foldl_preserves_clauseShiftCompat b t' w (cand :: candsTail) st st' offset hOffset hCompat
    -- ys list lengths are equal
    have hLenEq : foldRes.1.length = foldRes'.1.length :=
      mkY_foldl_fst_length_eq b t' w (cand :: candsTail) st st'
    -- ys lists shift pointwise
    -- Use mkDw_fold_pointwise_shift but need to handle let-binding unification
    have hYsShift : ∀ i (hi : i < foldRes.1.length),
        shiftVarFresh b offset (foldRes.1.get ⟨i, hi⟩) = foldRes'.1.get ⟨i, hLenEq ▸ hi⟩ := by
      intro i hi
      obtain ⟨y, hy⟩ := mkY_foldl_all_fresh b t' w (cand :: candsTail) st i hi
      simp only [FVar.toVar] at hy
      -- Convert List.get to getElem in both hy and goal
      simp only [List.get_eq_getElem] at hy ⊢
      -- hy is now: fold...[i] = Var.Fresh y.id (with explicit fold)
      -- goal is: shiftVarFresh b offset foldRes.1[i] = foldRes'.1[i] (with let bindings)
      -- These are definitionally equal, so use conv to rewrite
      conv_lhs => rw [show foldRes.1[i] = _ from hy]
      -- This reduces shiftVarFresh (Var.Fresh y.id) to Var.Fresh (y.id + offset)
      simp only [shiftVarFresh]
      -- mkDw_fold_pointwise_shift says foldRes'[i] = Fresh (y.id + offset)
      -- Convert offset convention: we have st'.nextFresh = st.nextFresh + offset
      -- The lemma wants offset = st'.nextFresh - st.nextFresh
      have hOffset' : offset = st'.nextFresh - st.nextFresh := by omega
      have hMono : st.nextFresh ≤ st'.nextFresh := by omega
      -- Apply mkDw_fold_pointwise_shift
      have hShift := mkDw_fold_pointwise_shift b t' w (cand :: candsTail) st st' offset
        hOffset' hMono
      -- Convert from get to getElem?
      have hGet : foldRes.1[i]? = some (Var.Fresh y.id) := by
        simp only [List.getElem?_eq_some_iff, foldRes]
        exact ⟨hi, hy⟩
      have hGet' := hShift i y.id hGet
      -- Convert back to get
      rw [List.getElem?_eq_some_iff] at hGet'
      exact hGet'.2.symm
    -- Apply mkBigOrIff_preserves_clauseShiftCompat_shifted
    exact mkBigOrIff_preserves_clauseShiftCompat_shifted b foldRes.1 foldRes'.1
      foldRes.2 foldRes'.2 offset hFoldOff hFoldCompat hLenEq hYsShift

omit [DecidableEq S.AtomicPredType] in
/-- Helper: eventWitnessStep fold produces witness vars that shift correctly. -/
lemma eventWitnessStep_foldl_witnessVars_shift (b : Bounds S)
    (pairs : List (Var b × Var b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    let vs := (pairs.foldl (eventWitnessStep b) ([], st)).1
    let vs' := (pairs.foldl (eventWitnessStep b) ([], st')).1
    vs.length = vs'.length ∧
    ∀ i (hi : i < vs.length), shiftVarFresh b offset (vs.get ⟨i, hi⟩) = vs'.get ⟨i, by
      have hLen : vs.length = vs'.length := by
        simp only [vs, vs', foldl_eventWitnessStep_length, List.length_nil, Nat.zero_add]
      exact hLen ▸ hi⟩ := by
  simp only
  constructor
  · -- Length equality
    simp only [foldl_eventWitnessStep_length, List.length_nil, Nat.zero_add]
  · -- Element shift
    intro i hi
    have hLen : (pairs.foldl (eventWitnessStep b) ([], st)).1.length = pairs.length := by
      simp only [foldl_eventWitnessStep_length, List.length_nil, Nat.zero_add]
    have hiPairs : i < pairs.length := hLen ▸ hi
    -- Use foldl_eventWitnessStep_vars_indexed
    have hVi := foldl_eventWitnessStep_vars_indexed b pairs ([], st) i hiPairs
    have hVi' := foldl_eventWitnessStep_vars_indexed b pairs ([], st') i hiPairs
    simp only [List.length_nil, Nat.zero_add] at hVi hVi'
    -- vi = Fresh(st.nextFresh + i), vi' = Fresh(st'.nextFresh + i)
    have hLen' : (pairs.foldl (eventWitnessStep b) ([], st')).1.length = pairs.length := by
      simp only [foldl_eventWitnessStep_length, List.length_nil, Nat.zero_add]
    have hi' : i < (pairs.foldl (eventWitnessStep b) ([], st')).1.length := hLen' ▸ hiPairs
    -- Convert getElem? results to getElem
    have hGet : (pairs.foldl (eventWitnessStep b) ([], st)).1[i] =
        Var.Fresh (st.nextFresh + i) := by
      have h := List.getElem?_eq_some_iff.mp hVi
      exact h.2
    have hGet' : (pairs.foldl (eventWitnessStep b) ([], st')).1[i]'hi' =
        Var.Fresh (st'.nextFresh + i) := by
      have h := List.getElem?_eq_some_iff.mp hVi'
      exact h.2
    simp only [List.get_eq_getElem, shiftVarFresh, hGet, hGet', hOffset]
    ring_nf

omit [DecidableEq S.AtomicPredType] in
/-- Helper: encodeFormulaEvent preserves clauseShiftCompat. -/
lemma encodeFormulaEvent_preserves_clauseShiftCompat (b : Bounds S)
    (w : WId b) (evt : Signature.EventType S) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset) :
    clauseShiftCompat b
      (encodeFormulaEvent b w evt st).2
      (encodeFormulaEvent b w evt st').2 offset := by
  simp only [encodeFormulaEvent]
  -- Stage 1: eventWitnessStep fold
  let pairs := eventWitnessPairs b w evt
  have hNF := eventWitnessPairs_nonFresh b w evt
  let fold_st := pairs.foldl (eventWitnessStep b) ([], st)
  let fold_st' := pairs.foldl (eventWitnessStep b) ([], st')
  have hOff1 : fold_st'.2.nextFresh = fold_st.2.nextFresh + offset :=
    foldl_eventWitnessStep_offset b pairs ([], st) ([], st') offset hOffset
  have hComp1 : clauseShiftCompat b fold_st.2 fold_st'.2 offset :=
    eventWitnessStep_foldl_preserves_clauseShiftCompat b pairs st st' offset hOffset hCompat hNF
  -- Stage 2: mkBigOrIff with shifted witness vars
  have hVsShift := eventWitnessStep_foldl_witnessVars_shift b pairs st st' offset hOffset
  have hVsLen : fold_st.1.length = fold_st'.1.length := hVsShift.1
  have hVsOff : ∀ i (hi : i < fold_st.1.length),
      shiftVarFresh b offset (fold_st.1.get ⟨i, hi⟩) = fold_st'.1.get ⟨i, hVsLen ▸ hi⟩ :=
    hVsShift.2
  exact mkBigOrIff_preserves_clauseShiftCompat_shifted b fold_st.1 fold_st'.1
    fold_st.2 fold_st'.2 offset hOff1 hComp1 hVsLen hVsOff

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The state component (.2) of preEqObligationStep fold doesn't depend on the first
    component (list) of accumulator. This is a stronger version of
    `preEqObligation_fold_clauses_indep` that proves full state equality. -/
lemma preEqObligationStep_fold_state_indep
    (b : Bounds S) (t t' : b.times)
    (xs : List (WId b))
    (acc : List (FVar b) × EncState b) :
    (xs.foldl (preEqObligationStep b t t') acc).2 =
    (xs.foldl (preEqObligationStep b t t') ([], acc.2)).2 := by
  classical
  revert acc
  induction xs with
  | nil => intro acc; rfl
  | cons w ws ih =>
    intro acc
    simp only [List.foldl_cons]
    cases hDw : mkDw b t' w acc.2 with
    | mk d stDw =>
      cases hOw : mkOw b t w d stDw with
      | mk o stOw =>
        have h1 : preEqObligationStep b t t' acc w = (o :: acc.1, stOw) := by
          simp [preEqObligationStep, hDw, hOw]
        have h2 : preEqObligationStep b t t' ([], acc.2) w = ([o], stOw) := by
          simp [preEqObligationStep, hDw, hOw]
        rw [h1, h2]
        -- Now both have stOw as the state, so by IH the final states are equal
        have ih1 := ih (o :: acc.1, stOw)
        have ih2 := ih ([o], stOw)
        simp only at ih1 ih2
        rw [ih1, ih2]

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: preEqObligationStep fold preserves clauseShiftCompat.
    This is the most complex helper, covering stages 1-2 of the pipeline. -/
lemma preEqObligationStep_foldl_preserves_clauseShiftCompat (b : Bounds S) (t t' : b.times)
    (worlds : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset) :
    clauseShiftCompat b
      (worlds.foldl (preEqObligationStep b t t') ([], st)).2
      (worlds.foldl (preEqObligationStep b t t') ([], st')).2 offset := by
  -- Induction on worlds
  revert st st' hOffset hCompat
  induction worlds with
  | nil =>
    intro st st' hOffset hCompat
    simp only [List.foldl_nil]
    exact hCompat
  | cons w wTail ihTail =>
    intro st st' hOffset hCompat
    simp only [List.foldl_cons]
    -- One step of preEqObligationStep: mkDw then mkOw
    -- Apply IH with the result states

    -- Define intermediate results
    let step := preEqObligationStep b t t' ([], st) w
    let step' := preEqObligationStep b t t' ([], st') w

    -- Offset preserved after one step
    have hStepOff : step'.2.nextFresh = step.2.nextFresh + offset :=
      preEqObligationStep_offset b t t' ([], st) ([], st') w offset hOffset

    -- clauseShiftCompat after one step
    -- preEqObligationStep does mkDw then mkOw
    have hStepCompat : clauseShiftCompat b step.2 step'.2 offset := by
      simp only [step, step', preEqObligationStep]
      -- Need to show clauseShiftCompat through mkDw then mkOw
      -- Get d offset
      have hDwOff : (mkDw b t' w st').2.nextFresh = (mkDw b t' w st).2.nextFresh + offset :=
        mkDw_offset b t' w st st' offset hOffset
      have hDOff : (mkDw b t' w st').1.id = (mkDw b t' w st).1.id + offset := by
        -- Use mkDw_fst_id: (mkDw b t' w st).1.id = if cands.isEmpty then st.nextFresh
        --                                          else st.nextFresh + cands.length
        have hId := mkDw_fst_id b t' w st
        have hId' := mkDw_fst_id b t' w st'
        -- Both use the same cands, so the condition is the same
        let cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
        change _ = if cands.isEmpty then _ else _ at hId
        change _ = if cands.isEmpty then _ else _ at hId'
        split at hId
        · -- cands.isEmpty = true
          rename_i hEmpty
          simp only [hEmpty, ↓reduceIte] at hId'
          omega
        · -- cands.isEmpty = false
          rename_i hNonEmpty
          simp only [hNonEmpty, Bool.false_eq_true, ↓reduceIte] at hId'
          omega
      -- clauseShiftCompat through mkDw - use the dedicated helper lemma
      have hDwCompat : clauseShiftCompat b (mkDw b t' w st).2 (mkDw b t' w st').2 offset :=
        mkDw_preserves_clauseShiftCompat b t' w st st' offset hOffset hCompat
      -- Apply mkOw_preserves_clauseShiftCompat
      exact mkOw_preserves_clauseShiftCompat b t w (mkDw b t' w st).1 (mkDw b t' w st').1
        (mkDw b t' w st).2 (mkDw b t' w st').2 offset hDwOff hDwCompat hDOff

    -- Apply IH - the fold result state only depends on the initial state, not the acc list
    -- preEqObligationStep b t t' (os, st) w and preEqObligationStep b t t' ([], st) w
    -- produce the same .2 component
    have hFoldEq : (wTail.foldl (preEqObligationStep b t t') step).2 =
        (wTail.foldl (preEqObligationStep b t t') ([], step.2)).2 :=
      preEqObligationStep_fold_state_indep b t t' wTail step
    have hFoldEq' : (wTail.foldl (preEqObligationStep b t t') step').2 =
        (wTail.foldl (preEqObligationStep b t t') ([], step'.2)).2 :=
      preEqObligationStep_fold_state_indep b t t' wTail step'
    rw [hFoldEq, hFoldEq']
    exact ihTail step.2 step'.2 hStepOff hStepCompat

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: preEqAccStep fold preserves clauseShiftCompat.
    preEqAccStep allocates next, then adds 3 clauses via addAccStep:
    - [neg next, pos cur]
    - [neg next, pos o]
    - [neg cur, neg o, pos next]
    All are Fresh vars that shift by offset between the two runs. -/
lemma preEqAccStep_foldl_preserves_clauseShiftCompat (b : Bounds S)
    (os os' : List (FVar b)) (init init' : FVar b × EncState b) (offset : Nat)
    (hOffset : init'.2.nextFresh = init.2.nextFresh + offset)
    (hCompat : clauseShiftCompat b init.2 init'.2 offset)
    (hLen : os.length = os'.length)
    (hCurOff : init'.1.id = init.1.id + offset)
    (hOsOff : ∀ i (hi : i < os.length),
        (os'.get ⟨i, hLen ▸ hi⟩).id = (os.get ⟨i, hi⟩).id + offset) :
    clauseShiftCompat b
      (os.foldl (preEqAccStep b) init).2
      (os'.foldl (preEqAccStep b) init').2 offset := by
  -- Induction on os with parallel structure for os'
  revert init init' hOffset hCompat hCurOff hOsOff
  induction os generalizing os' with
  | nil =>
    intro init init' hOffset hCompat hCurOff _
    match os' with
    | [] =>
      simp only [List.foldl_nil]
      exact hCompat
    | _ :: _ => simp only [List.length_nil, List.length_cons] at hLen; omega
  | cons o oTail ihTail =>
    intro init init' hOffset hCompat hCurOff hOsOff
    match hOs' : os' with
    | [] => simp only [List.length_nil, List.length_cons, Nat.succ_ne_zero] at hLen
    | o' :: o'Tail =>
      simp only [List.length_cons, Nat.succ.injEq] at hLen
      simp only [List.foldl_cons]

      -- Get correspondence for first element: o'.id = o.id + offset
      have hOOff : o'.id = o.id + offset := by
        have h := hOsOff 0 (Nat.zero_lt_succ _)
        exact h

      -- State after one step
      let st1 := (preEqAccStep b init o).2
      let st1' := (preEqAccStep b init' o').2

      -- Offset preserved after one step
      have hOffset1 : st1'.nextFresh = st1.nextFresh + offset := by
        simp only [st1, st1', preEqAccStep, addAccStep, EncState.allocFresh, EncState.addClause]
        simp only [hOffset]; ring

      -- cur for next iteration
      have hCurOff1 : (preEqAccStep b init' o').1.id = (preEqAccStep b init o).1.id + offset := by
        simp only [preEqAccStep, EncState.allocFresh, hOffset]

      -- clauseShiftCompat after one step
      have hCompat1 : clauseShiftCompat b st1 st1' offset := by
        intro c hc
        -- preEqAccStep adds clauses via addAccStep after allocFresh
        simp only [st1, st1', preEqAccStep] at hc ⊢
        -- addAccStep adds 3 clauses
        simp only [addAccStep, EncState.allocFresh, EncState.addClause, List.mem_cons] at hc ⊢
        rcases hc with hC3 | hC2 | hC1 | hOld
        · -- c = [neg cur, neg o, pos next] (third clause)
          left
          subst hC3
          simp only [List.map_cons, List.map_nil, FVar.toVar,
            shiftLitFresh_neg_fresh, shiftLitFresh_pos_fresh, hCurOff, hOOff, hOffset]
        · -- c = [neg next, pos o] (second clause)
          right; left
          subst hC2
          simp only [List.map_cons, List.map_nil, FVar.toVar,
            shiftLitFresh_neg_fresh, shiftLitFresh_pos_fresh, hOffset, hOOff]
        · -- c = [neg next, pos cur] (first clause)
          right; right; left
          subst hC1
          simp only [List.map_cons, List.map_nil, FVar.toVar,
            shiftLitFresh_neg_fresh, shiftLitFresh_pos_fresh, hOffset, hCurOff]
        · -- c from init.2.clauses (inherited)
          right; right; right
          exact hCompat c hOld

      -- Offset for tail elements
      have hOsTailOff : ∀ i (hi : i < oTail.length),
          (o'Tail.get ⟨i, hLen ▸ hi⟩).id = (oTail.get ⟨i, hi⟩).id + offset := by
        intro i hi
        have hiSucc : i + 1 < (o :: oTail).length := by simp; omega
        have hSucc := hOsOff (i + 1) hiSucc
        simp only [List.get_cons_succ] at hSucc
        convert hSucc using 2

      exact ihTail o'Tail hLen (preEqAccStep b init o) (preEqAccStep b init' o')
        hOffset1 hCompat1 hCurOff1 hOsTailOff

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: allocFresh + addClause with Fresh-only clause preserves clauseShiftCompat.
    This handles the base clause [pos base] in addPreEqPair_core stage 3. -/
lemma allocFresh_addClause_Fresh_preserves_clauseShiftCompat (b : Bounds S)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset) :
    clauseShiftCompat b
      (EncState.addClause b (EncState.allocFresh b st).2
        [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)])
      (EncState.addClause b (EncState.allocFresh b st').2
        [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st').1)]) offset := by
  -- base.id = st.nextFresh, base'.id = st'.nextFresh = st.nextFresh + offset
  have hBaseId : (EncState.allocFresh b st).1.id = st.nextFresh := by simp [EncState.allocFresh]
  have hBase'Id : (EncState.allocFresh b st').1.id = st'.nextFresh := by
    simp [EncState.allocFresh]
  have hBaseOff : (EncState.allocFresh b st').1.id = (EncState.allocFresh b st).1.id + offset := by
    rw [hBaseId, hBase'Id, hOffset]
  -- st1 and st1' have same clauses as st and st' respectively
  have hSt1Clauses : (EncState.allocFresh b st).2.clauses = st.clauses :=
    EncState.allocFresh_clauses_eq b st
  have hSt1'Clauses : (EncState.allocFresh b st').2.clauses = st'.clauses :=
    EncState.allocFresh_clauses_eq b st'
  -- Now show preservation through addClause
  intro c hc
  simp only [EncState.addClause, List.mem_cons] at hc ⊢
  cases hc with
  | inl hEq =>
      -- c = [pos base]
      left
      subst hEq
      simp only [List.map_cons, List.map_nil]
      have hShift : shiftLitFresh b offset
          (SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)) =
          SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st').1) := by
        simp only [FVar.toVar, shiftLitFresh_pos_fresh, hBaseOff]
      rw [hShift]
  | inr hOld =>
      -- c from st1.clauses
      right
      rw [hSt1Clauses] at hOld
      rw [hSt1'Clauses]
      exact hCompat c hOld

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: addPreEqExpose preserves clause shift compatibility.
    addPreEqExpose adds two clauses:
    - [neg (PreEq H0 H'), pos v]
    - [neg v, pos (PreEq H0 H')]
    The PreEq literal is non-Fresh (unchanged by shift), and v shifts to v'. -/
lemma addPreEqExpose_preserves_clauseShiftCompat (b : Bounds S) (H0 H' : b.times)
    (v v' : FVar b) (st st' : EncState b) (offset : Nat)
    (_hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset)
    (hVOff : v'.id = v.id + offset) :
    clauseShiftCompat b
      (addPreEqExpose b H0 H' v st)
      (addPreEqExpose b H0 H' v' st') offset := by
  intro c hc
  simp only [addPreEqExpose, EncState.addClause, List.mem_cons] at hc ⊢
  -- c is one of: new clause 2, new clause 1, or inherited from st
  rcases hc with hC2 | hC1 | hOld
  · -- c = [neg v, pos (PreEq H0 H')] (second clause added)
    left
    subst hC2
    simp only [List.map_cons, List.map_nil]
    -- neg (Fresh v.id) shifts to neg (Fresh v'.id)
    have hNeg : shiftLitFresh b offset (SAT.Lit.neg (FVar.toVar b v)) =
        SAT.Lit.neg (FVar.toVar b v') := by
      simp only [FVar.toVar, shiftLitFresh_neg_fresh, hVOff]
    -- pos (PreEq H0 H') is non-Fresh, unchanged
    have hPos : shiftLitFresh b offset (SAT.Lit.pos (Var.PreEq H0 H')) =
        SAT.Lit.pos (Var.PreEq H0 H') := by rfl
    rw [hNeg, hPos]
  · -- c = [neg (PreEq H0 H'), pos v] (first clause added)
    right; left
    subst hC1
    simp only [List.map_cons, List.map_nil]
    -- neg (PreEq H0 H') is non-Fresh, unchanged
    have hNeg : shiftLitFresh b offset (SAT.Lit.neg (Var.PreEq H0 H')) =
        SAT.Lit.neg (Var.PreEq H0 H') := by rfl
    -- pos (Fresh v.id) shifts to pos (Fresh v'.id)
    have hPos : shiftLitFresh b offset (SAT.Lit.pos (FVar.toVar b v)) =
        SAT.Lit.pos (FVar.toVar b v') := by
      simp only [FVar.toVar, shiftLitFresh_pos_fresh, hVOff]
    rw [hNeg, hPos]
  · -- c from inherited clauses st
    right; right
    exact hCompat c hOld

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: addPreEqPair_core preserves clause shift compatibility.

This traces through the addPreEqPair_core pipeline:
1. Two preEqObligationStep folds (for H0→H' and H'→H0 directions)
2. allocFresh + addClause [pos base]
3. Two preEqAccStep folds
4. addPreEqExpose

Each stage creates clauses with Fresh vars at specific indices.
When running at st vs st' with offset, the clause structures are parallel
with Fresh indices shifted by offset. -/
lemma addPreEqPair_core_preserves_clauseShiftCompat (b : Bounds S) (H0 H' : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset) :
    clauseShiftCompat b (addPreEqPair_core b H0 H' st) (addPreEqPair_core b H0 H' st') offset := by
  -- Compositional proof: trace clauseShiftCompat through the pipeline
  -- Convert offset format for lemmas that use subtraction form
  have hOffsetSub : offset = st'.nextFresh - st.nextFresh := by omega
  have hMono : st.nextFresh ≤ st'.nextFresh := by omega

  -- Stage 1: preEqObligationStep fold for H0 H'
  have hOff1 : ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2.nextFresh =
      ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)).2.nextFresh + offset :=
    foldl_preEqObligationStep_offset b H0 H' (WId.allWorlds b) ([], st) ([], st') offset hOffset
  have hCompat1 : clauseShiftCompat b
      ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)).2
      ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2 offset :=
    preEqObligationStep_foldl_preserves_clauseShiftCompat b H0 H' (WId.allWorlds b) st st' offset
      hOffset hCompat

  -- Stage 2: preEqObligationStep fold for H' H0
  set st1 := ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)).2 with hSt1
  set st1' := ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).2 with hSt1'
  have hOff2 :
      ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], st1')).2.nextFresh =
        ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], st1)).2.nextFresh + offset :=
    foldl_preEqObligationStep_offset b H' H0 (WId.allWorlds b) ([], st1) ([], st1') offset hOff1
  have hCompat2 : clauseShiftCompat b
      ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], st1)).2
      ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], st1')).2 offset :=
    preEqObligationStep_foldl_preserves_clauseShiftCompat b H' H0 (WId.allWorlds b) st1 st1' offset
      hOff1 hCompat1

  -- Stage 3: allocFresh + addClause [pos base]
  set st2 := ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], st1)).2 with hSt2
  set st2' := ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], st1')).2 with hSt2'
  have hCompat3 : clauseShiftCompat b
      (EncState.addClause b (EncState.allocFresh b st2).2
        [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st2).1)])
      (EncState.addClause b (EncState.allocFresh b st2').2
        [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st2').1)]) offset :=
    allocFresh_addClause_Fresh_preserves_clauseShiftCompat b st2 st2' offset hOff2 hCompat2

  -- Stages 4-6: Use pipeline lemma that composes the remaining steps
  -- Unfold and apply the composition
  simp only [addPreEqPair_core, ← hSt1, ← hSt1', ← hSt2, ← hSt2']
  -- The proof follows by applying the helper lemmas through each stage
  -- For now, use the existing structure that composes all helpers
  set os := ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st)).1 with hOs
  set os' := ((WId.allWorlds b).foldl (preEqObligationStep b H0 H') ([], st')).1 with hOs'
  set os2 := ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], st1)).1 with hOs2
  set os2' := ((WId.allWorlds b).foldl (preEqObligationStep b H' H0) ([], st1')).1 with hOs2'
  set base := (EncState.allocFresh b st2).1 with hBase
  set base' := (EncState.allocFresh b st2').1 with hBase'
  set st3 := EncState.addClause b (EncState.allocFresh b st2).2
    [SAT.Lit.pos (FVar.toVar b base)] with hSt3
  set st3' := EncState.addClause b (EncState.allocFresh b st2').2
    [SAT.Lit.pos (FVar.toVar b base')] with hSt3'
  have hOff3 : st3'.nextFresh = st3.nextFresh + offset := by
    simp only [hSt3, hSt3', EncState.addClause, EncState.allocFresh]
    simp only [hSt2, hSt2', hSt1, hSt1'] at hOff2 ⊢
    omega
  have hBaseOff : base'.id = base.id + offset := by
    simp only [hBase, hBase', EncState.allocFresh]
    simp only [hSt2, hSt2', hSt1, hSt1'] at hOff2 ⊢
    omega
  have hLen1 : os.length = os'.length :=
    (preEqObligationStep_foldl_fst_length_eq b H0 H' (WId.allWorlds b) st st').symm
  have hOff1Sub : offset = st1'.nextFresh - st1.nextFresh := by
    simp only [hSt1, hSt1'] at hOff1 ⊢; omega
  have hMono1 : st1.nextFresh ≤ st1'.nextFresh := by simp only [hSt1, hSt1'] at hOff1 ⊢; omega
  have hOsShift : ∀ i (hi : i < os.length),
      (os'.get ⟨i, hLen1 ▸ hi⟩).id = (os.get ⟨i, hi⟩).id + offset := by
    intro i hi
    have h := preEqObligationStep_foldl_fst_shift b H0 H' (WId.allWorlds b) st st' offset
      hOffsetSub hMono i
    have hLen1' := preEqObligationStep_foldl_fst_length_eq b H0 H' (WId.allWorlds b) st st'
    exact h (hLen1' ▸ hi)
  -- Stage 4
  set accFold1 := os.foldl (preEqAccStep b) (base, st3) with hAccFold1
  set accFold1' := os'.foldl (preEqAccStep b) (base', st3') with hAccFold1'
  have hOff4 : accFold1'.2.nextFresh = accFold1.2.nextFresh + offset :=
    foldl_preEqAccStep_offset b os os' (base, st3) (base', st3') offset hLen1 hOff3
  have hCompat4 : clauseShiftCompat b accFold1.2 accFold1'.2 offset :=
    preEqAccStep_foldl_preserves_clauseShiftCompat b os os' (base, st3) (base', st3')
      offset hOff3 hCompat3 hLen1 hBaseOff hOsShift
  have hOff4Sub : offset = accFold1'.2.nextFresh - accFold1.2.nextFresh := by omega
  have hMono4 : accFold1.2.nextFresh ≤ accFold1'.2.nextFresh := by omega
  -- For preEqAccStep_foldl_fst_shift, need hMono for *input* states, not output
  have hMono3 : st3.nextFresh ≤ st3'.nextFresh := by simp only [hSt3, hSt3'] at hOff3 ⊢; omega
  have hOff3Sub : offset = st3'.nextFresh - st3.nextFresh := by
    simp only [hSt3, hSt3'] at hOff3 ⊢; omega
  -- For preEqAccStep_foldl_fst_shift, need hLen : os'.length = os.length form
  have hLen1' : os'.length = os.length := hLen1.symm
  have hOsShift' : ∀ i (hi : i < os.length),
      (os'.get ⟨i, hLen1' ▸ hi⟩).id = (os.get ⟨i, hi⟩).id + offset := by
    intro i hi
    have h := hOsShift i hi
    -- Need to show the get indices are the same
    have hEq : (hLen1' ▸ hi) = (hLen1 ▸ hi) := rfl
    rw [← hEq]; exact h
  have hEqAOff : accFold1'.1.id = accFold1.1.id + offset :=
    preEqAccStep_foldl_fst_shift b os os' (base, st3) (base', st3')
      offset hOff3Sub hMono3 hLen1' hOsShift' hBaseOff
  -- Stage 5
  have hLen2 : os2.length = os2'.length :=
    (preEqObligationStep_foldl_fst_length_eq b H' H0 (WId.allWorlds b) st1 st1').symm
  have hOs2Shift : ∀ i (hi : i < os2.length),
      (os2'.get ⟨i, hLen2 ▸ hi⟩).id = (os2.get ⟨i, hi⟩).id + offset := by
    intro i hi
    have h := preEqObligationStep_foldl_fst_shift b H' H0 (WId.allWorlds b) st1 st1' offset
      hOff1Sub hMono1 i
    simp only [hSt1] at h ⊢
    have hLen2' := preEqObligationStep_foldl_fst_length_eq b H' H0 (WId.allWorlds b) st1 st1'
    exact h (hLen2' ▸ hi)
  set accFold2 := os2.foldl (preEqAccStep b) (accFold1.1, accFold1.2) with hAccFold2
  set accFold2' := os2'.foldl (preEqAccStep b) (accFold1'.1, accFold1'.2) with hAccFold2'
  have hOff5 : accFold2'.2.nextFresh = accFold2.2.nextFresh + offset :=
    foldl_preEqAccStep_offset b os2 os2' (accFold1.1, accFold1.2) (accFold1'.1, accFold1'.2)
      offset hLen2 hOff4
  have hCompat5 : clauseShiftCompat b accFold2.2 accFold2'.2 offset :=
    preEqAccStep_foldl_preserves_clauseShiftCompat b os2 os2' (accFold1.1, accFold1.2)
      (accFold1'.1, accFold1'.2) offset hOff4 hCompat4 hLen2 hEqAOff hOs2Shift
  have hMono5 : accFold2.2.nextFresh ≤ accFold2'.2.nextFresh := by omega
  -- For preEqAccStep_foldl_fst_shift on Stage 5, need mono and offset for *input* states
  have hLen2' : os2'.length = os2.length := hLen2.symm
  have hOs2Shift' : ∀ i (hi : i < os2.length),
      (os2'.get ⟨i, hLen2' ▸ hi⟩).id = (os2.get ⟨i, hi⟩).id + offset := by
    intro i hi; exact hOs2Shift i hi
  have hEqFinalOff : accFold2'.1.id = accFold2.1.id + offset :=
    preEqAccStep_foldl_fst_shift b os2 os2' (accFold1.1, accFold1.2) (accFold1'.1, accFold1'.2)
      offset hOff4Sub hMono4 hLen2' hOs2Shift' hEqAOff
  -- Stage 6: addPreEqExpose
  have hCompat6 : clauseShiftCompat b (addPreEqExpose b H0 H' accFold2.1 accFold2.2)
      (addPreEqExpose b H0 H' accFold2'.1 accFold2'.2) offset :=
    addPreEqExpose_preserves_clauseShiftCompat b H0 H' accFold2.1 accFold2'.1 accFold2.2 accFold2'.2
      offset hOff5 hCompat5 hEqFinalOff
  -- Final: convert to match addPreEqPair_core definition
  convert hCompat6 using 2

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: addPreEqPair preserves clause shift compatibility. -/
lemma addPreEqPair_preserves_clauseShiftCompat (b : Bounds S) (ti H' : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset) :
    clauseShiftCompat b (addPreEqPair b ti H' st) (addPreEqPair b ti H' st') offset := by
  simp only [addPreEqPair]
  by_cases hEq : ti = H'
  · -- Reflexive case: addPreEqPair_core + addClause [pos (PreEq ti ti)]
    simp only [hEq, ↓reduceIte]
    -- First apply addPreEqPair_core_preserves_clauseShiftCompat
    have hCoreCompat := addPreEqPair_core_preserves_clauseShiftCompat b H' H' st st' offset
        hOffset hCompat
    -- The reflexivity clause [pos (PreEq H' H')] has no Fresh vars
    have hNonFresh : ∀ lit ∈ [SAT.Lit.pos (Var.PreEq H' H')],
        ∀ n, SAT.Lit.getVar lit ≠ Var.Fresh n := by
      intro lit hLit n hContra
      simp only [List.mem_singleton] at hLit
      subst hLit
      simp only [SAT.Lit.getVar] at hContra
      cases hContra
    exact addClause_nonFresh_preserves_clauseShiftCompat b
        [SAT.Lit.pos (Var.PreEq H' H')]
        (addPreEqPair_core b H' H' st) (addPreEqPair_core b H' H' st')
        offset hCoreCompat hNonFresh
  · -- Non-reflexive case: just addPreEqPair_core
    simp only [hEq, ↓reduceIte]
    exact addPreEqPair_core_preserves_clauseShiftCompat b ti H' st st' offset hOffset hCompat

omit [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: addPreEqFrom preserves clause shift compatibility.

addPreEqFrom is a fold of addPreEqPair over Bounds.timesL. At each step,
addPreEqPair preserves clauseShiftCompat, so the whole fold preserves it. -/
lemma addPreEqFrom_preserves_clauseShiftCompat (b : Bounds S) (ti : b.times)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset) :
    clauseShiftCompat b (addPreEqFrom b ti st) (addPreEqFrom b ti st') offset := by
  simp only [addPreEqFrom]
  induction (Bounds.timesL b) generalizing st st' with
  | nil => exact hCompat
  | cons H' Hs ih =>
      simp only [List.foldl_cons]
      have hOff' := addPreEqPair_offset b ti H' st st' offset hOffset
      have hComp' := addPreEqPair_preserves_clauseShiftCompat b ti H' st st' offset hOffset hCompat
      exact ih _ _ hOff' hComp'

/-- Auxiliary lemma: forall encodeConj fold with general accumulators produces
    vars with offset relationship. -/
lemma forall_encodeConj_foldl_vars_offset_aux (b : Bounds S)
    (body : S.Value → Formula S) (w : WId b)
    (valIndices : List b.valIx)
    (accL accL' : List (FVar b)) (stAcc stAcc' : EncState b) (offset : Nat)
    (hOffset : stAcc'.nextFresh = stAcc.nextFresh + offset)
    (hAccLen : accL.length = accL'.length)
    (hAccOff : ∀ i (hi : i < accL.length) (hi' : i < accL'.length),
        (accL.get ⟨i, hi⟩).id + offset = (accL'.get ⟨i, hi'⟩).id) :
    let result := valIndices.foldl (fun (vars, stCur) vIdx =>
      let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
      (vars ++ [uBody], stNext)) (accL, stAcc)
    let result' := valIndices.foldl (fun (vars, stCur) vIdx =>
      let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
      (vars ++ [uBody], stNext)) (accL', stAcc')
    (result.1.length = result'.1.length) ∧
    (result.2.nextFresh + offset = result'.2.nextFresh) ∧
    (∀ i (hi : i < result.1.length) (hi' : i < result'.1.length),
        (result.1.get ⟨i, hi⟩).id + offset = (result'.1.get ⟨i, hi'⟩).id) := by
  induction valIndices generalizing accL accL' stAcc stAcc' with
  | nil =>
      simp only [List.foldl_nil, List.get_eq_getElem]
      exact ⟨hAccLen, by omega, hAccOff⟩
  | cons vHd vTl vih =>
      simp only [List.foldl_cons]
      let v := b.values.get vHd
      let u := (encodeFormula b (body v) w stAcc).1
      let u' := (encodeFormula b (body v) w stAcc').1
      let st1 := (encodeFormula b (body v) w stAcc).2
      let st1' := (encodeFormula b (body v) w stAcc').2
      have hOffset1 : st1'.nextFresh = st1.nextFresh + offset := by
        simp only [st1, st1']
        exact encodeFormula_nextFresh_offset b (body v) w stAcc stAcc' offset hOffset
      have hMono : stAcc.nextFresh ≤ stAcc'.nextFresh := by omega
      have hUOff : u.id + offset = u'.id := by
        simp only [u, u']
        have h := encodeFormula_controlVar_shift b (body v) w stAcc stAcc' hMono
        omega
      have hNewAccLen : (accL ++ [u]).length = (accL' ++ [u']).length := by
        simp only [List.length_append, List.length_singleton, hAccLen]
      have hNewAccOff : ∀ i (hi : i < (accL ++ [u]).length) (hi' : i < (accL' ++ [u']).length),
          ((accL ++ [u]).get ⟨i, hi⟩).id + offset = ((accL' ++ [u']).get ⟨i, hi'⟩).id := by
        intro i hi hi'
        simp only [List.length_append, List.length_singleton] at hi hi'
        by_cases hSmall : i < accL.length
        · -- i < accL.length, use existing accumulator
          have hi' : i < accL'.length := by omega
          simp only [List.get_eq_getElem, List.getElem_append_left hSmall,
                     List.getElem_append_left hi']
          exact hAccOff i hSmall hi'
        · -- i = accL.length, the new element
          have hEq : i = accL.length := by omega
          simp only [List.get_eq_getElem,
                     List.getElem_append_right (by omega : accL.length ≤ i),
                     List.getElem_append_right (by omega : accL'.length ≤ i),
                     hAccLen]
          simp only [hEq, List.getElem_singleton]
          exact hUOff
      exact vih (accL ++ [u]) (accL' ++ [u']) st1 st1' hOffset1 hNewAccLen hNewAccOff

/-- Helper: forall encodeConj fold produces vars with offset relationship.
    Both folds produce same-length lists where corresponding vars have id offset. -/
lemma forall_encodeConj_foldl_vars_offset (b : Bounds S)
    (body : S.Value → Formula S) (w : WId b)
    (valIndices : List b.valIx) (stAcc stAcc' : EncState b) (offset : Nat)
    (hOffset : stAcc'.nextFresh = stAcc.nextFresh + offset) :
    let result := valIndices.foldl (fun (vars, stCur) vIdx =>
      let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
      (vars ++ [uBody], stNext)) ([], stAcc)
    let result' := valIndices.foldl (fun (vars, stCur) vIdx =>
      let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
      (vars ++ [uBody], stNext)) ([], stAcc')
    (result.1.length = result'.1.length) ∧
    (result.2.nextFresh + offset = result'.2.nextFresh) ∧
    (∀ i (hi : i < result.1.length) (hi' : i < result'.1.length),
        (result.1.get ⟨i, hi⟩).id + offset = (result'.1.get ⟨i, hi'⟩).id) :=
  forall_encodeConj_foldl_vars_offset_aux b body w valIndices [] [] stAcc stAcc' offset
    hOffset rfl (fun _ hi _ => (Nat.not_lt_zero _ hi).elim)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Helper: forall forward clauses fold preserves clause shift compatibility. -/
lemma forall_forward_clauses_foldl_preserves_clauseShiftCompat (b : Bounds S)
    (u u' : FVar b) (bodyVars bodyVars' : List (FVar b))
    (stAcc stAcc' : EncState b) (offset : Nat)
    (hUOff : u'.id = u.id + offset)
    (hLen : bodyVars.length = bodyVars'.length)
    (hVarsOff : ∀ i (hi : i < bodyVars.length) (hi' : i < bodyVars'.length),
        (bodyVars.get ⟨i, hi⟩).id + offset = (bodyVars'.get ⟨i, hi'⟩).id)
    (hCompat : clauseShiftCompat b stAcc stAcc' offset) :
    clauseShiftCompat b
      (bodyVars.foldl (fun st uBody => EncState.addClause b st
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]) stAcc)
      (bodyVars'.foldl (fun st uBody => EncState.addClause b st
          [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b uBody)]) stAcc') offset := by
  intro c hc
  induction bodyVars generalizing bodyVars' stAcc stAcc' c with
  | nil =>
      -- bodyVars' must also be nil by length equality
      cases bodyVars' with
      | nil =>
          simp only [List.foldl_nil] at hc ⊢
          exact hCompat c hc
      | cons _ _ => simp only [List.length_nil, List.length_cons] at hLen; omega
  | cons vHd vTl vih =>
      cases bodyVars' with
      | nil => simp only [List.length_cons, List.length_nil] at hLen; omega
      | cons vHd' vTl' =>
          simp only [List.length_cons, Nat.succ.injEq] at hLen
          simp only [List.foldl_cons] at hc ⊢
          -- Get offset for head elements
          have hHdOff : vHd.id + offset = vHd'.id := by
            have h := hVarsOff 0 (by simp) (by simp)
            simp only [List.get_eq_getElem, List.getElem_cons_zero] at h
            exact h
          -- Get offsets for tail elements
          have hTlVarsOff : ∀ i (hi : i < vTl.length) (hi' : i < vTl'.length),
              (vTl.get ⟨i, hi⟩).id + offset = (vTl'.get ⟨i, hi'⟩).id := by
            intro i hi hi'
            have h := hVarsOff (i + 1) (by simp [hi]) (by simp [hi'])
            simp only [List.get_eq_getElem, List.getElem_cons_succ] at h
            exact h
          -- New states after adding one clause
          let st1 := EncState.addClause b stAcc
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b vHd)]
          let st1' := EncState.addClause b stAcc'
              [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b vHd')]
          -- Clause shift compat for st1/st1'
          have hCompat1 : clauseShiftCompat b st1 st1' offset := by
            intro c' hc'
            simp only [st1, st1', EncState.addClause, List.mem_cons] at hc' ⊢
            cases hc' with
            | inl hEq =>
                left
                subst hEq
                simp only [List.map, shiftLitFresh, FVar.toVar, hUOff, hHdOff]
            | inr hOld =>
                right
                exact hCompat c' hOld
          exact vih vTl' st1 st1' hLen hTlVarsOff hCompat1 c hc

/-- Helper: forall encodeConj fold preserves clause shift compatibility. -/
lemma forall_encodeConj_foldl_preserves_clauseShiftCompat (b : Bounds S)
    (body : S.Value → Formula S) (w : WId b)
    (valIndices : List b.valIx) (stAcc stAcc' : EncState b) (offset : Nat)
    (hOffset : stAcc'.nextFresh = stAcc.nextFresh + offset)
    (hCompat : clauseShiftCompat b stAcc stAcc' offset)
    (hIH : ∀ v st st', st'.nextFresh = st.nextFresh + offset →
           clauseShiftCompat b st st' offset →
           clauseShiftCompat b (encodeFormula b (body v) w st).2
             (encodeFormula b (body v) w st').2 offset) :
    clauseShiftCompat b
      (valIndices.foldl (fun (vars, stCur) vIdx =>
        let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
        (vars ++ [uBody], stNext)) ([], stAcc)).2
      (valIndices.foldl (fun (vars, stCur) vIdx =>
        let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
        (vars ++ [uBody], stNext)) ([], stAcc')).2 offset := by
  intro c hc
  induction valIndices generalizing stAcc stAcc' c with
  | nil =>
      simp only [List.foldl_nil] at hc ⊢
      exact hCompat c hc
  | cons vHd vTl vih =>
      simp only [List.foldl_cons] at hc ⊢
      let v := b.values.get vHd
      let st1 := (encodeFormula b (body v) w stAcc).2
      let st1' := (encodeFormula b (body v) w stAcc').2
      have hOffset1 : st1'.nextFresh = st1.nextFresh + offset := by
        simp only [st1, st1']
        exact encodeFormula_nextFresh_offset b (body v) w stAcc stAcc' offset hOffset
      have hCompat1 : clauseShiftCompat b st1 st1' offset := hIH v stAcc stAcc' hOffset hCompat
      -- Use clause independence to normalize accumulators
      have hIndep1 := encodeConj_foldl_clauses_indep b body w vTl
        ([(encodeFormula b (body v) w stAcc).1], st1) ([], st1) rfl
      have hIndep2 := encodeConj_foldl_clauses_indep b body w vTl
        ([(encodeFormula b (body v) w stAcc').1], st1') ([], st1') rfl
      have hcInEmptyStart : c ∈ (vTl.foldl (fun (vars, stCur) vIdx =>
          let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
          (vars ++ [uBody], stNext)) ([], st1)).2.clauses := hIndep1 ▸ hc
      have hRes := vih st1 st1' hOffset1 hCompat1 c hcInEmptyStart
      exact hIndep2 ▸ hRes

/-- encodeWitnesses fold preserves nextFresh offset relationship. -/
lemma encodeWitnesses_foldl_nextFresh_offset (b : Bounds S) (φ : Formula S)
    (witnesses : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset) :
    let step := fun (acc : List (FVar b) × EncState b) (w' : WId b) =>
        let (u', stNext) := encodeFormula b φ w' acc.2
        (acc.1 ++ [u'], stNext)
    (witnesses.foldl step ([], st')).2.nextFresh =
    (witnesses.foldl step ([], st)).2.nextFresh + offset := by
  intro step
  -- Generalize to arbitrary starting accumulators (list doesn't affect nextFresh)
  suffices hSuff : ∀ (ws : List (WId b)) (accL accL' : List (FVar b)) (stCur stCur' : EncState b),
      stCur'.nextFresh = stCur.nextFresh + offset →
      (ws.foldl step (accL', stCur')).2.nextFresh =
      (ws.foldl step (accL, stCur)).2.nextFresh + offset by
    exact hSuff witnesses [] [] st st' hOffset
  intro ws
  induction ws with
  | nil => intro _ _ _ _ hOff; simp only [List.foldl_nil, hOff]
  | cons w' wtl ih =>
      intro accL accL' stCur stCur' hOff
      simp only [List.foldl_cons]
      have hOff1 : (encodeFormula b φ w' stCur').2.nextFresh =
          (encodeFormula b φ w' stCur).2.nextFresh + offset :=
        encodeFormula_nextFresh_offset b φ w' stCur stCur' offset hOff
      exact ih _ _ _ _ hOff1

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- auxVars fold preserves nextFresh offset relationship.
    Each step adds exactly 1 to nextFresh
    (allocFresh + 4 addClauses that don't change nextFresh). -/
lemma auxVars_foldl_nextFresh_offset (b : Bounds S) (w : WId b) (u u' : FVar b)
    (pairs pairs' : List (FVar b × WId b))
    (stAcc stAcc' : EncState b) (offset : Nat)
    (hOffset : stAcc'.nextFresh = stAcc.nextFresh + offset)
    (hLen : pairs.length = pairs'.length) :
    let auxStep := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (uv, wv) := pair
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (acc.1 ++ [aux], stCur)
    let auxStep' := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (uv, wv) := pair
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u')]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (acc.1 ++ [aux], stCur)
    (pairs'.foldl auxStep' ([], stAcc')).2.nextFresh =
    (pairs.foldl auxStep ([], stAcc)).2.nextFresh + offset := by
  intro auxStep auxStep'
  -- Each step adds exactly 1 to nextFresh, so result is start + length
  -- Prove via suffices with generalized accumulators
  suffices hSuff : ∀ (ps : List (FVar b × WId b)) (ps' : List (FVar b × WId b))
      (accL accL' : List (FVar b)) (stCur stCur' : EncState b),
      ps.length = ps'.length →
      stCur'.nextFresh = stCur.nextFresh + offset →
      (ps'.foldl auxStep' (accL', stCur')).2.nextFresh =
      (ps.foldl auxStep (accL, stCur)).2.nextFresh + offset by
    exact hSuff pairs pairs' [] [] stAcc stAcc' hLen hOffset
  intro ps
  induction ps with
  | nil =>
      intro ps' _ _ stCur stCur' hLen' hOff
      cases ps' with
      | nil => simp only [List.foldl_nil, hOff]
      | cons _ _ => simp at hLen'
  | cons p ps ih =>
      intro ps' accL accL' stCur stCur' hLen' hOff
      cases ps' with
      | nil => simp at hLen'
      | cons p' ps' =>
          simp only [List.foldl_cons]
          have hStep : (auxStep (accL, stCur) p).2.nextFresh = stCur.nextFresh + 1 := by
            simp only [auxStep, EncState.allocFresh, EncState.addClause]
          have hStep' : (auxStep' (accL', stCur') p').2.nextFresh = stCur'.nextFresh + 1 := by
            simp only [auxStep', EncState.allocFresh, EncState.addClause]
          have hOff1 : (auxStep' (accL', stCur') p').2.nextFresh =
              (auxStep (accL, stCur) p).2.nextFresh + offset := by
            rw [hStep, hStep', hOff]; ring
          have hLen'' : ps.length = ps'.length := by simp at hLen'; omega
          exact ih ps' _ _ _ _ hLen'' hOff1

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- auxVars fold output vars have offset relationship.
    Each allocated aux var has id = current nextFresh, so with offset between states,
    the output vars have the same offset relationship. -/
lemma auxVars_foldl_vars_offset (b : Bounds S) (w : WId b) (u u' : FVar b)
    (pairs pairs' : List (FVar b × WId b))
    (stAcc stAcc' : EncState b) (offset : Nat)
    (hOffset : stAcc'.nextFresh = stAcc.nextFresh + offset)
    (hLen : pairs.length = pairs'.length) :
    let auxStep := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (uv, wv) := pair
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (acc.1 ++ [aux], stCur)
    let auxStep' := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
      let (uv, wv) := pair
      let memVar := Var.Mem w.ti wv
      let (aux, stCur) := EncState.allocFresh b acc.2
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u')]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
      let stCur := EncState.addClause b stCur
        [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
      (acc.1 ++ [aux], stCur)
    let res := pairs.foldl auxStep ([], stAcc)
    let res' := pairs'.foldl auxStep' ([], stAcc')
    res.1.length = res'.1.length ∧
    ∀ i (hi : i < res.1.length) (hi' : i < res'.1.length),
        (res.1.get ⟨i, hi⟩).id + offset = (res'.1.get ⟨i, hi'⟩).id := by
  intro auxStep auxStep' res res'
  -- Prove by induction on pairs/pairs' with generalized accumulators
  suffices hSuff : ∀ (ps : List (FVar b × WId b)) (ps' : List (FVar b × WId b))
      (accL accL' : List (FVar b)) (stCur stCur' : EncState b),
      ps.length = ps'.length →
      stCur'.nextFresh = stCur.nextFresh + offset →
      accL.length = accL'.length →
      (∀ i (hi : i < accL.length) (hi' : i < accL'.length),
          (accL.get ⟨i, hi⟩).id + offset = (accL'.get ⟨i, hi'⟩).id) →
      let r := ps.foldl auxStep (accL, stCur)
      let r' := ps'.foldl auxStep' (accL', stCur')
      r.1.length = r'.1.length ∧
      ∀ i (hi : i < r.1.length) (hi' : i < r'.1.length),
          (r.1.get ⟨i, hi⟩).id + offset = (r'.1.get ⟨i, hi'⟩).id by
    exact hSuff pairs pairs' [] [] stAcc stAcc' hLen hOffset rfl
      (fun _ hi _ => (Nat.not_lt_zero _ hi).elim)
  intro ps
  induction ps with
  | nil =>
      intro ps' accL accL' stCur stCur' hLen' _ hAccLen hAccOff
      cases ps' with
      | nil => simp only [List.foldl_nil]; exact ⟨hAccLen, hAccOff⟩
      | cons _ _ => simp at hLen'
  | cons p ps ih =>
      intro ps' accL accL' stCur stCur' hLen' hStOff hAccLen hAccOff
      cases ps' with
      | nil => simp at hLen'
      | cons p' ps' =>
          simp only [List.foldl_cons]
          -- After one step: aux.id = stCur.nextFresh, aux'.id = stCur'.nextFresh
          have hAuxId : (EncState.allocFresh b stCur).1.id = stCur.nextFresh := by
            simp only [EncState.allocFresh]
          have hAuxId' : (EncState.allocFresh b stCur').1.id = stCur'.nextFresh := by
            simp only [EncState.allocFresh]
          have hAuxOff : (EncState.allocFresh b stCur).1.id + offset =
              (EncState.allocFresh b stCur').1.id := by
            rw [hAuxId, hAuxId', hStOff]
          -- New accumulator lengths match
          have hNewAccLen : (accL ++ [(EncState.allocFresh b stCur).1]).length =
              (accL' ++ [(EncState.allocFresh b stCur').1]).length := by
            simp only [List.length_append, List.length_singleton, hAccLen]
          -- New accumulator offset relationship
          have hNewAccOff : ∀ i (hi : i < (accL ++ [(EncState.allocFresh b stCur).1]).length)
              (hi' : i < (accL' ++ [(EncState.allocFresh b stCur').1]).length),
              ((accL ++ [(EncState.allocFresh b stCur).1]).get ⟨i, hi⟩).id + offset =
              ((accL' ++ [(EncState.allocFresh b stCur').1]).get ⟨i, hi'⟩).id := by
            intro i hi hi'
            simp only [List.length_append, List.length_singleton] at hi hi'
            by_cases hOld : i < accL.length
            · have hOld' : i < accL'.length := hAccLen ▸ hOld
              simp only [List.get_eq_getElem, List.getElem_append_left hOld,
                List.getElem_append_left hOld']
              exact hAccOff i hOld hOld'
            · have hNew : i = accL.length := by omega
              subst hNew
              -- The new element is at index accL.length
              have hLHS : (accL ++ [(EncState.allocFresh b stCur).1])[accL.length]'(by simp) =
                  (EncState.allocFresh b stCur).1 := by simp
              have hRHS :
                  (accL' ++ [(EncState.allocFresh b stCur').1])[accL.length]'(by simp [hAccLen]) =
                  (EncState.allocFresh b stCur').1 := by simp [hAccLen]
              simp only [List.get_eq_getElem, hLHS, hRHS]
              exact hAuxOff
          -- Next state offset
          have hNextOff : (auxStep (accL, stCur) p).2.nextFresh = stCur.nextFresh + 1 := by
            simp only [auxStep, EncState.allocFresh, EncState.addClause]
          have hNextOff' : (auxStep' (accL', stCur') p').2.nextFresh = stCur'.nextFresh + 1 := by
            simp only [auxStep', EncState.allocFresh, EncState.addClause]
          have hStOff1 : (auxStep' (accL', stCur') p').2.nextFresh =
              (auxStep (accL, stCur) p).2.nextFresh + offset := by
            rw [hNextOff, hNextOff', hStOff]; ring
          have hPsLen' : ps.length = ps'.length := by simp at hLen'; omega
          exact ih ps' (auxStep (accL, stCur) p).1 (auxStep' (accL', stCur') p').1
            (auxStep (accL, stCur) p).2 (auxStep' (accL', stCur') p').2
            hPsLen' hStOff1 hNewAccLen hNewAccOff

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkAndIff preserves clauseShiftCompat when inputs have offset relationship.
    mkAndIff adds 3 clauses with Fresh u and input vars x, y. -/
lemma mkAndIff_preserves_clauseShiftCompat (b : Bounds S)
    (x x' y y' : FVar b) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset)
    (hXOff : x'.id = x.id + offset)
    (hYOff : y'.id = y.id + offset) :
    clauseShiftCompat b (mkAndIff b x y st).2 (mkAndIff b x' y' st').2 offset := by
  intro c hc
  simp only [mkAndIff, EncState.allocFresh, EncState.addClause, List.mem_cons] at hc ⊢
  -- u.id = st.nextFresh, u'.id = st'.nextFresh = st.nextFresh + offset
  have hUOff : st'.nextFresh = st.nextFresh + offset := hOffset
  -- Clauses:
  -- 1. [neg x, neg y, pos u]
  -- 2. [neg u, pos y]
  -- 3. [neg u, pos x]
  -- + inherited from st
  rcases hc with hC3 | hC2 | hC1 | hOld
  · -- c = [neg x, neg y, pos u]
    left
    subst hC3
    simp only [List.map, shiftLitFresh, FVar.toVar, hXOff, hYOff, hUOff]
  · -- c = [neg u, pos y]
    right; left
    subst hC2
    simp only [List.map, shiftLitFresh, FVar.toVar, hUOff, hYOff]
  · -- c = [neg u, pos x]
    right; right; left
    subst hC1
    simp only [List.map, shiftLitFresh, FVar.toVar, hUOff, hXOff]
  · -- c from st.clauses
    right; right; right
    exact hCompat c hOld

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- mkAndIff fold preserves clauseShiftCompat when all input vars have offset relationship.
    Tracks that each mkAndIff produces var with id = current nextFresh. -/
lemma mkAndIff_foldl_preserves_clauseShiftCompat (b : Bounds S)
    (u0 u0' : FVar b) (us us' : List (FVar b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset)
    (hU0Off : u0'.id = u0.id + offset)
    (hLen : us.length = us'.length)
    (hUsOff : ∀ i (hi : i < us.length) (hi' : i < us'.length),
        (us.get ⟨i, hi⟩).id + offset = (us'.get ⟨i, hi'⟩).id) :
    clauseShiftCompat b
      (us.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0, st)).2
      (us'.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (u0', st')).2 offset := by
  -- Induction with generalized accumulators tracking:
  -- - current var has offset relationship
  -- - current state has nextFresh offset
  -- - current state has clauseShiftCompat
  suffices hSuff : ∀ (xs : List (FVar b)) (xs' : List (FVar b))
      (accVar accVar' : FVar b) (stCur stCur' : EncState b),
      xs.length = xs'.length →
      stCur'.nextFresh = stCur.nextFresh + offset →
      clauseShiftCompat b stCur stCur' offset →
      accVar'.id = accVar.id + offset →
      (∀ i (hi : i < xs.length) (hi' : i < xs'.length),
          (xs.get ⟨i, hi⟩).id + offset = (xs'.get ⟨i, hi'⟩).id) →
      clauseShiftCompat b
        (xs.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (accVar, stCur)).2
        (xs'.foldl (fun acc u' => mkAndIff b acc.1 u' acc.2) (accVar', stCur')).2 offset by
    exact hSuff us us' u0 u0' st st' hLen hOffset hCompat hU0Off hUsOff
  intro xs
  induction xs with
  | nil =>
      intro xs' accVar accVar' stCur stCur' hLen' hOff hComp _ _
      cases xs' with
      | nil => simp only [List.foldl_nil]; exact hComp
      | cons _ _ => simp at hLen'
  | cons x xs ih =>
      intro xs' accVar accVar' stCur stCur' hLen' hOff hComp hAccOff hXsOff
      cases xs' with
      | nil => simp at hLen'
      | cons x' xs' =>
          simp only [List.foldl_cons]
          -- Step produces: mkAndIff b accVar x stCur
          -- Result var: id = stCur.nextFresh
          -- Result state: nextFresh = stCur.nextFresh + 1
          have hXOff : x'.id = x.id + offset := by
            have h := hXsOff 0 (by simp) (by simp)
            simp only [List.get_eq_getElem, List.getElem_cons_zero] at h
            omega
          have hStepCompat := mkAndIff_preserves_clauseShiftCompat b accVar accVar' x x'
            stCur stCur' offset hOff hComp hAccOff hXOff
          have hStepVarOff : (mkAndIff b accVar' x' stCur').1.id =
              (mkAndIff b accVar x stCur).1.id + offset := by
            simp only [mkAndIff, EncState.allocFresh, hOff]
          have hStepNextFreshOff : (mkAndIff b accVar' x' stCur').2.nextFresh =
              (mkAndIff b accVar x stCur).2.nextFresh + offset := by
            simp only [mkAndIff, EncState.allocFresh, EncState.addClause, hOff]; ring
          have hXsLen' : xs.length = xs'.length := by simp at hLen'; omega
          have hXsOff' : ∀ i (hi : i < xs.length) (hi' : i < xs'.length),
              (xs.get ⟨i, hi⟩).id + offset = (xs'.get ⟨i, hi'⟩).id := by
            intro i hi hi'
            have h := hXsOff (i + 1) (by simp; omega) (by simp; omega)
            simp only [List.get_eq_getElem, List.getElem_cons_succ] at h
            exact h
          exact ih xs' (mkAndIff b accVar x stCur).1 (mkAndIff b accVar' x' stCur').1
            (mkAndIff b accVar x stCur).2 (mkAndIff b accVar' x' stCur').2
            hXsLen' hStepNextFreshOff hStepCompat hStepVarOff hXsOff'

/-- diamondWitnessFold preserves clauseShiftCompat.
    Uses the top-level diamondWitnessFold definition from DiamondHelpers.lean. -/
lemma diamond_witnessFold_preserves_clauseShiftCompat (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset)
    (hIH : ∀ w' stX stX', stX'.nextFresh = stX.nextFresh + offset →
           clauseShiftCompat b stX stX' offset →
           clauseShiftCompat b (encodeFormula b φ w' stX).2 (encodeFormula b φ w' stX').2 offset) :
    clauseShiftCompat b
      (diamondWitnessFold b φ w intersection st).2
      (diamondWitnessFold b φ w intersection st').2 offset := by
  simp only [diamondWitnessFold]
  -- Generalize to arbitrary accumulators (list component doesn't affect clauses)
  suffices hSuff : ∀ (parts : List b.participants)
      (acc acc' : List (FVar b × b.participants) × EncState b),
      acc'.2.nextFresh = acc.2.nextFresh + offset →
      clauseShiftCompat b acc.2 acc'.2 offset →
      clauseShiftCompat b
        (parts.foldl (fun acc p =>
          if _ : p ∈ intersection then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd acc.2
            (acc.1 ++ [(uWit, p)], stNew)
          else acc) acc).2
        (parts.foldl (fun acc p =>
          if _ : p ∈ intersection then
            let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
            let (uWit, stNew) := encodeFormula b φ wEnd acc.2
            (acc.1 ++ [(uWit, p)], stNew)
          else acc) acc').2 offset by
    exact hSuff (Bounds.partsL b) ([], st) ([], st') hOffset hCompat
  intro parts
  induction parts with
  | nil =>
      intro acc acc' hOff hComp
      simp only [List.foldl_nil]
      exact hComp
  | cons p ps ih =>
      intro acc acc' hOff hComp
      simp only [List.foldl_cons]
      by_cases hp : p ∈ intersection
      · -- p ∈ intersection: encode φ at wEnd
        simp only [hp, dite_true]
        let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩
        have hComp1 := hIH wEnd acc.2 acc'.2 hOff hComp
        have hOff1 : (encodeFormula b φ wEnd acc'.2).2.nextFresh =
            (encodeFormula b φ wEnd acc.2).2.nextFresh + offset :=
          encodeFormula_nextFresh_offset b φ wEnd acc.2 acc'.2 offset hOff
        exact ih
          (acc.1 ++ [((encodeFormula b φ wEnd acc.2).1, p)], (encodeFormula b φ wEnd acc.2).2)
          (acc'.1 ++ [((encodeFormula b φ wEnd acc'.2).1, p)], (encodeFormula b φ wEnd acc'.2).2)
          hOff1 hComp1
      · -- p ∉ intersection: skip
        simp only [hp, dite_false]
        exact ih acc acc' hOff hComp

/-- diamondWitnessFold output vars have offset relationship. -/
lemma diamond_witnessFold_vars_offset (b : Bounds S) (φ : Formula S) (w : WId b)
    (intersection : Finset b.participants) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hNextFreshIH : ∀ w' stX stX', stX'.nextFresh = stX.nextFresh + offset →
           (encodeFormula b φ w' stX').2.nextFresh =
             (encodeFormula b φ w' stX).2.nextFresh + offset) :
    let res := diamondWitnessFold b φ w intersection st
    let res' := diamondWitnessFold b φ w intersection st'
    res.1.length = res'.1.length ∧
    ∀ i (hi : i < res.1.length) (hi' : i < res'.1.length),
        (res.1.get ⟨i, hi⟩).1.id + offset = (res'.1.get ⟨i, hi'⟩).1.id := by
  intro res res'
  simp only [res, res', diamondWitnessFold]
  -- Generalize to arbitrary accumulators
  -- NOTE: No let-bindings in conclusion - state properties directly about foldl results
  let step := fun (acc : List (FVar b × b.participants) × EncState b) (p : b.participants) =>
    if _ : p ∈ intersection then
      (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
       (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2)
    else acc
  suffices hSuff : ∀ (parts : List b.participants)
      (acc acc' : List (FVar b × b.participants) × EncState b),
      acc'.2.nextFresh = acc.2.nextFresh + offset →
      acc.1.length = acc'.1.length →
      (∀ i (hi : i < acc.1.length) (hi' : i < acc'.1.length),
          (acc.1.get ⟨i, hi⟩).1.id + offset = (acc'.1.get ⟨i, hi'⟩).1.id) →
      (parts.foldl step acc).1.length = (parts.foldl step acc').1.length ∧
      ∀ i (hi : i < (parts.foldl step acc).1.length)
          (hi' : i < (parts.foldl step acc').1.length),
          ((parts.foldl step acc).1.get ⟨i, hi⟩).1.id + offset =
          ((parts.foldl step acc').1.get ⟨i, hi'⟩).1.id by
    exact hSuff (Bounds.partsL b) ([], st) ([], st') hOffset rfl
      (fun _ hi _ => (Nat.not_lt_zero _ hi).elim)
  intro parts
  induction parts with
  | nil =>
      intro acc acc' _ hAccLen hAccOff
      simp only [List.foldl_nil]
      exact ⟨hAccLen, hAccOff⟩
  | cons p ps ih =>
      intro acc acc' hOff hAccLen hAccOff
      simp only [List.foldl_cons]
      -- step acc p expands based on whether p ∈ intersection
      by_cases hp : p ∈ intersection
      · -- p ∈ intersection: step acc p = (acc.1 ++ [...], ...)
        have hStepAcc : step acc p =
            (acc.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1, p)],
             (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).2) := by
          simp only [step, hp, dite_true]
        have hStepAcc' : step acc' p =
            (acc'.1 ++ [((encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc'.2).1, p)],
             (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc'.2).2) := by
          simp only [step, hp, dite_true]
        -- Use encodeFormula_controlVar_shift: control var shifts by offset
        have hMono : acc.2.nextFresh ≤ acc'.2.nextFresh := by omega
        have hWitOff : (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2).1.id + offset =
            (encodeFormula b φ ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc'.2).1.id := by
          have hShift := encodeFormula_controlVar_shift b φ
            ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2 acc'.2 hMono
          rw [hShift, hOff]
          omega
        have hOff1 := hNextFreshIH ⟨p, ⟨0, Nat.zero_lt_succ _⟩, w.ti⟩ acc.2 acc'.2 hOff
        have hNewAccLen : (step acc p).1.length = (step acc' p).1.length := by
          simp only [hStepAcc, hStepAcc', List.length_append, List.length_singleton, hAccLen]
        have hNewAccOff : ∀ i (hi : i < (step acc p).1.length) (hi' : i < (step acc' p).1.length),
            ((step acc p).1.get ⟨i, hi⟩).1.id + offset = ((step acc' p).1.get ⟨i, hi'⟩).1.id := by
          intro i hi hi'
          simp only [hStepAcc, hStepAcc', List.length_append, List.length_singleton] at hi hi'
          by_cases hOld : i < acc.1.length
          · have hOld' : i < acc'.1.length := hAccLen ▸ hOld
            simp only [hStepAcc, hStepAcc', List.get_eq_getElem,
              List.getElem_append_left hOld, List.getElem_append_left hOld']
            exact hAccOff i hOld hOld'
          · -- i = acc.1.length = acc'.1.length (since hAccLen)
            have hNew : i = acc.1.length := by omega
            have hNew' : i = acc'.1.length := by omega
            simp only [hStepAcc, hStepAcc', List.get_eq_getElem] at *
            have hLen : acc.1.length = acc'.1.length := hAccLen
            subst hNew
            simp only [List.getElem_append, Nat.lt_irrefl, dite_false,
                       Nat.sub_self, List.getElem_cons_zero, hLen]
            exact hWitOff
        have hOff1' : (step acc' p).2.nextFresh = (step acc p).2.nextFresh + offset := by
          simp only [hStepAcc, hStepAcc']
          exact hOff1
        exact ih (step acc p) (step acc' p) hOff1' hNewAccLen hNewAccOff
      · -- p ∉ intersection: step acc p = acc, step acc' p = acc'
        have hStepAcc : step acc p = acc := by simp only [step, hp, dite_false]
        have hStepAcc' : step acc' p = acc' := by simp only [step, hp, dite_false]
        rw [hStepAcc, hStepAcc']
        exact ih acc acc' hOff hAccLen hAccOff

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- encodeTupleControl new clauses shift correctly.
    If witnessVars[i].id + offset = witnessVars'[i].id for corresponding Fresh vars,
    and st'.nextFresh = st.nextFresh + offset, then new clauses from encodeTupleControl
    with st shift to become new clauses from encodeTupleControl with st'. -/
lemma encodeTupleControl_new_clause_shifts (b : Bounds S) (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (witnessVars witnessVars' : List (Var b)) (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (_hStCompat : clauseShiftCompat b st st' offset)
    (hVarsLen : witnessVars.length = witnessVars'.length)
    (hVarsOff : ∀ i (hi : i < witnessVars.length) (hi' : i < witnessVars'.length),
        ∃ n n', witnessVars.get ⟨i, hi⟩ = Var.Fresh n ∧
                witnessVars'.get ⟨i, hi'⟩ = Var.Fresh n' ∧ n + offset = n')
    (c : SAT.Clause (Var b))
    (hcNew : c ∈ (encodeTupleControl b learners tuple witnessVars st).2.clauses)
    (hcNotOld : c ∉ st.clauses) :
    c.map (shiftLitFresh b offset) ∈
      (encodeTupleControl b learners tuple witnessVars' st').2.clauses := by
  -- Unfold encodeTupleControl
  simp only [encodeTupleControl] at hcNew ⊢

  -- Name the allocated fresh vars
  rcases hAlloc : EncState.allocFresh b st with ⟨uTuple, stAlloc⟩
  rcases hAlloc' : EncState.allocFresh b st' with ⟨uTuple', stAlloc'⟩
  simp only [hAlloc] at hcNew ⊢

  -- uTuple.id = st.nextFresh, uTuple'.id = st'.nextFresh = st.nextFresh + offset
  have hUId : uTuple.id = st.nextFresh := by
    simp only [EncState.allocFresh] at hAlloc
    injection hAlloc with h _
    exact congrArg FVar.id h.symm
  have hUId' : uTuple'.id = st'.nextFresh := by
    simp only [EncState.allocFresh] at hAlloc'
    injection hAlloc' with h _
    exact congrArg FVar.id h.symm
  have hUOff : uTuple'.id = uTuple.id + offset := by rw [hUId, hUId', hOffset]

  -- stAlloc.clauses = st.clauses
  have hAllocClauses : stAlloc.clauses = st.clauses := by
    simp only [EncState.allocFresh] at hAlloc; injection hAlloc with _ h; simp [← h]
  have hAllocClauses' : stAlloc'.clauses = st'.clauses := by
    simp only [EncState.allocFresh] at hAlloc'; injection hAlloc' with _ h; simp [← h]

  -- Define guards (same for both since they don't depend on state)
  let guards := (learners.zip tuple).map fun (ℓ, Q) =>
    SAT.Lit.neg (Var.MinQ (b.findValueIndex ℓ) Q)

  -- Define intermediate states
  let st1 := EncState.addClause b stAlloc
    ([SAT.Lit.neg (FVar.toVar b uTuple)] ++ guards ++ witnessVars.map SAT.Lit.pos)
  let st1' := EncState.addClause b stAlloc'
    ([SAT.Lit.neg (FVar.toVar b uTuple')] ++ guards ++ witnessVars'.map SAT.Lit.pos)

  let st2 := (learners.zip tuple).foldl (fun stAcc (ℓ, Q) =>
    EncState.addClause b stAcc
      [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
       SAT.Lit.pos (FVar.toVar b uTuple)]) st1
  let st2' := (learners.zip tuple).foldl (fun stAcc (ℓ, Q) =>
    EncState.addClause b stAcc
      [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
       SAT.Lit.pos (FVar.toVar b uTuple')]) st1'

  let st3 := witnessVars.foldl (fun stAcc v =>
    EncState.addClause b stAcc [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)]) st2
  let st3' := witnessVars'.foldl (fun stAcc v =>
    EncState.addClause b stAcc [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple')]) st2'

  -- hcNew : c ∈ st3.clauses, need: c.map shift ∈ st3'.clauses
  -- Track backwards: c ∉ st.clauses = stAlloc.clauses, so c was added in one of the phases

  -- Helper: shiftLitFresh preserves MinQ vars
  have hShiftMinQ : ∀ vIdx Q, shiftLitFresh b offset (SAT.Lit.pos (Var.MinQ vIdx Q)) =
      SAT.Lit.pos (Var.MinQ vIdx Q) := by
    intro vIdx Q; simp [shiftLitFresh]
  have hShiftMinQNeg : ∀ vIdx Q, shiftLitFresh b offset (SAT.Lit.neg (Var.MinQ vIdx Q)) =
      SAT.Lit.neg (Var.MinQ vIdx Q) := by
    intro vIdx Q; simp [shiftLitFresh]

  -- Helper: shiftLitFresh maps uTuple to uTuple'
  have hShiftU : shiftLitFresh b offset (SAT.Lit.pos (FVar.toVar b uTuple)) =
      SAT.Lit.pos (FVar.toVar b uTuple') := by
    simp [shiftLitFresh, FVar.toVar, hUOff]
  have hShiftUNeg : shiftLitFresh b offset (SAT.Lit.neg (FVar.toVar b uTuple)) =
      SAT.Lit.neg (FVar.toVar b uTuple') := by
    simp [shiftLitFresh, FVar.toVar, hUOff]

  -- Helper: guards map to themselves (MinQ vars don't shift)
  have hShiftGuards : guards.map (shiftLitFresh b offset) = guards := by
    simp only [guards, List.map_map, Function.comp_def]
    apply List.ext_get
    · simp only [List.length_map]
    · intro i hi _
      simp only [List.length_map] at hi
      simp only [List.get_eq_getElem, List.getElem_map]
      exact hShiftMinQNeg _ _

  -- Helper: witnessVars.map pos shifts to witnessVars'.map pos
  have hShiftWitness : (witnessVars.map SAT.Lit.pos).map (shiftLitFresh b offset) =
      witnessVars'.map SAT.Lit.pos := by
    apply List.ext_get
    · simp only [List.length_map, hVarsLen]
    · intro i hi hi'
      simp only [List.length_map] at hi hi'
      simp only [List.get_eq_getElem, List.getElem_map]
      -- Get the Fresh var offset relationship
      obtain ⟨n, n', hVn, hVn', hOff'⟩ := hVarsOff i hi (hVarsLen ▸ hi)
      -- Convert from .get form to bracket form
      simp only [List.get_eq_getElem] at hVn hVn'
      rw [hVn, hVn']
      simp only [shiftLitFresh, hOff']

  -- Phase 1: Check if c is the forward clause
  by_cases hcSt1 : c ∈ st1.clauses
  · -- c ∈ st1.clauses
    simp only [st1, EncState.addClause, List.mem_cons] at hcSt1
    cases hcSt1 with
    | inl hEq =>
        -- c is the forward clause
        subst hEq
        -- Show shifted clause is in st1'.clauses, then subset to st3'
        have hForward' : ([SAT.Lit.neg (FVar.toVar b uTuple)] ++ guards ++
            witnessVars.map SAT.Lit.pos).map (shiftLitFresh b offset) =
            [SAT.Lit.neg (FVar.toVar b uTuple')] ++ guards ++ witnessVars'.map SAT.Lit.pos := by
          simp only [List.map_append, List.map_cons, List.map_nil, hShiftUNeg, hShiftGuards,
                     hShiftWitness]
        rw [hForward']
        -- This clause is in st1'.clauses
        have hIn1' : [SAT.Lit.neg (FVar.toVar b uTuple')] ++ guards ++
            witnessVars'.map SAT.Lit.pos ∈ st1'.clauses := by
          simp [st1', EncState.addClause]
        -- st1'.clauses ⊆ st2'.clauses ⊆ st3'.clauses
        have hSub12' : st1'.clauses ⊆ st2'.clauses := by
          apply foldl_subset_state (f := fun stAcc (pr : S.Value × Finset b.participants) =>
            EncState.addClause b stAcc [SAT.Lit.pos (Var.MinQ (b.findValueIndex pr.1) pr.2),
               SAT.Lit.pos (FVar.toVar b uTuple')])
          intro stAcc pr; exact EncState.addClause_subset_clauses b stAcc _
        have hSub23' : st2'.clauses ⊆ st3'.clauses := by
          apply foldl_subset_state (f := fun stAcc v =>
            EncState.addClause b stAcc [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple')])
          intro stAcc v; exact EncState.addClause_subset_clauses b stAcc _
        exact hSub23' (hSub12' hIn1')
    | inr hOld =>
        -- c was in stAlloc.clauses = st.clauses, contradiction with hcNotOld
        rw [hAllocClauses] at hOld
        exact absurd hOld hcNotOld
  · -- c ∉ st1.clauses, check phase 2
    by_cases hcSt2 : c ∈ st2.clauses
    · -- c ∈ st2.clauses but c ∉ st1.clauses, so c is a guard clause
      -- Use induction to find which guard clause
      have hGuardClause : ∃ pr ∈ learners.zip tuple,
          c = [SAT.Lit.pos (Var.MinQ (b.findValueIndex pr.1) pr.2),
               SAT.Lit.pos (FVar.toVar b uTuple)] := by
        -- c ∈ st2.clauses \ st1.clauses, so c was added during the guard fold
        -- Use helper to find which guard clause
        have hAux : ∀ (prs : List (S.Value × Finset b.participants)) (stInit : EncState b),
            c ∈ (prs.foldl (fun stAcc (ℓ, Q) => EncState.addClause b stAcc
              [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
               SAT.Lit.pos (FVar.toVar b uTuple)]) stInit).clauses →
            c ∉ stInit.clauses →
            ∃ pr ∈ prs, c = [SAT.Lit.pos (Var.MinQ (b.findValueIndex pr.1) pr.2),
               SAT.Lit.pos (FVar.toVar b uTuple)] := by
          intro prs
          induction prs with
          | nil =>
              intro stInit hIn hNotIn
              simp at hIn
              exact absurd hIn hNotIn
          | cons pr prs' ih =>
              intro stInit hIn hNotIn
              simp only [List.foldl_cons] at hIn
              let st_step := EncState.addClause b stInit
                [SAT.Lit.pos (Var.MinQ (b.findValueIndex pr.1) pr.2),
                 SAT.Lit.pos (FVar.toVar b uTuple)]
              by_cases hcStep : c ∈ st_step.clauses
              · simp only [st_step, EncState.addClause, List.mem_cons] at hcStep
                cases hcStep with
                | inl hEq => exact ⟨pr, List.mem_cons_self, hEq⟩
                | inr hOld => exact absurd hOld hNotIn
              · have ⟨pr', hMem, hEq⟩ := ih st_step hIn hcStep
                exact ⟨pr', List.mem_cons.mpr (Or.inr hMem), hEq⟩
        exact hAux (learners.zip tuple) st1 hcSt2 hcSt1
      obtain ⟨⟨ℓ, Q⟩, hPairMem, hcEq⟩ := hGuardClause
      subst hcEq
      -- Shifted clause
      have hShifted : [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
           SAT.Lit.pos (FVar.toVar b uTuple)].map (shiftLitFresh b offset) =
          [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
           SAT.Lit.pos (FVar.toVar b uTuple')] := by
        simp [hShiftMinQ, hShiftU]
      rw [hShifted]
      -- This clause is added during phase 2 of st' - prove directly
      -- Use foldl_exists_state_subset to show the clause exists
      have hExists :=
        foldl_exists_state_subset
          (f := fun stAcc (pq : S.Value × Finset b.participants) =>
            EncState.addClause b stAcc [SAT.Lit.pos (Var.MinQ (b.findValueIndex pq.1) pq.2),
               SAT.Lit.pos (FVar.toVar b uTuple')])
          (hStep := by
            intro stAcc pq
            exact EncState.addClause_subset_clauses (b := b) stAcc _)
          (xs := learners.zip tuple)
          (x := (ℓ, Q)) (init := st1') hPairMem
      rcases hExists with ⟨st_k, hSub⟩
      have hIn :
          [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
           SAT.Lit.pos (FVar.toVar b uTuple')] ∈
            (EncState.addClause b st_k
              [SAT.Lit.pos (Var.MinQ (b.findValueIndex ℓ) Q),
               SAT.Lit.pos (FVar.toVar b uTuple')]).clauses := by
        simp [EncState.addClause]
      have hIn_st2' := hSub hIn
      have hSub_st3' : st2'.clauses ⊆ st3'.clauses := by
        apply foldl_subset_state (f := fun stAcc v =>
          EncState.addClause b stAcc [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple')])
        intro stAcc v; exact EncState.addClause_subset_clauses b stAcc _
      exact hSub_st3' hIn_st2'
    · -- c ∉ st2.clauses, so c is a witness clause (from phase 3)
      have hWitnessClause : ∃ v ∈ witnessVars,
          c = [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)] := by
        -- c ∈ st3.clauses \ st2.clauses, so c was added during the witness fold
        -- First show c ∈ st3.clauses
        have hcSt3 : c ∈ st3.clauses := hcNew
        -- Use helper to find which witness clause
        have hAux : ∀ (vs : List (Var b)) (stInit : EncState b),
            c ∈ (vs.foldl (fun stAcc v => EncState.addClause b stAcc
              [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)]) stInit).clauses →
            c ∉ stInit.clauses →
            ∃ v ∈ vs, c = [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)] := by
          intro vs
          induction vs with
          | nil =>
              intro stInit hIn hNotIn
              simp at hIn
              exact absurd hIn hNotIn
          | cons v vs' ih =>
              intro stInit hIn hNotIn
              simp only [List.foldl_cons] at hIn
              let st_step := EncState.addClause b stInit
                [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)]
              by_cases hcStep : c ∈ st_step.clauses
              · simp only [st_step, EncState.addClause, List.mem_cons] at hcStep
                cases hcStep with
                | inl hEq => exact ⟨v, List.mem_cons_self, hEq⟩
                | inr hOld => exact absurd hOld hNotIn
              · have ⟨v', hMem, hEq⟩ := ih st_step hIn hcStep
                exact ⟨v', List.mem_cons.mpr (Or.inr hMem), hEq⟩
        exact hAux witnessVars st2 hcSt3 hcSt2
      obtain ⟨v, hVMem, hcEq⟩ := hWitnessClause
      subst hcEq
      -- v ∈ witnessVars, find corresponding v' ∈ witnessVars'
      have ⟨idx, hVEq⟩ := List.mem_iff_get.mp hVMem
      have hi : idx.val < witnessVars.length := idx.isLt
      have hi' : idx.val < witnessVars'.length := by rw [← hVarsLen]; exact hi
      obtain ⟨n, n', hN, hN', hNOff⟩ := hVarsOff idx.val hi hi'
      -- v = Var.Fresh n
      have hN2 : witnessVars.get idx = Var.Fresh n := hN
      rw [hVEq] at hN2
      -- v' = Var.Fresh n'
      let v' := witnessVars'.get ⟨idx.val, hi'⟩
      have hV'Eq : v' = Var.Fresh n' := hN'
      -- Shifted clause
      have hShifted : [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b uTuple)].map
          (shiftLitFresh b offset) =
          [SAT.Lit.neg v', SAT.Lit.pos (FVar.toVar b uTuple')] := by
        simp only [List.map_cons, List.map_nil, hShiftU]
        congr 1
        simp [shiftLitFresh, hN2, hV'Eq, hNOff]
      rw [hShifted]
      -- This clause is in st3' - prove directly
      have hV'Mem : v' ∈ witnessVars' := List.get_mem witnessVars' ⟨idx.val, hi'⟩
      -- Use foldl_exists_state_subset over the witness fold
      have hExists :=
        foldl_exists_state_subset
          (f := fun stAcc v' =>
            EncState.addClause b stAcc
              [SAT.Lit.neg v', SAT.Lit.pos (FVar.toVar b uTuple')])
          (hStep := by
            intro stAcc v'
            exact EncState.addClause_subset_clauses (b := b) stAcc _)
          (xs := witnessVars') (x := v') (init := st2') hV'Mem
      rcases hExists with ⟨st_k, hSub⟩
      have hIn :
          [SAT.Lit.neg v', SAT.Lit.pos (FVar.toVar b uTuple')] ∈
            (EncState.addClause b st_k
              [SAT.Lit.neg v', SAT.Lit.pos (FVar.toVar b uTuple')]).clauses := by
        simp [EncState.addClause]
      exact hSub hIn

/-- diamondStep preserves clauseShiftCompat.
    The step consists of witnessFold + encodeTupleControl.
    Clauses from witnessFold shift by IH, new clauses from encodeTupleControl also shift. -/
lemma diamond_step_preserves_clauseShiftCompat (b : Bounds S) (φ : Formula S) (w : WId b)
    (learners : List S.Value)
    (tuple : List (Finset b.participants))
    (acc acc' : List (FVar b) × EncState b) (offset : Nat)
    (hOffset : acc'.2.nextFresh = acc.2.nextFresh + offset)
    (hCompat : clauseShiftCompat b acc.2 acc'.2 offset)
    (hIH_compat : ∀ w' stX stX', stX'.nextFresh = stX.nextFresh + offset →
           clauseShiftCompat b stX stX' offset →
           clauseShiftCompat b (encodeFormula b φ w' stX).2 (encodeFormula b φ w' stX').2 offset)
    (hIH_offset : ∀ w' stX stX' off, stX'.nextFresh = stX.nextFresh + off →
           (encodeFormula b φ w' stX').2.nextFresh = (encodeFormula b φ w' stX).2.nextFresh + off) :
    clauseShiftCompat b
      (diamondStep b learners φ w acc tuple).2
      (diamondStep b learners φ w acc' tuple).2 offset := by
  unfold clauseShiftCompat
  intro c hc
  simp only [diamondStep] at hc ⊢
  let intersection := tuple.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
  let wf := diamondWitnessFold b φ w intersection acc.2
  let wf' := diamondWitnessFold b φ w intersection acc'.2

  -- Key properties of witnessFold
  have hWfCompat : clauseShiftCompat b wf.2 wf'.2 offset :=
    diamond_witnessFold_preserves_clauseShiftCompat b φ w intersection acc.2 acc'.2 offset
      hOffset hCompat hIH_compat

  -- c ∈ (encodeTupleControl ...).2.clauses
  -- Check if c was in wf.2.clauses (from witnessFold)
  by_cases hcWf : c ∈ wf.2.clauses
  · -- c was in witnessFold result - use clauseShiftCompat
    have hcShift := hWfCompat c hcWf
    exact encodeTupleControl_clauses_subset b learners tuple
      (wf'.1.map (fun u => FVar.toVar b u.1)) wf'.2 hcShift
  · -- c is new from encodeTupleControl - use encodeTupleControl_new_clause_shifts
    -- Need: wf'.2.nextFresh = wf.2.nextFresh + offset
    have hWfOffset : wf'.2.nextFresh = wf.2.nextFresh + offset :=
      diamondWitnessFold_offset b φ w intersection acc.2 acc'.2 offset hOffset hIH_offset
    -- Need: witnessVars have offset relationship
    let witnessVars := wf.1.map (fun u => FVar.toVar b u.1)
    let witnessVars' := wf'.1.map (fun u => FVar.toVar b u.1)
    -- Specialize hIH_offset to the fixed offset for diamond_witnessFold_vars_offset
    have hIH_offset_specialized : ∀ w' stX stX', stX'.nextFresh = stX.nextFresh + offset →
           (encodeFormula b φ w' stX').2.nextFresh =
             (encodeFormula b φ w' stX).2.nextFresh + offset :=
      fun w' stX stX' hOff => hIH_offset w' stX stX' offset hOff
    have hVarsInfo := diamond_witnessFold_vars_offset b φ w intersection acc.2 acc'.2 offset
      hOffset hIH_offset_specialized
    have hVarsLen : witnessVars.length = witnessVars'.length := by
      simp only [witnessVars, witnessVars', List.length_map]
      exact hVarsInfo.1
    have hVarsOff : ∀ i (hi : i < witnessVars.length) (hi' : i < witnessVars'.length),
        ∃ n n', witnessVars.get ⟨i, hi⟩ = Var.Fresh n ∧
                witnessVars'.get ⟨i, hi'⟩ = Var.Fresh n' ∧ n + offset = n' := by
      intro i hi hi'
      simp only [witnessVars, witnessVars', List.length_map] at hi hi'
      have hOff := hVarsInfo.2 i hi hi'
      simp only [witnessVars, witnessVars', List.get_eq_getElem, List.getElem_map]
      simp only [FVar.toVar]
      exact ⟨(wf.1.get ⟨i, hi⟩).1.id, (wf'.1.get ⟨i, hi'⟩).1.id, rfl, rfl, hOff⟩
    exact encodeTupleControl_new_clause_shifts b learners tuple witnessVars witnessVars'
      wf.2 wf'.2 offset hWfOffset hWfCompat hVarsLen hVarsOff c hc hcWf

/-- Folding diamondStep produces tupleVars with offset relationship.
    Each tuple produces one uTuple, and since nextFresh offset is preserved,
    corresponding uTuples have id offset relationship.

    Key insight: Each diamondStep appends exactly one var with id = current witnessFold nextFresh.
    Since witnessFold preserves nextFresh offset, the appended vars have offset relationship. -/
lemma diamond_tuples_foldl_vars_offset (b : Bounds S) (φ : Formula S) (w : WId b)
    (learners : List S.Value) (tuples : List (List (Finset b.participants)))
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hIH_offset : ∀ w' stX stX' off, stX'.nextFresh = stX.nextFresh + off →
           (encodeFormula b φ w' stX').2.nextFresh = (encodeFormula b φ w' stX).2.nextFresh + off) :
    let res := tuples.foldl (diamondStep b learners φ w) ([], st)
    let res' := tuples.foldl (diamondStep b learners φ w) ([], st')
    res.1.length = res'.1.length ∧
    ∀ i (hi : i < res.1.length) (hi' : i < res'.1.length),
        (res.1.get ⟨i, hi⟩).id + offset = (res'.1.get ⟨i, hi'⟩).id := by
  intro res res'
  -- The fold produces exactly tuples.length vars
  have hGenLen : ∀ (xs : List (List (Finset b.participants)))
      (acc : List (FVar b) × EncState b),
      (xs.foldl (diamondStep b learners φ w) acc).1.length = acc.1.length + xs.length := by
    intro xs acc
    induction xs generalizing acc with
    | nil => simp
    | cons x xs' ih =>
        simp only [List.foldl_cons, List.length_cons]
        rw [ih (diamondStep b learners φ w acc x)]
        simp only [diamondStep, List.length_append, List.length_singleton]
        ring
  -- Show lengths equal
  constructor
  · simp only [res, res', hGenLen, List.length_nil, zero_add]
  · -- For each index i, show offset relationship
    -- Key: each diamondStep appends one var with id = witnessFold.nextFresh
    -- Since witnessFold preserves offset, appended vars have offset relationship
    suffices hSuff : ∀ (ts : List (List (Finset b.participants)))
        (acc acc' : List (FVar b) × EncState b),
        acc'.2.nextFresh = acc.2.nextFresh + offset →
        acc.1.length = acc'.1.length →
        (∀ j (hj : j < acc.1.length) (hj' : j < acc'.1.length),
            (acc.1.get ⟨j, hj⟩).id + offset = (acc'.1.get ⟨j, hj'⟩).id) →
        ∀ i (hi : i < (ts.foldl (diamondStep b learners φ w) acc).1.length)
            (hi' : i < (ts.foldl (diamondStep b learners φ w) acc').1.length),
            ((ts.foldl (diamondStep b learners φ w) acc).1.get ⟨i, hi⟩).id + offset =
            ((ts.foldl (diamondStep b learners φ w) acc').1.get ⟨i, hi'⟩).id by
      intro i hi hi'
      exact hSuff tuples ([], st) ([], st') hOffset rfl
        (fun _ hj _ => absurd hj (Nat.not_lt_zero _)) i hi hi'
    intro ts acc acc' hAccOff hAccLen hAccVarsOff i hi hi'
    induction ts generalizing acc acc' i with
    | nil =>
        simp only [List.foldl_nil] at hi
        exact hAccVarsOff i hi hi'
    | cons t ts' ih =>
        simp only [List.foldl_cons] at hi hi' ⊢
        let step := diamondStep b learners φ w acc t
        let step' := diamondStep b learners φ w acc' t
        -- step.1 = acc.1 ++ [uTuple], step'.1 = acc'.1 ++ [uTuple']
        have hStepLen : step.1.length = acc.1.length + 1 := by
          simp only [step, diamondStep, List.length_append, List.length_singleton]
        have hStepLen' : step'.1.length = acc'.1.length + 1 := by
          simp only [step', diamondStep, List.length_append, List.length_singleton]
        have hStepLenEq : step.1.length = step'.1.length := by
          simp only [hStepLen, hStepLen', hAccLen]
        -- State offset for next iteration
        have hStepOffset : step'.2.nextFresh = step.2.nextFresh + offset :=
          diamondStep_offset b learners φ w t acc acc' offset hAccOff hIH_offset
        -- Vars offset for step
        have hStepVarsOff : ∀ j (hj : j < step.1.length) (hj' : j < step'.1.length),
            (step.1.get ⟨j, hj⟩).id + offset = (step'.1.get ⟨j, hj'⟩).id := by
          intro j hj hj'
          simp only [List.get_eq_getElem]
          by_cases hCmp : j < acc.1.length
          · -- j < acc.1.length: from original accumulator
            have hCmp' : j < acc'.1.length := hAccLen ▸ hCmp
            have hGet : step.1[j] = acc.1[j] := by
              simp only [step, diamondStep]; exact List.getElem_append_left hCmp
            have hGet' : step'.1[j] = acc'.1[j] := by
              simp only [step', diamondStep]; exact List.getElem_append_left hCmp'
            rw [hGet, hGet']; exact hAccVarsOff j hCmp hCmp'
          · -- j ≥ acc.1.length: newly appended var
            have hCmp' : ¬(j < acc'.1.length) := by rw [hAccLen] at hCmp; exact hCmp
            have hJ : j = acc.1.length := by
              simp only [step, diamondStep, List.length_append, List.length_singleton] at hj; omega
            subst hJ  -- Replace j with acc.1.length everywhere
            let intersection := t.foldl (· ∩ ·) (Finset.univ : Finset b.participants)
            let wf := diamondWitnessFold b φ w intersection acc.2
            let wf' := diamondWitnessFold b φ w intersection acc'.2
            have hWfOffset : wf'.2.nextFresh = wf.2.nextFresh + offset :=
              diamondWitnessFold_offset b φ w intersection acc.2 acc'.2 offset hAccOff hIH_offset
            have hId := encodeTupleControl_fst_id b learners t
              (wf.1.map (fun u => FVar.toVar b u.1)) wf.2
            have hId' := encodeTupleControl_fst_id b learners t
              (wf'.1.map (fun u => FVar.toVar b u.1)) wf'.2
            -- Use pattern from line 3517: simplify list access to singleton
            simp only [step, step', diamondStep, intersection, wf, wf', List.getElem_append,
              Nat.lt_irrefl, dite_false, Nat.sub_self, List.getElem_cons_zero, hAccLen]
              at hId hId' hWfOffset ⊢
            omega
        exact ih step step' hStepOffset hStepLenEq hStepVarsOff i hi hi'

/-- Folding diamondStep preserves clauseShiftCompat. -/
lemma diamond_tuples_foldl_preserves_clauseShiftCompat (b : Bounds S) (φ : Formula S) (w : WId b)
    (learners : List S.Value)
    (tuples : List (List (Finset b.participants)))
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hCompat : clauseShiftCompat b st st' offset)
    (hIH_compat : ∀ w' stX stX', stX'.nextFresh = stX.nextFresh + offset →
           clauseShiftCompat b stX stX' offset →
           clauseShiftCompat b (encodeFormula b φ w' stX).2 (encodeFormula b φ w' stX').2 offset)
    (hIH_offset : ∀ w' stX stX' off, stX'.nextFresh = stX.nextFresh + off →
           (encodeFormula b φ w' stX').2.nextFresh = (encodeFormula b φ w' stX).2.nextFresh + off) :
    clauseShiftCompat b
      (tuples.foldl (diamondStep b learners φ w) ([], st)).2
      (tuples.foldl (diamondStep b learners φ w) ([], st')).2 offset := by
  -- Key lemma: foldl.2 only depends on acc.2, not acc.1
  have hIndep : ∀ (ts : List (List (Finset b.participants)))
      (acc1 acc2 : List (FVar b) × EncState b),
      acc1.2 = acc2.2 →
      (ts.foldl (diamondStep b learners φ w) acc1).2 =
      (ts.foldl (diamondStep b learners φ w) acc2).2 := by
    intro ts acc1 acc2 hEq
    induction ts generalizing acc1 acc2 with
    | nil => simp only [List.foldl_nil, hEq]
    | cons t ts' ih' =>
        simp only [List.foldl_cons]
        apply ih'
        simp only [diamondStep, hEq]
  induction tuples generalizing st st' with
  | nil => simp only [List.foldl_nil]; exact hCompat
  | cons tuple tuples ih =>
      simp only [List.foldl_cons]
      let acc := diamondStep b learners φ w ([], st) tuple
      let acc' := diamondStep b learners φ w ([], st') tuple
      have hStepCompat : clauseShiftCompat b acc.2 acc'.2 offset :=
        diamond_step_preserves_clauseShiftCompat b φ w learners tuple ([], st) ([], st') offset
          hOffset hCompat hIH_compat hIH_offset
      have hStepOffset : acc'.2.nextFresh = acc.2.nextFresh + offset :=
        diamondStep_offset b learners φ w tuple ([], st) ([], st') offset hOffset hIH_offset
      -- Use IH with ([], acc.2) and ([], acc'.2)
      have hIhResult := ih acc.2 acc'.2 hStepOffset hStepCompat
      -- Show (foldl f acc tuples).2 = (foldl f ([], acc.2) tuples).2
      have h1 := hIndep tuples acc ([], acc.2) rfl
      have h2 := hIndep tuples acc' ([], acc'.2) rfl
      rw [h1, h2]
      exact hIhResult

/-- encodeFormula preserves clause shift compatibility.
    If input states have clause shift compat, output states do too. -/
lemma encodeFormula_preserves_clause_shift_compat (b : Bounds S) (φ : Formula S) (w : WId b)
    (st st' : EncState b) (offset : Nat)
    (hOffset : st'.nextFresh = st.nextFresh + offset)
    (hStClauseShift : clauseShiftCompat b st st' offset) :
    clauseShiftCompat b (encodeFormula b φ w st).2 (encodeFormula b φ w st').2 offset := by
  unfold clauseShiftCompat at *
  -- Helper: st.nextFresh ≤ st'.nextFresh
  have hMono : st.nextFresh ≤ st'.nextFresh := by omega
  induction φ generalizing w st st' with
  | bot =>
      intro c hc
      simp only [encodeFormula, EncState.addClause, List.mem_cons] at hc
      cases hc with
      | inl hEq =>
          -- c = [neg (Fresh st.nextFresh)]
          subst hEq
          simp only [encodeFormula, EncState.addClause, List.mem_cons]
          left
          simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh, hOffset]
      | inr hTail =>
          simp only [EncState.allocFresh] at hTail
          have hShifted := hStClauseShift c hTail
          simp only [encodeFormula, EncState.addClause, List.mem_cons]
          right
          simp only [EncState.allocFresh]
          exact hShifted
  | eq v1 v2 =>
      intro c hc
      simp only [encodeFormula] at hc
      by_cases hEq : (v1 == v2) = true
      · simp only [hEq, ↓reduceIte, EncState.addClause, EncState.allocFresh] at hc
        rw [List.mem_cons] at hc
        cases hc with
        | inl hEq' =>
            subst hEq'
            simp only [encodeFormula, hEq, ↓reduceIte, EncState.addClause, List.mem_cons]
            left
            simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh, hOffset]
        | inr hTail =>
            have hShifted := hStClauseShift c hTail
            simp only [encodeFormula, hEq, ↓reduceIte, EncState.addClause, List.mem_cons]
            right
            simp only [EncState.allocFresh]
            exact hShifted
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte, EncState.addClause,
          EncState.allocFresh] at hc
        rw [List.mem_cons] at hc
        cases hc with
        | inl hEq' =>
            subst hEq'
            simp only [encodeFormula, hEq, Bool.false_eq_true, ↓reduceIte,
                       EncState.addClause, List.mem_cons]
            left
            simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh, hOffset]
        | inr hTail =>
            have hShifted := hStClauseShift c hTail
            simp only [encodeFormula, hEq, Bool.false_eq_true, ↓reduceIte,
                       EncState.addClause, List.mem_cons]
            right
            simp only [EncState.allocFresh]
            exact hShifted
  | seq =>
      intro c hc
      simp only [encodeFormula, EncState.addClause, List.mem_cons] at hc
      rcases hc with hEq1 | hEq2 | hTail
      · -- c = second clause [neg Seq, pos Fresh]
        simp only [FVar.toVar, EncState.allocFresh] at hEq1
        subst hEq1
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        left
        simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh, hOffset]
      · -- c = first clause [neg Fresh, pos Seq]
        simp only [FVar.toVar, EncState.allocFresh] at hEq2
        subst hEq2
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        right; left
        simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh, hOffset]
      · -- c from st
        simp only [EncState.allocFresh] at hTail
        have hShifted := hStClauseShift c hTail
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        right; right
        simp only [EncState.allocFresh]
        exact hShifted
  | imp φ1 φ2 ih1 ih2 =>
      intro c hc
      -- Define intermediate states
      let st1 := (encodeFormula b φ1 w st).2
      let st1' := (encodeFormula b φ1 w st').2
      let st2 := (encodeFormula b φ2 w st1).2
      let st2' := (encodeFormula b φ2 w st1').2
      -- Offset relations
      have hOffset1 : st1'.nextFresh = st1.nextFresh + offset := by
        simp only [st1, st1']
        exact encodeFormula_nextFresh_offset b φ1 w st st' offset hOffset
      have hOffset2 : st2'.nextFresh = st2.nextFresh + offset := by
        simp only [st2, st2', st1, st1']
        exact encodeFormula_nextFresh_offset b φ2 w st1 st1' offset hOffset1
      have hMono1 : st1.nextFresh ≤ st1'.nextFresh := by omega
      -- Recursive clause shift compat
      have hComp1 := ih1 w st st' hOffset hStClauseShift hMono
      have hComp2 := ih2 w st1 st1' hOffset1 hComp1 hMono1
      -- Analyze c
      simp only [encodeFormula, EncState.addClause, List.mem_cons] at hc
      rcases hc with hEq1 | hEq2 | hEq3 | hTail
      · -- c = [neg u, neg u1, pos u2]
        simp only [FVar.toVar, EncState.allocFresh] at hEq1
        subst hEq1
        have hOff1Diff : st1'.nextFresh - st1.nextFresh = offset := by omega
        have hOffDiff : st'.nextFresh - st.nextFresh = offset := by omega
        have hU1Off := encodeFormula_controlVar_shift b φ1 w st st' hMono
        have hU2Off := encodeFormula_controlVar_shift b φ2 w st1 st1' hMono1
        rw [hOff1Diff] at hU2Off
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        left
        simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh]
        simp only [st1, st1'] at hOffset2 hU2Off
        rw [← hOffset2, ← hU2Off]
        simp only [hOffDiff] at hU1Off
        rw [hU1Off]
      · -- c = [neg u2, pos u]
        simp only [FVar.toVar, EncState.allocFresh] at hEq2
        subst hEq2
        have hOff1Diff : st1'.nextFresh - st1.nextFresh = offset := by omega
        have hU2Off := encodeFormula_controlVar_shift b φ2 w st1 st1' hMono1
        rw [hOff1Diff] at hU2Off
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        right; left
        simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh]
        simp only [st1, st1'] at hOffset2 hU2Off
        rw [← hOffset2, ← hU2Off]
      · -- c = [pos u1, pos u]
        simp only [FVar.toVar, EncState.allocFresh] at hEq3
        subst hEq3
        have hOffDiff : st'.nextFresh - st.nextFresh = offset := by omega
        have hU1Off := encodeFormula_controlVar_shift b φ1 w st st' hMono
        rw [hOffDiff] at hU1Off
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        right; right; left
        simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh]
        rw [← hOffset2, hU1Off]
      · -- c from st2
        have hShifted := hComp2 c hTail
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        right; right; right
        exact hShifted
  | atEnd φ ih =>
      intro c hc
      let wEnd : WId b := ⟨w.p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
      let st1 := (encodeFormula b φ wEnd st).2
      let st1' := (encodeFormula b φ wEnd st').2
      have hOffset1 : st1'.nextFresh = st1.nextFresh + offset := by
        simp only [st1, st1']
        exact encodeFormula_nextFresh_offset b φ wEnd st st' offset hOffset
      have hComp1 := ih wEnd st st' hOffset hStClauseShift hMono
      simp only [encodeFormula, EncState.addClause, List.mem_cons] at hc
      rcases hc with hEq1 | hEq2 | hTail
      · -- c = [neg u1, pos u]
        simp only [FVar.toVar, EncState.allocFresh] at hEq1
        subst hEq1
        have hOffDiff : st'.nextFresh - st.nextFresh = offset := by omega
        have hU1Off := encodeFormula_controlVar_shift b φ wEnd st st' hMono
        rw [hOffDiff] at hU1Off
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        left
        simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh]
        simp only [st1, st1'] at hOffset1
        rw [← hOffset1, ← hU1Off]
      · -- c = [neg u, pos u1]
        simp only [FVar.toVar, EncState.allocFresh] at hEq2
        subst hEq2
        have hOffDiff : st'.nextFresh - st.nextFresh = offset := by omega
        have hU1Off := encodeFormula_controlVar_shift b φ wEnd st st' hMono
        rw [hOffDiff] at hU1Off
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        right; left
        simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh]
        simp only [st1, st1'] at hOffset1
        rw [← hOffset1, ← hU1Off]
      · -- c from st1
        have hShifted := hComp1 c hTail
        simp only [encodeFormula, EncState.addClause, List.mem_cons]
        right; right
        exact hShifted
  | predicate atom =>
      intro c hc
      by_cases hcOld : c ∈ st.clauses
      · -- c from inherited clauses: use hStClauseShift then subset
        have hShifted := hStClauseShift c hcOld
        exact encodeFormula_clauses_subset b (Formula.predicate atom) w st' hShifted
      · -- c is NEW from predicate encoding
        by_cases hNoFresh : clauseHasNoFresh c
        · -- c has no Fresh vars: c.map shiftLitFresh = c
          have hcEq : c.map (shiftLitFresh b offset) = c := shiftClause_nonFresh b offset c hNoFresh
          rw [hcEq]
          exact encodeFormula_predicate_nonFresh_deterministic b atom w st st' c hc hcOld hNoFresh
        · -- c has Fresh vars (from mkBigOrIff or addPreEqFrom Tseytin gadgets)
          simp only [clauseHasNoFresh, not_forall] at hNoFresh
          obtain ⟨lit, hLit, n, hFresh⟩ := hNoFresh
          simp only [ne_eq, not_not] at hFresh
          -- Track through predicate encoding stages
          let pred : Signature.AtomicPredType S := ⟨atom.sym, atom.args⟩
          let idxs := predIxList b pred
          let literals := idxs.map (fun k => Var.Pred w.p w.ti k)
          let st1 := (mkBigOrIff b literals st).2
          let st1' := (mkBigOrIff b literals st').2
          let st2 := addPreEqFrom b w.ti st1
          let st2' := addPreEqFrom b w.ti st1'
          -- Split on whether c is from mkBigOrIff (st1) or addPreEqFrom (st2 \ st1)
          by_cases hcInSt1 : c ∈ st1.clauses
          · -- Case 1: c ∈ st1.clauses (from mkBigOrIff)
            have hLitsNonFresh : ∀ v ∈ literals, ∀ m, v ≠ Var.Fresh m := by
              intro v hv m
              simp only [literals, List.mem_map] at hv
              obtain ⟨k, _, rfl⟩ := hv
              intro hContra; cases hContra
            have hCompat := mkBigOrIff_preserves_clauseShiftCompat b literals st st' offset hOffset
              hStClauseShift hLitsNonFresh c hcInSt1
            -- Show mkBigOrIff output is subset of final encoding output
            simp only [encodeFormula]
            split
            · -- idxs = []: output is mkBigOrIff
              exact hCompat
            · -- idxs ≠ []: mkBigOrIff output is subset of final
              have hSt1St2' : st1'.clauses ⊆ st2'.clauses := addPreEqFrom_clauses_subset b w.ti st1'
              have hSt2St3' : st2'.clauses ⊆ (addPreEqReflAll b st2').clauses :=
                addPreEqReflAll_clauses_subset b st2'
              let st3' := addPreEqReflAll b st2'
              have hSt3Final : st3'.clauses ⊆ ((Bounds.timesL b).foldl (fun stCur H' =>
                  idxs.foldl (fun stAcc k =>
                    let backward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                     SAT.Lit.neg (Var.Pred w.p H' k),
                                     SAT.Lit.pos (Var.Pred w.p w.ti k)]
                    let forward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                    SAT.Lit.neg (Var.Pred w.p w.ti k),
                                    SAT.Lit.pos (Var.Pred w.p H' k)]
                    EncState.addClause b (EncState.addClause b stAcc backward) forward)
                      stCur) st3').clauses := by
                apply foldl_subset_state
                intro stCur H'
                apply foldl_subset_state
                intro stAcc k
                calc stAcc.clauses
                    ⊆ (EncState.addClause b stAcc _).clauses :=
                      EncState.addClause_subset_clauses b stAcc _
                  _ ⊆ (EncState.addClause b (EncState.addClause b stAcc _) _).clauses :=
                      EncState.addClause_subset_clauses b _ _
              exact hSt3Final (hSt2St3' (hSt1St2' hCompat))
          · -- Case 2: c ∉ st1.clauses but in final output
            -- Since c has Fresh vars, c is NOT from addPreEqReflAll or predicateFold
            -- (those only add non-Fresh clauses). So c must be from addPreEqFrom.
            simp only [encodeFormula] at hc
            split at hc
            · -- idxs = []: impossible since c ∉ st1 but c ∈ st1
              exact absurd hc hcInSt1
            · -- idxs ≠ []
              rename_i hNeIdxs
              -- First show c ∈ st2.clauses (addPreEqFrom output)
              let st3 := addPreEqReflAll b st2
              have hSt1St2 : st1.clauses ⊆ st2.clauses := addPreEqFrom_clauses_subset b w.ti st1
              have hSt2St3 : st2.clauses ⊆ st3.clauses := addPreEqReflAll_clauses_subset b st2
              -- Determine which stage c came from
              by_cases hcSt2 : c ∈ st2.clauses
              · -- c from addPreEqFrom - use addPreEqFrom_preserves_clauseShiftCompat
                have hSt1Offset : st1'.nextFresh = st1.nextFresh + offset := by
                  simp only [st1, st1', mkBigOrIff_nextFresh, hOffset]; ring
                have hLitsNonFresh : ∀ v ∈ literals, ∀ m, v ≠ Var.Fresh m := by
                  intro v hv m
                  simp only [literals, List.mem_map] at hv
                  obtain ⟨k, _, rfl⟩ := hv
                  intro hContra; cases hContra
                have hMkBigOrIffCompat : clauseShiftCompat b st1 st1' offset := by
                  intro c' hc'
                  exact mkBigOrIff_preserves_clauseShiftCompat b literals st st' offset hOffset
                    hStClauseShift hLitsNonFresh c' hc'
                have hAddPreEqCompat := addPreEqFrom_preserves_clauseShiftCompat b w.ti
                    st1 st1' offset hSt1Offset hMkBigOrIffCompat
                have hShifted := hAddPreEqCompat c hcSt2
                -- Show st2' clauses are subset of final output
                have hSt2St3' : st2'.clauses ⊆ (addPreEqReflAll b st2').clauses :=
                  addPreEqReflAll_clauses_subset b st2'
                let st3' := addPreEqReflAll b st2'
                -- Connect st3' to encodeFormula output
                have hNeIdxs' : ¬idxs = [] := hNeIdxs
                have hFinalEq : (encodeFormula b (Formula.predicate atom) w st').2.clauses =
                    ((Bounds.timesL b).foldl (fun stCur H' =>
                      idxs.foldl (fun stAcc k =>
                        let backward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                         SAT.Lit.neg (Var.Pred w.p H' k),
                                         SAT.Lit.pos (Var.Pred w.p w.ti k)]
                        let forward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                        SAT.Lit.neg (Var.Pred w.p w.ti k),
                                        SAT.Lit.pos (Var.Pred w.p H' k)]
                        EncState.addClause b (EncState.addClause b stAcc backward) forward)
                          stCur) st3').clauses := by
                  simp only [encodeFormula, st1', st2', st3', idxs, pred, dif_neg hNeIdxs']; rfl
                have hSt3Final : st3'.clauses ⊆ ((Bounds.timesL b).foldl (fun stCur H' =>
                    idxs.foldl (fun stAcc k =>
                      let backward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                       SAT.Lit.neg (Var.Pred w.p H' k),
                                       SAT.Lit.pos (Var.Pred w.p w.ti k)]
                      let forward := [SAT.Lit.neg (Var.PreEq w.ti H'),
                                      SAT.Lit.neg (Var.Pred w.p w.ti k),
                                      SAT.Lit.pos (Var.Pred w.p H' k)]
                      EncState.addClause b (EncState.addClause b stAcc backward) forward)
                        stCur) st3').clauses := by
                  apply foldl_subset_state
                  intro stCur H'
                  apply foldl_subset_state
                  intro stAcc k
                  calc stAcc.clauses
                      ⊆ (EncState.addClause b stAcc _).clauses :=
                        EncState.addClause_subset_clauses b stAcc _
                    _ ⊆ (EncState.addClause b (EncState.addClause b stAcc _) _).clauses :=
                        EncState.addClause_subset_clauses b _ _
                rw [hFinalEq]
                exact hSt3Final (hSt2St3' hShifted)
              · -- c not from addPreEqFrom, check later stages (derive contradiction)
                -- Since c has Fresh vars but is not from st1 (mkBigOrIff) or st2 (addPreEqFrom),
                -- it must be from st3 (addPreEqReflAll) or predicateFold. But both only add
                -- non-Fresh clauses, so c can't have Fresh vars - contradiction.
                exfalso
                by_cases hcSt3 : c ∈ st3.clauses
                · -- c from addPreEqReflAll - these are [pos (PreEq t t)], no Fresh
                  have hReflClauses := addPreEqReflAll_clauses_nonFresh b st2 c hcSt3 hcSt2
                  exact absurd hFresh (hReflClauses lit hLit n)
                · -- c from predicateFold - these are [PreEq, Pred], no Fresh
                  let backward := fun (H' : b.times) (k : b.predIx) =>
                    [SAT.Lit.neg (Var.PreEq w.ti H'), SAT.Lit.neg (Var.Pred w.p H' k),
                     SAT.Lit.pos (Var.Pred w.p w.ti k)]
                  let forward := fun (H' : b.times) (k : b.predIx) =>
                    [SAT.Lit.neg (Var.PreEq w.ti H'), SAT.Lit.neg (Var.Pred w.p w.ti k),
                     SAT.Lit.pos (Var.Pred w.p H' k)]
                  have hMem := nested_foldl_addClause2_mem b (Bounds.timesL b) idxs st3
                    backward forward c hc
                  rcases hMem with hcSt3' | ⟨H', _, k', _, hBackOrFwd⟩
                  · exact hcSt3 hcSt3'
                  · have hNoFreshBF : ∀ (H'' : b.times) (k'' : b.predIx) (lit' : SAT.Lit (Var b)),
                        lit' ∈ backward H'' k'' ∨ lit' ∈ forward H'' k'' →
                        ∀ m, SAT.Lit.getVar lit' ≠ Var.Fresh m := by
                      intro H'' k'' lit' hIn m hContra
                      rcases hIn with hB | hF
                      · simp only [backward, List.mem_cons, List.mem_nil_iff, or_false] at hB
                        rcases hB with rfl | rfl | rfl
                          <;> simp only [SAT.Lit.getVar] at hContra <;> cases hContra
                      · simp only [forward, List.mem_cons, List.mem_nil_iff, or_false] at hF
                        rcases hF with rfl | rfl | rfl
                          <;> simp only [SAT.Lit.getVar] at hContra <;> cases hContra
                    rcases hBackOrFwd with hBack | hFwd
                    · exact hNoFreshBF H' k' lit (Or.inl (hBack ▸ hLit)) n hFresh
                    · exact hNoFreshBF H' k' lit (Or.inr (hFwd ▸ hLit)) n hFresh
  | event atom =>
      intro c hc
      simp only [encodeFormula] at hc ⊢
      -- Match on the decoded event - both hypothesis and goal have same structure
      match hDec : b.decodeMaybeEvent w.ei with
      | MaybeEvent.some e =>
          simp only [hDec] at hc ⊢
          by_cases hEq : e = ⟨atom.sym, atom.args⟩
          · -- e = evt: use encodeFormulaEvent
            simp only [dif_pos hEq] at hc ⊢
            let evt : Signature.EventType S := ⟨atom.sym, atom.args⟩
            exact encodeFormulaEvent_preserves_clauseShiftCompat b w evt st st' offset
              hOffset hStClauseShift c hc
          · -- e ≠ evt: allocFresh + [neg u]
            simp only [dif_neg hEq, EncState.addClause, List.mem_cons] at hc ⊢
            rcases hc with hNew | hOld
            · -- c = [neg (Fresh st.nextFresh)]
              left
              simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh, hOffset, hNew]
            · -- c from st.clauses
              right
              simp only [EncState.allocFresh] at hOld ⊢
              exact hStClauseShift c hOld
      | MaybeEvent.none =>
          simp only [hDec, EncState.addClause, List.mem_cons] at hc ⊢
          rcases hc with hNew | hOld
          · -- c = [neg (Fresh st.nextFresh)]
            left
            simp only [List.map, shiftLitFresh, FVar.toVar, EncState.allocFresh, hOffset, hNew]
          · -- c from st.clauses
            right
            simp only [EncState.allocFresh] at hOld ⊢
            exact hStClauseShift c hOld
  | past φ ih =>
      intro c hc
      -- Past encoding: allocFresh → encodeWitnesses fold → auxVars fold → Type2 clause

      -- Stage 1: allocFresh
      let u := (EncState.allocFresh b st).1
      let u' := (EncState.allocFresh b st').1
      let st1 := (EncState.allocFresh b st).2
      let st1' := (EncState.allocFresh b st').2
      let witnesses := (WId.allWorlds b).filterMap fun w' => if w'.p = w.p then some w' else none

      have hUOff : u'.id = u.id + offset := by simp only [u, u', EncState.allocFresh, hOffset]
      have hOffset1 : st1'.nextFresh = st1.nextFresh + offset := by
        simp only [st1, st1', EncState.allocFresh, hOffset]; ring
      have hCompat1 : clauseShiftCompat b st1 st1' offset := by
        intro c' hc'; simp only [st1, st1', EncState.allocFresh] at hc' ⊢
        exact hStClauseShift c' hc'

      -- Stage 2: encodeWitnesses fold
      let encWitStep := fun (uvars, stCur) w' =>
          let res := encodeFormula b φ w' stCur
          (uvars ++ [res.1], res.2)
      let result2 := witnesses.foldl encWitStep ([], st1)
      let result2' := witnesses.foldl encWitStep ([], st1')
      let witnessVars := result2.1
      let witnessVars' := result2'.1
      let st2 := result2.2
      let st2' := result2'.2

      have hIH' : ∀ w' stX stX', stX'.nextFresh = stX.nextFresh + offset →
          clauseShiftCompat b stX stX' offset →
          clauseShiftCompat b (encodeFormula b φ w' stX).2
            (encodeFormula b φ w' stX').2 offset := by
        intro w' stX stX' hOffX hCompX
        have hMonoX : stX.nextFresh ≤ stX'.nextFresh := by omega
        exact ih w' stX stX' hOffX hCompX hMonoX

      have hCompat2 : clauseShiftCompat b st2 st2' offset := by
        simp only [st2, st2', result2, result2']
        exact encodeWitnesses_foldl_preserves_clauseShiftCompat b φ witnesses st1 st1' offset
          hOffset1 hCompat1 hIH'
      have hOffset2 : st2'.nextFresh = st2.nextFresh + offset := by
        simp only [st2, st2', result2, result2']
        exact encodeWitnesses_foldl_nextFresh_offset b φ witnesses st1 st1' offset hOffset1

      -- Get witnessVars offset relationship
      have hMono1 : st1.nextFresh ≤ st1'.nextFresh := by omega
      have hNextFreshIH : ∀ w' stX stX', stX'.nextFresh = stX.nextFresh + offset →
          stX.nextFresh ≤ stX'.nextFresh →
          (encodeFormula b φ w' stX').2.nextFresh =
            (encodeFormula b φ w' stX).2.nextFresh + offset :=
        fun w' stX stX' hOff _ => encodeFormula_nextFresh_offset b φ w' stX stX' offset hOff
      have hVarsInfo := encodeWitnesses_foldl_vars_offset b φ witnesses st1 st1' offset
        hOffset1 hMono1 hNextFreshIH
      have hVarsLen : witnessVars.length = witnessVars'.length := by
        simp only [witnessVars, witnessVars', result2, result2']
        exact hVarsInfo.1
      have hVarsOff : ∀ i (hi : i < witnessVars.length) (hi' : i < witnessVars'.length),
          (witnessVars.get ⟨i, hi⟩).id + offset = (witnessVars'.get ⟨i, hi'⟩).id := by
        simp only [witnessVars, witnessVars', result2, result2']
        exact hVarsInfo.2

      -- Stage 3: auxVars fold
      -- Define step functions matching the helper lemmas
      let auxStep := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
        let (uv, wv) := pair
        let memVar := Var.Mem w.ti wv
        let (aux, stCur) := EncState.allocFresh b acc.2
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
        (acc.1 ++ [aux], stCur)
      let auxStep' := fun (acc : List (FVar b) × EncState b) (pair : FVar b × WId b) =>
        let (uv, wv) := pair
        let memVar := Var.Mem w.ti wv
        let (aux, stCur) := EncState.allocFresh b acc.2
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b u')]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg memVar, SAT.Lit.neg (FVar.toVar b uv), SAT.Lit.pos (FVar.toVar b aux)]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos memVar]
        let stCur := EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b aux), SAT.Lit.pos (FVar.toVar b uv)]
        (acc.1 ++ [aux], stCur)

      let pairs := witnessVars.zip witnesses
      let pairs' := witnessVars'.zip witnesses

      have hPairsLen : pairs.length = pairs'.length := by
        simp only [pairs, pairs', List.length_zip, hVarsLen]
      have hPairsOff : ∀ i (hi : i < pairs.length) (hi' : i < pairs'.length),
          (pairs.get ⟨i, hi⟩).1.id + offset = (pairs'.get ⟨i, hi'⟩).1.id ∧
          (pairs.get ⟨i, hi⟩).2 = (pairs'.get ⟨i, hi'⟩).2 := by
        intro i hi hi'
        simp only [pairs, pairs'] at hi hi' ⊢
        have hi1 : i < witnessVars.length := by simp [List.length_zip] at hi; omega
        have hi1' : i < witnessVars'.length := by simp [List.length_zip] at hi'; omega
        constructor
        · simp only [List.get_eq_getElem, List.getElem_zip]
          exact hVarsOff i hi1 hi1'
        · simp only [List.get_eq_getElem, List.getElem_zip]

      let result3 := pairs.foldl auxStep ([], st2)
      let result3' := pairs'.foldl auxStep' ([], st2')
      let auxVarsLocal := result3.1
      let auxVarsLocal' := result3'.1
      let st3 := result3.2
      let st3' := result3'.2

      have hCompat3 : clauseShiftCompat b st3 st3' offset := by
        simp only [st3, st3', result3, result3', auxStep, auxStep']
        exact auxVars_foldl_preserves_clauseShiftCompat b w u u' pairs pairs' st2 st2' offset
          hOffset2 hCompat2 hUOff hPairsLen hPairsOff

      have hOffset3 : st3'.nextFresh = st3.nextFresh + offset := by
        simp only [st3, st3', result3, result3', auxStep, auxStep']
        exact auxVars_foldl_nextFresh_offset b w u u' pairs pairs' st2 st2' offset
          hOffset2 hPairsLen

      have hAuxVarsInfo := auxVars_foldl_vars_offset b w u u' pairs pairs' st2 st2' offset
        hOffset2 hPairsLen
      have hAuxVarsLen : auxVarsLocal.length = auxVarsLocal'.length := by
        simp only [auxVarsLocal, auxVarsLocal', result3, result3', auxStep, auxStep']
        exact hAuxVarsInfo.1
      have hAuxVarsOff : ∀ i (hi : i < auxVarsLocal.length) (hi' : i < auxVarsLocal'.length),
          (auxVarsLocal.get ⟨i, hi⟩).id + offset = (auxVarsLocal'.get ⟨i, hi'⟩).id := by
        simp only [auxVarsLocal, auxVarsLocal', result3, result3', auxStep, auxStep']
        exact hAuxVarsInfo.2

      -- Stage 4: Type2 clause [neg u, aux₁, ..., auxₙ]
      let type2 := [SAT.Lit.neg (FVar.toVar b u)] ++
        auxVarsLocal.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))
      let type2' := [SAT.Lit.neg (FVar.toVar b u')] ++
        auxVarsLocal'.map (fun aux => SAT.Lit.pos (FVar.toVar b aux))

      have hType2Shift : type2.map (shiftLitFresh b offset) = type2' := by
        simp only [type2, type2', List.map_append, List.map_cons, List.map_nil, List.map_map]
        -- Goal: [shifted neg u] ++ (shifted auxVars) = [neg u'] ++ auxVars'
        congr 1
        · -- neg u shifts to neg u'
          simp only [shiftLitFresh, FVar.toVar, hUOff]
        · -- auxVars shift to auxVars'
          apply List.ext_getElem
          · simp only [List.length_map, hAuxVarsLen]
          · intro i hi hi'
            simp only [List.getElem_map, Function.comp_apply, shiftLitFresh, FVar.toVar]
            simp only [List.length_map] at hi hi'
            have h := hAuxVarsOff i hi hi'
            simp only [List.get_eq_getElem] at h
            simp only [h]

      let st4 := EncState.addClause b st3 type2
      let st4' := EncState.addClause b st3' type2'

      have hCompat4 : clauseShiftCompat b st4 st4' offset := by
        intro c' hc'
        simp only [st4, st4', EncState.addClause, List.mem_cons] at hc' ⊢
        cases hc' with
        | inl hEq => left; rw [hEq, hType2Shift]
        | inr hOld => right; exact hCompat3 c' hOld

      -- Connect to the actual encoding result
      simp only [encodeFormula] at hc ⊢
      exact hCompat4 c hc
  | «forall» body ih =>
      intro c hc
      -- Forall encoding structure:
      -- 1. allocFresh → u, st1
      -- 2. encodeConj fold (encodeFormula for body(v)) → bodyVars, st2
      -- 3. Forward clauses fold: [¬u, uᵢ] → st3
      -- 4. Backward clause: [¬u₁, ..., ¬uₙ, u] → st4

      -- Define intermediate states
      let u := (EncState.allocFresh b st).1
      let u' := (EncState.allocFresh b st').1
      let st1 := (EncState.allocFresh b st).2
      let st1' := (EncState.allocFresh b st').2

      -- u and u' offset
      have hUOff : u'.id = u.id + offset := by
        simp only [u, u', EncState.allocFresh, hOffset]

      -- st1/st1' offset
      have hOffset1 : st1'.nextFresh = st1.nextFresh + offset := by
        simp only [st1, st1', EncState.allocFresh, hOffset]; ring

      -- st1/st1' clause shift compat
      have hCompat1 : clauseShiftCompat b st1 st1' offset := by
        intro c' hc'
        simp only [st1, st1', EncState.allocFresh] at hc' ⊢
        exact hStClauseShift c' hc'

      -- IH wrapper for encodeConj fold
      have hIH' : ∀ v stX stX', stX'.nextFresh = stX.nextFresh + offset →
          clauseShiftCompat b stX stX' offset →
          clauseShiftCompat b (encodeFormula b (body v) w stX).2
            (encodeFormula b (body v) w stX').2 offset := by
        intro v stX stX' hOffX hCompX
        have hMonoX : stX.nextFresh ≤ stX'.nextFresh := by omega
        exact ih v w stX stX' hOffX hCompX hMonoX

      -- Clause shift compat through encodeConj fold
      have hCompat2 : clauseShiftCompat b
          ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
            let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
            (vars ++ [uBody], stNext)) ([], st1)).2
          ((List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
            let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
            (vars ++ [uBody], stNext)) ([], st1')).2 offset :=
        forall_encodeConj_foldl_preserves_clauseShiftCompat b body w (List.finRange b.nVals)
          st1 st1' offset hOffset1 hCompat1 hIH'

      -- Define bodyVars and st2
      let result := (List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
        let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
        (vars ++ [uBody], stNext)) ([], st1)
      let result' := (List.finRange b.nVals).foldl (fun (vars, stCur) vIdx =>
        let (uBody, stNext) := encodeFormula b (body (b.values.get vIdx)) w stCur
        (vars ++ [uBody], stNext)) ([], st1')
      let bodyVars := result.1
      let bodyVars' := result'.1
      let st2 := result.2
      let st2' := result'.2

      -- Get offset relationship for bodyVars
      have hVarsInfo := forall_encodeConj_foldl_vars_offset b body w (List.finRange b.nVals)
        st1 st1' offset hOffset1
      obtain ⟨hLenEq, hOffset2, hVarsOff⟩ := hVarsInfo

      -- Forward clauses fold preserves compat
      have hCompat3 : clauseShiftCompat b
          (bodyVars.foldl (fun stCur uBody => EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]) st2)
          (bodyVars'.foldl (fun stCur uBody => EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b uBody)]) st2') offset := by
        apply forall_forward_clauses_foldl_preserves_clauseShiftCompat b u u' bodyVars bodyVars'
          st2 st2' offset hUOff hLenEq
        · intro i hi hi'
          have h := hVarsOff i hi hi'
          omega
        · exact hCompat2

      let st3 := bodyVars.foldl (fun stCur uBody => EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b uBody)]) st2
      let st3' := bodyVars'.foldl (fun stCur uBody => EncState.addClause b stCur
          [SAT.Lit.neg (FVar.toVar b u'), SAT.Lit.pos (FVar.toVar b uBody)]) st2'

      -- Backward clause: [¬u₁, ..., ¬uₙ, u]
      let backClause := bodyVars.map (fun uBody => SAT.Lit.neg (FVar.toVar b uBody))
        ++ [SAT.Lit.pos (FVar.toVar b u)]
      let backClause' := bodyVars'.map (fun uBody => SAT.Lit.neg (FVar.toVar b uBody))
        ++ [SAT.Lit.pos (FVar.toVar b u')]

      -- Show backward clause shifts correctly
      have hBackShift : backClause.map (shiftLitFresh b offset) = backClause' := by
        simp only [backClause, backClause', List.map_append, List.map_map]
        congr 1
        · -- bodyVars.map (shift ∘ neg) = bodyVars'.map neg
          -- Both are lists of same length with equal elements
          have hMapEq : List.map (shiftLitFresh b offset ∘ fun uBody =>
              SAT.Lit.neg (FVar.toVar b uBody)) bodyVars =
              List.map (fun uBody => SAT.Lit.neg (FVar.toVar b uBody)) bodyVars' := by
            apply List.ext_getElem
            · simp only [List.length_map]; exact hLenEq
            · intro i hi hi'
              simp only [List.length_map] at hi hi'
              simp only [List.getElem_map, Function.comp_apply, FVar.toVar, shiftLitFresh]
              -- bodyVars = result.1 = (foldl...).1, same for bodyVars'
              -- Goal: neg (Fresh (bodyVars[i].id + offset)) = neg (Fresh bodyVars'[i].id)
              -- hVarsOff gives: result.1[i].id + offset = result'.1[i].id
              -- Since bodyVars = result.1 and bodyVars' = result'.1, this is exactly what we need
              simp only [bodyVars, bodyVars', result, result'] at hi hi' ⊢
              have hOff := hVarsOff i hi hi'
              simp only [List.get_eq_getElem] at hOff
              simp_all
          exact hMapEq
        · -- [pos u] shifts to [pos u']
          simp only [List.map, shiftLitFresh, FVar.toVar, hUOff]

      -- Final clause shift compat
      have hCompat4 : clauseShiftCompat b
          (EncState.addClause b st3 backClause)
          (EncState.addClause b st3' backClause') offset := by
        intro c' hc'
        simp only [EncState.addClause, List.mem_cons] at hc' ⊢
        cases hc' with
        | inl hEq =>
            left
            rw [hEq, hBackShift]
        | inr hOld =>
            right
            exact hCompat3 c' hOld

      -- Show c is in the final state
      -- The goal and hc both refer to encodeFormula ... which equals our st4
      simp only [encodeFormula] at hc ⊢
      exact hCompat4 c hc
  | diamond learners φ ih =>
      intro c hc
      -- Diamond encoding has 3 phases:
      -- 1. Generate tuples (deterministic, same for st and st')
      -- 2. Fold over tuples with diamondStep → (tupleVars, stTuples)
      -- 3. Final phase: match tupleVars, either allocFresh+addClause or mkAndIff fold

      -- CRITICAL: Define getMinQs with EXACT inline form from encodeFormula
      -- (NOT diamondGetMinQs, which won't unify after simp only [encodeFormula])
      let getMinQs (ℓ : S.Value) : List (Finset b.participants) :=
        let vIdx := b.findValueIndex ℓ
        let allVars := Var.allMinQ b vIdx
        allVars.filterMap fun v =>
          match v with
          | Var.MinQ _ Q => some Q
          | _ => none
      let quorumSets := learners.map getMinQs
      let tuples := cartesianProduct quorumSets

      -- Define fold results using diamondStep (bridge lemma will match)
      let tupleVars := (tuples.foldl (diamondStep b learners φ w) ([], st)).1
      let stTuples := (tuples.foldl (diamondStep b learners φ w) ([], st)).2
      let tupleVars' := (tuples.foldl (diamondStep b learners φ w) ([], st')).1
      let stTuples' := (tuples.foldl (diamondStep b learners φ w) ([], st')).2

      -- Build IH wrappers
      have hIH_compat : ∀ w' stX stX', stX'.nextFresh = stX.nextFresh + offset →
          clauseShiftCompat b stX stX' offset →
          clauseShiftCompat b (encodeFormula b φ w' stX).2
            (encodeFormula b φ w' stX').2 offset := by
        intro w' stX stX' hOffX hCompX
        unfold clauseShiftCompat
        intro c' hc'
        have hMono' : stX.nextFresh ≤ stX'.nextFresh := by omega
        exact ih w' stX stX' hOffX hCompX hMono' c' hc'
      have hIH_offset : ∀ w' stX stX' off, stX'.nextFresh = stX.nextFresh + off →
          (encodeFormula b φ w' stX').2.nextFresh = (encodeFormula b φ w' stX).2.nextFresh + off :=
        fun w' stX stX' off hOff => encodeFormula_nextFresh_offset b φ w' stX stX' off hOff

      -- Get clauseShiftCompat for stTuples/stTuples'
      have hFoldCompat : clauseShiftCompat b stTuples stTuples' offset :=
        diamond_tuples_foldl_preserves_clauseShiftCompat b φ w learners tuples st st' offset
          hOffset hStClauseShift hIH_compat hIH_offset

      have hFoldOffset : stTuples'.nextFresh = stTuples.nextFresh + offset :=
        diamondStep_foldl_offset b learners φ w tuples st st' offset hOffset hIH_offset

      -- Check if c is in stTuples.clauses (from the fold) or new (from final phase)
      by_cases hcTuples : c ∈ stTuples.clauses
      · -- CASE 1: c ∈ stTuples.clauses - use clauseShiftCompat
        have hcTuples' : c.map (shiftLitFresh b offset) ∈ stTuples'.clauses :=
          hFoldCompat c hcTuples

        -- Unfold encodeFormula and rewrite to use diamondStep
        simp only [encodeFormula]
        rw [encodeFormula_diamond_step_unfolded_eq]

        -- Split on the match in the goal
        split
        · -- Case: empty list - allocFresh + addClause preserves stTuples'.clauses
          simp only [EncState.addClause, List.mem_cons]
          right
          exact EncState.allocFresh_clauses_eq (b := b) stTuples' ▸ hcTuples'
        · -- Case: cons - mkAndIff fold preserves stTuples'.clauses
          rename_i u0' us' _
          have hAndFold : stTuples'.clauses ⊆
              (us'.foldl (fun (acc : FVar b × EncState b) u' =>
                mkAndIff b acc.1 u' acc.2) (u0', stTuples')).2.clauses :=
            foldl_subset_snd
              (f := fun (acc : FVar b × EncState b) u' => mkAndIff b acc.1 u' acc.2)
              (hStep := fun acc u' => mkAndIff_clauses_subset b acc.1 u' acc.2)
              (xs := us') (init := (u0', stTuples'))
          exact hAndFold hcTuples'

      · -- CASE 2: c ∉ stTuples.clauses - c is from final phase, must track shift
        -- Get vars offset info upfront (using my local tuples)
        have hVarsInfo := diamond_tuples_foldl_vars_offset b φ w learners tuples st st' offset
          hOffset hIH_offset
        have hFoldLen := diamondStep_foldl_length_eq b learners φ w tuples st st'

        simp only [encodeFormula] at hc ⊢
        rw [encodeFormula_diamond_step_unfolded_eq] at hc ⊢

        -- After the bridge lemma, both hc and goal use diamondStep with the same tuples
        -- (inline tuples = my local tuples by definitional equality)
        -- The split hypotheses will be about my local tupleVars/tupleVars' definitions

        -- The split discriminant hypotheses say tupleVars = [] or = u0 :: us, etc.
        -- We can use these to rewrite hFoldLen and hVarsInfo
        split at hc
        · -- Source: nil case
          rename_i hSrcNil  -- hSrcNil : tupleVars = []
          split
          · -- Goal: nil case - both empty
            simp only [EncState.addClause, List.mem_cons] at hc ⊢
            cases hc with
            | inl hEq =>
                left
                simp only [EncState.allocFresh] at hEq ⊢
                subst hEq
                simp only [List.map, shiftLitFresh, FVar.toVar]
                -- Goal: Fresh stTuples.nextFresh + offset = Fresh stTuples'.nextFresh
                -- Convert goal to use my local definitions
                change [SAT.Lit.pos (Var.Fresh (stTuples.nextFresh + offset))] =
                       [SAT.Lit.pos (Var.Fresh stTuples'.nextFresh)]
                simp only [hFoldOffset]
            | inr hOld =>
                simp only [EncState.allocFresh] at hOld
                exact absurd hOld hcTuples
          · -- Goal: cons case but source nil - impossible (same length)
            rename_i u0' us' hGoalCons  -- hGoalCons : tupleVars' = u0' :: us'
            -- Bridge: discriminant hypotheses are definitionally equal to my local defs
            have hSrcNilLocal : tupleVars = [] := hSrcNil
            have hGoalConsLocal : tupleVars' = u0' :: us' := hGoalCons
            -- hFoldLen uses my local tuples, so now we can rewrite
            have hFoldLen' : tupleVars'.length = tupleVars.length := hFoldLen
            rw [hSrcNilLocal, hGoalConsLocal] at hFoldLen'
            simp only [List.length_nil, List.length_cons] at hFoldLen'
            omega
        · -- Source: cons case
          rename_i u0 us hSrcCons  -- hSrcCons : tupleVars = u0 :: us
          split
          · -- Goal: nil but source cons - impossible (same length)
            rename_i hGoalNil  -- hGoalNil : tupleVars' = []
            -- Bridge: discriminant hypotheses are definitionally equal to my local defs
            have hSrcConsLocal : tupleVars = u0 :: us := hSrcCons
            have hGoalNilLocal : tupleVars' = [] := hGoalNil
            -- hFoldLen uses my local tuples, so now we can rewrite
            have hFoldLen' : tupleVars'.length = tupleVars.length := hFoldLen
            rw [hSrcConsLocal, hGoalNilLocal] at hFoldLen'
            simp only [List.length_nil, List.length_cons] at hFoldLen'
            omega
          · -- Goal: cons case - both have mkAndIff fold
            rename_i u0' us' hGoalCons  -- hGoalCons : (inline fold for st').1 = u0' :: us'

            -- Bridge: my tupleVars/tupleVars' are definitionally equal to the inline forms
            -- hSrcCons and hGoalCons are about inline forms, which = my local defs
            have hTupleVarsEq : tupleVars = u0 :: us := hSrcCons
            have hTupleVars'Eq : tupleVars' = u0' :: us' := hGoalCons

            -- Length equality
            have hUsLen : us.length = us'.length := by
              have h := hFoldLen
              -- Convert h from internal form to use tupleVars/tupleVars'
              change tupleVars'.length = tupleVars.length at h
              simp only [hTupleVarsEq, hTupleVars'Eq, List.length_cons] at h
              omega

            -- u0 offset
            have hU0Off : u0'.id = u0.id + offset := by
              have hLen1 : 0 < tupleVars.length := by rw [hTupleVarsEq]; simp
              have hLen1' : 0 < tupleVars'.length := by rw [hTupleVars'Eq]; simp
              have h := hVarsInfo.2 0 hLen1 hLen1'
              -- Convert h from internal form to use tupleVars/tupleVars'
              change (tupleVars.get ⟨0, hLen1⟩).id + offset =
                     (tupleVars'.get ⟨0, hLen1'⟩).id at h
              simp only [hTupleVarsEq, hTupleVars'Eq, List.get_eq_getElem,
                         List.getElem_cons_zero] at h
              omega

            -- us elements offset
            have hUsOff : ∀ i (hi : i < us.length) (hi' : i < us'.length),
                (us.get ⟨i, hi⟩).id + offset = (us'.get ⟨i, hi'⟩).id := by
              intro i hi hi'
              -- Need to show us[i] + offset = us'[i]
              -- We know (tupleVars.get (i+1)) + offset = (tupleVars'.get (i+1))
              -- And tupleVars = u0 :: us, tupleVars' = u0' :: us'
              -- So (u0 :: us)[i+1] = us[i]
              have hLen1 : i + 1 < (u0 :: us).length := by simp; omega
              have hLen1' : i + 1 < (u0' :: us').length := by simp; omega
              have hLen2 : i + 1 < tupleVars.length := by rw [hTupleVarsEq]; exact hLen1
              have hLen2' : i + 1 < tupleVars'.length := by rw [hTupleVars'Eq]; exact hLen1'
              have h := hVarsInfo.2 (i + 1) hLen2 hLen2'
              -- Convert to use tupleVars/tupleVars'
              change (tupleVars.get ⟨i + 1, hLen2⟩).id + offset =
                     (tupleVars'.get ⟨i + 1, hLen2'⟩).id at h
              -- Now use that tupleVars = u0 :: us, tupleVars' = u0' :: us'
              simp only [hTupleVarsEq, hTupleVars'Eq, List.get_eq_getElem,
                         List.getElem_cons_succ] at h
              convert h using 2

            -- Apply mkAndIff_foldl_preserves_clauseShiftCompat
            exact mkAndIff_foldl_preserves_clauseShiftCompat b u0 u0' us us' stTuples stTuples'
              offset hFoldOffset hFoldCompat hU0Off hUsLen hUsOff c hc

end Encoding
