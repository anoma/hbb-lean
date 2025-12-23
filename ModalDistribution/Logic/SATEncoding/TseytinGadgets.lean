import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Types

/-!
# Tseytin Transformation Gadgets

This file provides reusable Tseytin transformation utilities for encoding boolean
formulas into CNF. These gadgets are used to build the PreEq and formula encodings.

## Main Components

- `mkIff`: Tseytin gadget for biconditional (a ↔ b)
- `mkMemEq`: Tseytin for membership bit equality
- `addAccStep`: Tseytin for conjunction accumulation (next ↔ cur ∧ bit)
- `mkBigOrIff`: Tseytin gadget for disjunction (u ↔ ⋁ vs)
- `addPreEqExpose`: Expose PreEq with fresh variable (used by PreEq encoding)
- `addPreEqReflAll`: Global reflexivity units for PreEq
- Various helper lemmas for clause subset preservation

## References

See Plan.md sections on Tseytin transformation and CNF encoding.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-! ## Tseytin Transformation

The Tseytin transformation converts a formula into an equisatisfiable CNF by:
1. Introducing auxiliary variables for each subformula
2. Adding clauses that enforce equivalence between the aux var and the subformula
3. Asserting that the top-level aux variable must be true

We use stateful encoding with `EncState` to accumulate clauses and allocate fresh variables.
-/

/-- Cartesian product of a list of lists. -/
def cartesianProduct {α : Type _} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss =>
      let rest := cartesianProduct xss
      xs.flatMap fun x => rest.map fun r => x :: r

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma addClause_fold_subset
    (b : Bounds S) (has : FVar b) :
    ∀ (zs : List (FVar b)) (st : EncState b),
      st.clauses ⊆
        (zs.foldl
          (fun stCur z =>
            EncState.addClause b stCur
              [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos (FVar.toVar b has)])
          st).clauses := by
  classical
  intro zs
  induction zs with
  | nil =>
      intro st clause hClause
      simpa [List.foldl]
  | cons z zs ih =>
      intro st clause hClause
      let clause' :=
        [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos (FVar.toVar b has)]
      have hSubsetAdd :
          st.clauses ⊆ (EncState.addClause b st clause').clauses :=
        EncState.addClause_subset_clauses (b := b) st clause'
      have hClause' :
          clause ∈ (EncState.addClause b st clause').clauses :=
        hSubsetAdd hClause
      have hResult :
          clause ∈
            (zs.foldl
              (fun stCur z =>
                EncState.addClause b stCur
                  [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos (FVar.toVar b has)])
              (EncState.addClause b st clause')).clauses :=
        ih (EncState.addClause b st clause') hClause'
      simpa [List.foldl, clause'] using hResult

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma foldl_has_clause_mem
    (b : Bounds S) (has : FVar b) (st : EncState b) :
    ∀ {zs : List (FVar b)} {z : FVar b},
      z ∈ zs →
        [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos (FVar.toVar b has)] ∈
          (zs.foldl
            (fun stCur z =>
              EncState.addClause b stCur
                [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos (FVar.toVar b has)])
            st).clauses := by
  classical
  intro zs
  revert st
  induction zs with
  | nil =>
      intro st z hMem
      cases hMem
  | cons z₀ zs ih =>
      intro st z hMem
      let stepFn :=
        fun (stCur : EncState b) (w : FVar b) =>
          EncState.addClause b stCur
            [SAT.Lit.neg (FVar.toVar b w), SAT.Lit.pos (FVar.toVar b has)]
      have hSplit : z = z₀ ∨ z ∈ zs := by
        simpa [List.mem_cons] using hMem
      let stHead := stepFn st z₀
      rcases hSplit with rfl | hTail
      · have hClauseInStHead :
            [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos (FVar.toVar b has)] ∈ stHead.clauses := by
          simp [stHead, stepFn, EncState.addClause, List.mem_cons]
        have hClauseInTail :
            [SAT.Lit.neg (FVar.toVar b z), SAT.Lit.pos (FVar.toVar b has)] ∈
              (zs.foldl stepFn stHead).clauses :=
          (addClause_fold_subset (b := b) (has := has) zs stHead) hClauseInStHead
        simpa [List.foldl, stepFn, stHead] using hClauseInTail
      · have hClauseTail :=
          ih (st := stHead) (z := z) hTail
        simpa [List.foldl, stepFn, stHead] using hClauseTail

/-- Build eq1 ↔ (a ↔ b) with 4 clauses.
    Encodes bidirectional equality of two boolean variables. -/
def mkIff (b : Bounds S) (a bvar : FVar b) (st : EncState b) : FVar b × EncState b :=
  let (eq1, st1) := EncState.allocFresh b st
  -- eq1 → (a → b): [¬eq1, ¬a, b]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b eq1), SAT.Lit.neg (FVar.toVar b a), SAT.Lit.pos (FVar.toVar b bvar)]
  -- eq1 → (b → a): [¬eq1, a, ¬b]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b eq1), SAT.Lit.pos (FVar.toVar b a), SAT.Lit.neg (FVar.toVar b bvar)]
  -- (a=false ∧ b=false) → eq1: [eq1, a, b]
  let st1 := EncState.addClause b st1
    [SAT.Lit.pos (FVar.toVar b eq1), SAT.Lit.pos (FVar.toVar b a), SAT.Lit.pos (FVar.toVar b bvar)]
  -- (a=true ∧ b=true) → eq1: [eq1, ¬a, ¬b]
  let st1 := EncState.addClause b st1
    [SAT.Lit.pos (FVar.toVar b eq1), SAT.Lit.neg (FVar.toVar b a), SAT.Lit.neg (FVar.toVar b bvar)]
  (eq1, st1)

/-- Build u ↔ (x ∧ y) with 3 clauses.
    Clauses: (¬u ∨ x), (¬u ∨ y), (¬x ∨ ¬y ∨ u) -/
def mkAndIff (b : Bounds S) (x y : FVar b) (st : EncState b) : FVar b × EncState b :=
  let (u, st1) := EncState.allocFresh b st
  -- u → x: [¬u, x]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x)]
  -- u → y: [¬u, y]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b y)]
  -- (x ∧ y) → u: [¬x, ¬y, u]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)]
  (u, st1)


/-- Encodes v ↔ Mem(H, w).
    Clauses: (¬v ∨ Mem(H, w)), (¬Mem(H, w) ∨ v) -/
def addMemVar (b : Bounds S) (H : b.times) (w : WId b) (st : EncState b) : FVar b × EncState b :=
  let (v, st1) := EncState.allocFresh b st
  -- v → Mem(H, w): [¬v, Mem(H, w)]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b v), SAT.Lit.pos (Var.Mem H w)]
  -- Mem(H, w) → v: [¬Mem(H, w), v]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (Var.Mem H w), SAT.Lit.pos (FVar.toVar b v)]
  (v, st1)

/-- Build u ↔ (x ∨ y) with 3 clauses.
    Clauses: (¬x ∨ u), (¬y ∨ u), (¬u ∨ x ∨ y) -/
def mkOrIff (b : Bounds S) (x y : FVar b) (st : EncState b) : FVar b × EncState b :=
  let (u, st1) := EncState.allocFresh b st
  -- x → u: [¬x, u]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)]
  -- y → u: [¬y, u]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)]
  -- u → (x ∨ y): [¬u, x, y]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b y)]
  (u, st1)

/-- Build u ↔ (x → y) with 3 clauses.
    Equivalent to u ↔ (¬x ∨ y).
    Clauses: (x ∨ u), (¬y ∨ u), (¬u ∨ ¬x ∨ y) -/
def mkImpIff (b : Bounds S) (x y : FVar b) (st : EncState b) : FVar b × EncState b :=
  let (u, st1) := EncState.allocFresh b st
  -- ¬x → u (x ∨ u): [x, u]
  let st1 := EncState.addClause b st1
    [SAT.Lit.pos (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)]
  -- y → u (¬y ∨ u): [¬y, u]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)]
  -- u → (¬x ∨ y): [¬u, ¬x, y]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b y)]
  (u, st1)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- mkAndIff increases nextFresh by exactly 1. -/
lemma mkAndIff_nextFresh (b : Bounds S) (x y : FVar b) (st : EncState b) :
    (mkAndIff b x y st).2.nextFresh = st.nextFresh + 1 := by
  simp [mkAndIff, EncState.addClause, EncState.allocFresh_nextFresh]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- mkAndIff is monotonic in nextFresh. -/
lemma mkAndIff_nextFresh_mono (b : Bounds S) (x y : FVar b) (st : EncState b) :
    st.nextFresh ≤ (mkAndIff b x y st).2.nextFresh := by
  rw [mkAndIff_nextFresh]; omega

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkAndIff_clauses_subset (b : Bounds S) (x y : FVar b) (st : EncState b) :
    st.clauses ⊆ (mkAndIff b x y st).2.clauses := by
  classical
  unfold mkAndIff
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      have hAllocSub : st.clauses ⊆ st1.clauses := by
        have eq : st1 = (EncState.allocFresh b st).2 := by simp [hAlloc]
        intro clause h
        rw [eq, EncState.allocFresh_clauses_eq]
        exact h
      have hAdd1 :=
        EncState.addClause_subset_clauses (b := b) st1
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x)]
      have hAdd2 := EncState.addClause_subset_clauses (b := b)
        (EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x)])
        [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b y)]
      have hAdd3 := EncState.addClause_subset_clauses (b := b)
        (EncState.addClause b
          (EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x)])
          [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b y)])
        [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)]
      exact List.Subset.trans hAllocSub (List.Subset.trans hAdd1 (List.Subset.trans hAdd2 hAdd3))

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- mkAndIff preserves well-formedness if x and y have ids < st.nextFresh. -/
lemma mkAndIff_wf (b : Bounds S) (x y : FVar b) (st : EncState b)
    (hWF : EncState.WellFormed st)
    (hx : x.id < st.nextFresh) (hy : y.id < st.nextFresh) :
    EncState.WellFormed (mkAndIff b x y st).2 := by
  simp only [mkAndIff]
  -- After allocFresh: u.id = st.nextFresh, st1.nextFresh = st.nextFresh + 1
  have hAllocWF : (EncState.allocFresh b st).2.WellFormed := EncState.allocFresh_wf hWF
  have hAllocNext : (EncState.allocFresh b st).2.nextFresh = st.nextFresh + 1 :=
    EncState.allocFresh_nextFresh b st
  -- u.id = st.nextFresh
  have hUId : (EncState.allocFresh b st).1.id = st.nextFresh := by
    simp only [EncState.allocFresh]
  -- All clauses use only: u (id = st.nextFresh), x (id < st.nextFresh), y (id < st.nextFresh)
  -- After allocFresh, nextFresh = st.nextFresh + 1
  -- So all Fresh vars have id < st.nextFresh + 1
  -- Clause 1: [¬u, x]
  have hC1 : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
      SAT.Lit.pos (FVar.toVar b x)] (EncState.allocFresh b st).2.nextFresh := by
    intro lit hLit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h =>
      subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hUId, hAllocNext]; omega
    | inr h =>
      subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hAllocNext]; omega
  have hWF1 := EncState.addClause_wf hAllocWF _ hC1
  -- Clause 2: [¬u, y]
  have hC2 : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
      SAT.Lit.pos (FVar.toVar b y)] (EncState.allocFresh b st).2.nextFresh := by
    intro lit hLit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
    cases hLit with
    | inl h =>
      subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hUId, hAllocNext]; omega
    | inr h =>
      subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hAllocNext]; omega
  have hWF2 := EncState.addClause_wf hWF1 _ hC2
  -- Clause 3: [¬x, ¬y, u]
  have hC3 : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.neg (FVar.toVar b y),
      SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)]
      (EncState.allocFresh b st).2.nextFresh := by
    intro lit hLit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
    rcases hLit with h | h | h
    · subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hAllocNext]; omega
    · subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hAllocNext]; omega
    · subst h; simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hUId, hAllocNext]; omega
  exact EncState.addClause_wf hWF2 _ hC3

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOrIff_clauses_subset (b : Bounds S) (x y : FVar b) (st : EncState b) :
    st.clauses ⊆ (mkOrIff b x y st).2.clauses := by
  classical
  unfold mkOrIff
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      have hAllocSub : st.clauses ⊆ st1.clauses := by
        have eq : st1 = (EncState.allocFresh b st).2 := by simp [hAlloc]
        intro clause h
        rw [eq, EncState.allocFresh_clauses_eq]
        exact h
      have hAdd1 :=
        EncState.addClause_subset_clauses (b := b) st1
          [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)]
      have hAdd2 := EncState.addClause_subset_clauses (b := b)
        (EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)])
        [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)]
      have hAdd3 := EncState.addClause_subset_clauses (b := b)
        (EncState.addClause b
          (EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)])
          [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)])
        [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b y)]
      exact List.Subset.trans hAllocSub (List.Subset.trans hAdd1 (List.Subset.trans hAdd2 hAdd3))

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkImpIff_clauses_subset (b : Bounds S) (x y : FVar b) (st : EncState b) :
    st.clauses ⊆ (mkImpIff b x y st).2.clauses := by
  classical
  unfold mkImpIff
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      have hAllocSub : st.clauses ⊆ st1.clauses := by
        have eq : st1 = (EncState.allocFresh b st).2 := by simp [hAlloc]
        intro clause h
        rw [eq, EncState.allocFresh_clauses_eq]
        exact h
      have hAdd1 :=
        EncState.addClause_subset_clauses (b := b) st1
          [SAT.Lit.pos (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)]
      have hAdd2 := EncState.addClause_subset_clauses (b := b)
        (EncState.addClause b st1 [SAT.Lit.pos (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)])
        [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)]
      have hAdd3 := EncState.addClause_subset_clauses (b := b)
        (EncState.addClause b
          (EncState.addClause b st1 [SAT.Lit.pos (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)])
          [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)])
        [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b y)]
      exact List.Subset.trans hAllocSub (List.Subset.trans hAdd1 (List.Subset.trans hAdd2 hAdd3))

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkAndIff_adequate_forward (b : Bounds S) (x y : FVar b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses : (mkAndIff b x y st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hU : σ (FVar.toVar b (mkAndIff b x y st).1) = true) :
    σ (FVar.toVar b x) = true ∧ σ (FVar.toVar b y) = true := by
  classical
  unfold mkAndIff at hClauses hU
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      simp only [hAlloc] at hClauses hU
      have hAll := List.all_eq_true.mp hClauses
      let c1 := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x)]
      let c2 := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b y)]
      have hC1 : c1 ∈ (EncState.addClause b
          (EncState.addClause b
            (EncState.addClause b st1 c1)
            c2)
          [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.neg (FVar.toVar b y),
           SAT.Lit.pos (FVar.toVar b u)]).clauses := by
        simp [EncState.addClause]
      have hC2 : c2 ∈ (EncState.addClause b
          (EncState.addClause b
            (EncState.addClause b st1 c1)
            c2)
          [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.neg (FVar.toVar b y),
           SAT.Lit.pos (FVar.toVar b u)]).clauses := by
        simp [EncState.addClause]
      have hEval1 := hAll c1 hC1
      have hEval2 := hAll c2 hC2
      simp [c1, SAT.Clause.eval, SAT.Lit.eval, List.foldl, hU] at hEval1
      simp [c2, SAT.Clause.eval, SAT.Lit.eval, List.foldl, hU] at hEval2
      exact ⟨hEval1, hEval2⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkAndIff_adequate_backward (b : Bounds S) (x y : FVar b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses : (mkAndIff b x y st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hx : σ (FVar.toVar b x) = true)
    (hy : σ (FVar.toVar b y) = true) :
    σ (FVar.toVar b (mkAndIff b x y st).1) = true := by
  classical
  unfold mkAndIff at hClauses
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      simp only [hAlloc] at hClauses
      have hAll := List.all_eq_true.mp hClauses
      let c3 := [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.neg (FVar.toVar b y),
                 SAT.Lit.pos (FVar.toVar b u)]
      have hC3 : c3 ∈ (EncState.addClause b
          (EncState.addClause b
            (EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x)])
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b y)])
          c3).clauses := by
        simp [EncState.addClause]
      have hEval3 := hAll c3 hC3
      unfold mkAndIff
      rw [hAlloc]
      simp only
      simp [c3, SAT.Clause.eval, SAT.Lit.eval, List.foldl, hx, hy] at hEval3
      exact hEval3

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOrIff_adequate_forward (b : Bounds S) (x y : FVar b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses : (mkOrIff b x y st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hU : σ (FVar.toVar b (mkOrIff b x y st).1) = true) :
    σ (FVar.toVar b x) = true ∨ σ (FVar.toVar b y) = true := by
  classical
  unfold mkOrIff at hClauses hU
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      simp only [hAlloc] at hClauses hU
      have hAll := List.all_eq_true.mp hClauses
      let c3 := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x),
                 SAT.Lit.pos (FVar.toVar b y)]
      have hC3 : c3 ∈ (EncState.addClause b
          (EncState.addClause b
            (EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)])
            [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)])
          c3).clauses := by
        simp [EncState.addClause]
      have hEval3 := hAll c3 hC3
      simp [c3, SAT.Clause.eval, SAT.Lit.eval, List.foldl, hU] at hEval3
      exact hEval3

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOrIff_adequate_backward (b : Bounds S) (x y : FVar b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses : (mkOrIff b x y st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hOr : σ (FVar.toVar b x) = true ∨ σ (FVar.toVar b y) = true) :
    σ (FVar.toVar b (mkOrIff b x y st).1) = true := by
  classical
  unfold mkOrIff at hClauses
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      simp only [hAlloc] at hClauses
      have hAll := List.all_eq_true.mp hClauses
      let c1 := [SAT.Lit.neg (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)]
      let c2 := [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)]
      unfold mkOrIff
      rw [hAlloc]
      simp only
      cases hOr with
      | inl hx =>
          have hC1 : c1 ∈ (EncState.addClause b
              (EncState.addClause b
                (EncState.addClause b st1 c1)
                c2)
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x),
               SAT.Lit.pos (FVar.toVar b y)]).clauses := by
            simp [EncState.addClause]
          have hEval1 := hAll c1 hC1
          simp [c1, SAT.Clause.eval, SAT.Lit.eval, List.foldl, hx] at hEval1
          exact hEval1
      | inr hy =>
          have hC2 : c2 ∈ (EncState.addClause b
              (EncState.addClause b
                (EncState.addClause b st1 c1)
                c2)
              [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.pos (FVar.toVar b x),
               SAT.Lit.pos (FVar.toVar b y)]).clauses := by
            simp [EncState.addClause]
          have hEval2 := hAll c2 hC2
          simp [c2, SAT.Clause.eval, SAT.Lit.eval, List.foldl, hy] at hEval2
          exact hEval2

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkImpIff_adequate_forward (b : Bounds S) (x y : FVar b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses : (mkImpIff b x y st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hU : σ (FVar.toVar b (mkImpIff b x y st).1) = true) :
    σ (FVar.toVar b x) = true → σ (FVar.toVar b y) = true := by
  classical
  unfold mkImpIff at hClauses hU
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      simp only [hAlloc] at hClauses hU
      intro hx
      have hAll := List.all_eq_true.mp hClauses
      let c3 := [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b x),
                 SAT.Lit.pos (FVar.toVar b y)]
      have hC3 : c3 ∈ (EncState.addClause b
          (EncState.addClause b
            (EncState.addClause b st1 [SAT.Lit.pos (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)])
            [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)])
          c3).clauses := by
        simp [EncState.addClause]
      have hEval3 := hAll c3 hC3
      simp [c3, SAT.Clause.eval, SAT.Lit.eval, List.foldl, hU, hx] at hEval3
      exact hEval3

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkImpIff_adequate_backward (b : Bounds S) (x y : FVar b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses : (mkImpIff b x y st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hImp : σ (FVar.toVar b x) = true → σ (FVar.toVar b y) = true) :
    σ (FVar.toVar b (mkImpIff b x y st).1) = true := by
  classical
  unfold mkImpIff at hClauses
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      simp only [hAlloc] at hClauses
      have hAll := List.all_eq_true.mp hClauses
      let c1 := [SAT.Lit.pos (FVar.toVar b x), SAT.Lit.pos (FVar.toVar b u)]
      let c2 := [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (FVar.toVar b u)]
      unfold mkImpIff
      rw [hAlloc]
      simp only
      by_cases hx : σ (FVar.toVar b x)
      · have hy := hImp hx
        have hC2 : c2 ∈ (EncState.addClause b
            (EncState.addClause b
              (EncState.addClause b st1 c1)
              c2)
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b x),
             SAT.Lit.pos (FVar.toVar b y)]).clauses := by
          simp [EncState.addClause]
        have hEval2 := hAll c2 hC2
        simp [c2, SAT.Clause.eval, SAT.Lit.eval, List.foldl, hy] at hEval2
        exact hEval2
      · have hC1 : c1 ∈ (EncState.addClause b
            (EncState.addClause b
              (EncState.addClause b st1 c1)
              c2)
            [SAT.Lit.neg (FVar.toVar b u), SAT.Lit.neg (FVar.toVar b x),
             SAT.Lit.pos (FVar.toVar b y)]).clauses := by
          simp [EncState.addClause]
        have hEval1 := hAll c1 hC1
        simp [c1, SAT.Clause.eval, SAT.Lit.eval, List.foldl, hx] at hEval1
        exact hEval1

/-- All predicate indices whose table entry equals the predicate atom. -/
def predIxList (b : Bounds S) (pred : Signature.AtomicPredType S) :
    List b.predIx :=
  (List.finRange b.nPreds).filter (fun k => decide (b.preds.get k = pred))

/-- Tseytin gadget enforcing equality of Mem bits for two prehistories at a world. -/
def mkMemEq (b : Bounds S) (H H' : b.times) (w : WId b)
    (st : EncState b) : FVar b × EncState b :=
  let (eqb, st1) := EncState.allocFresh b st
  let memH  := Var.Mem H w
  let memH' := Var.Mem H' w
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg memH, SAT.Lit.pos memH']
  let st2 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos memH, SAT.Lit.neg memH']
  let st3 := EncState.addClause b st2
    [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.pos memH, SAT.Lit.pos memH']
  let st4 := EncState.addClause b st3
    [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.neg memH, SAT.Lit.neg memH']
  (eqb, st4)

/-- Tseytin gadget enforcing `next ↔ (cur ∧ eqBit)` using three clauses. -/
def addAccStep (b : Bounds S)
    (cur next eqb : FVar b) (st : EncState b) : EncState b :=
  let st1 := EncState.addClause b st
    [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)]
  let st2 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)]
  EncState.addClause b st2
    [ SAT.Lit.neg (FVar.toVar b cur)
    , SAT.Lit.neg (FVar.toVar b eqb)
    , SAT.Lit.pos (FVar.toVar b next) ]

/-- Emit clauses witnessing structural equality of prehistories `H0` and `H'`. -/
def addPreEqExpose (b : Bounds S) (H0 H' : b.times)
    (v : FVar b) (st : EncState b) : EncState b :=
  let st1 :=
    EncState.addClause b st
      [SAT.Lit.neg (Var.PreEq H0 H'), SAT.Lit.pos (FVar.toVar b v)]
  EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b v), SAT.Lit.pos (Var.PreEq H0 H')]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma addPreEqExpose_clauses_subset (b : Bounds S)
    (H0 H' : b.times) (v : FVar b) (st : EncState b) :
    st.clauses ⊆ (addPreEqExpose b H0 H' v st).clauses := by
  classical
  intro clause hClause
  unfold addPreEqExpose
  have h₁ :
      clause ∈
        (EncState.addClause b st
          [SAT.Lit.neg (Var.PreEq H0 H'), SAT.Lit.pos (FVar.toVar b v)]).clauses :=
    (EncState.addClause_subset_clauses
      (b := b)
      (st := st)
      (clause :=
        [SAT.Lit.neg (Var.PreEq H0 H'), SAT.Lit.pos (FVar.toVar b v)])) hClause
  have h₂ :
      clause ∈
        (EncState.addClause b
          (EncState.addClause b st
            [SAT.Lit.neg (Var.PreEq H0 H'), SAT.Lit.pos (FVar.toVar b v)])
          [SAT.Lit.neg (FVar.toVar b v), SAT.Lit.pos (Var.PreEq H0 H')]).clauses :=
    (EncState.addClause_subset_clauses
      (b := b)
      (st := EncState.addClause b st
        [SAT.Lit.neg (Var.PreEq H0 H'), SAT.Lit.pos (FVar.toVar b v)])
      (clause :=
        [SAT.Lit.neg (FVar.toVar b v), SAT.Lit.pos (Var.PreEq H0 H')])) h₁
  simpa using h₂

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- addPreEqExpose preserves nextFresh (only uses addClause). -/
lemma addPreEqExpose_nextFresh (b : Bounds S) (H0 H' : b.times) (v : FVar b) (st : EncState b) :
    (addPreEqExpose b H0 H' v st).nextFresh = st.nextFresh := by
  simp [addPreEqExpose, EncState.addClause]

/-- Add global reflexivity units for all time indices. -/
def addPreEqReflAll (b : Bounds S) (st : EncState b) : EncState b :=
  (Bounds.timesL b).foldl (fun acc t =>
    EncState.addClause b acc [SAT.Lit.pos (Var.PreEq t t)]) st

omit [DecidableEq S.Value] [DecidableEq S.EventType] in
/-- Membership in `predIxList` characterises matching table entries. -/
lemma predIxList_mem_iff (b : Bounds S) (pred : Signature.AtomicPredType S)
    (k : b.predIx) :
    k ∈ predIxList b pred ↔ b.preds.get k = pred := by
  classical
  unfold predIxList
  constructor
  · intro hk
    have hk' := List.mem_filter.mp hk
    simpa [decide_eq_true_eq] using hk'.2
  · intro hk
    refine List.mem_filter.mpr ?_
    exact ⟨by simp, by simp [hk]⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma foldl_subset_state {b : Bounds S} {α}
    (f : EncState b → α → EncState b)
    (hStep : ∀ st a, st.clauses ⊆ (f st a).clauses) :
    ∀ xs init, init.clauses ⊆ (List.foldl f init xs).clauses := by
  intro xs
  induction xs with
  | nil =>
      intro init
      simp
  | cons x xs ih =>
      intro init
      have h₁ := hStep init x
      have h₂ := ih (f init x)
      exact List.Subset.trans h₁ h₂

lemma exists_split_of_mem {α} {a : α} :
    ∀ {l : List α}, a ∈ l → ∃ as bs, l = as ++ a :: bs
  | [], h => by cases h
  | x :: xs, h => by
      have hx : a = x ∨ a ∈ xs := by
        simpa [List.mem_cons] using h
      cases hx with
      | inl hEq =>
          refine ⟨[], xs, ?_⟩
          simp [hEq]
      | inr hTail =>
          rcases exists_split_of_mem (l := xs) hTail with ⟨as, bs, hSplit⟩
          refine ⟨x :: as, bs, ?_⟩
          simp [hSplit]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- For any item in the list, there exists an intermediate state during the fold
    such that the result of applying `f` to that state and item is a subset of the final result.
    This avoids requiring monotonicity across different states (e.g. with fresh variables). -/
lemma foldl_exists_state_subset {b : Bounds S} {α}
    (f : EncState b → α → EncState b)
    (hStep : ∀ st a, st.clauses ⊆ (f st a).clauses)
    (xs : List α) (x : α) (init : EncState b)
    (hMem : x ∈ xs) :
    ∃ st_k, (f st_k x).clauses ⊆ (List.foldl f init xs).clauses := by
  have hEx := exists_split_of_mem hMem
  rcases hEx with ⟨as, bs, hSplit⟩
  rw [hSplit, List.foldl_append, List.foldl_cons]
  let st_k := as.foldl f init
  exists st_k
  let st_next := f st_k x
  have h := foldl_subset_state f hStep bs st_next
  exact h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma foldl_subset_snd {b : Bounds S} {α β}
    (f : β × EncState b → α → β × EncState b)
    (hStep : ∀ st a, st.2.clauses ⊆ (f st a).2.clauses)
    (xs : List α) (init : β × EncState b) :
    init.2.clauses ⊆ (xs.foldl f init).2.clauses := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp
      have h1 := hStep init x
      have h2 := ih (f init x)
      exact List.Subset.trans h1 h2

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: foldl with pair accumulator is monotonic in nextFresh if each step is monotonic. -/
lemma foldl_nextFresh_mono_pair {b : Bounds S} {α β}
    (xs : List α) (init : β × EncState b)
    (f : β × EncState b → α → β × EncState b)
    (hMono : ∀ acc x, acc.2.nextFresh ≤ (f acc x).2.nextFresh) :
    init.2.nextFresh ≤ (xs.foldl f init).2.nextFresh := by
  induction xs generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (hMono init hd) (ih (f init hd))

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: foldl preserves well-formedness if each step preserves it. -/
lemma foldl_wf_state {b : Bounds S} {α}
    (xs : List α) (init : EncState b)
    (f : EncState b → α → EncState b)
    (hWFInit : init.WellFormed)
    (hStep : ∀ st x, st.WellFormed → (f st x).WellFormed) :
    (xs.foldl f init).WellFormed := by
  induction xs generalizing init with
  | nil => exact hWFInit
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (f init hd) (hStep init hd hWFInit)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Combined helper: foldl with addClause-like steps preserves both WF and nextFresh.
    Uses strong induction that tracks nextFresh preservation throughout. -/
lemma foldl_addClause_wf {b : Bounds S} {α}
    (xs : List α) (init : EncState b)
    (mkClause : α → SAT.Clause (Var b))
    (hWFInit : init.WellFormed)
    (hClause : ∀ x, clauseFreshBelow (mkClause x) init.nextFresh) :
    (xs.foldl (fun st x => EncState.addClause b st (mkClause x)) init).WellFormed ∧
    (xs.foldl (fun st x => EncState.addClause b st (mkClause x)) init).nextFresh =
      init.nextFresh := by
  induction xs generalizing init with
  | nil => exact ⟨hWFInit, rfl⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hNext : (EncState.addClause b init (mkClause hd)).nextFresh = init.nextFresh :=
      EncState.addClause_nextFresh b init _
    have hWFStep : (EncState.addClause b init (mkClause hd)).WellFormed :=
      EncState.addClause_wf hWFInit (mkClause hd) (hClause hd)
    have hClause' : ∀ x, clauseFreshBelow (mkClause x)
        (EncState.addClause b init (mkClause hd)).nextFresh := by
      intro x; rw [hNext]; exact hClause x
    have ⟨hWF', hNext'⟩ := ih (EncState.addClause b init (mkClause hd)) hWFStep hClause'
    exact ⟨hWF', by rw [hNext', hNext]⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Version of foldl_addClause_wf for pair lists where the step function destructures pairs. -/
lemma foldl_addClause_wf_pair {b : Bounds S} {α β}
    (xs : List (α × β)) (init : EncState b)
    (mkClause : α → β → SAT.Clause (Var b))
    (hWFInit : init.WellFormed)
    (hClause : ∀ a b, clauseFreshBelow (mkClause a b) init.nextFresh) :
    (xs.foldl (fun st p => EncState.addClause b st (mkClause p.1 p.2)) init).WellFormed ∧
    (xs.foldl (fun st p => EncState.addClause b st (mkClause p.1 p.2)) init).nextFresh =
      init.nextFresh := by
  have := foldl_addClause_wf xs init (fun p => mkClause p.1 p.2) hWFInit
    (fun ⟨a, b⟩ => hClause a b)
  convert this using 2

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Version of foldl_addClause_wf where clause validity depends on membership. -/
lemma foldl_addClause_wf_mem {b : Bounds S} {α}
    (xs : List α) (init : EncState b)
    (mkClause : α → SAT.Clause (Var b))
    (hWFInit : init.WellFormed)
    (hClause : ∀ x ∈ xs, clauseFreshBelow (mkClause x) init.nextFresh) :
    (xs.foldl (fun st x => EncState.addClause b st (mkClause x)) init).WellFormed ∧
    (xs.foldl (fun st x => EncState.addClause b st (mkClause x)) init).nextFresh =
      init.nextFresh := by
  induction xs generalizing init with
  | nil => exact ⟨hWFInit, rfl⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hNext : (EncState.addClause b init (mkClause hd)).nextFresh = init.nextFresh :=
      EncState.addClause_nextFresh b init _
    have hHdMem : hd ∈ hd :: tl := by simp
    have hWFStep : (EncState.addClause b init (mkClause hd)).WellFormed :=
      EncState.addClause_wf hWFInit (mkClause hd) (hClause hd hHdMem)
    have hClause' : ∀ x ∈ tl, clauseFreshBelow (mkClause x)
        (EncState.addClause b init (mkClause hd)).nextFresh := by
      intro x hx; rw [hNext]; exact hClause x (by simp [hx])
    have ⟨hWF', hNext'⟩ := ih (EncState.addClause b init (mkClause hd)) hWFStep hClause'
    exact ⟨hWF', by rw [hNext', hNext]⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma foldl_exists_state_subset_snd {b : Bounds S} {α β}
    (f : β × EncState b → α → β × EncState b)
    (hStep : ∀ st a, st.2.clauses ⊆ (f st a).2.clauses)
    (xs : List α) (x : α) (init : β × EncState b)
    (hMem : x ∈ xs) :
    ∃ st_k, (f st_k x).2.clauses ⊆ (List.foldl f init xs).2.clauses := by
  have hEx := exists_split_of_mem hMem
  rcases hEx with ⟨as, bs, hSplit⟩
  rw [hSplit, List.foldl_append, List.foldl_cons]
  let st_k := as.foldl f init
  exists st_k
  let st_next := f st_k x
  have h := foldl_subset_snd f hStep bs st_next
  exact h

lemma foldl_subset_fst {α β γ}
    (f : List γ × β → α → List γ × β)
    (hStep : ∀ st a, st.1 ⊆ (f st a).1) :
    ∀ xs init, init.1 ⊆ (List.foldl f init xs).1 := by
  intro xs init
  induction xs generalizing init with
  | nil =>
      simp
  | cons x xs ih =>
      simp
      have h₁ := hStep init x
      have h₂ := ih (f init x)
      exact List.Subset.trans h₁ h₂

lemma foldl_exists_state_subset_fst {α β γ}
    (f : List γ × β → α → List γ × β)
    (hStep : ∀ st a, st.1 ⊆ (f st a).1)
    (xs : List α) (x : α) (init : List γ × β)
    (hMem : x ∈ xs) :
    ∃ st_k, (f st_k x).1 ⊆ (List.foldl f init xs).1 := by
  have hEx := exists_split_of_mem hMem
  rcases hEx with ⟨as, bs, hSplit⟩
  rw [hSplit, List.foldl_append, List.foldl_cons]
  let st_k := as.foldl f init
  exists st_k
  let st_next := f st_k x
  have h := foldl_subset_fst f hStep bs st_next
  exact h

lemma foldl_cons_subset_fst {α β γ}
    (f : List γ × β → α → List γ × β)
    (hCons : ∀ st a, ∃ h, (f st a).1 = h :: st.1)
    (xs : List α) (init : List γ × β) :
    init.1 ⊆ (List.foldl f init xs).1 := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp
      rcases hCons init x with ⟨h, hEq⟩
      have hSub : init.1 ⊆ (f init x).1 := by rw [hEq]; simp
      exact List.Subset.trans hSub (ih (f init x))

/-- If a fold function always conses a new element to the list in the first component,
    then the head of the list produced at any step is present in the final list. -/
lemma foldl_cons_mem {α β γ}
    (f : List γ × β → α → List γ × β)
    (hCons : ∀ st a, ∃ h, (f st a).1 = h :: st.1)
    (xs : List α) (x : α) (init : List γ × β)
    (hMem : x ∈ xs) :
    ∃ st_k, (f st_k x).1.head? = some ((f st_k x).1.head (by
        rcases hCons st_k x with ⟨h, eq⟩; rw [eq]; simp)) ∧
      ((f st_k x).1.head (by rcases hCons st_k x with ⟨h, eq⟩; rw [eq]; simp))
        ∈ (List.foldl f init xs).1 := by
  have hEx := exists_split_of_mem hMem
  rcases hEx with ⟨as, bs, hSplit⟩
  rw [hSplit, List.foldl_append, List.foldl_cons]
  let st_k := as.foldl f init
  exists st_k
  rcases hCons st_k x with ⟨h, hEq⟩
  have h_head_opt : (f st_k x).1.head? = some h := by rw [hEq]; simp
  have h_eq_head : h = (f st_k x).1.head (by rw [hEq]; simp) := by
    rw [← Option.some_inj]
    rw [← h_head_opt]
    apply List.head?_eq_head
  rw [← h_eq_head]
  refine ⟨h_head_opt, ?_⟩
  have hIn : h ∈ (f st_k x).1 := by rw [hEq]; simp
  have hSub : (f st_k x).1 ⊆ (List.foldl f (f st_k x) bs).1 :=
    foldl_cons_subset_fst f hCons bs (f st_k x)
  exact hSub hIn

/-! ### Prefix-appending fold helpers -/

/-- For a step function of the form `(pfx, st) ↦ (pfx ++ [g st a], h st a)`,
the first component equals the initial prefix plus the result from starting with empty prefix. -/
lemma foldl_fst_prefix_append' {α β γ}
    (g : β → α → γ) (h : β → α → β)
    (xs : List α) (pfx : List γ) (st : β) :
    (xs.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a)) (pfx, st)).1 =
    pfx ++ (xs.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a)) ([], st)).1 := by
  induction xs generalizing pfx st with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.nil_append]
      rw [ih (pfx ++ [g st x]) (h st x), ih [g st x] (h st x)]
      simp only [List.append_assoc, List.singleton_append]

/-- For a step function where the second component only depends on the second component of
the input, starting with different prefixes gives the same second component. -/
lemma foldl_snd_prefix_indep' {α β γ}
    (g : β → α → γ) (h : β → α → β)
    (xs : List α) (pfx1 pfx2 : List γ) (st : β) :
    (xs.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a)) (pfx1, st)).2 =
    (xs.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a)) (pfx2, st)).2 := by
  induction xs generalizing pfx1 pfx2 st with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih _ _ _

/-- If an element is in the initial prefix and the step function appends to the first component,
    the element remains in the final list after folding. -/
lemma foldl_prefix_mem_fst' {α β γ}
    (g : β → α → γ) (h : β → α → β)
    (xs : List α) (pfx : List γ) (st : β) (x : γ) (hIn : x ∈ pfx) :
    x ∈ (xs.foldl (fun acc a => (acc.1 ++ [g acc.2 a], h acc.2 a)) (pfx, st)).1 := by
  induction xs generalizing pfx st with
  | nil => simp; exact hIn
  | cons a as ih =>
      simp only [List.foldl_cons]
      have hIn' : x ∈ pfx ++ [g st a] := List.mem_append_left _ hIn
      exact ih _ _ hIn'

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Variant of foldl_subset_snd that returns a direct subset. -/
lemma foldl_subset_snd' {b : Bounds S} {α β}
    (f : β × EncState b → α → β × EncState b)
    (hStep : ∀ st a, st.2.clauses ⊆ (f st a).2.clauses)
    (xs : List α) (init : β × EncState b) :
    init.2.clauses ⊆ (xs.foldl f init).2.clauses :=
  foldl_subset_snd f hStep xs init

/-! ### Clause monotonicity helper -/

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If `xs ⊆ ys` and every element of `ys` satisfies `P`, then every element of `xs` does. -/
lemma all_true_of_subset {α} {P : α → Bool} {xs ys : List α}
    (hSub : xs ⊆ ys) (hAll : ys.all P = true) :
    xs.all P = true := by
  classical
  refine List.all_eq_true.mpr ?_
  intro x hx
  have hx' : x ∈ ys := hSub hx
  exact (List.all_eq_true.mp hAll) _ hx'

/-! ### mkAndIff folding helpers -/

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Forward direction for a left-associated `mkAndIff` fold: if the result
    variable is true, then all inputs are true. -/
lemma mkAndIff_fold_forward
    (b : Bounds S) (vars : List (FVar b)) (u0 : FVar b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses :
      (vars.foldl (fun (acc : FVar b × EncState b) u' =>
          let (uAcc, stAcc) := acc
          mkAndIff b uAcc u' stAcc) (u0, st)).2.clauses.all
        (SAT.Clause.eval σ) = true)
    (hU :
      σ (FVar.toVar b
          (vars.foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (u0, st)).1) = true) :
    σ (FVar.toVar b u0) = true ∧ ∀ u' ∈ vars, σ (FVar.toVar b u') = true := by
  classical
  induction vars generalizing u0 st with
  | nil =>
      simpa [List.foldl] using hU
  | cons u us ih =>
      let res1 := mkAndIff b u0 u st
      let res :=
        us.foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (res1.1, res1.2)

      have hSubset_res1 :
          res1.2.clauses ⊆ res.2.clauses :=
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
          (xs := us)
          (init := (res1.1, res1.2))

      have hClauses_res : res.2.clauses.all (SAT.Clause.eval σ) = true := by
        simpa [res] using hClauses

      have hClauses_res1 : res1.2.clauses.all (SAT.Clause.eval σ) = true :=
        all_true_of_subset hSubset_res1 hClauses_res

      have hResTrue :
          σ (FVar.toVar b res1.1) = true ∧
            ∀ u' ∈ us, σ (FVar.toVar b u') = true :=
        ih (u0 := res1.1) (st := res1.2)
          (by simpa [res] using hClauses)
          (by
            have hRes_eq :
                ((u :: us).foldl (fun (acc : FVar b × EncState b) u' =>
                  let (uAcc, stAcc) := acc
                  mkAndIff b uAcc u' stAcc) (u0, st)).1 = res.1 := by
              rfl
            simpa [res, hRes_eq] using hU)

      have hAnd := mkAndIff_adequate_forward b u0 u st σ hClauses_res1 hResTrue.1
      refine ⟨hAnd.1, ?_⟩
      intro u' hMem
      cases hMem with
      | head =>
          simpa using hAnd.2
      | tail _ hMemTail =>
          exact hResTrue.2 u' hMemTail

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Backward direction for a left-associated `mkAndIff` fold: if all inputs are
    true, then the result variable is true. -/
lemma mkAndIff_fold_backward
    (b : Bounds S) (vars : List (FVar b)) (u0 : FVar b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses :
      (vars.foldl (fun (acc : FVar b × EncState b) u' =>
          let (uAcc, stAcc) := acc
          mkAndIff b uAcc u' stAcc) (u0, st)).2.clauses.all
        (SAT.Clause.eval σ) = true)
    (hInputs : σ (FVar.toVar b u0) = true ∧ ∀ u' ∈ vars, σ (FVar.toVar b u') = true) :
    σ (FVar.toVar b
        (vars.foldl (fun (acc : FVar b × EncState b) u' =>
          let (uAcc, stAcc) := acc
          mkAndIff b uAcc u' stAcc) (u0, st)).1) = true := by
  classical
  induction vars generalizing u0 st with
  | nil =>
      simpa [List.foldl] using hInputs.1
  | cons u us ih =>
      let res1 := mkAndIff b u0 u st
      let res :=
        us.foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (res1.1, res1.2)

      have hSubset_res1 :
          res1.2.clauses ⊆ res.2.clauses :=
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
          (xs := us)
          (init := (res1.1, res1.2))

      have hClauses_res : res.2.clauses.all (SAT.Clause.eval σ) = true := by
        simpa [res] using hClauses

      have hClauses_res1 : res1.2.clauses.all (SAT.Clause.eval σ) = true :=
        all_true_of_subset hSubset_res1 hClauses_res

      have hRes1 :
          σ (FVar.toVar b res1.1) = true :=
        mkAndIff_adequate_backward b u0 u st σ hClauses_res1
          hInputs.1 (hInputs.2 u (by simp))

      have hInputs_tail : σ (FVar.toVar b res1.1) = true ∧
          ∀ u' ∈ us, σ (FVar.toVar b u') = true := by
        refine ⟨hRes1, ?_⟩
        intro u' hMem
        exact hInputs.2 u' (List.mem_cons_of_mem _ hMem)

      have hTail := ih (u0 := res1.1) (st := res1.2) hClauses_res hInputs_tail
      have hRes_eq :
          ((u :: us).foldl (fun (acc : FVar b × EncState b) u' =>
            let (uAcc, stAcc) := acc
            mkAndIff b uAcc u' stAcc) (u0, st)).1 = res.1 := by
        rfl
      simpa [res, hRes_eq] using hTail

/-! ### List/product helpers -/

lemma cartesianProduct_mem_length {α : Type _} {xs : List (List α)} {ys : List α}
    (hMem : ys ∈ cartesianProduct xs) : ys.length = xs.length := by
  classical
  induction xs generalizing ys with
  | nil =>
      simp [cartesianProduct] at hMem
      subst hMem
      simp
  | cons x xs ih =>
      simp [cartesianProduct] at hMem
      rcases hMem with ⟨a, ha, ys', hys', rfl⟩
      have hLen := ih hys'
      simp [hLen]

lemma cartesianProduct_ne_nil {α : Type _} {xs : List (List α)}
    (hNonempty : ∀ ys ∈ xs, ys ≠ []) : cartesianProduct xs ≠ [] := by
  classical
  induction xs with
  | nil =>
      simp [cartesianProduct]
  | cons ys yss ih =>
      have hYs : ys ≠ [] := hNonempty ys (by simp)
      have hTail : cartesianProduct yss ≠ [] := ih (by
        intro ys' hMem
        exact hNonempty ys' (by simp [hMem]))
      match ys with
      | [] => exact absurd rfl hYs
      | head :: tail =>
          intro hEmpty
          simp only [cartesianProduct] at hEmpty
          have hFlat : ∀ x ∈ (head :: tail),
              (cartesianProduct yss).map (x :: ·) = [] :=
            List.flatMap_eq_nil_iff.mp hEmpty
          have hMapNil := hFlat head (by simp)
          have hRestEmpty : cartesianProduct yss = [] := List.map_eq_nil_iff.mp hMapNil
          exact hTail hRestEmpty

lemma foldl_length_succ {β γ δ : Type _}
    (f : (List β × δ) → γ → (List β × δ))
    (xs : List γ) (init : List β × δ)
    (hStep : ∀ acc x, (f acc x).1.length = acc.1.length + 1) :
    (xs.foldl f init).1.length = init.1.length + xs.length := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons x xs ih =>
      have hLen := hStep init x
      simpa [List.foldl, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hLen] using
        ih (f init x)

lemma mem_get {α : Type _} {x : α} {xs : List α} (h : x ∈ xs) :
    ∃ i : Fin xs.length, xs.get i = x := by
  classical
  rcases List.mem_iff_getElem?.mp h with ⟨i, hi⟩
  simp only [List.getElem?_eq_some_iff] at hi
  rcases hi with ⟨hLt, hEq⟩
  exact ⟨⟨i, hLt⟩, hEq⟩

/-- Helper: mapping a composed function over zip is the same as mapping over
    the zipped mapped list. -/
lemma map_zip_left_map {α β γ δ : Type _} (f : α → β) (g : β → γ → δ)
    (xs : List α) (ys : List γ) :
    (xs.zip ys).map (fun (a, c) => g (f a) c) =
    ((xs.map f).zip ys).map (fun (b, c) => g b c) := by
  induction xs generalizing ys with
  | nil => simp [List.zip_nil_left]
  | cons x xs ih =>
      cases ys with
      | nil => simp [List.zip_nil_right]
      | cons y ys =>
          simp only [List.map_cons, List.zip_cons_cons, List.map]
          exact congrArg _ (ih ys)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkMemEq_clauses_subset (b : Bounds S)
    (H H' : b.times) (w : WId b) (st : EncState b) :
    st.clauses ⊆ (mkMemEq b H H' w st).2.clauses := by
  classical
  unfold mkMemEq
  cases hAlloc : EncState.allocFresh b st with
  | mk eqb st1 =>
      intro clause hClause
      have hAllocSub :
          clause ∈ st1.clauses := by
        have : st1 = (EncState.allocFresh b st).2 := by simp [hAlloc]
        simp [this, EncState.allocFresh_clauses_eq, hClause]
      have hStep1 :
          clause ∈
            (EncState.addClause b st1
              [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
                SAT.Lit.pos (Var.Mem H' w)]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b) (st := st1)
          (clause :=
            [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
             SAT.Lit.pos (Var.Mem H' w)])) hAllocSub
      have hStep2 :
          clause ∈
            (EncState.addClause b
              (EncState.addClause b st1
                [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
                  SAT.Lit.pos (Var.Mem H' w)])
              [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
                SAT.Lit.neg (Var.Mem H' w)]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b)
          (st := EncState.addClause b st1
            [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
              SAT.Lit.pos (Var.Mem H' w)])
          (clause :=
            [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
             SAT.Lit.neg (Var.Mem H' w)])) hStep1
      have hStep3 :
          clause ∈
            (EncState.addClause b
              (EncState.addClause b
                (EncState.addClause b st1
                  [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
                    SAT.Lit.pos (Var.Mem H' w)])
                [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
                  SAT.Lit.neg (Var.Mem H' w)])
              [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
                SAT.Lit.pos (Var.Mem H' w)]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b)
          (st := EncState.addClause b
            (EncState.addClause b st1
              [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
                SAT.Lit.pos (Var.Mem H' w)])
            [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
              SAT.Lit.neg (Var.Mem H' w)])
          (clause :=
            [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
             SAT.Lit.pos (Var.Mem H' w)])) hStep2
      have hStep4 :
          clause ∈
            (EncState.addClause b
              (EncState.addClause b
                (EncState.addClause b
                  (EncState.addClause b st1
                    [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
                      SAT.Lit.pos (Var.Mem H' w)])
                  [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
                    SAT.Lit.neg (Var.Mem H' w)])
                [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
                  SAT.Lit.pos (Var.Mem H' w)])
              [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
                SAT.Lit.neg (Var.Mem H' w)]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b)
          (st := EncState.addClause b
            (EncState.addClause b
              (EncState.addClause b st1
                [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
                  SAT.Lit.pos (Var.Mem H' w)])
              [SAT.Lit.neg (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
                SAT.Lit.neg (Var.Mem H' w)])
            [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.pos (Var.Mem H w),
              SAT.Lit.pos (Var.Mem H' w)])
          (clause :=
            [SAT.Lit.pos (FVar.toVar b eqb), SAT.Lit.neg (Var.Mem H w),
             SAT.Lit.neg (Var.Mem H' w)])) hStep3
      simpa using hStep4

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma addAccStep_clauses_subset (b : Bounds S)
    (cur next eqb : FVar b) (st : EncState b) :
    st.clauses ⊆ (addAccStep b cur next eqb st).clauses := by
  classical
  unfold addAccStep
  intro clause hClause
  have h1 :
      clause ∈ (EncState.addClause b st
        [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)]).clauses :=
    (EncState.addClause_subset_clauses
      (b := b)
      (st := st)
      (clause :=
        [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)])) hClause
  have h2 :
      clause ∈ (EncState.addClause b
        (EncState.addClause b st
          [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)])
        [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)]).clauses :=
    (EncState.addClause_subset_clauses
      (b := b)
      (st := EncState.addClause b st
        [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)])
      (clause :=
        [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)])) h1
  have h3 :
      clause ∈ (EncState.addClause b
        (EncState.addClause b
          (EncState.addClause b st
            [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)])
          [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)])
        [ SAT.Lit.neg (FVar.toVar b cur)
        , SAT.Lit.neg (FVar.toVar b eqb)
        , SAT.Lit.pos (FVar.toVar b next) ]).clauses :=
    (EncState.addClause_subset_clauses
      (b := b)
      (st := EncState.addClause b
        (EncState.addClause b st
          [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b cur)])
        [SAT.Lit.neg (FVar.toVar b next), SAT.Lit.pos (FVar.toVar b eqb)])
      (clause :=
        [ SAT.Lit.neg (FVar.toVar b cur)
        , SAT.Lit.neg (FVar.toVar b eqb)
        , SAT.Lit.pos (FVar.toVar b next) ])) h2
  simpa using h3

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma addPreEqReflAll_mem (b : Bounds S) (t : b.times) (st : EncState b) :
    [SAT.Lit.pos (Var.PreEq t t)] ∈ (addPreEqReflAll b st).clauses := by
  classical
  unfold addPreEqReflAll
  have ht : t ∈ Bounds.timesL b := by simp [Bounds.timesL]
  obtain ⟨before, after, hSplit⟩ := List.mem_iff_append.mp ht
  rw [hSplit, List.foldl_append, List.foldl_cons]
  have hUnit : [SAT.Lit.pos (Var.PreEq t t)] ∈
      (EncState.addClause b
        (before.foldl (fun acc t' => EncState.addClause b acc [SAT.Lit.pos (Var.PreEq t' t')])
           st) [SAT.Lit.pos (Var.PreEq t t)]).clauses := by
    simp [EncState.addClause]
  have hStep : ∀ stAcc (t' : b.times),
      stAcc.clauses ⊆
        (EncState.addClause b stAcc [SAT.Lit.pos (Var.PreEq t' t')]).clauses := by
    intro stAcc t'
    exact EncState.addClause_subset_clauses (b := b) stAcc _
  have hSubset := foldl_subset_state
    (b := b)
    (f := fun acc t' => EncState.addClause b acc [SAT.Lit.pos (Var.PreEq t' t')])
    (hStep := hStep)
    (xs := after)
    (init := EncState.addClause b
      (before.foldl (fun acc t' => EncState.addClause b acc [SAT.Lit.pos (Var.PreEq t' t')])
         st) [SAT.Lit.pos (Var.PreEq t t)])
  exact hSubset hUnit

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma addPreEqReflAll_clauses_subset (b : Bounds S) (st : EncState b) :
    st.clauses ⊆ (addPreEqReflAll b st).clauses := by
  classical
  unfold addPreEqReflAll
  exact
    foldl_subset_state
      (b := b)
      (f := fun stCur t => EncState.addClause b stCur [SAT.Lit.pos (Var.PreEq t t)])
      (hStep := fun stCur t => EncState.addClause_subset_clauses (b := b) stCur _)
      (xs := Bounds.timesL b)
      (init := st)

/-- Tseytin gadget for `u ↔ (∨_{v ∈ vs} v)`. -/
def mkBigOrIff (b : Bounds S) (vs : List (Var b)) (st : EncState b) :
    FVar b × EncState b :=
  let (u, st1) := EncState.allocFresh b st
  let st2 := vs.foldl (fun stCur v =>
    EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]
  ) st1
  let st3 := EncState.addClause b st2
    (SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos)
  (u, st3)

/-- Helper lemma: getting elements from a list where all elements are true. -/
lemma List.get_of_all_true {α : Type*} {f : α → Bool}
    {l : List α} (h : l.all f = true) (i : Nat) (hi : i < l.length) :
    f (l.get ⟨i, hi⟩) = true := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    rw [List.all_cons] at h
    rw [Bool.and_eq_true] at h
    have ⟨hHead, hTail⟩ := h
    cases i with
    | zero =>
      simp only [List.get]
      exact hHead
    | succ i' =>
      simp only [List.get]
      have hi' : i' < tl.length := Nat.lt_of_succ_lt_succ hi
      exact ih hTail i' hi'

/-! ### Small SAT and list helpers -/

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If a clause `[¬v, u]` is satisfied and `σ v = true`, then `σ u = true`. -/
lemma witness_clause_eval_implies {α : Type _} (σ : SAT.Assignment α) {v u : α}
    (hEval : SAT.Clause.eval σ [SAT.Lit.neg v, SAT.Lit.pos u] = true)
    (hv : σ v = true) : σ u = true := by
  unfold SAT.Clause.eval at hEval
  simp [SAT.Lit.eval, hv] at hEval
  exact hEval

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If a guard clause `[v, u]` is satisfied and `σ v = false`, then `σ u = true`. -/
lemma guard_clause_eval_implies {α : Type _} (σ : SAT.Assignment α) {v u : α}
    (hEval : SAT.Clause.eval σ [SAT.Lit.pos v, SAT.Lit.pos u] = true)
    (hv : σ v = false) : σ u = true := by
  unfold SAT.Clause.eval at hEval
  simp [SAT.Lit.eval, hv] at hEval
  exact hEval

/-- Dropping to an index exposes the `get` element at the head. -/
lemma drop_eq_get_cons_drop {α : Type _} (l : List α) (i : Nat) (h : i < l.length) :
    l.drop i = l.get ⟨i, h⟩ :: l.drop i.succ := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => cases h
      | cons _ _ => simp
  | succ i ih =>
      cases l with
      | nil => cases h
      | cons head xs =>
          have hTail : i < xs.length := Nat.succ_lt_succ_iff.mp h
          have h' := ih (l := xs) hTail
          calc
            ((head :: xs).drop i.succ) = xs.drop i := by simp
            _ = xs.get ⟨i, hTail⟩ :: xs.drop i.succ := h'
            _ = ((head :: xs).get ⟨Nat.succ i, h⟩) :: xs.drop i.succ := by
              simp [List.get]
            _ = ((head :: xs).get ⟨Nat.succ i, h⟩)
                :: (head :: xs).drop (Nat.succ (Nat.succ i)) := by
              simp

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: foldl with addClause preserves old clauses. -/
lemma foldl_addClause_subset {α : Type} (b : Bounds S) (f : EncState b → α → EncState b)
    (xs : List α) (st : EncState b)
    (hPres : ∀ (st' : EncState b) (x : α), st'.clauses ⊆ (f st' x).clauses) :
    st.clauses ⊆ (xs.foldl f st).clauses := by
  induction xs generalizing st with
  | nil => exact List.Subset.refl _
  | cons x xs ih =>
      have h1 := hPres st x
      have h2 := ih (f st x)
      exact List.Subset.trans h1 h2

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Characterization of clauses in foldl addClause: either from initial state or added by fold. -/
lemma foldl_addClause_mem_iff {α : Type} (b : Bounds S)
    (mkClause : α → SAT.Clause (Var b)) (xs : List α) (st : EncState b)
    (clause : SAT.Clause (Var b)) :
    clause ∈ (xs.foldl (fun stCur x => EncState.addClause b stCur (mkClause x)) st).clauses ↔
    clause ∈ st.clauses ∨ (∃ x ∈ xs, clause = mkClause x) := by
  induction xs generalizing st with
  | nil =>
      simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [EncState.addClause]
      constructor
      · intro h
        cases h with
        | inl h' =>
            cases h' with
            | head => right; exact ⟨x, List.Mem.head xs, rfl⟩
            | tail _ h'' => left; exact h''
        | inr h' =>
            obtain ⟨x', hMem, hEq⟩ := h'
            right
            exact ⟨x', List.mem_cons_of_mem _ hMem, hEq⟩
      · intro h
        cases h with
        | inl h' => left; exact List.mem_cons_of_mem _ h'
        | inr h' =>
            obtain ⟨x', hMem, hEq⟩ := h'
            cases hMem with
            | head => left; rw [hEq]; exact List.Mem.head _
            | tail _ hTail => right; exact ⟨x', hTail, hEq⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- `mkBigOrIff` only appends clauses; it preserves the existing pool. -/
lemma mkBigOrIff_clauses_subset (b : Bounds S)
    (vs : List (Var b)) (st : EncState b) :
    st.clauses ⊆ (mkBigOrIff b vs st).2.clauses := by
  classical
  intro clause hClause
  unfold mkBigOrIff
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      have hAlloc' : clause ∈ st1.clauses := by
        have eq : st1 = (EncState.allocFresh b st).2 := by
          cases hAlloc
          rfl
        simpa [eq, EncState.allocFresh_clauses_eq] using hClause
      -- Clauses are preserved through the subsequent fold.
      set stFold :=
        vs.foldl
          (fun stCur v =>
            EncState.addClause b stCur
              [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)])
          st1
      have hFold :
          clause ∈ stFold.clauses := by
        -- Use the generic fold helper instantiated with `EncState.addClause`.
        have hSubset :=
          foldl_addClause_subset
            (b := b)
            (f := fun stCur v =>
              EncState.addClause b stCur
                [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)])
            (xs := vs) (st := st1)
            (hPres := fun stCur v =>
              EncState.addClause_subset_clauses
                (b := b)
                (st := stCur)
                (clause := [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]))
        simpa [stFold] using hSubset hAlloc'
      -- Final clause addition also preserves existing entries.
      have hFinal :=
        EncState.addClause_subset_clauses
          (b := b)
          (st := stFold)
          (clause := SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos)
      exact hFinal hFold

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Every unit clause added by `mkBigOrIff` appears in the accumulated clause list. -/
lemma mkBigOrIff_unit_clause_mem (b : Bounds S)
    (vs : List (Var b)) (st : EncState b) {v : Var b}
    (hv : v ∈ vs) :
    [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (mkBigOrIff b vs st).1)] ∈
      (mkBigOrIff b vs st).2.clauses := by
  classical
  obtain ⟨as, bs, hSplit⟩ := exists_split_of_mem (l := vs) hv
  unfold mkBigOrIff
  obtain ⟨u, st1⟩ := EncState.allocFresh b st
  -- Helper function used in the fold.
  let step :=
    fun stCur (w : Var b) =>
      EncState.addClause b stCur
        [SAT.Lit.neg w, SAT.Lit.pos (FVar.toVar b u)]
  -- Clause is added when processing the distinguished element `v`.
  have hHead :
      [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)] ∈
        (step (List.foldl step st1 as) v).clauses := by
    dsimp [step]
    simp [EncState.addClause, List.mem_cons]
  -- Clauses persist through the suffix of the fold.
  have hSuffix :
      (step (List.foldl step st1 as) v).clauses ⊆
        (List.foldl step (step (List.foldl step st1 as) v) bs).clauses := by
    simpa [step] using
      (foldl_addClause_subset
        (b := b)
        (f := step)
        (xs := bs)
        (st := step (List.foldl step st1 as) v)
        (hPres := fun stCur w =>
          EncState.addClause_subset_clauses
                   (b := b)
                   (st := stCur)
                   (clause := [SAT.Lit.neg w, SAT.Lit.pos (FVar.toVar b u)])))
  have hInSuffix := hSuffix hHead
  -- Reassemble the original fold using the split vs = as ++ v :: bs.
  have hFold :
      List.foldl step st1 (as ++ v :: bs) =
        List.foldl step (step (List.foldl step st1 as) v) bs := by
    simp [List.foldl_append, step]
  have hBase :
      [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)] ∈
        (List.foldl step st1 (as ++ v :: bs)).clauses := by
    simpa [hFold] using hInSuffix
  -- The final Tseytin gadget adds one more clause; existing ones persist.
  have hFinal :=
    EncState.addClause_subset_clauses
      (b := b)
      (st := List.foldl step st1 (as ++ v :: bs))
      (clause := SAT.Lit.neg (FVar.toVar b u) :: (as ++ v :: bs).map SAT.Lit.pos)
  -- Combine the steps and rewrite with the split representation.
  simpa [step, hSplit, hFold, EncState.addClause, List.map_append] using hFinal hBase

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkBigOrIff_long_clause_mem (b : Bounds S)
    (vs : List (Var b)) (st : EncState b) :
    (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b vs st).1) ::
      vs.map SAT.Lit.pos) ∈ (mkBigOrIff b vs st).2.clauses := by
  classical
  unfold mkBigOrIff
  obtain ⟨u, st1⟩ := EncState.allocFresh b st
  simp [EncState.addClause]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: clauses in the fold are either from base or are forward clauses. -/
private lemma mkBigOrIff_fold_clause_mem_aux (b : Bounds S)
    (vs : List (Var b)) (baseClauses : List (SAT.Clause (Var b)))
    (freshIdx : Nat) (clause : SAT.Clause (Var b)) :
    let initSt : EncState b := ⟨freshIdx + 1, baseClauses⟩
    clause ∈ (vs.foldl (fun acc w =>
        ⟨acc.nextFresh, [SAT.Lit.neg w, SAT.Lit.pos (Var.Fresh freshIdx)] :: acc.clauses⟩)
      initSt).clauses →
    clause ∈ baseClauses ∨ ∃ v ∈ vs, clause = [SAT.Lit.neg v, SAT.Lit.pos (Var.Fresh freshIdx)] := by
  intro initSt
  induction vs generalizing baseClauses with
  | nil =>
    intro hMem; left; exact hMem
  | cons v vs' ih =>
    intro hMem
    -- The new base for the recursive fold is [¬v, +u] :: baseClauses
    have hRec := ih ([SAT.Lit.neg v, SAT.Lit.pos (Var.Fresh freshIdx)] :: baseClauses) hMem
    cases hRec with
    | inl hInNew =>
      cases hInNew with
      | head => right; exact ⟨v, List.Mem.head _, rfl⟩
      | tail _ hInBase => left; exact hInBase
    | inr hFromVs' =>
      obtain ⟨v', hv', hEq⟩ := hFromVs'
      right; exact ⟨v', List.mem_cons_of_mem _ hv', hEq⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Characterization of clauses in mkBigOrIff: either from base state, a forward clause, or the
    backward clause. -/
lemma mkBigOrIff_clause_mem_iff (b : Bounds S)
    (vs : List (Var b)) (st : EncState b)
    (clause : SAT.Clause (Var b)) :
    clause ∈ (mkBigOrIff b vs st).2.clauses ↔
    clause ∈ st.clauses ∨
    (∃ v ∈ vs, clause = [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (mkBigOrIff b vs st).1)]) ∨
    clause = SAT.Lit.neg (FVar.toVar b (mkBigOrIff b vs st).1) :: vs.map SAT.Lit.pos := by
  classical
  constructor
  · intro hMem
    -- Unfold mkBigOrIff to expose structure
    have hU : (mkBigOrIff b vs st).1 = ⟨st.nextFresh⟩ := by
      simp only [mkBigOrIff, EncState.allocFresh]
    unfold mkBigOrIff at hMem
    simp only [EncState.addClause, EncState.allocFresh] at hMem
    cases hMem with
    | head =>
      -- This is the backward clause
      right; right
      simp only [mkBigOrIff, EncState.allocFresh]
    | tail _ hTail =>
      -- hTail is membership in the fold's clauses
      have hFoldMem := mkBigOrIff_fold_clause_mem_aux b vs st.clauses st.nextFresh clause hTail
      cases hFoldMem with
      | inl hBase => left; exact hBase
      | inr hForward =>
        right; left
        obtain ⟨v, hv, hEq⟩ := hForward
        refine ⟨v, hv, ?_⟩
        rw [hEq, hU]; rfl
  · intro h
    cases h with
    | inl hBase => exact mkBigOrIff_clauses_subset b vs st hBase
    | inr h' =>
      cases h' with
      | inl hForward =>
        obtain ⟨v, hv, hEq⟩ := hForward
        rw [hEq]
        exact mkBigOrIff_unit_clause_mem b vs st hv
      | inr hBack =>
        rw [hBack]
        exact mkBigOrIff_long_clause_mem b vs st

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma exists_mem_of_pos_clause_true {b : Bounds S} {σ : SAT.Assignment (Var b)}
    {vs : List (Var b)}
    (h : SAT.Clause.eval σ (vs.map SAT.Lit.pos) = true) :
    ∃ v ∈ vs, σ v = true := by
  classical
  induction vs with
  | nil =>
      simp [SAT.Clause.eval] at h
  | cons v vs ih =>
      have hEval := h
      unfold SAT.Clause.eval at hEval
      simp [List.foldl_cons, SAT.Lit.eval] at hEval
      cases hVal : σ v with
      | false =>
          have hRest :
              SAT.Clause.eval σ (vs.map SAT.Lit.pos) = true := by
            unfold SAT.Clause.eval
            simpa [SAT.Lit.eval, List.foldl_cons, hVal] using hEval
          rcases ih hRest with ⟨w, hw, hwσ⟩
          refine ⟨w, ?_, hwσ⟩
          simp [hw]
      | true =>
          refine ⟨v, by simp, ?_⟩
          simp [hVal]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkBigOrIff_exists_true (b : Bounds S) (vs : List (Var b)) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hAll : (mkBigOrIff b vs st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hU : σ (FVar.toVar b (mkBigOrIff b vs st).1) = true) :
    ∃ v ∈ vs, σ v = true := by
  classical
  have hClauseIn :=
    mkBigOrIff_long_clause_mem (b := b) (vs := vs) (st := st)
  have hClauseTrue :
      SAT.Clause.eval σ
        (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b vs st).1) ::
          vs.map SAT.Lit.pos) = true := by
    have hAllClauses := List.all_eq_true.mp hAll
    exact hAllClauses _ hClauseIn
  unfold SAT.Clause.eval at hClauseTrue
  simp [List.foldl_cons, SAT.Lit.eval, hU] at hClauseTrue
  exact exists_mem_of_pos_clause_true (b := b) (σ := σ) hClauseTrue

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkBigOrIff_fst (b : Bounds S) (vs : List (Var b)) (st : EncState b) :
    (mkBigOrIff b vs st).1 = { id := st.nextFresh } := by
  classical
  unfold mkBigOrIff
  simp [EncState.allocFresh]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkBigOrIff_nextFresh (b : Bounds S) (vs : List (Var b)) (st : EncState b) :
    (mkBigOrIff b vs st).2.nextFresh = st.nextFresh + 1 := by
  classical
  unfold mkBigOrIff EncState.allocFresh EncState.addClause
  simp only
  -- After fold and addClause, nextFresh is still st.nextFresh + 1
  have hFold : ∀ (init : EncState b),
      (vs.foldl (fun stCur v => { stCur with
          clauses := [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b ⟨st.nextFresh⟩)] :: stCur.clauses })
          init).nextFresh = init.nextFresh := by
    intro init
    induction vs generalizing init with
    | nil => rfl
    | cons v vs' ih => simp only [List.foldl_cons]; exact ih _
  exact hFold _

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: fold of addClause preserves nextFresh. -/
private lemma mkBigOrIff_fold_nextFresh (b : Bounds S) (u : FVar b) (vs : List (Var b))
    (init : EncState b) :
    (vs.foldl (fun stCur v =>
      EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]) init).nextFresh =
    init.nextFresh := by
  induction vs generalizing init with
  | nil => rfl
  | cons v vs' ih =>
    simp only [List.foldl_cons]
    rw [ih]; simp only [EncState.addClause]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: fold of addClause preserves well-formedness. -/
private lemma mkBigOrIff_fold_wf (b : Bounds S) (u : FVar b) (vs : List (Var b))
    (init : EncState b) (hInitWF : init.WellFormed)
    (hUBelow : u.id < init.nextFresh)
    (hVsSafe : ∀ v ∈ vs, ∀ n, v = Var.Fresh n → n < init.nextFresh) :
    (vs.foldl
      (fun stCur v => EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)])
      init).WellFormed := by
  induction vs generalizing init with
  | nil => exact hInitWF
  | cons v vs' ih =>
    simp only [List.foldl_cons]
    have hVsSafe' : ∀ v' ∈ vs', ∀ n, v' = Var.Fresh n → n < init.nextFresh := by
      intro v' hMem n hEq
      exact hVsSafe v' (List.mem_cons_of_mem v hMem) n hEq
    have hClauseFB : clauseFreshBelow
        [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)] init.nextFresh := by
      unfold clauseFreshBelow litFreshBelow
      intro lit hLit
      simp only [FVar.toVar, List.mem_cons, List.not_mem_nil, or_false] at hLit
      cases hLit with
      | inl h =>
        rw [h]; simp only [SAT.Lit.getVar]
        cases hV : v with
        | Fresh n =>
          exact hVsSafe v List.mem_cons_self n hV
        | _ => trivial
      | inr h =>
        rw [h]; simp only [SAT.Lit.getVar]; exact hUBelow
    set clause := [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)] with hClause
    have hAddWF := EncState.addClause_wf hInitWF clause hClauseFB
    have hAddNext : (EncState.addClause b init clause).nextFresh = init.nextFresh := by
      simp only [EncState.addClause]
    rw [← hAddNext] at hUBelow hVsSafe'
    simp only [] at ih hAddWF hUBelow hVsSafe' ⊢
    exact ih _ hAddWF hUBelow hVsSafe'

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- mkBigOrIff preserves well-formedness if input vars are "safe"
(Fresh vars have index < nextFresh). -/
lemma mkBigOrIff_wf (b : Bounds S) (vs : List (Var b)) (st : EncState b)
    (hWF : EncState.WellFormed st)
    (hVsSafe : ∀ v ∈ vs, ∀ n, v = Var.Fresh n → n < st.nextFresh) :
    EncState.WellFormed (mkBigOrIff b vs st).2 := by
  unfold mkBigOrIff
  set pair := EncState.allocFresh b st with hPair
  set u := pair.1 with hU
  set st1 := pair.2 with hSt1
  have hAllocWF : st1.WellFormed := EncState.allocFresh_wf hWF
  have hAllocNext : st1.nextFresh = st.nextFresh + 1 := by
    simp only [hSt1, hPair, EncState.allocFresh]
  have hUid : u.id = st.nextFresh := by simp only [hU, hPair, EncState.allocFresh]
  have hUBelow : u.id < st1.nextFresh := by omega
  have hVsSafe' : ∀ v ∈ vs, ∀ n, v = Var.Fresh n → n < st1.nextFresh := by
    intro v hMem n hEq; have := hVsSafe v hMem n hEq; omega
  -- st2 is the result of folding addClause over vs
  set st2 := vs.foldl (fun stCur v =>
    EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]) st1 with hSt2
  have hSt2Next : st2.nextFresh = st1.nextFresh := mkBigOrIff_fold_nextFresh b u vs st1
  have hSt2WF : st2.WellFormed := mkBigOrIff_fold_wf b u vs st1 hAllocWF hUBelow hVsSafe'
  -- The final clause
  set lastClause := (SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos) with hLastClause
  have hBound : st2.nextFresh = st.nextFresh + 1 := by rw [hSt2Next, hAllocNext]
  have hLastClauseFB : clauseFreshBelow lastClause st2.nextFresh := by
    rw [hBound]
    unfold clauseFreshBelow litFreshBelow
    intro lit hLit
    simp only [hLastClause, FVar.toVar, List.mem_cons, List.mem_map] at hLit
    cases hLit with
    | inl h =>
      rw [h]; simp only [SAT.Lit.getVar, hUid]; omega
    | inr h =>
      obtain ⟨v, hVMem, hLitEq⟩ := h
      subst hLitEq
      simp only [SAT.Lit.getVar]
      cases hV : v with
      | Fresh n =>
        have hLt := hVsSafe v hVMem n hV
        omega
      | _ => trivial
  exact EncState.addClause_wf hSt2WF lastClause hLastClauseFB

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Structural determinism for mkBigOrIff: if σ satisfies clauses from mkBigOrIff at st,
    then σ' (with Fresh vars shifted) satisfies clauses from mkBigOrIff at st'.

    The input variables vs are assumed to not contain Fresh vars >= st.nextFresh
    (typically they're Pred vars which satisfy this). -/
lemma mkBigOrIff_structural_determinism (b : Bounds S) (vs : List (Var b))
    (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st')
    (hVsNonFresh : ∀ v ∈ vs, ∀ n, v = Var.Fresh n → n < st.nextFresh)
    (σ : SAT.Assignment (Var b))
    (hSat : (mkBigOrIff b vs st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hSatBase : st'.clauses.all (SAT.Clause.eval σ) = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < st'.nextFresh then σ v
          else σ (Var.Fresh (n - offset))  -- Inline unshift for Fresh
      | _ => σ v
    (mkBigOrIff b vs st').2.clauses.all (SAT.Clause.eval σ') = true := by
  classical
  intro σ'
  rw [List.all_eq_true]
  intro clause hClause

  -- The clauses in mkBigOrIff at st' are:
  -- 1. Inherited from st'.clauses
  -- 2. Short clauses [¬v, u'] for each v ∈ vs where u' = Fresh(st'.nextFresh)
  -- 3. Long clause [¬u', v₁, ..., vₙ]

  -- First, establish key facts about control vars
  have hUst : (mkBigOrIff b vs st).1 = ⟨st.nextFresh⟩ := mkBigOrIff_fst b vs st
  have hUst' : (mkBigOrIff b vs st').1 = ⟨st'.nextFresh⟩ := mkBigOrIff_fst b vs st'

  -- Unfolding mkBigOrIff structure at st'
  simp only [mkBigOrIff] at hClause
  simp only [EncState.addClause] at hClause

  -- Three cases for clause membership
  cases hClause with
  | head =>
      -- Long clause [¬u', pos v₁, ..., pos vₙ] where u' = Fresh(st'.nextFresh)
      -- Corresponding clause at st is [¬u, pos v₁, ..., pos vₙ] where u = Fresh(st.nextFresh)
      have hLongClauseSt : (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b vs st).1) ::
          vs.map SAT.Lit.pos) ∈ (mkBigOrIff b vs st).2.clauses :=
        mkBigOrIff_long_clause_mem b vs st
      have hEvalSt := List.all_eq_true.mp hSat _ hLongClauseSt

      -- The clause evaluates to true under σ
      rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt
      rw [SAT.Clause.eval_eq_any, List.any_eq_true]
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
      -- hLitMem : lit ∈ (¬u :: vs.map pos)
      rcases hLitMem with ⟨⟩ | ⟨_, hMapMem⟩
      · -- lit = ¬u (the head)
        refine ⟨SAT.Lit.neg (FVar.toVar b ⟨st'.nextFresh⟩), List.Mem.head _, ?_⟩
        simp only [SAT.Lit.eval] at hLitTrue ⊢
        simp only [FVar.toVar, hUst] at hLitTrue
        simp only [FVar.toVar]
        simp only [σ', Nat.lt_irrefl, ↓reduceIte]
        have hEq : st'.nextFresh - offset = st.nextFresh := by
          rw [hOffset]; omega
        rw [hEq]
        exact hLitTrue
      · -- lit ∈ vs.map pos (hMapMem already in correct form for obtain)
        obtain ⟨v, hVMem, hLitEq⟩ := List.mem_map.mp hMapMem
        have hPosVMem : SAT.Lit.pos v ∈ vs.map SAT.Lit.pos :=
          List.mem_map_of_mem (f := SAT.Lit.pos) hVMem
        refine ⟨SAT.Lit.pos v, List.mem_cons_of_mem _ hPosVMem, ?_⟩
        simp only [SAT.Lit.eval]
        simp only [← hLitEq, SAT.Lit.eval] at hLitTrue
        cases hv : v with
        | Fresh n =>
            have hLt := hVsNonFresh v hVMem n hv
            simp only [σ']
            have hLt' : n < st'.nextFresh := Nat.lt_of_lt_of_le hLt hMono
            simp only [hLt', ↓reduceIte]
            simp only [hv] at hLitTrue
            exact hLitTrue
        | _ =>
            simp only [σ']
            simp only [hv] at hLitTrue
            exact hLitTrue

  | tail _ hTail =>
      -- Either a short clause or inherited
      simp only [EncState.allocFresh] at hTail

      -- We need to distinguish these cases. Let's use classical reasoning.
      by_cases hInBase : clause ∈ st'.clauses
      · -- Inherited clause from st'.clauses
        have hEvalBase := List.all_eq_true.mp hSatBase clause hInBase
        rw [SAT.Clause.eval_eq_any] at hEvalBase ⊢
        rw [List.any_eq_true] at hEvalBase ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalBase
        refine ⟨lit, hLitMem, ?_⟩
        -- Use well-formedness to show all Fresh vars are < st'.nextFresh
        have hClauseWF : clauseFreshBelow clause st'.nextFresh := hWF clause hInBase
        cases lit with
        | pos v =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases v with
            | Fresh n =>
                -- For inherited clause, n < st'.nextFresh (well-formedness)
                have hLt : n < st'.nextFresh := by
                  have h := hClauseWF (SAT.Lit.pos (Var.Fresh n)) hLitMem
                  simp only [litFreshBelow, SAT.Lit.getVar] at h
                  exact h
                simp only [σ', hLt, ↓reduceIte]
                exact hLitTrue
            | _ => exact hLitTrue
        | neg v =>
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            cases v with
            | Fresh n =>
                have hLt : n < st'.nextFresh := by
                  have h := hClauseWF (SAT.Lit.neg (Var.Fresh n)) hLitMem
                  simp only [litFreshBelow, SAT.Lit.getVar] at h
                  exact h
                simp only [σ', hLt, ↓reduceIte]
                exact hLitTrue
            | _ => exact hLitTrue
      · -- Short clause [¬v, u'] for some v ∈ vs
        have hShortForm : ∃ v ∈ vs, clause = [SAT.Lit.neg v,
            SAT.Lit.pos (FVar.toVar b ⟨st'.nextFresh⟩)] := by
          let u' : FVar b := ⟨st'.nextFresh⟩
          let step := fun (stCur : EncState b) (v : Var b) =>
            EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u')]
          have hFoldMem : clause ∈ (vs.foldl step (EncState.allocFresh b st').2).clauses := hTail
          have hAllocClauses : (EncState.allocFresh b st').2.clauses = st'.clauses :=
            EncState.allocFresh_clauses_eq b st'
          rw [foldl_addClause_mem_iff] at hFoldMem
          cases hFoldMem with
          | inl hOld =>
              rw [hAllocClauses] at hOld
              exact absurd hOld hInBase
          | inr hNew =>
              obtain ⟨v, hMem, hEq⟩ := hNew
              exact ⟨v, hMem, hEq⟩

        obtain ⟨v, hMem, hClauseEq⟩ := hShortForm

        -- The corresponding clause at st
        have hShortSt : [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (mkBigOrIff b vs st).1)] ∈
            (mkBigOrIff b vs st).2.clauses := mkBigOrIff_unit_clause_mem b vs st hMem
        have hEvalSt := List.all_eq_true.mp hSat _ hShortSt

        rw [hClauseEq]
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
        simp only [hUst] at hEvalSt

        obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
        -- hLitMem : lit ∈ [¬v, pos u]
        rcases hLitMem with ⟨⟩ | ⟨_, hTail'⟩
        · -- lit = ¬v
          refine ⟨SAT.Lit.neg v, List.Mem.head _, ?_⟩
          simp only [SAT.Lit.eval] at hLitTrue ⊢
          cases hv : v with
          | Fresh n =>
              have hLt := hVsNonFresh v hMem n hv
              simp only [σ']
              have hLt' : n < st'.nextFresh := Nat.lt_of_lt_of_le hLt hMono
              simp only [hLt', ↓reduceIte]
              simp only [hv] at hLitTrue
              exact hLitTrue
          | _ =>
              simp only [σ']
              simp only [hv] at hLitTrue
              exact hLitTrue
        · -- lit ∈ [pos u]
          rcases hTail' with ⟨⟩ | ⟨_, hEmpty⟩
          · -- lit = pos u
            refine ⟨SAT.Lit.pos (FVar.toVar b ⟨st'.nextFresh⟩),
                List.mem_cons_of_mem _ (List.Mem.head _), ?_⟩
            simp only [SAT.Lit.eval] at hLitTrue ⊢
            simp only [FVar.toVar] at hLitTrue ⊢
            simp only [σ', Nat.lt_irrefl, ↓reduceIte]
            have hEq : st'.nextFresh - offset = st.nextFresh := by
              rw [hOffset]; omega
            rw [hEq]
            exact hLitTrue
          · -- impossible: empty list
            cases hEmpty

end Encoding
