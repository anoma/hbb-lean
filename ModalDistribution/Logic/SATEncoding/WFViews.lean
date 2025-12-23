import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure

/-!
# CNF Well-Formedness Views

This file bridges the gap between `WF b σ` (CNF evaluation = true) and
concrete semantic properties about the assignment. It provides:

1. **List-level witness predicates** (ALO, AMO)
2. **Selector correctness lemmas** (pickTime, pickPlace, pickEvent)
3. **Acyclicity consequence** (time strictly decreases)
4. **WFViews structure** - clean API extracting all needed facts from WF

These lemmas unblock `decodePreFuel_stable` and other adequacy proofs
that need to reason about what WF b σ guarantees.

## References
- Plan.md "Decoder Termination" section
- Structure.lean for CNF constraint definitions
-/

open ModalDistribution

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## List-Level Witness Predicates -/

/-- At least one element of `xs` is true under `σ`. -/
def AtLeastOne {α} (xs : List α) (σ : α → Bool) : Prop :=
  ∃ x ∈ xs, σ x = true

/-- Pairwise exclusivity: at most one element can be true. -/
def PairwiseExclusive {α} [DecidableEq α] (xs : List α) (σ : α → Bool) : Prop :=
  ∀ {x y}, x ≠ y → x ∈ xs → y ∈ xs → σ x = true → σ y = false

/-- Exactly one element is true (ALO + AMO). -/
def ExactlyOne {α} [DecidableEq α] (xs : List α) (σ : α → Bool) : Prop :=
  AtLeastOne xs σ ∧ PairwiseExclusive xs σ

/-! ## Selector Utilities -/

/-- Pick the first true element in `xs`, or `dflt` if none. -/
def pickFirstTrue {α} (xs : List α) (σ : α → Bool) (dflt : α) : α :=
  match xs.find? (fun x => σ x = true) with
  | some x => x
  | none   => dflt

/-! ## List.find? Correctness Lemmas -/

/-- If `find?` returns `some x`, then `x ∈ xs` and `p x = true`. -/
lemma find?_mem_of_pred {α} :
    ∀ (xs : List α) (p : α → Bool) {x},
      xs.find? p = some x → x ∈ xs ∧ p x = true := by
  intro xs p x
  induction xs with
  | nil => intro h; cases h
  | cons a as ih =>
    intro h
    unfold List.find? at h
    split at h
    · -- If p a = true, then find? returns some a
      cases h
      constructor
      · simp
      · assumption
    · -- If p a = false, recurse on tail
      have := ih h
      constructor
      · simp [this.1]
      · exact this.2

/-- Helper: If find? succeeds on a predicate with decide, then the property holds. -/
lemma find?_decide_spec {α} (xs : List α) (σ : α → Bool) {x} :
    xs.find? (fun z => decide (σ z = true)) = some x → x ∈ xs ∧ σ x = true := by
  intro h
  have := find?_mem_of_pred xs (fun z => decide (σ z = true)) h
  constructor
  · exact this.1
  · have : decide (σ x = true) = true := this.2
    simp at this
    exact this

/-- If find? returns none, then no element satisfies the predicate. -/
lemma find?_none_forall {α} (xs : List α) (p : α → Bool) :
    xs.find? p = none → ∀ y ∈ xs, p y = false := by
  intro h y hy
  induction xs with
  | nil => cases hy
  | cons a as ih =>
    unfold List.find? at h
    split at h
    · -- If p a = true, then find? would return some a, contradiction
      cases h
    · -- If p a = false, recurse
      cases hy with
      | head => assumption
      | tail _ hy' => exact ih h hy'

/-- If `find?` succeeds on a boolean predicate, the witness satisfies the predicate. -/
lemma find?_some_true {α} (xs : List α) (p : α → Bool) {x} :
    xs.find? p = some x → p x = true := by
  intro h
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
    unfold List.find? at h
    cases hhd : p hd with
    | false =>
        have h' : tl.find? p = some x := by
          simpa [hhd] using h
        exact ih h'
    | true =>
        have hx : hd = x := by
          simpa [hhd] using h
        simp [hx.symm, hhd]

/-- Variant for decidable Prop predicates. -/
lemma find?_none_forall_prop {α} (xs : List α) (p : α → Prop) [DecidablePred p] :
    xs.find? p = none → ∀ y ∈ xs, ¬p y := by
  intro h y hy
  induction xs with
  | nil => cases hy
  | cons hd tl ih =>
    unfold List.find? at h
    split at h
    · -- If p hd, then find? would return some hd, contradiction
      cases h
    · -- If ¬p hd, recurse
      rename_i heq
      cases hy with
      | head =>
        -- heq : decide (p y) = false, need to show ¬p y
        intro hpy
        have : decide (p y) = true := decide_eq_true hpy
        rw [this] at heq
        cases heq
      | tail _ hy' => exact ih h hy'

/-- Variant for decidable Prop predicates - positive case. -/
lemma find?_some_prop {α} (xs : List α) (p : α → Prop) [DecidablePred p] {x} :
    xs.find? p = some x → x ∈ xs ∧ p x := by
  intro h
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
    unfold List.find? at h
    split at h
    · -- If p hd, then find? returns some hd
      rename_i heq
      cases h
      constructor
      · simp
      · exact of_decide_eq_true heq
    · -- If ¬p hd, recurse
      have := ih h
      constructor
      · simp [this.1]
      · exact this.2

/-- If a clause built from positive literals evaluates to true,
    some underlying variable must be true under the assignment. -/
lemma exists_true_of_eval_pos {Var} (σ : SAT.Assignment Var) :
    ∀ xs : List Var,
      SAT.Clause.eval σ (xs.map SAT.Lit.pos) = true →
        ∃ x ∈ xs, σ x = true := by
  classical
  intro xs
  induction xs with
  | nil =>
      intro h
      have : False := by simp at h
      exact this.elim
  | cons x xs ih =>
      intro hClause
      cases hx : σ x with
      | false =>
          have hTailClause :
              SAT.Clause.eval σ (xs.map SAT.Lit.pos) = true := by
            simpa [SAT.Clause.eval, List.map_cons, SAT.Lit.eval, hx] using hClause
          obtain ⟨y, hy_mem, hy_true⟩ := ih hTailClause
          exact ⟨y, by simp [hy_mem], hy_true⟩
      | true =>
          exact ⟨x, by simp, hx⟩

/-- Under exactly-one conditions, `pickFirstTrue` returns the unique true element. -/
lemma pickFirstTrue_spec_unique {α} [DecidableEq α]
    {xs : List α} {σ : α → Bool} {dflt x₀ : α} :
    AtLeastOne xs σ →
    PairwiseExclusive xs σ →
    (∀ x x', x ∈ xs → x' ∈ xs → σ x = true → σ x' = true → x = x') →
    pickFirstTrue xs σ dflt = x₀ →
    σ x₀ = true ∧ x₀ ∈ xs := by
  intro hALO hPE huniq hpick
  rcases hALO with ⟨x, hx, hxσ⟩
  unfold pickFirstTrue at hpick
  cases hfind : xs.find? (fun z => decide (σ z = true)) with
  | none =>
    -- If find? = none, then pickFirstTrue returns dflt
    -- But we have x ∈ xs with σ x = true, contradiction
    have hall := find?_none_forall xs (fun z => decide (σ z = true)) hfind
    have hxfalse := hall x hx
    simp at hxfalse
    rw [hxσ] at hxfalse
    cases hxfalse
  | some y =>
    have hy : y ∈ xs ∧ σ y = true := find?_decide_spec xs σ hfind
    rcases hy with ⟨hy_mem, hy_true⟩
    -- pickFirstTrue returns y when find? = some y
    rw [hfind] at hpick
    -- So x₀ = y
    have hyx₀ : y = x₀ := hpick
    subst hyx₀
    exact ⟨hy_true, hy_mem⟩

/-! ## Bridge Lemma: SAT.exo → ExactlyOne -/

/-- **Bridge lemma**: Evaluation of `SAT.exo xs` gives `ExactlyOne` on `xs`.

This is the key lemma that extracts semantic properties from CNF clauses.
Uses the algebraic structure: `exo = alo ∧ amo` to avoid clause-membership reasoning.

Strategy:
- `SAT.alo xs` = single clause `[x₁ ∨ ... ∨ xₙ]` → gives AtLeastOne
- `SAT.amo xs` = clauses `[¬xᵢ ∨ ¬xⱼ]` for all i≠j → gives PairwiseExclusive -/
lemma exo_eval_exactlyOne {Var : Type} [DecidableEq Var]
    (σ : SAT.Assignment Var) (xs : List Var) :
    (SAT.exo xs).eval σ = true → ExactlyOne xs (fun v => σ v) := by
  intro h
  -- exo = alo ∧ amo
  have := SAT.CNF.eval_and_true σ (SAT.alo xs) (SAT.amo xs)
  rw [SAT.exo] at h
  have ⟨halo, hamo⟩ := this.mp h
  constructor
  -- AtLeastOne from alo
  · unfold AtLeastOne
    have hAll :
        ∀ clause ∈ (SAT.alo xs).clauses, SAT.Clause.eval σ clause = true :=
      List.all_eq_true.mp (by simpa [SAT.CNF.eval] using halo)
    have hClause :
        SAT.Clause.eval σ (xs.map SAT.Lit.pos) = true := by
      have hmem : (xs.map SAT.Lit.pos) ∈ (SAT.alo xs).clauses := by
        simp [SAT.alo]
      exact hAll _ hmem
    exact exists_true_of_eval_pos σ xs hClause
  -- PairwiseExclusive from amo
  · unfold PairwiseExclusive
    intro x y hneq hx hy hσx
    -- amo contains clause [¬x ∨ ¬y] for this pair
    -- If σ x = true and clause is true, then σ y = false
    classical
    have hAllClauses :
        ∀ clause ∈ (SAT.amo xs).clauses, SAT.Clause.eval σ clause = true :=
      List.all_eq_true.mp (by simpa [SAT.CNF.eval] using hamo)
    have hAllList :
        ∀ clause ∈ ((xs.flatMap fun x₁ => xs.map fun y₁ => (x₁, y₁)).filter
                      fun (x₁, y₁) => x₁ ≠ y₁).map
            (fun (p : Var × Var) => [SAT.Lit.neg p.1, SAT.Lit.neg p.2]),
          SAT.Clause.eval σ clause = true :=
      by
        intro clause hclause
        have : clause ∈ (SAT.amo xs).clauses := by
          simpa [SAT.amo] using hclause
        exact hAllClauses _ this
    have hxypairs :
        (x, y) ∈ xs.flatMap (fun x₁ => xs.map fun y₁ => (x₁, y₁)) := by
      refine List.mem_flatMap.2 ?_
      refine ⟨x, hx, ?_⟩
      refine List.mem_map.2 ?_
      exact ⟨y, hy, rfl⟩
    have hxystrict :
        (x, y) ∈
            (xs.flatMap fun x₁ => xs.map fun y₁ => (x₁, y₁)).filter fun (x₁, y₁) => x₁ ≠ y₁ := by
      simp [hxypairs, hneq]
    have hClauseEval :
        SAT.Clause.eval σ [SAT.Lit.neg x, SAT.Lit.neg y] = true := by
      exact
        hAllList _
          (List.mem_map.2 ⟨(x, y), hxystrict, rfl⟩)
    have hDisj : σ x = false ∨ σ y = false := by
      simpa [SAT.Clause.eval_two_lit, SAT.Lit.eval] using hClauseEval
    refine hDisj.elim (fun hxFalse => ?_) (fun hyFalse => hyFalse)
    have : False := by
      simp [hσx] at hxFalse
    exact this.elim

/-! ## Uniqueness from ExactlyOne -/

/-- ExactlyOne implies uniqueness of the true element. -/
lemma unique_of_exactlyOne {α} [DecidableEq α] {xs : List α} {σ : α → Bool} :
    ExactlyOne xs σ →
    ∀ x x', x ∈ xs → x' ∈ xs → σ x = true → σ x' = true → x = x' := by
  intro ⟨_, hPE⟩ x x' hx hx' hσx hσx'
  by_contra hneq
  have := hPE hneq hx hx' hσx
  rw [hσx'] at this
  cases this

/-! ## WFViews Structure -/

/-- Structured view of consequences of WF b σ.

With canonical decoding using structural fields (w.ti, w.p, w.ei):
- World attributes come directly from structural fields
- No need for time_exo, place_exo, event_exo (no one-hot encoding needed)
- Acyclic constraint must still be enforced via CNF to ensure well-foundedness
-/
structure WFViews (b : Bounds S) (σ : SAT.Assignment (Var b)) : Prop where
  /-- Acyclic constraint: Mem(H, w) → w.ti.val < H.val
      Ensures decoded prehistories are well-founded. -/
  acyclic : ∀ (H : b.times) (w : WId b),
    σ (Var.Mem H w) = true →
    w.ti.val < H.val

/-! ## Extraction from WF -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Extract WFViews from WF b σ.

Extracts the acyclic constraint from cnfAcyclic, which is part of cnfWellFormed.
For every (H, w) where w.ti.val >= H.val, cnfAcyclic contains clause ¬Mem(H, w).
Since WF implies this clause is satisfied, we get Mem(H, w) → w.ti.val < H.val. -/
lemma WF.views (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ) :
    WFViews b σ := by
  classical
  -- Extract cnfAcyclic from cnfWellFormed
  have ⟨hAcyclic, _, _, _, _, _, _, _, _, _, _⟩ := (cnfWellFormed_eval_iff b σ).mp hWF

  -- Prove the acyclic constraint
  refine { acyclic := ?_ }
  intro H w hMem

  -- By contradiction: assume w.ti.val >= H.val
  by_contra hNotLt
  have hGeq : H.val ≤ w.ti.val := Nat.not_lt.mp hNotLt

  -- cnfAcyclic contains clause ¬Mem(H, w) for this pair
  have hAllClauses : ∀ clause ∈ (cnfAcyclic b).clauses, SAT.Clause.eval σ clause = true := by
    have : (cnfAcyclic b).clauses.all (SAT.Clause.eval σ) = true := by
      simpa [SAT.CNF.eval] using hAcyclic
    exact List.all_eq_true.mp this

  -- The clause [¬Mem(H, w)] is in the clauses
  have hClauseIn : [SAT.Lit.neg (Var.Mem H w)] ∈ (cnfAcyclic b).clauses := by
    unfold cnfAcyclic SAT.CNF.clauses
    refine List.mem_flatMap.mpr ?_
    refine ⟨H, by simp [Bounds.timesL], ?_⟩
    refine List.mem_filterMap.mpr ?_
    refine ⟨w, WId.mem_allWorlds b w, ?_⟩
    split
    · rename_i hLt
      -- w.ti.val < H.val contradicts our assumption
      omega
    · rfl

  have hClauseTrue := hAllClauses _ hClauseIn
  unfold SAT.Clause.eval at hClauseTrue
  simp only [List.foldl_cons, List.foldl_nil, SAT.Lit.eval, hMem] at hClauseTrue
  -- hClauseTrue : (false || !true) = true, which simplifies to false = true
  cases hClauseTrue

/-! ## Existence and Sequentiality Views -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Exists(H,p,t) ↔ ∃ w, Mem(H,w) ∧ w.p = p ∧ w.ti = t. -/
lemma Exists_iff_mem (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (H : b.times) (p : b.participants) (t : b.times) :
    σ (Var.Exists H p t) = true ↔
      ∃ w, σ (Var.Mem H w) = true ∧ w.p = p ∧ w.ti = t := by
  classical
  have ⟨_, _, _, _, _, _, _, _, hExists, hExistsBack, _⟩ :=
    (cnfWellFormed_eval_iff b σ).mp hWF

  constructor
  · -- Forward: Exists → ∃ w, Mem
    intro hEx
    -- Use cnfExists_back
    have hAllBack : (cnfExists_back b).clauses.all (SAT.Clause.eval σ) = true := by
      simpa [SAT.CNF.eval] using hExistsBack

    -- Consider the worlds that match p and t
    let ws := (WId.allWorlds b).filter (fun w => w.p = p ∧ w.ti = t)

    -- Prove that ws must be non-empty
    have hWsNonEmpty : ws ≠ [] := by
      intro hempty
      -- If ws is empty, then cnfExists_back contains clause [¬Exists H p t]
      have hClauseIn : [SAT.Lit.neg (Var.Exists H p t)] ∈ (cnfExists_back b).clauses := by
        unfold cnfExists_back SAT.CNF.clauses
        simp only [List.mem_flatMap, List.mem_map, Bounds.timesL, Bounds.partsL]
        refine ⟨H, by simp, ?_⟩
        refine ⟨p, by simp, ?_⟩
        refine ⟨t, by simp, ?_⟩
        -- Show that when ws is empty, the clause is [¬Exists H p t]
        -- The filter in the definition uses boolean AND with decide
        have : (WId.allWorlds b).filter (fun w => w.p = p ∧ w.ti = t) = [] := hempty
        simp only [this]
      have hClauseEval := (List.all_eq_true.mp hAllBack) _ hClauseIn
      simp [SAT.Clause.eval, SAT.Lit.eval, hEx] at hClauseEval

    -- Since ws is non-empty, extract a witness
    cases hws : ws with
    | nil => contradiction
    | cons w rest =>
      have hw : w ∈ ws := by simp [hws]
      have hwFilter := List.mem_filter.mp hw
      have hwProp : w.p = p ∧ w.ti = t := of_decide_eq_true hwFilter.2
      have hp := hwProp.1
      have hti := hwProp.2

      -- Now show that Mem(H, w) is true using cnfExists_back
      -- cnfExists_back contains clause: ¬Exists(H,p,t) ∨ Mem(H,w₁) ∨ ... ∨ Mem(H,wₙ)
      -- where w₁, ..., wₙ are all worlds with w.p = p and w.ti = t
      have hClauseIn :
          (SAT.Lit.neg (Var.Exists H p t) ::
           ws.map (fun w => SAT.Lit.pos (Var.Mem H w))) ∈ (cnfExists_back b).clauses := by
        unfold cnfExists_back SAT.CNF.clauses
        simp only [List.mem_flatMap, List.mem_map, Bounds.timesL, Bounds.partsL]
        refine ⟨H, by simp, ?_⟩
        refine ⟨p, by simp, ?_⟩
        refine ⟨t, by simp, ?_⟩
        -- Show that when ws is non-empty, the clause matches
        -- The filter expression should reduce to ws, which equals w :: rest
        change (match (WId.allWorlds b).filter (fun w => w.p = p ∧ w.ti = t) with
               | [] => [SAT.Lit.neg (Var.Exists H p t)]
               | _ => SAT.Lit.neg (Var.Exists H p t) ::
                      ((WId.allWorlds b).filter (fun w => w.p = p ∧ w.ti = t)).map
                        (fun w => SAT.Lit.pos (Var.Mem H w))) =
             SAT.Lit.neg (Var.Exists H p t) ::
               ws.map (fun w => SAT.Lit.pos (Var.Mem H w))
        have : (WId.allWorlds b).filter (fun w => w.p = p ∧ w.ti = t) = ws := rfl
        simp only [this, hws]

      have hClauseEval := (List.all_eq_true.mp hAllBack) _ hClauseIn
      simp [SAT.Clause.eval, SAT.Lit.eval, hEx] at hClauseEval

      -- hClauseEval says that some Mem(H, w') is true for some w' in ws
      have : ∃ w' ∈ ws, σ (Var.Mem H w') = true := by
        have :=
          exists_true_of_eval_pos σ (ws.map (fun w => Var.Mem H w)) (by simpa using hClauseEval)
        obtain ⟨v, hv, htrue⟩ := this
        obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hv
        exact ⟨w', hw', htrue⟩

      obtain ⟨w', hw', hMemTrue⟩ := this
      have hwFilter' := List.mem_filter.mp hw'
      have hwProp' : w'.p = p ∧ w'.ti = t := of_decide_eq_true hwFilter'.2
      exact ⟨w', hMemTrue, hwProp'.1, hwProp'.2⟩

  · -- Backward: ∃ w, Mem → Exists
    intro ⟨w, hMem, hp, hti⟩
    -- Use cnfExists (forward direction)
    have hAllFwd : (cnfExists b).clauses.all (SAT.Clause.eval σ) = true := by
      simpa [SAT.CNF.eval] using hExists
    let clause := [SAT.Lit.neg (Var.Mem H w), SAT.Lit.pos (Var.Exists H w.p w.ti)]
    have hClauseIn : clause ∈ (cnfExists b).clauses := by
      unfold cnfExists
      simp [clause, List.mem_flatMap, Bounds.timesL, List.mem_map]
      exact WId.mem_allWorlds b w
    have hClauseEval := (List.all_eq_true.mp hAllFwd) _ hClauseIn
    simp [SAT.Clause.eval, SAT.Lit.eval, hMem, clause] at hClauseEval
    -- hClauseEval : (false ∨ Exists) = true => Exists = true
    rw [hp, hti] at hClauseEval
    exact hClauseEval

/-! ### Sequentiality views (world-level) -/

/-! #### Helper definitions for sequentiality proofs -/

/-- All pairs (H, p, w₁, w₂) where w₁.p = w₂.p = p. -/
def seqAllPairs (b : Bounds S) : List (b.times × b.participants × WId b × WId b) :=
  (Bounds.timesL b).flatMap fun H =>
    (Bounds.partsL b).flatMap fun p =>
      let ws := (WId.allWorlds b).filter (fun w => w.p = p)
      ws.flatMap fun w₁ => ws.map fun w₂ => (H, p, w₁, w₂)

/-- Accessibility witnesses for a world - all worlds with same place and event. -/
def accWitnesses (b : Bounds S) (w : WId b) : List (WId b) :=
  (WId.allWorlds b).filter fun w₃ => w₃.p = w.p && w₃.ei = w.ei

/-- The incompBwd clause structure for a pair. -/
def incompBwdClause (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) : List (SAT.Lit (Var b)) :=
  let baseLits := [SAT.Lit.neg (Var.Mem H w₁), SAT.Lit.neg (Var.Mem H w₂),
                   SAT.Lit.pos (Var.Incomp H p w₁ w₂)]
  let acc12Lits := (accWitnesses b w₁).map fun w₃ => SAT.Lit.pos (Var.Acc w₁ w₂ w₃)
  let acc21Lits := (accWitnesses b w₂).map fun w₃ => SAT.Lit.pos (Var.Acc w₂ w₁ w₃)
  let worldEqLits := if w₁.ei = w₂.ei then [SAT.Lit.pos (Var.PreEq w₁.ti w₂.ti)] else []
  baseLits ++ acc12Lits ++ acc21Lits ++ worldEqLits

/-! #### Pair membership lemma -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- A pair (H, p, w₁, w₂) with matching participants is in seqAllPairs. -/
lemma mem_seqAllPairs (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p) :
    (H, p, w₁, w₂) ∈ seqAllPairs b := by
  simp only [seqAllPairs, List.mem_flatMap, List.mem_map, List.mem_filter,
             Bounds.timesL, Bounds.partsL]
  exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
         ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
         ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩

/-! #### Seq implies not Incomp -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If Seq(H,p) is true and cnfSeq is satisfied, then Incomp(H,p,w₁,w₂) is false. -/
lemma seq_implies_not_incomp (b : Bounds S) (σ : SAT.Assignment (Var b))
    (H : b.times) (p : b.participants) (w₁ w₂ : WId b)
    (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hAllSeq : (cnfSeq b).clauses.all (SAT.Clause.eval σ) = true)
    (hSeqTrue : σ (Var.Seq H p) = true) :
    σ (Var.Incomp H p w₁ w₂) = false := by
  have hPairMem := mem_seqAllPairs b H p w₁ w₂ hp₁ hp₂
  let seqToNoIncompClause := [SAT.Lit.neg (Var.Seq H p), SAT.Lit.neg (Var.Incomp H p w₁ w₂)]
  have hClauseIn : seqToNoIncompClause ∈ (cnfSeq b).clauses := by
    unfold cnfSeq
    simp only [List.append_assoc, List.mem_append]
    right; right; right; left
    simp only [List.mem_map]
    exact ⟨(H, p, w₁, w₂), hPairMem, rfl⟩
  have hClauseEval := (List.all_eq_true.mp hAllSeq) _ hClauseIn
  simpa [seqToNoIncompClause, SAT.Clause.eval, SAT.Lit.eval, List.foldl,
         hSeqTrue, Bool.not_true, Bool.false_or] using hClauseEval

/-! #### incompBwd clause membership -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The incompBwd clause is in cnfSeq. -/
lemma incompBwdClause_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p) :
    incompBwdClause b H p w₁ w₂ ∈ (cnfSeq b).clauses := by
  have hPairMem := mem_seqAllPairs b H p w₁ w₂ hp₁ hp₂
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  right; right; left
  simp only [List.mem_map]
  use (H, p, w₁, w₂)
  constructor
  · exact hPairMem
  · simp only [incompBwdClause, accWitnesses, List.append_assoc]

/-! #### Literal membership in incompBwd clause -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- ¬Mem H w₁ is in the incompBwd clause. -/
lemma negMem1_mem_incompBwdClause (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) : SAT.Lit.neg (Var.Mem H w₁) ∈ incompBwdClause b H p w₁ w₂ := by
  simp only [incompBwdClause]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact .head _

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- ¬Mem H w₂ is in the incompBwd clause. -/
lemma negMem2_mem_incompBwdClause (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) : SAT.Lit.neg (Var.Mem H w₂) ∈ incompBwdClause b H p w₁ w₂ := by
  simp only [incompBwdClause]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact .tail _ (.head _)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Incomp H p w₁ w₂ is in the incompBwd clause. -/
lemma incomp_mem_incompBwdClause (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) : SAT.Lit.pos (Var.Incomp H p w₁ w₂) ∈ incompBwdClause b H p w₁ w₂ := by
  simp only [incompBwdClause]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact .tail _ (.tail _ (.head _))

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Acc w₁ w₂ w₃ literals are in the incompBwd clause for witnesses of w₁. -/
lemma acc12_mem_incompBwdClause (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ w₃ : WId b) (hw₃ : w₃ ∈ accWitnesses b w₁) :
    SAT.Lit.pos (Var.Acc w₁ w₂ w₃) ∈ incompBwdClause b H p w₁ w₂ := by
  simp only [incompBwdClause]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨w₃, hw₃, rfl⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Acc w₂ w₁ w₃ literals are in the incompBwd clause for witnesses of w₂. -/
lemma acc21_mem_incompBwdClause (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ w₃ : WId b) (hw₃ : w₃ ∈ accWitnesses b w₂) :
    SAT.Lit.pos (Var.Acc w₂ w₁ w₃) ∈ incompBwdClause b H p w₁ w₂ := by
  simp only [incompBwdClause]
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨w₃, hw₃, rfl⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- PreEq w₁.ti w₂.ti is in the incompBwd clause when events match. -/
lemma preEq_mem_incompBwdClause (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) (hEvEq : w₁.ei = w₂.ei) :
    SAT.Lit.pos (Var.PreEq w₁.ti w₂.ti) ∈ incompBwdClause b H p w₁ w₂ := by
  simp only [incompBwdClause, hEvEq, ↓reduceIte]
  apply List.mem_append_right
  exact .head _

/-! #### Exhaustive literal case analysis -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- A literal in incompBwdClause is one of the known forms. -/
lemma lit_cases_incompBwdClause (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) (lit : SAT.Lit (Var b))
    (hLitMem : lit ∈ incompBwdClause b H p w₁ w₂) :
    lit = SAT.Lit.neg (Var.Mem H w₁) ∨
    lit = SAT.Lit.neg (Var.Mem H w₂) ∨
    lit = SAT.Lit.pos (Var.Incomp H p w₁ w₂) ∨
    (∃ w₃ ∈ accWitnesses b w₁, lit = SAT.Lit.pos (Var.Acc w₁ w₂ w₃)) ∨
    (∃ w₃ ∈ accWitnesses b w₂, lit = SAT.Lit.pos (Var.Acc w₂ w₁ w₃)) ∨
    (w₁.ei = w₂.ei ∧ lit = SAT.Lit.pos (Var.PreEq w₁.ti w₂.ti)) := by
  unfold incompBwdClause at hLitMem
  -- Split the conditional first
  split_ifs at hLitMem with hEvEq
  · -- Case: w₁.ei = w₂.ei, so worldEqLits = [SAT.Lit.pos (Var.PreEq w₁.ti w₂.ti)]
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hLitMem
    -- Structure after simp: or-chain of equalities and existentials
    aesop
  · -- Case: w₁.ei ≠ w₂.ei, so worldEqLits = []
    simp only [List.append_nil, List.mem_append, List.mem_cons, List.mem_map] at hLitMem
    aesop

/-! #### Main sequentiality lemma -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If two worlds for participant `p` are both in `H` and `Seq(H,p)` is true,
the sequentiality clause forces world-level comparability: either Acc holds
(for accessibility), or when events match, PreEq holds (for worldEq).

Uses the Tseytin encoding with Acc witnesses to derive comparability from
`seqToNoIncomp` and `incompBwd` clauses. The PreEq disjunct only applies
when w₁.ei = w₂.ei, since worldEq requires event equality. -/
lemma seq_world_comparable (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hSeqTrue : σ (Var.Seq H p) = true)
    (hMem₁ : σ (Var.Mem H w₁) = true) (hMem₂ : σ (Var.Mem H w₂) = true) :
    (∃ w₃ ∈ accWitnesses b w₁, σ (Var.Acc w₁ w₂ w₃) = true) ∨
    (∃ w₃ ∈ accWitnesses b w₂, σ (Var.Acc w₂ w₁ w₃) = true) ∨
    (w₁.ei = w₂.ei ∧ σ (Var.PreEq w₁.ti w₂.ti) = true) := by
  classical
  -- Extract cnfSeq satisfaction from WF
  have ⟨_, _, _, _, _, _, _, _, _, _, hSeq⟩ := (cnfWellFormed_eval_iff b σ).mp hWF
  have hAllSeq : (cnfSeq b).clauses.all (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hSeq

  -- Step 1: Incomp is false
  have hIncompFalse := seq_implies_not_incomp b σ H p w₁ w₂ hp₁ hp₂ hAllSeq hSeqTrue

  -- Step 2: Get a true literal from incompBwd clause
  have hClauseIn := incompBwdClause_mem_cnfSeq b H p w₁ w₂ hp₁ hp₂
  have hClauseEval := (List.all_eq_true.mp hAllSeq) _ hClauseIn
  rw [SAT.Clause.eval_eq_any] at hClauseEval
  simp only [List.any_eq_true] at hClauseEval
  obtain ⟨lit, hLitMem, hLitTrue⟩ := hClauseEval

  -- Step 3: Case analysis on what literal is true
  have hCases := lit_cases_incompBwdClause b H p w₁ w₂ lit hLitMem
  rcases hCases with rfl | rfl | rfl | ⟨w₃, hw₃mem, rfl⟩ | ⟨w₃, hw₃mem, rfl⟩ | ⟨hEvEq, rfl⟩
  · -- lit = ¬Mem H w₁ - contradicts hMem₁
    simp [SAT.Lit.eval, hMem₁] at hLitTrue
  · -- lit = ¬Mem H w₂ - contradicts hMem₂
    simp [SAT.Lit.eval, hMem₂] at hLitTrue
  · -- lit = Incomp H p w₁ w₂ - contradicts hIncompFalse
    simp [SAT.Lit.eval, hIncompFalse] at hLitTrue
  · -- lit = Acc w₁ w₂ w₃ with w₃ ∈ accWitnesses b w₁
    left
    exact ⟨w₃, hw₃mem, by simp [SAT.Lit.eval] at hLitTrue; exact hLitTrue⟩
  · -- lit = Acc w₂ w₁ w₃ with w₃ ∈ accWitnesses b w₂
    right; left
    exact ⟨w₃, hw₃mem, by simp [SAT.Lit.eval] at hLitTrue; exact hLitTrue⟩
  · -- lit = PreEq w₁.ti w₂.ti with events matching
    right; right
    simp [SAT.Lit.eval] at hLitTrue
    exact ⟨hEvEq, hLitTrue⟩

/-! #### Helper lemmas for seq_from_sequential -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- A (H, p, w₁, w₂) tuple is in the allPairs list used by cnfSeq. -/
lemma mem_cnfSeq_allPairs (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p) :
    (H, p, w₁, w₂) ∈ (Bounds.timesL b).flatMap fun H =>
      (Bounds.partsL b).flatMap fun p =>
        let ws := (WId.allWorlds b).filter (fun w => w.p = p)
        ws.flatMap fun w₁ => ws.map fun w₂ => (H, p, w₁, w₂) := by
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bounds.timesL, Bounds.partsL]
  exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
         ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
         ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The incompFwd clause for Mem w₁ is in cnfSeq. -/
lemma incompFwd_mem1_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p) :
    [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.pos (Var.Mem H w₁)] ∈ (cnfSeq b).clauses := by
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  right; left
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bounds.timesL, Bounds.partsL]
  refine ⟨(H, p, w₁, w₂), ?_, ?_⟩
  · exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
           ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
           ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩
  · simp only [List.mem_append, List.mem_cons, true_or]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The incompFwd clause for Mem w₂ is in cnfSeq. -/
lemma incompFwd_mem2_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p) :
    [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.pos (Var.Mem H w₂)] ∈ (cnfSeq b).clauses := by
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  right; left
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bounds.timesL, Bounds.partsL]
  refine ⟨(H, p, w₁, w₂), ?_, ?_⟩
  · exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
           ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
           ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩
  · simp only [List.mem_append, List.mem_cons, true_or, or_true]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The incompFwd clause for ¬PreEq is in cnfSeq when events match. -/
lemma incompFwd_preEq_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p) (hEvEq : w₁.ei = w₂.ei) :
    [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.neg (Var.PreEq w₁.ti w₂.ti)] ∈
    (cnfSeq b).clauses := by
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  right; left
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bounds.timesL, Bounds.partsL]
  refine ⟨(H, p, w₁, w₂), ?_, ?_⟩
  · exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
           ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
           ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩
  · -- Navigate to worldEqClauses: memClauses ++ acc12Clauses ++ acc21Clauses ++ worldEqClauses
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_filter, hEvEq,
               ↓reduceIte]
    -- After simp with hEvEq: worldEqClauses = [[...]] which simplifies to True ∨ _ ∈ []
    right; right; right; left; trivial

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Extract Mem truth from a two-literal clause where first literal is false. -/
lemma mem_from_two_lit_clause {b : Bounds S} (σ : SAT.Assignment (Var b))
    (var₁ var₂ : Var b) (hVar1True : σ var₁ = true)
    (hClauseEval : SAT.Clause.eval σ [SAT.Lit.neg var₁, SAT.Lit.pos var₂] = true) :
    σ var₂ = true := by
  simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, hVar1True,
             Bool.not_true, Bool.false_or] at hClauseEval
  exact hClauseEval

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Extract ¬var₂ from a two-literal clause where first literal is false. -/
lemma negVar_from_two_lit_clause {b : Bounds S} (σ : SAT.Assignment (Var b))
    (var₁ var₂ : Var b) (hVar1True : σ var₁ = true)
    (hClauseEval : SAT.Clause.eval σ [SAT.Lit.neg var₁, SAT.Lit.neg var₂] = true) :
    σ var₂ = false := by
  simp only [SAT.Clause.eval, SAT.Lit.eval, List.foldl, hVar1True,
             Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hClauseEval
  exact hClauseEval

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The noIncompToSeq clause is in cnfSeq. -/
lemma noIncompToSeq_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants) :
    let ws := (WId.allWorlds b).filter (fun w => w.p = p)
    let incompLits := ws.flatMap fun w₁ => ws.map fun w₂ => SAT.Lit.pos (Var.Incomp H p w₁ w₂)
    (SAT.Lit.pos (Var.Seq H p) :: incompLits) ∈ (cnfSeq b).clauses := by
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  right; right; right; right
  simp only [List.mem_flatMap, List.mem_map, Bounds.timesL, Bounds.partsL]
  exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, rfl⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The incompFwd clause for ¬Acc(w₁,w₂,w₃) is in cnfSeq when w₃ is a valid witness. -/
lemma incompFwd_acc12_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ w₃ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hw₃p : w₃.p = w₁.p) (hw₃ei : w₃.ei = w₁.ei) :
    [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.neg (Var.Acc w₁ w₂ w₃)] ∈
    (cnfSeq b).clauses := by
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  right; left
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bounds.timesL, Bounds.partsL]
  refine ⟨(H, p, w₁, w₂), ?_, ?_⟩
  · exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
           ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
           ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩
  · rw [List.mem_append, List.mem_append, List.mem_append]
    right; left
    rw [List.mem_map]
    refine ⟨w₃, ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨WId.mem_allWorlds b w₃, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hw₃p, hw₃ei⟩

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The incompFwd clause for ¬Acc(w₂,w₁,w₃) is in cnfSeq when w₃ is a valid witness. -/
lemma incompFwd_acc21_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ w₃ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hw₃p : w₃.p = w₂.p) (hw₃ei : w₃.ei = w₂.ei) :
    [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.neg (Var.Acc w₂ w₁ w₃)] ∈
    (cnfSeq b).clauses := by
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  right; left
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bounds.timesL, Bounds.partsL]
  refine ⟨(H, p, w₁, w₂), ?_, ?_⟩
  · exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
           ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
           ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩
  · rw [List.mem_append, List.mem_append, List.mem_append]
    right; right; left
    rw [List.mem_map]
    refine ⟨w₃, ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨WId.mem_allWorlds b w₃, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hw₃p, hw₃ei⟩

/-! ### Acc definition clause membership -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The accDef forward clause `Acc → Mem` is in cnfSeq. -/
lemma accDef_mem_clause_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ w₃ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hw₃p : w₃.p = w₁.p) (hw₃ei : w₃.ei = w₁.ei) :
    [SAT.Lit.neg (Var.Acc w₁ w₂ w₃), SAT.Lit.pos (Var.Mem w₂.ti w₃)] ∈
    (cnfSeq b).clauses := by
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  left  -- accDef is first
  rw [List.mem_flatMap]
  refine ⟨(H, p, w₁, w₂), ?_, ?_⟩
  · -- Show (H, p, w₁, w₂) ∈ allPairs
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bounds.timesL, Bounds.partsL]
    exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
           ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
           ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩
  · -- Now show clause ∈ (accWitnesses w₁).flatMap (fun w₃ => [c1, c2, c3])
    rw [List.mem_flatMap]
    refine ⟨w₃, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨WId.mem_allWorlds b w₃, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hw₃p, hw₃ei⟩
    · -- clause ∈ [c1, c2, c3] where c1 = [¬Acc, Mem]
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      left
      trivial

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The accDef forward clause `Acc → PreEq` is in cnfSeq. -/
lemma accDef_preEq_clause_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ w₃ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hw₃p : w₃.p = w₁.p) (hw₃ei : w₃.ei = w₁.ei) :
    [SAT.Lit.neg (Var.Acc w₁ w₂ w₃), SAT.Lit.pos (Var.PreEq w₃.ti w₁.ti)] ∈
    (cnfSeq b).clauses := by
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  left  -- accDef is first
  rw [List.mem_flatMap]
  refine ⟨(H, p, w₁, w₂), ?_, ?_⟩
  · simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bounds.timesL, Bounds.partsL]
    exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
           ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
           ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩
  · -- Show clause in flatMap result
    rw [List.mem_flatMap]
    refine ⟨w₃, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨WId.mem_allWorlds b w₃, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hw₃p, hw₃ei⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false]
      right; left
      trivial

/-! ### Acc soundness lemmas -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If Acc(w₁,w₂,w₃) = true, then Mem(w₂.ti, w₃) = true. -/
lemma acc_implies_mem (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (H : b.times) (p : b.participants) (w₁ w₂ w₃ : WId b)
    (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hw₃p : w₃.p = w₁.p) (hw₃ei : w₃.ei = w₁.ei)
    (hAcc : σ (Var.Acc w₁ w₂ w₃) = true) :
    σ (Var.Mem w₂.ti w₃) = true := by
  have ⟨_, _, _, _, _, _, _, _, _, _, hSeqCNF⟩ :=
    (cnfWellFormed_eval_iff b σ).mp hWF
  have hAllSeq : (cnfSeq b).clauses.all (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hSeqCNF
  have hClause := (List.all_eq_true.mp hAllSeq) _
    (accDef_mem_clause_mem_cnfSeq b H p w₁ w₂ w₃ hp₁ hp₂ hw₃p hw₃ei)
  -- hClause : [¬Acc, Mem].eval = true
  -- With Acc = true, we get Mem = true
  rw [SAT.Clause.eval_eq_any] at hClause
  simp only [List.any_eq_true, SAT.Lit.eval, List.mem_cons, List.mem_nil_iff, or_false] at hClause
  obtain ⟨lit, hLitMem, hLitEval⟩ := hClause
  rcases hLitMem with hEq | hEq
  · subst hEq; simp [hAcc] at hLitEval
  · subst hEq; exact hLitEval

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If Acc(w₁,w₂,w₃) = true, then PreEq(w₃.ti, w₁.ti) = true. -/
lemma acc_implies_preEq (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (H : b.times) (p : b.participants) (w₁ w₂ w₃ : WId b)
    (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hw₃p : w₃.p = w₁.p) (hw₃ei : w₃.ei = w₁.ei)
    (hAcc : σ (Var.Acc w₁ w₂ w₃) = true) :
    σ (Var.PreEq w₃.ti w₁.ti) = true := by
  have ⟨_, _, _, _, _, _, _, _, _, _, hSeqCNF⟩ :=
    (cnfWellFormed_eval_iff b σ).mp hWF
  have hAllSeq : (cnfSeq b).clauses.all (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hSeqCNF
  have hClause := (List.all_eq_true.mp hAllSeq) _
    (accDef_preEq_clause_mem_cnfSeq b H p w₁ w₂ w₃ hp₁ hp₂ hw₃p hw₃ei)
  rw [SAT.Clause.eval_eq_any] at hClause
  simp only [List.any_eq_true, SAT.Lit.eval, List.mem_cons, List.mem_nil_iff, or_false] at hClause
  obtain ⟨lit, hLitMem, hLitEval⟩ := hClause
  rcases hLitMem with hEq | hEq
  · subst hEq; simp [hAcc] at hLitEval
  · subst hEq; exact hLitEval

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- The accDef backward clause `Mem ∧ PreEq → Acc` is in cnfSeq. -/
lemma accDef_back_clause_mem_cnfSeq (b : Bounds S) (H : b.times) (p : b.participants)
    (w₁ w₂ w₃ : WId b) (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hw₃p : w₃.p = w₁.p) (hw₃ei : w₃.ei = w₁.ei) :
    [SAT.Lit.neg (Var.Mem w₂.ti w₃), SAT.Lit.neg (Var.PreEq w₃.ti w₁.ti),
     SAT.Lit.pos (Var.Acc w₁ w₂ w₃)] ∈
    (cnfSeq b).clauses := by
  unfold cnfSeq
  simp only [List.append_assoc, List.mem_append]
  left  -- accDef is first
  rw [List.mem_flatMap]
  refine ⟨(H, p, w₁, w₂), ?_, ?_⟩
  · -- Show (H, p, w₁, w₂) ∈ allPairs
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bounds.timesL, Bounds.partsL]
    exact ⟨H, List.mem_finRange H, p, List.mem_finRange p, w₁,
           ⟨WId.mem_allWorlds b w₁, decide_eq_true hp₁⟩, w₂,
           ⟨WId.mem_allWorlds b w₂, decide_eq_true hp₂⟩, rfl⟩
  · -- Now show clause ∈ (accWitnesses w₁).flatMap (fun w₃ => [c1, c2, c3])
    rw [List.mem_flatMap]
    refine ⟨w₃, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨WId.mem_allWorlds b w₃, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hw₃p, hw₃ei⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false]
      right; right
      trivial

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Completeness for Acc: if Mem(w₂.ti, w₃) ∧ PreEq(w₃.ti, w₁.ti) hold,
    then Acc(w₁,w₂,w₃) = true. -/
lemma mem_preEq_implies_acc (b : Bounds S) (σ : SAT.Assignment (Var b)) (hWF : WF b σ)
    (H : b.times) (p : b.participants) (w₁ w₂ w₃ : WId b)
    (hp₁ : w₁.p = p) (hp₂ : w₂.p = p)
    (hw₃p : w₃.p = w₁.p) (hw₃ei : w₃.ei = w₁.ei)
    (hMem : σ (Var.Mem w₂.ti w₃) = true)
    (hPreEq : σ (Var.PreEq w₃.ti w₁.ti) = true) :
    σ (Var.Acc w₁ w₂ w₃) = true := by
  have ⟨_, _, _, _, _, _, _, _, _, _, hSeqCNF⟩ :=
    (cnfWellFormed_eval_iff b σ).mp hWF
  have hAllSeq : (cnfSeq b).clauses.all (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hSeqCNF
  have hClause := (List.all_eq_true.mp hAllSeq) _
    (accDef_back_clause_mem_cnfSeq b H p w₁ w₂ w₃ hp₁ hp₂ hw₃p hw₃ei)
  rw [SAT.Clause.eval_eq_any] at hClause
  simp only [List.any_eq_true, SAT.Lit.eval, List.mem_cons, List.mem_nil_iff, or_false] at hClause
  obtain ⟨lit, hLitMem, hLitEval⟩ := hClause
  rcases hLitMem with hEq | hEq | hEq
  · subst hEq; simp [hMem] at hLitEval
  · subst hEq; simp [hPreEq] at hLitEval
  · subst hEq; exact hLitEval

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If all pairs are world-comparable (via Acc or PreEq+event match), the Seq variable must be true.
    Uses the Tseytin encoding with Incomp and Acc witnesses.
    The hypothesis requires world-level comparability: for any two worlds w₁, w₂ with participant p
    that are both in H, they are comparable via Acc witnesses or (PreEq when events match).

    Note: The w₃ witness must be in accWitnesses (i.e., w₃.p = w₁.p ∧ w₃.ei = w₁.ei for acc12,
    or w₃.p = w₂.p ∧ w₃.ei = w₂.ei for acc21). This matches what seq_world_comparable provides. -/
lemma seq_from_sequential (b : Bounds S) (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) (H : b.times) (p : b.participants)
    (hCmpWorld : ∀ w₁ w₂ : WId b, w₁.p = p → w₂.p = p →
      σ (Var.Mem H w₁) = true → σ (Var.Mem H w₂) = true →
      (∃ w₃ ∈ accWitnesses b w₁, σ (Var.Acc w₁ w₂ w₃) = true) ∨
      (∃ w₃ ∈ accWitnesses b w₂, σ (Var.Acc w₂ w₁ w₃) = true) ∨
      (w₁.ei = w₂.ei ∧ σ (Var.PreEq w₁.ti w₂.ti) = true)) :
    σ (Var.Seq H p) = true := by
  classical
  have ⟨_, _, _, _, _, _, _, _, _, _, hSeqCNF⟩ :=
    (cnfWellFormed_eval_iff b σ).mp hWF
  have hAllSeq : (cnfSeq b).clauses.all (SAT.Clause.eval σ) = true := by
    simpa [SAT.CNF.eval] using hSeqCNF

  -- Get the noIncompToSeq clause evaluation
  have hNoIncompToSeqEval := (List.all_eq_true.mp hAllSeq) _ (noIncompToSeq_mem_cnfSeq b H p)

  -- Show all Incomp vars are false
  have hAllIncompFalse : ∀ w₁ w₂ : WId b, w₁.p = p → w₂.p = p →
      σ (Var.Incomp H p w₁ w₂) = false := by
    intro w₁ w₂ hp₁ hp₂
    by_contra hIncompTrue
    push_neg at hIncompTrue
    simp only [Bool.not_eq_false] at hIncompTrue

    -- From incompFwd: if Incomp = true, then Mem H w₁ = true and Mem H w₂ = true
    have hMem1 : σ (Var.Mem H w₁) = true :=
      mem_from_two_lit_clause σ _ _ hIncompTrue
        ((List.all_eq_true.mp hAllSeq) _ (incompFwd_mem1_mem_cnfSeq b H p w₁ w₂ hp₁ hp₂))

    have hMem2 : σ (Var.Mem H w₂) = true :=
      mem_from_two_lit_clause σ _ _ hIncompTrue
        ((List.all_eq_true.mp hAllSeq) _ (incompFwd_mem2_mem_cnfSeq b H p w₁ w₂ hp₁ hp₂))

    -- From hCmpWorld: since both are in H, they are comparable
    have hCmp := hCmpWorld w₁ w₂ hp₁ hp₂ hMem1 hMem2

    -- Case analysis on comparability - each case contradicts incompFwd clauses
    rcases hCmp with ⟨w₃, hw₃mem, hAcc12⟩ | ⟨w₃, hw₃mem, hAcc21⟩ | ⟨hEvEq, hPreEq⟩
    · -- Case: Acc(w₁, w₂, w₃) = true contradicts incompFwd clause Incomp → ¬Acc
      -- hw₃mem : w₃ ∈ accWitnesses b w₁, which means w₃.p = w₁.p ∧ w₃.ei = w₁.ei
      simp only [accWitnesses, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hw₃mem
      obtain ⟨_, hw₃p, hw₃ei⟩ := hw₃mem
      have hNotAcc : σ (Var.Acc w₁ w₂ w₃) = false :=
        negVar_from_two_lit_clause σ _ _ hIncompTrue
          ((List.all_eq_true.mp hAllSeq) _
            (incompFwd_acc12_mem_cnfSeq b H p w₁ w₂ w₃ hp₁ hp₂ hw₃p hw₃ei))
      simp [hAcc12] at hNotAcc
    · -- Case: Acc(w₂, w₁, w₃) = true - symmetric argument
      simp only [accWitnesses, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hw₃mem
      obtain ⟨_, hw₃p, hw₃ei⟩ := hw₃mem
      have hNotAcc : σ (Var.Acc w₂ w₁ w₃) = false :=
        negVar_from_two_lit_clause σ _ _ hIncompTrue
          ((List.all_eq_true.mp hAllSeq) _
            (incompFwd_acc21_mem_cnfSeq b H p w₁ w₂ w₃ hp₁ hp₂ hw₃p hw₃ei))
      simp [hAcc21] at hNotAcc
    · -- Case: events match and PreEq = true
      have hNotPreEq : σ (Var.PreEq w₁.ti w₂.ti) = false :=
        negVar_from_two_lit_clause σ _ _ hIncompTrue
          ((List.all_eq_true.mp hAllSeq) _ (incompFwd_preEq_mem_cnfSeq b H p w₁ w₂ hp₁ hp₂ hEvEq))
      simp [hPreEq] at hNotPreEq

  -- Clause: Seq ∨ Incomp₁ ∨ Incomp₂ ∨ ... evaluates to true
  -- Since all Incomp are false, Seq must be true
  rw [SAT.Clause.eval_eq_any] at hNoIncompToSeqEval
  simp only [List.any_eq_true, SAT.Lit.eval, List.mem_cons] at hNoIncompToSeqEval
  obtain ⟨lit, hLitMem, hLitEval⟩ := hNoIncompToSeqEval
  rcases hLitMem with hEq | hIncompMem
  · -- lit = SAT.Lit.pos (Var.Seq H p)
    subst hEq; exact hLitEval
  · -- lit is some Incomp literal - but all Incomps are false
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hIncompMem
    obtain ⟨w₁, ⟨_, hp₁'⟩, w₂, ⟨_, hp₂'⟩, hEq⟩ := hIncompMem
    subst hEq
    have := hAllIncompFalse w₁ w₂ (of_decide_eq_true hp₁') (of_decide_eq_true hp₂')
    simp [this] at hLitEval

end Encoding
