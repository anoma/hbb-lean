import ModalDistribution.Logic.Syntax
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var

/-!
# SAT Encoding Types

This file defines the core types needed for formula encoding and model checking:
- `Assumption`: What to check (end-valid vs all-world-valid)
- `FVar`: Fresh variables for Tseytin transformation
- `EncState`: Stateful encoding with clause accumulation

## References
- Plan.md sections on Formula Encoding and Assumption Encoding
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}

/-! ## Assumptions -/

/-- Model checking assumption: what property to verify.

Two modes:
- `endFormula φ`: Check φ at the end of history (all participants, † event, root time)
- `worldFormula φ`: Check φ at ALL reachable worlds (gated by ReachT)

See Plan.md "Assumption Encoding" section for encoding strategy. -/
inductive Assumption (S : Signature) : Type 1 where
  | endFormula : Formula S → Assumption S
  | worldFormula : Formula S → Assumption S

/-! ## Tseytin Encoding State -/

/-- Fresh variable identifier for Tseytin transformation.

Each subformula gets allocated a unique control variable during encoding.
The `id` field distinguishes formula variables from structural variables (Var b). -/
structure FVar (b : Bounds S) where
  /-- Unique identifier for this formula control variable. -/
  id : Nat
deriving DecidableEq, Repr

namespace FVar

variable (b : Bounds S)

/-- Convert formula variable to SAT variable.

Formula control variables use the dedicated Var.Fresh constructor, keeping them
separate from semantic variables (Mem, Pred, etc.) for clean adequacy proofs. -/
@[inline] def toVar (fv : FVar b) : Var b :=
  Var.Fresh fv.id

end FVar

/-- Cache key for prehistory equality builders. -/
abbrev PreEqKey (b : Bounds S) :=
  b.times × b.times

/-- Encoding state for Tseytin transformation.

Maintains:
- `nextFresh`: Counter for allocating fresh FVars
- `clauses`: Accumulated CNF clauses during encoding

Pattern: recursive encoding returns (control_var, updated_state). -/
structure EncState (b : Bounds S) where
  /-- Next available fresh variable ID. -/
  nextFresh : Nat
  /-- Accumulated CNF clauses. -/
  clauses : List (SAT.Clause (Var b))

namespace EncState

variable (b : Bounds S)

/-- Initial encoding state with no clauses. -/
def empty : EncState b :=
  { nextFresh := 0, clauses := [] }

/-- Allocate a fresh formula variable. -/
def allocFresh (st : EncState b) : FVar b × EncState b :=
  let fv := { id := st.nextFresh : FVar b }
  let st' := { st with nextFresh := st.nextFresh + 1 }
  (fv, st')

/-- Add a clause to the encoding state. -/
def addClause (st : EncState b) (clause : SAT.Clause (Var b)) : EncState b :=
  { st with clauses := clause :: st.clauses }

/-- Add multiple clauses to the encoding state. -/
def addClauses (st : EncState b) (newClauses : List (SAT.Clause (Var b))) : EncState b :=
  { st with clauses := newClauses ++ st.clauses }

/-- Extract the accumulated CNF formula. -/
def toCNF (st : EncState b) : SAT.CNF (Var b) :=
  SAT.CNF.mk st.clauses

lemma allocFresh_clauses_eq (st : EncState b) :
    (EncState.allocFresh b st).2.clauses = st.clauses := by
  simp [EncState.allocFresh]

lemma allocFresh_fst (st : EncState b) :
    (EncState.allocFresh b st).1.id = st.nextFresh := by
  simp [EncState.allocFresh]

lemma addClause_subset_clauses (st : EncState b) (clause : SAT.Clause (Var b)) :
    st.clauses ⊆ (EncState.addClause b st clause).clauses := by
  intro C hC
  simp [EncState.addClause, hC]

lemma addClause_clauses_eq (st : EncState b) (clause : SAT.Clause (Var b)) :
    (EncState.addClause b st clause).clauses = clause :: st.clauses := by
  simp [EncState.addClause]

lemma addClauses_subset_clauses (st : EncState b) (newClauses : List (SAT.Clause (Var b))) :
    st.clauses ⊆ (EncState.addClauses b st newClauses).clauses := by
  intro C hC
  simp [EncState.addClauses, List.mem_append, hC]

lemma addClause_length_le (st : EncState b) (c : SAT.Clause (Var b)) :
    st.clauses.length ≤ (EncState.addClause b st c).clauses.length := by
  simp [EncState.addClause]

lemma allocFresh_length_le (st : EncState b) :
    st.clauses.length ≤ (EncState.allocFresh b st).2.clauses.length := by
  simp [EncState.allocFresh]

lemma allocFresh_nextFresh (st : EncState b) :
    (EncState.allocFresh b st).2.nextFresh = st.nextFresh + 1 := by
  simp [EncState.allocFresh]

lemma addClause_nextFresh (st : EncState b) (clause : SAT.Clause (Var b)) :
    (EncState.addClause b st clause).nextFresh = st.nextFresh := by
  simp [EncState.addClause]

lemma addClauses_nextFresh (st : EncState b) (newClauses : List (SAT.Clause (Var b))) :
    (EncState.addClauses b st newClauses).nextFresh = st.nextFresh := by
  simp [EncState.addClauses]

end EncState

/-! ## Well-formedness for EncState

The well-formedness invariant: all Fresh variables appearing in clauses have
index less than nextFresh. This ensures that extending the assignment to a
newly-allocated Fresh variable doesn't affect existing clause satisfaction. -/

/-- A literal is "below" a Fresh index if any Fresh var has index < that bound. -/
def litFreshBelow {S : Signature} {b : Bounds S} (lit : SAT.Lit (Var b)) (bound : Nat) : Prop :=
  match lit.getVar with
  | Var.Fresh n => n < bound
  | _ => True

/-- A clause has all Fresh vars below a bound. -/
def clauseFreshBelow {S : Signature} {b : Bounds S}
  (clause : SAT.Clause (Var b)) (bound : Nat) : Prop :=
  ∀ lit ∈ clause, litFreshBelow lit bound

/-- An EncState is well-formed if all Fresh vars in clauses have index < nextFresh. -/
def EncState.WellFormed {S : Signature} {b : Bounds S} (st : EncState b) : Prop :=
  ∀ clause ∈ st.clauses, clauseFreshBelow clause st.nextFresh

/-- The empty encoding state is well-formed. -/
lemma EncState.empty_wf {S : Signature} {b : Bounds S} :
  EncState.WellFormed (EncState.empty b) := by
  unfold EncState.WellFormed EncState.empty
  intro clause hClause
  simp at hClause

/-- Well-formedness is preserved when nextFresh increases (without adding clauses). -/
lemma EncState.WellFormed.of_nextFresh_le {S : Signature} {b : Bounds S} {st1 st2 : EncState b}
    (hwf : EncState.WellFormed st1)
    (hClauses : st2.clauses = st1.clauses)
    (hLE : st1.nextFresh ≤ st2.nextFresh) :
    EncState.WellFormed st2 := by
  unfold EncState.WellFormed clauseFreshBelow litFreshBelow at hwf ⊢
  intro clause hClause lit hLit
  rw [hClauses] at hClause
  specialize hwf clause hClause lit hLit
  cases h : lit.getVar with
  | Fresh n =>
      simp only [h] at hwf ⊢
      exact Nat.lt_of_lt_of_le hwf hLE
  | _ => trivial

/-- allocFresh preserves well-formedness. -/
lemma EncState.allocFresh_wf {S : Signature} {b : Bounds S} {st : EncState b}
    (hwf : EncState.WellFormed st) :
    EncState.WellFormed (EncState.allocFresh b st).2 := by
  apply hwf.of_nextFresh_le
  · exact EncState.allocFresh_clauses_eq b st
  · simp [EncState.allocFresh_nextFresh]

/-- addClause preserves well-formedness if the new clause has Fresh vars below nextFresh. -/
lemma EncState.addClause_wf {S : Signature} {b : Bounds S} {st : EncState b}
    (hwf : EncState.WellFormed st)
    (clause : SAT.Clause (Var b))
    (hClause : clauseFreshBelow clause st.nextFresh) :
    EncState.WellFormed (EncState.addClause b st clause) := by
  unfold EncState.WellFormed at hwf ⊢
  intro c hC
  simp only [EncState.addClause] at hC ⊢
  cases hC with
  | head => exact hClause
  | tail _ hTail => exact hwf c hTail

/-- addClauses preserves well-formedness if all new clauses have Fresh vars below nextFresh. -/
lemma EncState.addClauses_wf {S : Signature} {b : Bounds S} {st : EncState b}
    (hwf : EncState.WellFormed st)
    (newClauses : List (SAT.Clause (Var b)))
    (hNew : ∀ c ∈ newClauses, clauseFreshBelow c st.nextFresh) :
    EncState.WellFormed (EncState.addClauses b st newClauses) := by
  unfold EncState.WellFormed at hwf ⊢
  intro c hC
  simp only [EncState.addClauses] at hC ⊢
  rw [List.mem_append] at hC
  cases hC with
  | inl h => exact hNew c h
  | inr h => exact hwf c h

/-- Key lemma: if st is well-formed and n = st.nextFresh, then Fresh n
    cannot appear in any literal in st.clauses. -/
lemma EncState.WellFormed.fresh_not_in_clauses {S : Signature} {b : Bounds S} {st : EncState b}
    (hwf : EncState.WellFormed st)
    {clause : SAT.Clause (Var b)} (hClause : clause ∈ st.clauses)
    {lit : SAT.Lit (Var b)} (hLit : lit ∈ clause) :
    lit.getVar ≠ Var.Fresh st.nextFresh := by
  intro hEq
  unfold EncState.WellFormed clauseFreshBelow litFreshBelow at hwf
  have h := hwf clause hClause lit hLit
  simp only [hEq] at h
  exact Nat.lt_irrefl st.nextFresh h

/-- If st is well-formed and lit is a Fresh n var in st.clauses, then n < st.nextFresh. -/
lemma EncState.WellFormed.fresh_lt_nextFresh {S : Signature} {b : Bounds S} {st : EncState b}
    (hwf : EncState.WellFormed st)
    (clause : SAT.Clause (Var b)) (hClause : clause ∈ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ clause)
    (n : Nat) (hFresh : lit.getVar = Var.Fresh n) :
    n < st.nextFresh := by
  unfold EncState.WellFormed clauseFreshBelow litFreshBelow at hwf
  have h := hwf clause hClause lit hLit
  simp only [hFresh] at h
  exact h

end Encoding
