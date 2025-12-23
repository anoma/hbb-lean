import ModalDistribution.Core.Prehistory
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.PreEqEncoding

/-!
# Assumption Encoding

This file provides semantic predicates and the top-level encoding interface
for the SAT-based model checker. It includes predicates for checking if
assumptions hold in a decoded prehistory, and the main public API for
building complete SAT encodings.

## Main Components

### Section 1: Semantic Predicates
- `assumptionHolds`: Check if a single assumption holds in a prehistory
- `assumptionsHold`: Check if all assumptions in a list hold

### Section 2: Assumption Encoding
- `encodeEnd`: Encode end-of-prehistory constraint
- `encodeAllWorld`: Encode a formula for all world IDs
- `encodeΓ`: Encode assumption list as implications
- `encodeAssumptions`: Top-level assumption encoding
- `assumptions`: Public API for building complete encodings

## Dependencies

This is the top-level module in the encoding stack:
- Imports `FormulaEncoding` which provides the main formula encoder
- `FormulaEncoding` imports `PreEqEncoding` for prehistory equality
- `PreEqEncoding` imports `TseytinGadgets` for CNF utilities

## References

See CLAUDE.md and the user's specification for the complete architecture.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-! ## Semantic Predicates -/

/-- A model satisfies an assumption if the corresponding formula holds
    at the appropriate locations.
    - `endFormula φ`: φ must hold at the end of time (root prehistory)
    - `worldFormula φ`: φ must hold at all worlds in the model -/
def assumptionHolds {P : Type} [Nonempty P] (M : Model S P) (a : Assumption S) : Prop :=
  match a with
  | .endFormula φ => EndValid M φ
  | .worldFormula φ => AllWorldValid M φ

/-- A list of assumptions holds if all individual assumptions holds. -/
def assumptionsHold {P : Type} [Nonempty P] (M : Model S P) (Γ : List (Assumption S)) : Prop :=
  ∀ a ∈ Γ, assumptionHolds M a

/-- Encode an assumption that must hold at the end of time for all participants. -/
def encodeEndStep (b : Bounds S) (φ : Formula S)
    (st : EncState b) (p : b.participants) : EncState b :=
  let wEnd : WId b := ⟨p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩
  let (u, st') := encodeFormula b φ wEnd st
  EncState.addClause b st' [SAT.Lit.pos (FVar.toVar b u)]

def encodeEnd (b : Bounds S) (φ : Formula S) (st : EncState b) : EncState b :=
  (Bounds.partsL b).foldl (encodeEndStep b φ) st

lemma encodeEndStep_clauses_subset (b : Bounds S) (φ : Formula S)
    (st : EncState b) (p : b.participants) :
    st.clauses ⊆ (encodeEndStep b φ st p).clauses := by
  classical
  unfold encodeEndStep
  set wEnd := (⟨p, ⟨0, Nat.zero_lt_succ _⟩, b.root⟩ : WId b)
  set res := encodeFormula b φ wEnd st
  have hSubset : st.clauses ⊆ res.2.clauses := encodeFormula_clauses_subset b φ wEnd st
  intro clause hClause
  have hClause' : clause ∈ res.2.clauses := hSubset hClause
  exact EncState.addClause_subset_clauses b res.2 [SAT.Lit.pos (FVar.toVar b res.1)] hClause'

lemma encodeEnd_clauses_subset (b : Bounds S) (φ : Formula S) (st : EncState b) :
    st.clauses ⊆ (encodeEnd b φ st).clauses := by
  classical
  refine
    foldl_subset_state
      (b := b)
      (f := encodeEndStep b φ)
      (hStep := fun stAcc p => encodeEndStep_clauses_subset b φ stAcc p)
      (xs := Bounds.partsL b)
      (init := st)

def encodeAllWorldStep (b : Bounds S) (φ : Formula S)
    (st : EncState b) (w : WId b) : EncState b :=
  let (u, st') := encodeFormula b φ w st
  EncState.addClause b st'
    [SAT.Lit.neg (Var.ReachT w.ti), SAT.Lit.pos (FVar.toVar b u)]

/-- Encode an assumption that must hold at every reachable world. -/
def encodeAllWorld (b : Bounds S) (φ : Formula S) (st : EncState b) : EncState b :=
  (WId.allWorlds b).foldl (encodeAllWorldStep b φ) st

lemma encodeAllWorldStep_clauses_subset (b : Bounds S) (φ : Formula S)
    (st : EncState b) (w : WId b) :
    st.clauses ⊆ (encodeAllWorldStep b φ st w).clauses := by
  classical
  unfold encodeAllWorldStep
  set res := encodeFormula b φ w st
  have hSubset : st.clauses ⊆ res.2.clauses := encodeFormula_clauses_subset b φ w st
  intro clause hClause
  have hClause' : clause ∈ res.2.clauses := hSubset hClause
  exact EncState.addClause_subset_clauses b res.2
    [SAT.Lit.neg (Var.ReachT w.ti), SAT.Lit.pos (FVar.toVar b res.1)]
    hClause'

lemma encodeAllWorld_clauses_subset (b : Bounds S) (φ : Formula S) (st : EncState b) :
    st.clauses ⊆ (encodeAllWorld b φ st).clauses := by
  classical
  refine
    foldl_subset_state
      (b := b)
      (f := encodeAllWorldStep b φ)
      (hStep := fun stAcc w => encodeAllWorldStep_clauses_subset b φ stAcc w)
      (xs := WId.allWorlds b)
      (init := st)

/-- Encode a list of assumptions by threading the encoding state. -/
def encodeΓ (b : Bounds S) : List (Assumption S) → EncState b → EncState b
  | [],      st => st
  | a :: Γ', st =>
      let st' :=
        match a with
        | .endFormula φ   => encodeEnd b φ st
        | .worldFormula φ => encodeAllWorld b φ st
      encodeΓ b Γ' st'

/-- Clauses only accumulate while encoding assumptions. -/
lemma encodeΓ_clauses_subset (b : Bounds S) :
    ∀ Γ (st : EncState b),
      st.clauses ⊆ (encodeΓ b Γ st).clauses
  | [],      st => by
      intro clause hClause
      simpa using hClause
  | a :: Γ', st => by
      classical
      cases a with
      | endFormula φ =>
          have hStep : st.clauses ⊆ (encodeEnd b φ st).clauses :=
            encodeEnd_clauses_subset b φ st
          have hTail := encodeΓ_clauses_subset b Γ' (encodeEnd b φ st)
          intro clause hClause
          exact hTail (hStep hClause)
      | worldFormula φ =>
          have hStep : st.clauses ⊆ (encodeAllWorld b φ st).clauses :=
            encodeAllWorld_clauses_subset b φ st
          have hTail := encodeΓ_clauses_subset b Γ' (encodeAllWorld b φ st)
          intro clause hClause
          exact hTail (hStep hClause)

/-- Top-level encoding returning both CNF and final state.
    The state contains the nextFresh counter needed for variable enumeration. -/
def encodeAssumptionsWithState (b : Bounds S) (Γ : List (Assumption S)) :
    SAT.CNF (Var b) × EncState b :=
  let st := encodeΓ b Γ (EncState.empty b)
  let stWithPreEq := addPreEqAll b st
  (SAT.CNF.band [cnfWellFormed b, SAT.CNF.mk stWithPreEq.clauses], stWithPreEq)

/-- Top-level encoding for structural constraints and assumptions.
    Adds PreEq clauses once at the end for soundness of Seq and Event encodings. -/
def encodeAssumptions (b : Bounds S) (Γ : List (Assumption S)) : SAT.CNF (Var b) :=
  (encodeAssumptionsWithState b Γ).1

/-- A satisfying assignment for the assumptions CNF. -/
def assumptions (b : Bounds S) (σ : SAT.Assignment (Var b)) (Γ : List (Assumption S)) : Prop :=
  (encodeAssumptions b Γ).eval σ = true

end Encoding
