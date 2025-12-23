import Mathlib.Data.Finset.Basic
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Bitmask.Core

/-!
# SAT Variables for Model Checking

This file defines the propositional variables used in the CNF encoding of modal logic
formulas and model constraints.

## Variable Types

The encoding uses several types of Boolean variables:

### Structural Variables (History Well-Formedness)
- `Mem(H, w)`: World `w` is a member of prehistory `H`
- `Level(ti, j)`: Fuel level for time `ti` is at least `j` (monotone prefix)
- `Edge(H, H')`: There exists a world in `H` with time component `H'`

### Semantic Variables
- `Pred(p, ti, k)`: Predicate `k` holds for participant `p` at time `ti`

### Learner Variables (Semifilter)
- `MinQ(v, Q)`: Quorum `Q` is a minimal quorum for value `v`

### Reachability Variables (for AllWorldValid)
- `ReachT(H)`: Time index `H` is reachable from root via happens-before

## Design Notes

- All variables are indexed by finite types (`Fin n`)
- `DecidableEq` derivation allows use in CNF constraints
- The `Repr` derivation is helpful for debugging

-/

open ModalDistribution

namespace Encoding

variable {S : Signature}

/-- Propositional variables for the SAT encoding.
    Each constructor represents a different type of Boolean variable in the CNF. -/
inductive Var (b : Bounds S) : Type where
  /-- World membership: `Mem(H, w)` means world `w` ∈ prehistory at index `H`. -/
  | Mem : b.times → WId b → Var b

  /-- Fuel level: `Level(ti, j)` means fuel for time `ti` is at least `j`.
      Encoded using prefix-closed (monotone) levels without uniqueness constraints.
      Used to align decoder fuel with semantic time comparisons. -/
  | Level : b.times → Fin (b.nTimes.succ) → Var b

  /-- Predicate truth table: `Pred(p, ti, k)` means predicate `k` holds
      for participant `p` at time index `ti`. -/
  | Pred : b.participants → b.times → b.predIx → Var b

  /-- Minimal quorum selector: `MinQ(v, Q)` means `Q` is a minimal quorum for value `v`. -/
  | MinQ : b.valIx → Finset b.participants → Var b

  /-- Time reachability: `ReachT(H)` means time index `H` is reachable from root
      via the happens-before relation. -/
  | ReachT : b.times → Var b

  /-- Edge aggregation: `Edge(H, H')` means there exists some world `w` in `Mem(H, w)`
      where `w.ti = H'`. Used for hereditary transitivity encoding. -/
  | Edge : b.times → b.times → Var b

  /-- Fresh Tseytin variable: `Fresh(id)` is a control variable for formula encoding.
      These are allocated during Tseytin transformation and represent subformula truth.
      Kept separate from semantic variables (Mem, Pred, etc.) for clean adequacy proofs. -/
  | Fresh : Nat → Var b

  /-- Existence aggregator: `Exists(H, p, t)` means there exists some world w with
      Mem(H,w) ∧ Place(w,p) ∧ Time(w,t). -/
  | Exists : b.times → b.participants → b.times → Var b
  /-- Canonical prehistory equality flag: `PreEq(H, H')` holds when all worlds
      agree on membership in both prehistories. -/
  | PreEq : b.times → b.times → Var b
  /-- Sequentiality control: `Seq(H, p)` means all worlds with participant p in
      prehistory H are totally ordered by happens-before. -/
  | Seq : b.times → b.participants → Var b

  /-- Representative index selector: `Rep(vIdx)` means value index `vIdx` is the
      canonical representative for its value equivalence class.
      Used to handle duplicate values in b.values by selecting one index per semantic value. -/
  | Rep : b.valIx → Var b

  /-- Incomparability witness: `Incomp(H, p, w₁, w₂)` means pair (w₁, w₂) witnesses
      non-sequentiality at (H, p). True iff both worlds are in H but neither is
      in the other's time prehistory.
      Used for full Tseytin encoding of Seq ↔ (all pairs comparable). -/
  | Incomp : b.times → b.participants → WId b → WId b → Var b

  /-- Accessibility witness: `Acc(w₁, w₂, w₃)` means w₃ witnesses that w₁ is accessible from w₂.
      True iff Mem(w₂.ti, w₃) ∧ PreEq(w₃.ti, w₁.ti), where w₃ has same place/event as w₁.
      The semantic accessibility relation is: Acc(w₁,w₂) = ⋁_{w₃} Acc(w₁,w₂,w₃).
      Used for membership-based sequentiality encoding. -/
  | Acc : WId b → WId b → WId b → Var b
deriving DecidableEq

-- Note: Repr derivation is omitted because MinQ contains Finset which has unsafe Repr

namespace Var

variable {b : Bounds S}

/-! ## Variable Categories

These functions help categorize variables by their purpose, useful for
analysis and optimization.
-/

/-- Check if a variable is structural (history well-formedness). -/
def isStructural : Var b → Bool
  | Mem _ _         => true
  | Level _ _       => true
  | Pred _ _ _      => false
  | MinQ _ _        => false
  | ReachT _        => false
  | Edge _ _        => true
  | Fresh _         => false
  | Exists _ _ _    => false
  | PreEq _ _       => true
  | Seq _ _         => false
  | Rep _           => false
  | Incomp _ _ _ _  => false
  | Acc _ _ _       => false

/-- Check if a variable is semantic (formula evaluation). -/
def isSemantic : Var b → Bool
  | Pred _ _ _ => true
  | _          => false

-- Note: Seq is both semantic (represents .seq formula) and structural (enforces ordering)
-- We categorize it as sequentiality for clarity

/-- Check if a variable is related to learners/semifilters. -/
def isLearner : Var b → Bool
  | MinQ _ _ => true
  | Rep _    => true
  | _        => false

/-- Check if a variable is related to reachability. -/
def isReachability : Var b → Bool
  | ReachT _ => true
  | _        => false

/-- Check if a variable is a transitivity optimization variable. -/
def isTransitivityOpt : Var b → Bool
  | Edge _ _    => true
  | _           => false

/-- Check if a variable is a sequentiality-related variable. -/
def isSequentiality : Var b → Bool
  | Exists _ _ _    => true
  | Seq _ _         => true
  | Incomp _ _ _ _  => true
  | Acc _ _ _       => true
  | _               => false

/-- Check if a variable is a fresh Tseytin variable (allocated during formula encoding). -/
def isFresh : Var b → Bool
  | Fresh _ => true
  | _       => false

end Var

/-- Predicate version of isFresh for use in theorem statements. -/
def isFreshVar {b : Bounds S} (v : Var b) : Prop := v.isFresh = true

/-! ## Variable Enumeration Helpers

These functions enumerate all variables of a particular type, useful for
generating constraints that quantify over all variables of a kind.
-/

namespace Var

variable (b : Bounds S)

/-- Enumerate all `Mem` variables. -/
def allMem : List (Var b) :=
  (Bounds.timesL b).flatMap fun H =>
    (WId.allWorlds b).map fun w =>
      Var.Mem H w

/-- Enumerate all `Pred` variables. -/
def allPred : List (Var b) :=
  (Bounds.partsL b).flatMap fun p =>
    (Bounds.timesL b).flatMap fun ti =>
      (Bounds.predIxL b).map fun k =>
        Var.Pred p ti k

/-- Enumerate all `MinQ` variables for a given value index using bitmask enumeration.
    Used in `cnfLearners` to generate constraints over all possible quorums.

    This is computable (unlike `Finset.powerset.toList`) and provides deterministic
    ordering for stable DIMACS export. Each subset is represented by a bitmask where
    bit i indicates whether participant i is in the quorum. -/
def allMinQ (b : Bounds S) (v : b.valIx) : List (Var b) :=
  let nParts := b.nParticipants
  let numSubsets := Nat.shiftLeft 1 nParts  -- 2^nParts
  (List.finRange numSubsets).map fun mask =>
    Var.MinQ v (Encoding.bitmaskToFinset nParts mask.val)

/-- Enumerate all `ReachT` variables. -/
def allReachT : List (Var b) :=
  (Bounds.timesL b).map fun H =>
    Var.ReachT H

/-- Enumerate all `Edge` variables. -/
def allEdge : List (Var b) :=
  (Bounds.timesL b).flatMap fun H =>
    (Bounds.timesL b).map fun H' =>
      Var.Edge H H'

/-- Enumerate all `Level` variables for a given time index. -/
def allLevel (ti : b.times) : List (Var b) :=
  List.finRange (b.nTimes.succ) |>.map fun j =>
    Var.Level ti j

end Var

end Encoding

namespace Encoding

variable {S : Signature}

/-! ## Fuel Level Decoder -/

/-- Read the largest j with Level(ti,j)=true; if none, return 0.
    This implements the max-level decoding for per-time fuel. -/
def fuelOf (b : Bounds S) (σ : SAT.Assignment (Var b)) (ti : b.times) : Nat :=
  let js := List.finRange (b.nTimes.succ) |>.reverse
  match js.find? (fun j => σ (Var.Level ti j) = true) with
  | some j => j.val
  | none   => 0

end Encoding
