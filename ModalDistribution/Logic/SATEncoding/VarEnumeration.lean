import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Types
import Mathlib.Data.List.Basic
import Std.Data.HashMap

/-!
# Variable Enumeration for DIMACS Export

This file provides bidirectional mapping between `Var b` and DIMACS integer indices.

## Main Definitions

- `enumerateVars`: List all variables in deterministic order
- `VarMapping`: Bidirectional mapping with proven invariants
- `mkVarMapping`: Construct mapping from encoding state

## Design Notes

- DIMACS uses 1-based indices (variable 0 is invalid)
- Variables are enumerated in a fixed order for deterministic output
- `Fresh` variables are bounded by `st.nextFresh` from encoding state
- `MinQ` variables enumerate all 2^nParticipants finsets per value index
-/

open ModalDistribution

namespace Encoding

variable {S : Signature}

/-! ## Additional Enumeration Helpers -/

namespace Var

variable (b : Bounds S)

/-- Enumerate all `Level` variables across all time indices. -/
def allLevelFull : List (Var b) :=
  (Bounds.timesL b).flatMap fun ti =>
    (List.finRange (b.nTimes.succ)).map fun j =>
      Var.Level ti j

/-- Enumerate all `Exists` variables. -/
def allExists : List (Var b) :=
  (Bounds.timesL b).flatMap fun H =>
    (Bounds.partsL b).flatMap fun p =>
      (Bounds.timesL b).map fun t =>
        Var.Exists H p t

/-- Enumerate all `PreEq` variables. -/
def allPreEq : List (Var b) :=
  (Bounds.timesL b).flatMap fun H =>
    (Bounds.timesL b).map fun H' =>
      Var.PreEq H H'

/-- Enumerate all `Seq` variables. -/
def allSeq : List (Var b) :=
  (Bounds.timesL b).flatMap fun H =>
    (Bounds.partsL b).map fun p =>
      Var.Seq H p

/-- Enumerate all `Rep` variables. -/
def allRep : List (Var b) :=
  (Bounds.valIxL b).map fun v =>
    Var.Rep v

/-- Enumerate all `MinQ` variables across all value indices. -/
def allMinQFull : List (Var b) :=
  (Bounds.valIxL b).flatMap fun v =>
    allMinQ b v

/-- Enumerate `Fresh` variables from 0 to maxFresh-1. -/
def allFresh (maxFresh : Nat) : List (Var b) :=
  (List.range maxFresh).map fun id =>
    Var.Fresh id

/-- Enumerate all `Incomp` variables (incomparability witnesses for sequentiality). -/
def allIncomp : List (Var b) :=
  (Bounds.timesL b).flatMap fun H =>
    (Bounds.partsL b).flatMap fun p =>
      let ws := (WId.allWorlds b).filter (fun w => w.p = p)
      ws.flatMap fun w₁ =>
        ws.map fun w₂ =>
          Var.Incomp H p w₁ w₂

/-- Enumerate all `Acc` variables (accessibility witnesses for sequentiality). -/
def allAcc : List (Var b) :=
  (WId.allWorlds b).flatMap fun w₁ =>
    (WId.allWorlds b).flatMap fun w₂ =>
      (WId.allWorlds b).map fun w₃ =>
        Var.Acc w₁ w₂ w₃

end Var

/-! ## Complete Variable Enumeration -/

/-- Enumerate all variables in deterministic order. -/
def enumerateVars (b : Bounds S) (maxFresh : Nat) : List (Var b) :=
  Var.allMem b ++
  Var.allLevelFull b ++
  Var.allEdge b ++
  Var.allReachT b ++
  Var.allPreEq b ++
  Var.allPred b ++
  Var.allExists b ++
  Var.allSeq b ++
  Var.allMinQFull b ++
  Var.allRep b ++
  Var.allIncomp b ++
  Var.allAcc b ++
  Var.allFresh b maxFresh

/-! ## Variable Mapping -/

/-- Find index of element in list using recursion. Returns list length if not found.
    DEPRECATED: Use VarMapping.toIndex instead which uses O(1) HashMap lookup. -/
def findVarIndex {S : Signature} {b : Bounds S} (vars : List (Var b)) (v : Var b) : Nat :=
  match vars with
  | [] => 0  -- Not found, will be handled by caller
  | x :: xs => if x = v then 0 else 1 + findVarIndex xs v

/-! ## Hashable instances for Var components -/

/-- Hash for WId using component hashes. -/
instance {S : Signature} {b : Bounds S} : Hashable (WId b) where
  hash w := mixHash (hash w.p) (mixHash (hash w.ei) (hash w.ti))

/-- Convert Finset to bitmask for hashing.
    Uses the existing `finsetToBitmask` function from Bitmask.Core. -/
private def finsetHashNat {n : Nat} (s : Finset (Fin n)) : Nat :=
  Encoding.finsetToBitmask s

/-- Hash for Finset using bitmask representation. -/
instance {n : Nat} : Hashable (Finset (Fin n)) where
  hash s := hash (finsetHashNat s)

/-- Hash for Var using constructor tags and component hashes. -/
instance {S : Signature} {b : Bounds S} : Hashable (Var b) where
  hash v := match v with
    | .Mem H w => mixHash 0 (mixHash (hash H) (hash w))
    | .Level ti j => mixHash 1 (mixHash (hash ti) (hash j))
    | .Pred p ti k => mixHash 2 (mixHash (hash p) (mixHash (hash ti) (hash k)))
    | .MinQ v Q => mixHash 3 (mixHash (hash v) (hash Q))
    | .ReachT H => mixHash 4 (hash H)
    | .Edge H H' => mixHash 5 (mixHash (hash H) (hash H'))
    | .Fresh id => mixHash 6 (hash id)
    | .Exists H p t => mixHash 7 (mixHash (hash H) (mixHash (hash p) (hash t)))
    | .PreEq H H' => mixHash 8 (mixHash (hash H) (hash H'))
    | .Seq H p => mixHash 9 (mixHash (hash H) (hash p))
    | .Rep v => mixHash 10 (hash v)
    | .Incomp H p w₁ w₂ =>
        mixHash 11 (mixHash (hash H) (mixHash (hash p) (mixHash (hash w₁) (hash w₂))))
    | .Acc w₁ w₂ w₃ => mixHash 12 (mixHash (hash w₁) (mixHash (hash w₂) (hash w₃)))

/-- BEq for Var using DecidableEq. -/
instance {S : Signature} {b : Bounds S} : BEq (Var b) where
  beq v1 v2 := v1 = v2

/-- Bidirectional mapping between `Var b` and DIMACS indices (1-based).
    Uses HashMap for O(1) lookup from variable to index. -/
structure VarMapping (b : Bounds S) where
  /-- List of all variables in enumeration order. -/
  vars : List (Var b)
  /-- HashMap from variable to 0-based index. -/
  varToIdx : Std.HashMap (Var b) Nat
  /-- Number of variables. -/
  numVars : Nat
  /-- List length equals numVars. -/
  numVars_eq : vars.length = numVars

namespace VarMapping

variable {b : Bounds S}

/-- Build HashMap from variable list. -/
def buildHashMap (vars : List (Var b)) : Std.HashMap (Var b) Nat :=
  vars.foldlIdx (fun idx m v => m.insert v idx) (Std.HashMap.emptyWithCapacity vars.length)

/-- Convert variable to 1-based DIMACS index.
    Returns 0 if variable not found (should not happen for valid encodings). -/
def toIndex (m : VarMapping b) (v : Var b) : Nat :=
  match m.varToIdx.get? v with
  | some idx => idx + 1  -- Convert to 1-based
  | none => 0  -- Variable not in mapping

/-- Convert 1-based DIMACS index to variable.
    Returns none for invalid indices. -/
def fromIndex (m : VarMapping b) (idx : Nat) : Option (Var b) :=
  if idx > 0 ∧ idx ≤ m.numVars then
    m.vars[idx - 1]?
  else
    none

end VarMapping

/-! ## Building the VarMapping -/

/-- Build a VarMapping from bounds and maxFresh. -/
def mkVarMapping (b : Bounds S) (maxFresh : Nat) : VarMapping b :=
  let vars := enumerateVars b maxFresh
  { vars := vars
    varToIdx := VarMapping.buildHashMap vars
    numVars := vars.length
    numVars_eq := rfl }

/-- Create VarMapping from EncState. -/
def mkVarMappingFromState (b : Bounds S) (st : EncState b) : VarMapping b :=
  mkVarMapping b st.nextFresh

end Encoding
