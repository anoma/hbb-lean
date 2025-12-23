import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.VarEnumeration

/-!
# DIMACS Export and Assignment Parsing

This file provides functions to:
1. Export CNF formulas to DIMACS format
2. Parse SAT solver output into assignments

## DIMACS Format

```
p cnf <num_vars> <num_clauses>
<lit1> <lit2> ... 0
...
```

Variables are numbered 1..n (positive = true, negative = false).
Each clause ends with 0.

## Solver Output Format (CaDiCaL)

```
s SATISFIABLE
v 1 -2 3 ... 0
v 4 -5 ... 0
```

Or:
```
s UNSATISFIABLE
```
-/

open ModalDistribution

namespace Encoding

variable {S : Signature}

/-! ## DIMACS Export -/

/-- Convert a literal to DIMACS format (signed integer). -/
def litToDIMACS {S : Signature} {b : Bounds S} (m : VarMapping b) : SAT.Lit (Var b) → Int
  | .pos v => (m.toIndex v : Int)
  | .neg v => -(m.toIndex v : Int)

/-- Convert a clause to DIMACS format (space-separated integers ending in 0). -/
def clauseToDIMACS {S : Signature} {b : Bounds S}
    (m : VarMapping b) (c : SAT.Clause (Var b)) : String :=
  let lits := c.map (fun l => toString (litToDIMACS m l))
  String.intercalate " " lits ++ " 0"

/-- Export CNF to DIMACS format. -/
def exportDIMACS {S : Signature} {b : Bounds S}
    (m : VarMapping b) (cnf : SAT.CNF (Var b)) : String :=
  let header := s!"p cnf {m.numVars} {cnf.clauses.length}\n"
  let clauses := cnf.clauses.map (clauseToDIMACS m)
  header ++ String.intercalate "\n" clauses ++ "\n"

/-! ## Assignment Parsing -/

/-- Parse a single integer from a string. -/
def parseIntOpt (s : String) : Option Int :=
  let s := s.trim
  if s.isEmpty then none
  else if s.startsWith "-" then
    match s.drop 1 |>.toNat? with
    | some n => some (-(n : Int))
    | none => none
  else
    match s.toNat? with
    | some n => some (n : Int)
    | none => none

/-- Parse a line starting with "v " into a list of signed integers.
    Stops at 0 or end of line. -/
def parseVLine (line : String) : List Int :=
  if line.startsWith "v " then
    let tokens := (line.drop 2).splitOn " "
    tokens.filterMap parseIntOpt |>.filter (· ≠ 0)
  else
    []

/-- Parse all "v" lines from solver output into a list of signed integers. -/
def parseAllVLines (output : String) : List Int :=
  let lines := output.splitOn "\n"
  lines.flatMap parseVLine

/-- Convert list of signed integers to SAT.Assignment using VarMapping. -/
def assignmentFromInts {S : Signature} {b : Bounds S}
    (m : VarMapping b) (ints : List Int) : SAT.Assignment (Var b) :=
  fun v =>
    let idx := m.toIndex v
    if idx = 0 then false  -- Variable not in mapping
    else
      -- Check if positive or negative literal appears
      if ints.contains (idx : Int) then true
      else if ints.contains (-(idx : Int)) then false
      else false  -- Default to false for unassigned variables

/-- Parse solver output into SAT.Assignment.
    Returns none if parsing fails. -/
def parseAssignment {S : Signature} {b : Bounds S}
    (m : VarMapping b) (output : String) : Option (SAT.Assignment (Var b)) :=
  let ints := parseAllVLines output
  if ints.isEmpty then none
  else some (assignmentFromInts m ints)

/-! ## Solver Result Types -/

/-- Result from SAT solver invocation. -/
inductive SolverResult where
  | sat (assignment : String)  -- Raw output containing assignment
  | unsat
  | unknown (msg : String)
  deriving Repr

/-- Check if solver output indicates SAT. -/
def isSAT (output : String) : Bool :=
  output.containsSubstr "s SATISFIABLE"

/-- Check if solver output indicates UNSAT. -/
def isUNSAT (output : String) : Bool :=
  output.containsSubstr "s UNSATISFIABLE"

/-- Classify solver output. -/
def classifySolverOutput (output : String) : SolverResult :=
  if isSAT output then .sat output
  else if isUNSAT output then .unsat
  else .unknown s!"Unexpected solver output"

end Encoding
