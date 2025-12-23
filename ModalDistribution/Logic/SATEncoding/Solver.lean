import ModalDistribution.Logic.SATEncoding.DIMACS

/-!
# SAT Solver Integration

This file provides functions to call external SAT solvers (CaDiCaL) from Lean.

## Usage

```lean
#eval do
  let result ← callCaDiCaL "p cnf 2 2\n1 2 0\n-1 -2 0\n"
  IO.println s!"Result: {repr result}"
```

## Requirements

CaDiCaL must be installed and available in PATH:
- From source: https://github.com/arminbiere/cadical
-/

open ModalDistribution

namespace Encoding

/-! ## CaDiCaL Integration -/

/-- Call CaDiCaL SAT solver on DIMACS input.

    Strategy:
    1. Write DIMACS to temporary file
    2. Spawn CaDiCaL process
    3. Parse output for SAT/UNSAT and assignment
    4. Clean up temp file

    Returns: SolverResult (sat with output, unsat, or unknown with message) -/
def callCaDiCaL (dimacs : String) (timeout : Option Nat := none) : IO SolverResult := do
  -- Create temp file
  let tmpDir ← IO.FS.createTempDir
  let tmpPath := tmpDir / "problem.cnf"

  try
    -- Write DIMACS to temp file
    IO.FS.writeFile tmpPath dimacs

    -- Build command args
    let args : Array String := match timeout with
      | none => #[tmpPath.toString]
      | some t => #["-t", toString t, tmpPath.toString]

    -- Spawn CaDiCaL
    let output ← IO.Process.output {
      cmd := "cadical"
      args := args
    }

    -- Classify result
    let result := classifySolverOutput output.stdout

    return result

  catch e =>
    return .unknown s!"Solver error: {e}"

  finally
    -- Clean up temp files (best effort)
    try
      IO.FS.removeFile tmpPath
      IO.FS.removeDir tmpDir
    catch _ =>
      pure ()

/-- Check if CaDiCaL is available in PATH. -/
def checkCaDiCaLAvailable : IO Bool := do
  try
    let output ← IO.Process.output {
      cmd := "cadical"
      args := #["--version"]
    }
    return output.exitCode == 0
  catch _ =>
    return false

/-! ## Higher-Level Interface -/

/-- Solve a CNF formula and return the parsed assignment if SAT.

    Returns:
    - `some (some assignment)` if SAT
    - `some none` if UNSAT
    - `none` if error -/
def solveCNF {S : Signature} {b : Bounds S}
    (m : VarMapping b) (cnf : SAT.CNF (Var b))
    (timeout : Option Nat := none) : IO (Option (Option (SAT.Assignment (Var b)))) := do
  let dimacs := exportDIMACS m cnf
  let result ← callCaDiCaL dimacs timeout
  match result with
  | .sat output =>
      match parseAssignment m output with
      | some σ => return some (some σ)
      | none => return none  -- Parse error
  | .unsat => return some none
  | .unknown _ => return none

end Encoding
