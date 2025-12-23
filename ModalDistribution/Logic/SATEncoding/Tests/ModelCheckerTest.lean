import ModalDistribution.Logic.SATEncoding.ModelChecker

/-!
# Model Checker Tests

This file provides basic tests for the SAT-based model checker.

## Requirements

CaDiCaL SAT solver must be installed:
- From source: https://github.com/arminbiere/cadical

## Usage

To check solver availability:
```lean
#eval checkCaDiCaLAvailable
```

To use the model checker with custom bounds:
1. Define a Signature
2. Create Bounds for that signature
3. Create assumptions (List of Assumption S)
4. Call checkAssumptions
-/

open ModalDistribution
open Encoding

/-! ## CaDiCaL Availability Check -/

/-- Check if CaDiCaL is available. -/
def testCaDiCaLAvailable : IO Unit := do
  IO.println "Checking CaDiCaL availability..."
  let available ← checkCaDiCaLAvailable
  if available then
    IO.println "  CaDiCaL: Available ✓"
  else
    IO.println "  CaDiCaL: NOT FOUND"
    IO.println "  Please install: sudo apt install cadical"

/-! ## Direct DIMACS Test (no Lean types needed) -/

/-- Test CaDiCaL with a simple DIMACS problem. -/
def testSimpleDIMACS : IO Unit := do
  IO.println "Test: Simple DIMACS problem"

  -- Simple SAT problem: (x1 ∨ x2) ∧ (¬x1 ∨ x2) ∧ (x1 ∨ ¬x2)
  -- Solution: x1 = true, x2 = true
  let dimacs := "p cnf 2 3\n1 2 0\n-1 2 0\n1 -2 0\n"

  IO.println s!"  Input: (x1 ∨ x2) ∧ (¬x1 ∨ x2) ∧ (x1 ∨ ¬x2)"

  let result ← callCaDiCaL dimacs
  match result with
  | .sat output =>
      IO.println "  Result: SAT ✓"
      -- Show first part of output
      let lines := output.splitOn "\n"
      for line in lines.take 5 do
        if line.startsWith "v" || line.startsWith "s" then
          IO.println s!"  {line}"
  | .unsat =>
      IO.println "  Result: UNSAT (unexpected!)"
  | .unknown msg =>
      IO.println s!"  Result: Unknown - {msg}"

/-- Test CaDiCaL with an UNSAT problem. -/
def testUNSATDIMACS : IO Unit := do
  IO.println "Test: Simple UNSAT problem"

  -- UNSAT problem: (x1) ∧ (¬x1)
  let dimacs := "p cnf 1 2\n1 0\n-1 0\n"

  IO.println s!"  Input: (x1) ∧ (¬x1)"

  let result ← callCaDiCaL dimacs
  match result with
  | .sat _ =>
      IO.println "  Result: SAT (unexpected!)"
  | .unsat =>
      IO.println "  Result: UNSAT ✓"
  | .unknown msg =>
      IO.println s!"  Result: Unknown - {msg}"

/-! ## Main -/

def main : IO Unit := do
  IO.println "=== Model Checker Tests ==="
  IO.println ""

  testCaDiCaLAvailable
  IO.println ""

  let available ← checkCaDiCaLAvailable
  if available then
    testSimpleDIMACS
    IO.println ""
    testUNSATDIMACS
    IO.println ""
    IO.println "=== All tests completed ==="
  else
    IO.println "Skipping solver tests (CaDiCaL not available)"
