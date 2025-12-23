import ModalDistribution.Logic.SATEncoding.Solver
import ModalDistribution.Logic.SATEncoding.AssumptionEncoding
import ModalDistribution.Logic.SATEncoding.Adequacy.Main
import ModalDistribution.Logic.SATEncoding.PrettyPrint

/-!
# SAT-Based Model Checker

This file provides the main model checking interface that:
1. Encodes assumptions to CNF
2. Calls CaDiCaL SAT solver
3. Verifies results and constructs proofs

## Main Definitions

- `CheckResult`: Result type for model checking (sat with model, unsat, or unknown)
- `checkAssumptions`: Main IO function to check if assumptions are satisfiable
- `checkAssumptionsWithProof`: Check and produce Lean proof if SAT
- `checkAssumptionsWithModel`: Check and return ModelData for printing if SAT

## Usage

```lean
#eval do
  let result ← checkAssumptions bounds assumptions
  match result with
  | .sat => IO.println "SAT: Model exists"
  | .unsat => IO.println "UNSAT: No model exists"
  | .unknown msg => IO.println s!"Unknown: {msg}"
```
-/

open ModalDistribution

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-! ## Result Types -/

/-- Result of model checking attempt (without proof). -/
inductive CheckResult where
  | sat        -- Satisfiable (model exists)
  | unsat      -- Unsatisfiable (no model)
  | unknown (msg : String)  -- Error or timeout
  deriving Repr

/-! ## Core Model Checking Function -/

/-- Check if assumptions are satisfiable.

    This is the main entry point for model checking. It:
    1. Builds the CNF encoding
    2. Builds the variable mapping
    3. Exports to DIMACS and calls CaDiCaL
    4. Parses and verifies the result

    Returns CheckResult indicating SAT, UNSAT, or error. -/
def checkAssumptions (b : Bounds S) (Γ : List (Assumption S))
    (timeout : Option Nat := none) : IO CheckResult := do
  let (cnf, st) := encodeAssumptionsWithState b Γ
  let varMap := mkVarMappingFromState b st
  let dimacs := exportDIMACS varMap cnf
  let solverResult ← callCaDiCaL dimacs timeout

  match solverResult with
  | .unsat => return .unsat
  | .unknown msg => return .unknown msg
  | .sat output =>
      match parseAssignment varMap output with
      | none => return .unknown "Failed to parse solver output"
      | some σ =>
          if cnf.eval σ then
            return .sat
          else
            return .unknown "Solver returned invalid assignment (CNF not satisfied)"

/-- Check assumptions and return the satisfying assignment if SAT.

    This version returns the actual assignment for debugging. -/
def checkAssumptionsWithAssignment (b : Bounds S) (Γ : List (Assumption S))
    (timeout : Option Nat := none)
    : IO (CheckResult × Option (SAT.Assignment (Var b))) := do
  let (cnf, st) := encodeAssumptionsWithState b Γ
  let varMap := mkVarMappingFromState b st
  let dimacs := exportDIMACS varMap cnf
  let solverResult ← callCaDiCaL dimacs timeout

  match solverResult with
  | .unsat => return (.unsat, none)
  | .unknown msg => return (.unknown msg, none)
  | .sat output =>
      match parseAssignment varMap output with
      | none => return (.unknown "Failed to parse solver output", none)
      | some σ =>
          if cnf.eval σ then
            return (.sat, some σ)
          else
            return (.unknown "Solver returned invalid assignment", none)

/-! ## Proof-Producing Version -/

/-- Result with proof: if SAT, includes the model and proof. -/
inductive CheckResultWithProof (b : Bounds S) (Γ : List (Assumption S)) where
  | sat (σ : SAT.Assignment (Var b))
        (hEval : (encodeAssumptions b Γ).eval σ = true)
  | unsat
  | unknown (msg : String)

/-- Check assumptions and produce proof if SAT.

    If satisfiable, returns the assignment along with a proof that
    it satisfies the encoding. This proof can be used with
    `assumptions_adequate` to construct a model. -/
def checkAssumptionsWithProof (b : Bounds S) (Γ : List (Assumption S))
    (timeout : Option Nat := none) : IO (CheckResultWithProof b Γ) := do
  let (cnf, st) := encodeAssumptionsWithState b Γ
  let varMap := mkVarMappingFromState b st
  let dimacs := exportDIMACS varMap cnf
  let solverResult ← callCaDiCaL dimacs timeout

  match solverResult with
  | .unsat => return .unsat
  | .unknown msg => return .unknown msg
  | .sat output =>
      match parseAssignment varMap output with
      | none => return .unknown "Failed to parse solver output"
      | some σ =>
          if h : (encodeAssumptions b Γ).eval σ = true then
            return .sat σ h
          else
            return .unknown "Solver returned invalid assignment"

/-! ## Utilities -/

/-- Get statistics about the CNF encoding. -/
def encodingStats (b : Bounds S) (Γ : List (Assumption S)) : String :=
  let (cnf, st) := encodeAssumptionsWithState b Γ
  let varMap := mkVarMappingFromState b st
  s!"Variables: {varMap.numVars}, Clauses: {cnf.clauses.length}, " ++
  s!"Fresh vars: {st.nextFresh}"

/-- Export the CNF to a string for inspection. -/
def exportCNF (b : Bounds S) (Γ : List (Assumption S)) : String :=
  let (cnf, st) := encodeAssumptionsWithState b Γ
  let varMap := mkVarMappingFromState b st
  exportDIMACS varMap cnf

/-! ## Model Data Extraction -/

/-- Extract WF proof from encodeAssumptions evaluation.
    encodeAssumptions = band [cnfWellFormed, assumptions],
    so satisfaction implies cnfWellFormed is satisfied. -/
private lemma wf_from_encodeAssumptions (b : Bounds S) (Γ : List (Assumption S))
    (σ : SAT.Assignment (Var b))
    (h : (encodeAssumptions b Γ).eval σ = true) :
    WF b σ := by
  unfold encodeAssumptions at h
  have hBand := SAT.CNF.eval_band_true σ [cnfWellFormed b, SAT.CNF.mk _] |>.mp h
  exact hBand (cnfWellFormed b) (by simp)

/-- Check assumptions and return model data if SAT.

    This version extracts the full ModelData (prehistory, predicates, learner quorums)
    which can be pretty-printed for debugging and demonstration. -/
def checkAssumptionsWithModel (b : Bounds S) (Γ : List (Assumption S))
    (timeout : Option Nat := none)
    : IO (CheckResult × Option (ModelData S (Fin b.nParticipants) b)) := do
  let (cnf, st) := encodeAssumptionsWithState b Γ
  let varMap := mkVarMappingFromState b st
  let dimacs := exportDIMACS varMap cnf
  let solverResult ← callCaDiCaL dimacs timeout

  match solverResult with
  | .unsat => return (.unsat, none)
  | .unknown msg => return (.unknown msg, none)
  | .sat output =>
      match parseAssignment varMap output with
      | none => return (.unknown "Failed to parse solver output", none)
      | some σ =>
          -- cnf = encodeAssumptions b Γ by definition
          if h : (encodeAssumptions b Γ).eval σ = true then
            let hWF := wf_from_encodeAssumptions b Γ σ h
            let modelData := modelDataOf b σ hWF
            return (.sat, some modelData)
          else
            return (.unknown "Solver returned invalid assignment", none)

/-- Check and print model summary if SAT. -/
def checkAndPrint (b : Bounds S) (Γ : List (Assumption S))
    (timeout : Option Nat := none) : IO Unit := do
  let (result, modelOpt) ← checkAssumptionsWithModel b Γ timeout
  match result with
  | .sat =>
      match modelOpt with
      | some md =>
          IO.println "SAT: Found model"
          IO.println (formatModelData b md)
      | none =>
          IO.println "SAT: Model found but extraction failed"
  | .unsat =>
      IO.println "UNSAT: No model exists"
  | .unknown msg =>
      IO.println s!"Unknown: {msg}"

end Encoding
