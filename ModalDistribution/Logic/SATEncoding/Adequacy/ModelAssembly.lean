import Mathlib.Data.Nat.Bitwise
import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.Bitmask.Core
import ModalDistribution.Logic.SATEncoding.ListLemmas
import ModalDistribution.Logic.SATEncoding.FormulaEncoding
import ModalDistribution.Logic.SATEncoding.Adequacy.HereditaryTransitivity
import ModalDistribution.Logic.SATEncoding.Adequacy.LearnerConstruction

/-!
# Model Assembly from SAT Assignments

This file constructs full semantic `Model` instances from SAT assignments that satisfy
the well-formedness constraints.

## Main Results

- `finNonempty`: Nonempty instance for Fin b.nParticipants
- `modelOf`: Constructs a complete Model from WF assignment

## Strategy

The model is assembled from three components:
1. History with hereditary transitivity (from HereditaryTransitivity.lean)
2. Predicate interpretation (computable from modelDataOf)
3. Learner semifilters (from LearnerConstruction.lean)

## References

- HereditaryTransitivity.lean for heredFromWF
- LearnerConstruction.lean for learnerOf
- Decoder.lean for modelDataOf
-/

open ModalDistribution Encoding

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Model Assembly -/

/-- Fin n is nonempty when n > 0 (from positivity constraint). -/
instance finNonempty (b : Bounds S) : Nonempty (Fin b.nParticipants) :=
  ⟨⟨0, b.posParticipants⟩⟩

/-- Construct full `Model` from `ModelData` and well-formedness proof (noncomputable).

    This assembles:
    - History with hereditary transitivity proof
    - Predicate interpretation (already computable in ModelData)
    - Learner semifilters (constructed from LearnerData + WF proof)

    Note: This is noncomputable because it includes proof obligations.
    For inspection, use `modelDataOf` which is fully computable. -/
noncomputable def modelOf
    (b : Bounds S)
    (σ : SAT.Assignment (Var b))
    (hWF : WF b σ) :
    Model S (Fin b.nParticipants) :=
  let md := modelDataOf b σ hWF
  { history := { val := md.Hroot, hered := heredFromWF b σ hWF },
    predInterp := md.pred,
    learner := learnerOf b σ hWF }

/-! ## Note on Inspectability

The `modelOf` function is noncomputable due to proof obligations (hereditary transitivity,
semifilter axioms). However, end users can inspect the extracted model using the fully
computable `modelDataOf`:

- `modelDataOf b σ` gives:
  - `Hroot`: The root prehistory (computable)
  - `pred`: Time-accurate predicate interpretation (computable via `timeIndexOf`)
  - `learnData`: Minimal quorums as bitmasks (computable)

Users can examine the structure, predicates, and quorums without needing the proof parts.
The `modelOf` function is only needed for formal verification (adequacy theorems).
-/

end Encoding
