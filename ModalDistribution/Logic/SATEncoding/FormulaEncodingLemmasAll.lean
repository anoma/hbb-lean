import ModalDistribution.Logic.SATEncoding.Lemmas.Basic
import ModalDistribution.Logic.SATEncoding.Lemmas.DiamondHelpers
import ModalDistribution.Logic.SATEncoding.Lemmas.PredicateHelpers
import ModalDistribution.Logic.SATEncoding.Lemmas.StructuralDeterminism
import ModalDistribution.Logic.SATEncoding.Lemmas.WellFormedness
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure

/-!
# Formula Encoding Lemmas - Re-export Module

This module re-exports all lemma files from the Lemmas/ folder.
Import this single file to get access to all formula encoding lemmas.

## Module Structure

The lemmas are organized into the following files:
- `Basic`: Variable shifting, clause evaluation, basic infrastructure
- `DiamondHelpers`: Diamond encoding step definitions and helpers
- `PredicateHelpers`: Predicate encoding offset preservation helpers
- `StructuralDeterminism`: Main offset lemmas (encodeFormula_nextFresh_offset, etc.)
- `WellFormedness`: Well-formedness preservation and monotonicity lemmas
- `NewClausesStructure`: Individual formula case structural lemmas

These files contain the full content from FormulaEncodingLemmas.lean, organized
by topic for better maintainability.
-/

-- Re-export all namespaces
namespace Encoding
end Encoding
