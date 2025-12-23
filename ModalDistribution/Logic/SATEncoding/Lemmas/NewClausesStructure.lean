import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Common
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.ShiftedAssignment
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Bot
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Eq
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Seq
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Imp
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Predicate
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Event
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.AtEnd
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Past
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Forall
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Diamond
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Main

/-!
# New Clauses Structural Lemmas

This module provides structural determinism lemmas for formula encoding.
It re-exports all sub-modules for convenient access.

## Sub-modules

- `Common`: Shared helpers (nonFreshClausesCompat preservation, Fresh var lemmas)
- `ShiftedAssignment`: Threshold agreement lemmas for shiftedAssignment
- Per-constructor modules: Bot, Eq, Seq, Imp, Predicate, Event, AtEnd, Past, Forall, Diamond
- `Main`: Main `encodeFormula_structural_determinism_new_clauses` theorem
-/
