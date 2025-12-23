import ModalDistribution.Logic.SATEncoding.Adequacy.WFExtraction
import ModalDistribution.Logic.SATEncoding.Adequacy.HereditaryTransitivity
import ModalDistribution.Logic.SATEncoding.Adequacy.LearnerConstruction
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinBot
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinEq
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinSeq
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinPred
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinEvent
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinImp
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinAtEnd
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinForall
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinPast
import ModalDistribution.Logic.SATEncoding.Adequacy.TseytinDiamond
import ModalDistribution.Logic.SATEncoding.Adequacy.Main

/-!
# Adequacy: From SAT Assignments to Semantic Models

This file re-exports all adequacy components in a structured way.

The adequacy proof has been reorganized into the following modules:

## Core Components (in Adequacy/ directory)

### 1. WFExtraction.lean
- `wf_from_eval`: Extract well-formedness proof from CNF evaluation

### 2. HereditaryTransitivity.lean
- `mem_edge_subset`: Edge implies subset relationship
- `transitive_at_time`: Each prehistory is transitive
- `hered_at_time`: Each prehistory is hereditarily transitive
- `heredFromWF`: Root prehistory has required property

### 3. LearnerConstruction.lean
- Helper lemmas for CNF learner constraints
- `learnerOf`: Construct Semifilter from SAT assignment

### 4. ModelAssembly.lean
- `finNonempty`: Nonempty instance for participants
- `modelOf`: Construct full Model from ModelData + proofs

### 5. TseytinBot.lean, TseytinEq.lean, TseytinSeq.lean
- Placeholder stubs for Tseytin correctness lemmas
- To be completed with per-constructor proofs

### 6. WorldCorrespondence.lean
- `decodeWorld`: Decode WId to semantic World
- Placeholder lemmas for world variable correspondence

### 7. Main.lean
- `assumptions_adequate`: Main adequacy theorem

## File Organization

The original monolithic Adequacy.lean file has been split into logical components:
- Each component is self-contained with proper imports
- Dependencies flow: WFExtraction → HereditaryTransitivity → LearnerConstruction → ModelAssembly → Main
- Tseytin lemmas are separate as they will be filled in per-constructor

## Usage

Import this file to access all adequacy results:
```lean
import ModalDistribution.Logic.SATEncoding.Adequacy
```

Or import specific components as needed:
```lean
import ModalDistribution.Logic.SATEncoding.Adequacy.ModelAssembly
```

## References

- Plan.md section "Hereditary Transitivity from CNF"
- Structure.lean for CNF constraint definitions
- FormulaEncoding.lean for encoding definitions
-/
