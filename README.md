# Heterogeneous Broadcast in Lean 4

A complete Lean 4 formalization of the paper "Heterogeneous trust in reliable broadcast via modal logic and history structures". This repository contains mechanically verified proofs of three Byzantine broadcast algorithms using history structures and modal logic.

## What's in this repository?

This formalization includes:

- **Foundations (Section 2-3)**: History structures, prehistories, event-tuples, semifilters, and Kripke-style modal semantics
- **Modal Logic Framework (Section 4-5)**: Box/diamond modalities, quorum intersection properties, sequentiality, and liveness reasoning
- **Three Broadcast Algorithms**:
  - **ThyHBB1** (Section 6): Basic heterogeneous broadcast with unique proposals
  - **ThyHBB2** (Section 7): Improved protocol with non-equivocation
  - **ThyHBB3** (Section 8): Full protocol with correlation axioms
- **Correctness Proofs**: Agreement, Liveness 1, and Liveness 2 properties for all three algorithms

### Repository structure

```
ModalDistribution/
├── Core/              # Foundation: prehistories, histories, semifilters, models
│   ├── Prehistory.lean
│   ├── History.lean
│   ├── Semifilter.lean
│   └── Model.lean
├── Logic/             # Modal logic syntax, semantics, and axiom system
│   ├── Syntax.lean
│   ├── Semantics.lean
│   ├── AxiomSystem.lean
│   └── Properties/    # Modality properties, sequentiality, quorums
├── Examples/          # Includes the three broadcast algorithms and their proofs
│   ├── HistoryStructures.lean  # Common history structure definitions
│   ├── ThyLive.lean            # Liveness (Section 5.2)
│   ├── ThyHBB1/                # Section 6
│   │   ├── Axioms.lean
│   │   ├── Agreement.lean
│   │   ├── Liveness_One.lean
│   │   └── Liveness_Two.lean
│   ├── ThyHBB2/                # Section 7
│   │   └── [similar structure]
│   └── ThyHBB3/                # Section 8
│       └── [similar structure]
```

See [PAPER_MAPPING.md](PAPER_MAPPING.md) for a detailed mapping between paper definitions/theorems and their Lean implementations.

## Installation

### Prerequisites

You need:
1. **Lean 4** - A theorem prover and functional programming language
2. **elan** - The Lean version manager
3. **lake** - Lean's build tool (installed with Lean)

### Step-by-step installation (for paper readers new to Lean)

#### 1. Install elan (Lean version manager)

On Linux/macOS:
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

On Windows, download and run [elan-init.exe](https://github.com/leanprover/elan/releases).

After installation, restart your terminal or run:
```bash
source ~/.profile  # or source ~/.bashrc
```

#### 2. Clone this repository

```bash
git clone https://github.com/AHartNtkn/modal-dist-lean.git
cd modal-dist-lean
```

#### 3. Build the project

```bash
lake build
```

This will:
- Automatically install the correct Lean version (v4.24.0-rc1)
- Download and build Mathlib4 (the standard mathematical library)
- Build all formalized proofs

**Note**: The first build takes several minutes to several hours depending on system specs it compiles Mathlib4. Subsequent builds are much faster. Note that it needs to bould roughly 3100 files, which should give a clear idea how much progress has been made as you watch it build.

#### 4. (Optional) Install VS Code with Lean 4 extension

For the best experience viewing and stepping through proofs:

1. Install [Visual Studio Code](https://code.visualstudio.com/)
2. Install the "Lean 4" extension from the VS Code marketplace
3. Open this repository in VS Code: `code .`
4. Open any `.lean` file to see syntax highlighting and proof states

## How to explore the formalization

### For paper readers

If you're reading the paper and want to see how something is formalized:

1. Open [PAPER_MAPPING.md](PAPER_MAPPING.md)
2. Find the definition/theorem from the paper (e.g., "Definition 2.3.5")
3. Follow the file path to see the Lean code

Example: To see the Agreement proof for ThyHBB1 (Proposition 6.3.1), open `ModalDistribution/Examples/ThyHBB1/Agreement.lean`.

### In VS Code

1. Open a `.lean` file
2. Click anywhere in a proof
3. The "Lean Infoview" panel shows the proof state at that point
4. Hover over identifiers to see their types
5. Ctrl+click (or Cmd+click) on names to jump to definitions

## Verifying the proofs

To check that all proofs are valid:

```bash
lake build
```

If this completes without errors, all proofs are mechanically verified correct.

## License

This work is licensed under [CC-BY 4.0](LICENSE).
