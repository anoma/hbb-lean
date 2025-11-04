# ModalDistribution

A Lean 4 library formalizing modal logic and broadcast algorithms from the paper "Heterogeneous trust in reliable broadcast via modal logic and history structures".

## Overview

This library provides mechanically verified proofs of distributed broadcast protocols using semifilters and history structures. It formalizes three broadcast algorithms (ThyHBB1, ThyHBB2, ThyHBB3) and proves their correctness properties (Agreement, Liveness1, Liveness2).

## Installation

```bash
# Clone the repository
git clone https://github.com/AHartNtkn/modal-dist-lean.git
cd modal-dist-lean

# Build the project
lake build
```

## Usage

Import the library modules in your Lean 4 project:

```lean
import ModalDistribution.Core.Prehistory
import ModalDistribution.Logic.Syntax
import ModalDistribution.Algorithms.ThyHBB1
```

You may also simply open up the project in Visual Studio Code with the Lean 4 extension to step through proofs.

## Requirements

- Lean 4 (v4.24.0-rc1)
- Mathlib4
- Lake build system

## License

[License information to be added]
