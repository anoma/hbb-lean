# Heterogeneous Broadcast in Lean 4

A Lean 4 formalization of the paper "Heterogeneous trust in reliable broadcast via modal logic and history structures". This repository contains mechanically verified proofs of four broadcast algorithms using history structures and modal logic.

**Knowledge restriction on this branch:** `ThyLive` permits Knowledge bodies
exactly `E`, `K E`, and `Q_l E`, where `E` is an event atom. This is an explicit
amendment to Figure 6's unrestricted scheme; finite histories and semantics are
unchanged. All HBB1–3 correctness claims retain their mathematical meaning and are kernel-checked.
[The finite-model theorem](ModalDistribution/Examples/ThyLive/FiniteModel.lean)
exhibits a model of the restricted shared theory containing a live performed
event. It establishes nonvacuity of `ThyLive`, not of every full protocol theory.
[The finite-history investigation](HBB4_FINITE_HISTORIES.md) records the obstruction
for unrestricted Knowledge and its historical provenance.

**HBB4 CM, SW, and CW:** All three versions cap target-learner votes at
`MaxDepth(l) + 1`, permit self-source advancement, and use delivery sometime in the completed history.
Their agreement and liveness proofs require no three-quorum intersection axiom.
`MaxDepth` is the attained maximum of distinct-row causal-chain lengths, not a
separate budget. The rules are semantic schemata over the existing model because
legality quantifies over natural-number ranks, while the formula syntax quantifies
over values. Neither histories nor satisfaction semantics change.
[The finite-model theorem](ModalDistribution/Examples/ThyHBB4/FiniteModel.lean)
checks a common eight-event live execution for CM, SW, and CW with both
liveness premises. CM implies SW, and SW implies CW by kernel-checked proofs.
CW uses the weaker conflict-depth bound, which still suffices at the unchanged
delivery rank. The formalization does not yet include separating models proving
these coherence implications strict. The separate
[52-event executable audit](audits/hbb4_cm/INVESTIGATION.md) additionally exercises
distinct learners and failure of three-quorum intersection.

## Reading the proofs

The canonical `agreement`, `livenessOne`, and `livenessTwo` theorems use explicit
participants and semantic observations. Their `_modal` corollaries express the
same results in the paper's notation. Shared equivalences in
[Properties/Satisfaction.lean](ModalDistribution/Logic/Properties/Satisfaction.lean)
connect the two presentations.

Three world domains matter: a **possible world** has a history preceding or equal
to the model history; an **actual event** belongs to that history; a **final world**
`finalWorld M p` evaluates a participant at the full history with the null event.
Theory validity ranges over possible worlds. `ObservedAt M w φ` witnesses an
actual causal predecessor of `w`; `OccursAt M p φ` witnesses an event somewhere
in the full history at participant `p`, without asserting it follows an observation.
`Occurs M φ` permits any participant. `Correlated` makes the world at which
correlation is evaluated explicit.

For the correlation comparison, start with HBB3's `correlation_global_allPast`
and HBB4's `CausalMonotonicity`. The former assumes correlation at every final
participant; the latter starts from correlation at a single possible world.
Both use the same `Correlated` predicate.

## What's in this repository?

This formalization includes:

- **Foundations (Section 2-3)**: History structures, prehistories, event-tuples, semifilters, and Kripke-style modal semantics
- **Modal Logic Framework (Section 4-5)**: Box/diamond modalities, quorum intersection properties, sequentiality, and liveness reasoning
- **Broadcast Algorithms**:
  - **ThyHBB1** (Section 6): Basic heterogeneous broadcast with unique proposals
  - **ThyHBB2** (Section 7): Improved protocol with non-equivocation
  - **ThyHBB3** (Section 8): Full protocol with correlation axioms
  - **ThyHBB4 (CM/SW/CW)**: Capped rounds with three separately stated coherence conditions
- **Correctness Proofs**: Agreement, Liveness 1, and Liveness 2 properties for all four algorithms

### Repository structure

```
ModalDistribution/
├── Core/              # Foundation: prehistories, histories, semifilters, models
│   ├── Prehistory.lean
│   ├── History.lean
│   ├── Semifilter.lean
│   ├── Model.lean
│   └── ...            # Hand-rolled Set/Equiv infrastructure and tactics
├── Logic/             # Modal logic syntax, semantics, and axiom system
│   ├── Syntax.lean
│   ├── Semantics.lean
│   ├── AxiomSystem.lean
│   └── Properties/    # Satisfaction machinery, modalities, sequentiality, quorums
├── Examples/          # Broadcast algorithms and their proofs
│   ├── ThyLive.lean            # Liveness (Section 5.2)
│   ├── HBB.lean                # Axiom schemes shared by the three theories
│   ├── Counterexamples.lean    # Lemmas 4.2.1(3,4) and 4.2.3(3)
│   ├── ThyHBB1/                # Section 6
│   │   ├── Axioms.lean
│   │   ├── Safety.lean
│   │   ├── Uniqueness.lean
│   │   ├── Agreement.lean
│   │   ├── Liveness_One.lean
│   │   ├── Liveness_Two.lean
│   │   └── Correctness.lean
│   ├── ThyHBB2/                # Section 7
│   │   └── [similar, with Lemmas.lean in place of Safety/Uniqueness]
│   ├── ThyHBB3/                # Section 8
│   │   └── [similar, with Lemmas.lean in place of Safety/Uniqueness]
│   └── ThyHBB4/                # Corrected capped CM/SW/CW protocols
│       ├── Depth.lean         # Exact finite MaxDepth
│       ├── Axioms.lean        # Shared rules and CM/SW/CW axioms
│       ├── Coherence.lean     # CM ⇒ SW ⇒ CW proofs
│       ├── Semantics.lean
│       ├── Safety.lean        # Shared provenance and quorum lemmas
│       ├── StrictDepth.lean   # Strict row-inclusion chains
│       ├── Liveness.lean      # Capped progress and Liveness 1
│       ├── LivenessTwo.lean   # Shared fixed-source transfer
│       ├── CM.lean            # CM agreement and both liveness results
│       ├── SW.lean            # SW agreement and both liveness results
│       ├── CW.lean            # CW agreement and both liveness results
│       └── FiniteModel.lean   # Finite live protocol witness
└── AxiomAudit.lean    # Build-enforced axiom hygiene for the main theorems
```

See [PAPER_MAPPING.md](PAPER_MAPPING.md) for a detailed mapping between paper definitions/theorems and their Lean implementations; the same mapping is embedded in the sources (every anchored declaration's doc comment begins with `Paper: <item>.`). One representational choice to be aware of: prehistories are list-backed, realising the paper's inductive-datatype presentation rather than the quotiented set-theoretic definition — see the note in PAPER_MAPPING.md.

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
git clone https://github.com/anoma/hbb-lean.git
cd hbb-lean
```

(Or unpack the zip archive of this repository, if you have downloaded it from a DOI or other source.)

#### 3. Build and verify the proofs

```bash
# EITHER type
lake build
# OR (for informative verification announcements as each protocol is verified during the build) type
./build_with_announcements.sh
```
This builds the project **and verifies all proofs**. It will:
- Automatically install the correct Lean version (v4.24.0-rc1)
- Build and verify all formalized correctness proofs for ThyHBB1, ThyHBB2, and ThyHBB3

**What to expect during the build:**
- The project has no external dependencies beyond Lean itself, so the first build takes well under a minute on a typical machine
- You'll see messages like "✔ [13/38] Built ModalDistribution.Logic.Properties.Modalities (842ms)" as modules are being processed
- The build compiles 39 files total, which can be used to gauge build progress
- When you see modules from `ModalDistribution.Examples.ThyHBB1`, `ThyHBB2`, and `ThyHBB3` being processed, that's when the correctness properties (Agreement, Liveness 1, and Liveness 2) for each protocol are being verified
- Subsequent builds are much faster

**If the build completes without errors, all proofs are mechanically verified correct.** This means the correctness properties of all three broadcast protocols have been formally proven.

#### 4. (Optional) Install VS Code with Lean 4 extension

For the best experience viewing and stepping through proofs:

1. Install [Visual Studio Code](https://code.visualstudio.com/)
2. Open this repository in VS Code by running `code .` from the terminal in the repository directory
3. Install the "Lean 4" extension:
   - Click the "Extensions" icon in the VS Code sidebar (or press Ctrl+Shift+X / Cmd+Shift+X)
   - Search for "Lean 4"
   - Install the extension published by "leanprover"
   - **Note**: You may see a warning about installing extensions from unverified publishers. This is normal for first-time installation. The Lean 4 extension is the official extension from the Lean development team. You can verify this at the [official Lean installation page](https://lean-lang.org/install/)
4. Open any `.lean` file (e.g., `ModalDistribution.lean`) to see syntax highlighting and proof states
   - If prompted about opening in Restricted mode, you can choose either option

## How to explore the formalization

### For paper readers

If you're reading the paper and want to see how something is formalized:

1. Open [PAPER_MAPPING.md](PAPER_MAPPING.md)
2. Find the definition/theorem from the paper (e.g., "Definition 2.3.5")
3. Follow the file path to see the Lean code

Example: To see the Agreement proof for ThyHBB1 (Proposition 6.3.1), open `ModalDistribution/Examples/ThyHBB1/Agreement.lean`, or you may find the entry for that proposition in PAPER_MAPPING.md and click on its link, which will take you to the same place.

### In VS Code

1. Open a `.lean` file (e.g., `ModalDistribution.lean`)
2. Click anywhere in a proof
3. The "Lean Infoview" panel shows the proof state at that point
4. Hover over identifiers to see their types
5. Ctrl+click (or Cmd+click) on names to jump to definitions
6. Right click on terms to get a list of interactions

## License

This work is licensed under [CC-BY 4.0](LICENSE).
