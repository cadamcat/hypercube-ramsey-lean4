# Third-party code and mathematical sources

## OpenAI's Lean library

This project depends on [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, under the Apache-2.0 license. The upstream repository has no NOTICE file. Lake fetches the library; no OpenAI source file is copied into this repository.

The proof imports one module, `OAI.Combinatorics.Ramsey.Hypercube`. It provides the cube graph `cube` and the Ramsey number `ramseyNumber`, finite Ramsey bounds, cross-edge colourings between two host sides, and `counterexample_sequence_of_not_linear`, the paper's Lemma 2.1. `grep -rn '^import OAI' HypercubeRamsey` lists the importing files.

## Formal Conjectures definitions

The statement `Erdos181.erdos_181` and the definitions it uses are copied from Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/9d259649abe0b02d7a25f7589b872db679b35e21), commit `9d259649abe0b02d7a25f7589b872db679b35e21`, Copyright 2026 The Formal Conjectures Authors, under the Apache-2.0 license:

| Upstream file | Declarations | Copied into |
|---|---|---|
| `FormalConjectures/ErdosProblems/181.lean` | `Erdos181.erdos_181` (statement and docstring) | `Challenge.lean` |
| `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Hypercube.lean` | `SimpleGraph.hypercube`, `SimpleGraph.hypercube_adj` | `Challenge.lean`, `HypercubeRamsey/FormalConjectures.lean` |
| `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean` | `SimpleGraph.graphRamsey`, `SimpleGraph.diagonalGraphRamsey` | `Challenge.lean`, `HypercubeRamsey/FormalConjectures.lean` |

The copies drop the module-system wrappers, the theorem's `category` attribute and a TODO comment, use the current Mathlib path `Mathlib.Basic.Real.Basic` for the deprecated import `Mathlib.Data.Real.Basic`, merge the two definition files into one block, and leave out the other declarations and imports of `Ramsey.lean`. The header comments of `Challenge.lean` and `HypercubeRamsey/FormalConjectures.lean` record the changes to the definitions. `scripts/check_target.py defs` checks that each copied declaration appears verbatim in the upstream files; [docs/verification.md](docs/verification.md#statement-fidelity) describes the check.

## Mathlib and other Lean packages

The project uses [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612), commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, under the Apache-2.0 license. OpenAI's library pins Mathlib and further Lean packages; [lake-manifest.json](lake-manifest.json) records the exact revisions. These packages are fetched by Lake, not redistributed here, and their licenses and notices remain with them.

Lean is selected by [lean-toolchain](lean-toolchain) and installed separately.

## Mathematical sources

The formalized result is OpenAI, [*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf), Theorem 1.1. It answers a question of S. A. Burr and P. Erdős (*On the magnitude of generalized Ramsey numbers for graphs*, 1975, Section 7). The repository formalizes the result and does not claim new mathematics.
