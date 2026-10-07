# Third-party sources and dependencies

## Formal Conjectures definitions

The graph definitions used by the challenge and proof are copied from Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures), commit `9d259649abe0b02d7a25f7589b872db679b35e21`, under Apache-2.0:

| Repository files | Upstream source | Definitions |
|---|---|---|
| `Challenge.lean`, `HypercubeRamsey/FormalConjectures.lean` | `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Hypercube.lean` | `SimpleGraph.hypercube`, `SimpleGraph.hypercube_adj` |
| `Challenge.lean`, `HypercubeRamsey/FormalConjectures.lean` | `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean` | `SimpleGraph.graphRamsey`, `SimpleGraph.diagonalGraphRamsey` |

The copies omit the module-system wrappers, use the current Mathlib path for real-number basics, merge the two definition blocks, and leave out unrelated declarations and imports. The source files record these adaptations.

## OpenAI's Lean library

The project depends on [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, licensed under Apache-2.0. The imported module is `OAI.Combinatorics.Ramsey.Hypercube`; it provides OpenAI's cube and Ramsey-number definitions, finite Ramsey bounds and characterizations, and cross-colouring results used by the proof.

| Importing file | Imported module |
|---|---|
| `HypercubeRamsey/Bridge.lean` | `OAI.Combinatorics.Ramsey.Hypercube` |
| `HypercubeRamsey/Framework/Basic.lean` | `OAI.Combinatorics.Ramsey.Hypercube` |
| `HypercubeRamsey/S03/Height/Device.lean` | `OAI.Combinatorics.Ramsey.Hypercube` |
| `HypercubeRamsey/S03/Height/Selection.lean` | `OAI.Combinatorics.Ramsey.Hypercube` |

## Mathlib and transitive dependencies

The project uses Mathlib, commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, under Apache-2.0. OpenAI's library pins Mathlib and other Lean packages. [lake-manifest.json](lake-manifest.json) records the exact revisions; each dependency's source checkout carries its license and notices.

## Mathematical source

The formalized result is OpenAI, [*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf). It resolves the Burr–Erdős hypercube Ramsey conjecture. The repository formalizes the result and does not claim new mathematics.
