[English](README.md) | [简体中文](README_zh.md)

# The hypercube Ramsey number has linear order

This repository formalizes the theorem that an absolute constant `C > 0` bounds the diagonal Ramsey number of every `n`-dimensional hypercube by `C · 2^n`, for every natural `n` including zero. It is the result of OpenAI's paper *The hypercube Ramsey number has linear order*, which resolves the Burr–Erdős hypercube Ramsey conjecture. This repository formalizes that result and claims no new mathematics.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [AUTHORS.md](AUTHORS.md).
- Developed with AI assistance (Claude Code and Codex); all proofs are verified by the Lean 4 kernel.

## Formal statement

The challenge is Formal Conjectures' `Erdos181.erdos_181` at commit `9d259649abe0b02d7a25f7589b872db679b35e21`. Its statement is:

```lean
∃ C > (0 : ℝ), ∀ n : ℕ,
  (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n
```

Here `hypercube n` is the graph on `n`-bit vectors whose edges join vectors that differ in one coordinate. A monochromatic copy in the Ramsey number is an injective graph copy and need not be induced, as in the paper. The challenge defines `graphRamsey` using `sInf`; a proved bridge identifies it with OpenAI's least-positive Ramsey number. The target statement and copied definitions are in [Challenge.lean](Challenge.lean); the proof entry point is [HypercubeRamsey/Main.lean](HypercubeRamsey/Main.lean). [Challenge.json](Challenge.json) configures Comparator to compare them.

## Build and verify

Requirements: Git, Python 3, and [elan](https://github.com/leanprover/elan), with `lake` on `PATH`. From a fresh checkout, run:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

The release dependency pins OpenAI's library to its Git revision. Its `lake update` hook can exit after resolving dependencies and writing `lake-manifest.json` with an `iut: Lake resolved an unexpected checkout at …` message. Run the patch script next; it applies the Lean 4.34.1 compatibility patches and is safe to rerun after another `lake update`.

To build the theorem and check its axiom dependencies, run:

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

The script builds the proof and challenge modules with Lean's kernel checking enabled, then checks that `Erdos181.erdos_181` depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Fixed dependencies

- Lean `v4.34.1`, selected by [lean-toolchain](lean-toolchain).
- [Mathlib](https://github.com/leanprover-community/mathlib4), commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- OpenAI's [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- The remaining pinned dependencies and revisions are recorded in [lake-manifest.json](lake-manifest.json).

The Formal Conjectures source statement is [Erdos 181](https://github.com/google-deepmind/formal-conjectures/blob/9d259649abe0b02d7a25f7589b872db679b35e21/FormalConjectures/ErdosProblems/181.lean). The mathematical result is OpenAI, [*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf). See [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and [LICENSE](LICENSE) for the project license.
