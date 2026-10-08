[English](README.md) | [简体中文](README_zh.md)

# The hypercube Ramsey number has linear order, in Lean 4

An absolute constant `C > 0` bounds the Ramsey number of the `n`-dimensional hypercube by `C · 2^n` for every `n ≥ 0`: every red-blue colouring of the edges of a complete graph on at least `C · 2^n` vertices contains a monochromatic copy of the cube.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authors and attribution](AUTHORS.md).
- **Mathematical result:** OpenAI, [*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf), Theorem 1.1.
- Developed with AI assistance (Claude Code, Codex and Antigravity); all proofs are verified by the Lean 4 kernel.

## Main result

The repository proves Erdős problem 181 as stated in Google DeepMind's Formal Conjectures at commit `9d259649abe0b02d7a25f7589b872db679b35e21` ([181.lean](https://github.com/google-deepmind/formal-conjectures/blob/9d259649abe0b02d7a25f7589b872db679b35e21/FormalConjectures/ErdosProblems/181.lean)):

```lean
namespace Erdos181

open SimpleGraph

theorem erdos_181 :
    ∃ C > (0 : ℝ), ∀ n : ℕ,
      (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n
```

`hypercube n` is the graph on `Fin n → Bool` whose edges join vectors that differ in exactly one coordinate. `graphRamsey G H` is the `sInf` of the sizes `M` such that, for every graph `C` on `Fin M`, `G` is contained in `C` or `H` is contained in its complement; `diagonalGraphRamsey G` is `graphRamsey G G`. Containment is Mathlib's `IsContained`, an injective homomorphism, so a monochromatic copy need not be induced, as in the paper. For the cube this set of sizes is nonempty and does not contain `0`, so its `sInf` is the least positive such size and the bound is not vacuous: [Bridge.lean](HypercubeRamsey/Bridge.lean) proves that `diagonalGraphRamsey (hypercube n)` equals OpenAI's `ramseyNumber (cube n)`, an infimum over positive sizes, and [TargetProbes.lean](Audit/TargetProbes.lean) checks `2 ^ n ≤ diagonalGraphRamsey (hypercube n)`.

[Challenge.lean](Challenge.lean) holds this statement and the definitions it uses, copied from Formal Conjectures, and imports only Mathlib. [HypercubeRamsey/Main.lean](HypercubeRamsey/Main.lean) proves a theorem of the same name and statement over an identical copy of the definitions in [HypercubeRamsey/FormalConjectures.lean](HypercubeRamsey/FormalConjectures.lean). [Challenge.json](Challenge.json) configures Comparator to compare the two modules. [docs/verification.md](docs/verification.md) describes the statement checks and the differences from Formal Conjectures' files.

## How the proof is organized

The formal proof follows the paper. OpenAI's Lean library supplies the cube graph, its Ramsey number, finite Ramsey bounds, and the paper's Lemma 2.1: if `R(Q_n) / 2^n` is unbounded, there is a sequence of red-blue colourings between two equal host sides with no monochromatic cube across the sides. This repository formalizes the rest of the paper, which shows that no such sequence exists.

| Path | Content |
| --- | --- |
| `HypercubeRamsey/Bridge.lean` | `hypercube n` is OpenAI's `cube n`, and `diagonalGraphRamsey` agrees with OpenAI's `ramseyNumber` on it |
| `HypercubeRamsey/Framework/`, `HypercubeRamsey/Assembly.lean` | counterexample sequences, laws on the host sides, stages, patches and discrepancy bounds |
| `HypercubeRamsey/S03/` to `HypercubeRamsey/S18/` | Sections 3 to 18 of the paper |
| `HypercubeRamsey/PartC/` | definitions and constants shared by Sections 12 to 18 |
| `HypercubeRamsey/Tools/` | general lemmas: binomial and concentration estimates, martingales, cube geometry |
| `HypercubeRamsey/Interface.lean` | Corollaries 7.2, 10.2 and 11.4, with the argument of Sections 12 to 18, exclude a counterexample sequence |
| `HypercubeRamsey/Main.lean` | `Erdos181.erdos_181` |
| `Audit/TargetProbes.lean`, `Audit/IndependentRestatement.lean` | kernel-checked probes of the target's definitions, and a restatement of Theorem 1.1 in elementary terms proved equivalent to the target |

## Build and verify

Requirements: Git, Python 3, and [elan](https://github.com/leanprover/elan), with `lake` available on `PATH`. From the repository root, a fresh checkout is prepared with:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's `lake update` hook exits with an error beginning `iut: Lake resolved an unexpected checkout at …` after resolving the dependencies and writing `lake-manifest.json`. Run the patch script next; it applies OpenAI's Lean 4.34.1 compatibility patches to the fetched packages and can be run again after another `lake update`.

To check the statement and the axioms, run:

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

The script builds `HypercubeRamsey.Main`, checks that the definitions and the elaborated statement of `Erdos181.erdos_181` agree with `Challenge.lean`, and checks that the theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. It exits with status 0 when every check passes, 2 when the proof still depends on `sorryAx`, and 1 on any other failure. `./scripts/replay.sh` replays the theorem's module and everything it imports in a fresh Lean kernel environment. [docs/verification.md](docs/verification.md) describes each check and the Comparator configuration.

## Fixed dependencies

- Lean `v4.34.1`, selected by [lean-toolchain](lean-toolchain).
- [Mathlib](https://github.com/leanprover-community/mathlib4), commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- OpenAI's [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- The remaining dependency revisions, pinned by OpenAI's library, are fixed in [lake-manifest.json](lake-manifest.json).

## Mathematical references

- OpenAI, [*The hypercube Ramsey number has linear order*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf), September 23, 2026.
- S. A. Burr and P. Erdős, [On the magnitude of generalized Ramsey numbers for graphs](https://www.renyi.hu/~p_erdos/1975-26.pdf), in *Infinite and Finite Sets*, Vol. I, Colloquia Mathematica Societatis János Bolyai 10, North-Holland, 1975, 215–240. Section 7 asks whether the cubes have linear Ramsey numbers.
- [Erdős problem 181](https://www.erdosproblems.com/181).

## License

Apache-2.0; see [LICENSE](LICENSE), [NOTICE](NOTICE), and [third-party attribution](THIRD_PARTY.md).
