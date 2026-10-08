# Reproducing the verification

The project uses Lean `v4.34.1`, selected by [lean-toolchain](../lean-toolchain). Mathlib (commit `d13f23b723b8a846827a245b89c10fc7d3f11612`), OpenAI's library (commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`) and the other package revisions are locked in [lake-manifest.json](../lake-manifest.json).

## Fresh checkout

From the repository root, prepare the dependencies and build the project:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's Lake hook exits with an error beginning `iut: Lake resolved an unexpected checkout at …`. It has still resolved the dependencies and written `lake-manifest.json`; run the patch script after that error. The script applies the `*-lean4341.patch` files from OpenAI's package to the fetched packages and skips patches that are already applied. The hook leaves unused package clones under `.lake/packages/OAI/lean/.lake/packages/`; those clones can be removed.

## Statement and axiom checks

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

The script runs four checks in order and stops at the first failure:

1. `lake build HypercubeRamsey.Main` builds the theorem and every project module it imports.
2. `python3 scripts/check_target.py defs` checks that the block between the `BEGIN` and `END FORMAL CONJECTURES DEFINITIONS` markers is identical in `Challenge.lean` and `HypercubeRamsey/FormalConjectures.lean`, and that it holds only the copied declarations. The proof never imports `Challenge.lean`; this block is what its definitions share with the challenge.
3. `python3 scripts/check_target.py statement` elaborates `Challenge.lean` and, in a separate Lean run, `HypercubeRamsey.Main`. Each run prints, with `set_option pp.all true`, the type of `Erdos181.erdos_181` and the declarations `SimpleGraph.hypercube`, `SimpleGraph.graphRamsey`, `SimpleGraph.diagonalGraphRamsey`, `SimpleGraph.IsContained` and `SimpleGraph.Copy`. The two outputs must be identical. Separate runs are needed because both modules declare the same names.
4. `lake env lean --trust=0 scripts/Axioms.lean` prints the axioms of `Erdos181.erdos_181`, and `scripts/check_axioms.py` parses the report. The accepted axioms are `propext`, `Classical.choice` and `Quot.sound`.

The script exits with status 0 when all four checks pass. If the theorem or a dependency still has an open proof, the axiom report lists `sorryAx` and the script exits with status 2. Any other axiom, a missing or unparsable report, a Lean error, or a failed build or statement check gives status 1. The axiom report is written to `.lake/verification-results/axioms.log`. `python3 scripts/check_target.py types` runs checks 1, 3 and 4 in one command and fails on `sorryAx` like on any other axiom outside the accepted set.

The build compiles the project's modules and the modules of OpenAI's library they import. For Mathlib it uses the compiled artifacts that `lake exe cache get` downloads for the pinned revision and does not rebuild Mathlib from source; `scripts/replay.sh` rechecks those artifacts in the kernel.

## Kernel replay

```sh
./scripts/replay.sh
```

The script builds `HypercubeRamsey.Main` and runs `lake env leanchecker --fresh HypercubeRamsey.Main`, which replays the declarations of the main module and of every module it imports, cached dependency artifacts included, in a fresh Lean kernel environment. The output is written to `.lake/verification-results/replay.log`. The replay covers the whole of Mathlib that the proof imports and takes much longer than `verify.sh`. It is a second check by the same Lean kernel, not by an independent one.

## Comparator

[Challenge.json](../Challenge.json) configures [Comparator](https://github.com/leanprover/comparator) with the challenge module `Challenge`, the solution module `HypercubeRamsey.Main`, the theorem `Erdos181.erdos_181`, and the permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Comparator requires every declaration used in the statement of the listed theorem to be the same in both modules, and the solution's theorem to be accepted by the kernel with only the permitted axioms.

`definition_names` is empty. Comparator treats the names listed there as definition holes, for which it checks only the name, type, universe levels and safety, not the definition itself. The Formal Conjectures definitions are fixed parts of the statement, so listing them would weaken the comparison. Running Comparator requires `lean4export` built for the project's Lean version and the `landrun` sandbox; the Comparator repository describes the setup.

## Independent check of v1.0.0

On 8 October 2026 (UTC), release `v1.0.0` (commit `ad206e1bf8240c28b538dfe72f10364cbc1591da`) was cloned from GitHub onto a new Google Cloud virtual machine (`c4d-standard-32`, 32 cores, Ubuntu 24.04.5 LTS) and checked with the steps above, in order:

| Step | Result |
|---|---|
| `lake update` | exit 1 with the expected `iut: Lake resolved an unexpected checkout` error; all 43 packages checked out at the revisions locked in `lake-manifest.json` |
| `scripts/apply-oai-patches.sh` | exit 0, 23 patches applied |
| `lake exe cache get`, then `lake build` | exit 0 after 1483 s (9673 jobs), no errors and no `sorry` |
| `scripts/verify.sh` | exit 0; `Erdos181.erdos_181` depends on axioms `[propext, Classical.choice, Quot.sound]` |
| `lake env leanchecker --fresh HypercubeRamsey.Main` | exit 0 after 1334 s |
| Comparator with [Challenge.json](../Challenge.json) | exit 0: "Lean default kernel accepts the solution" |

Comparator was [`leanprover/comparator`](https://github.com/leanprover/comparator) at `ca04cfc`, with `lean4export` at `076e8e5` (the `v4.34.0` source) built with the project toolchain `v4.34.1`. It ran with comparator's development stand-in for the `landrun` sandbox, so it checked the statement match and kernel acceptance without isolating the build from the code it checks.

Software Heritage archived the repository with `v1.0.0` at this commit in snapshot `swh:1:snp:18d9fc2a98ef0dee8fc48803afe0e6d0e79eb3eb`.

## Statement fidelity

The statement is the paper's Theorem 1.1, clause by clause:

| Lean statement | Paper, Theorem 1.1 and its definitions |
|---|---|
| `∃ C > (0 : ℝ)` before `∀ n` | an absolute constant `C > 0`, independent of `n` |
| `∀ n : ℕ` | every integer `n ≥ 0`, including `n = 0`, where `R(Q_0) = 1` |
| `hypercube n` on `Fin n → Bool`, adjacency `#{i \| u i ≠ v i} = 1` | `Q_n` on `{0,1}^n`, adjacent when exactly one coordinate differs |
| a graph `C` on `Fin M` and its complement `Cᶜ` | a red-blue colouring of the edges of `K_M` |
| `IsContained`: Mathlib's `Nonempty (Copy G C)`, an injective homomorphism | a monochromatic copy, not required to be induced |
| `sInf` of the sizes `M` with the Ramsey property | the least positive such `M`; for the cube the set is nonempty and excludes `0` |
| `(diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n`, a natural-number power | `R(Q_n) ≤ C 2^n` |

Lean's `sInf` on `ℕ` returns `0` for the empty set, which would make the bound hold trivially. The following kernel-checked files exclude this and other misreadings:

- [Bridge.lean](../HypercubeRamsey/Bridge.lean): `HypercubeRamsey.diagonalGraphRamsey_hypercube` proves that `diagonalGraphRamsey (hypercube n)` equals OpenAI's `ramseyNumber (cube n)`, defined as the infimum over positive sizes with the Ramsey property.
- [Audit/TargetProbes.lean](../Audit/TargetProbes.lean): adjacency in `Q_2`, `2^n` vertices, `R(Q_0) = 1`, and `2 ^ n ≤ diagonalGraphRamsey (hypercube n)` for every `n`.
- [Audit/IndependentRestatement.lean](../Audit/IndependentRestatement.lean): `FidelityProbe.Indep` restates Theorem 1.1 with Mathlib's Hamming distance, symmetric `Bool`-valued colourings of `Fin M` and injective maps, without `sInf` and without the Formal Conjectures or OpenAI definitions. `FidelityProbe.fc_iff_indep` proves it equivalent to the target. Further examples check that `0` is never a Ramsey size, that copies need not be induced, and the direction of `IsContained`.

After `lake build`, check them with:

```sh
lake env lean Audit/TargetProbes.lean
lake env lean Audit/IndependentRestatement.lean
```

To check the copies against Formal Conjectures itself:

```sh
git clone https://github.com/google-deepmind/formal-conjectures
git -C formal-conjectures checkout 9d259649abe0b02d7a25f7589b872db679b35e21
python3 scripts/check_target.py defs formal-conjectures
```

With a checkout argument, `defs` also checks that each copied declaration, with its docstring and attribute, occurs verbatim in Formal Conjectures' `Hypercube.lean` and `Ramsey.lean`, and that the `Erdos181` section of `Challenge.lean` equals that of `181.lean` without its attribute line and TODO comment.

### Differences from Formal Conjectures' files

- The module-system wrappers (`module`, `public import`, `@[expose] public section`) are dropped; the project does not use the module system. They do not change the elaborated definitions.
- The import `Mathlib.Data.Real.Basic`, deprecated at the project's Mathlib pin `d13f23b`, is replaced by its current path `Mathlib.Basic.Real.Basic`. Formal Conjectures pins Mathlib `0df444a`. `SimpleGraph.Copy` has the same fields (`toHom`, `injective'`) at both pins; the order of the implicit arguments of `Copy` and `IsContained` differs between them, with the same meaning.
- The attribute `@[category research open, AMS 5]` on the theorem, which is Formal Conjectures metadata, and the comment `-- TODO: Add variants of the problem.` are omitted.
- The two definition files are merged into one block, so `graphRamsey` sits under `open scoped Finset`. The `EdgeColouring` import and the other declarations of `Ramsey.lean` are omitted. The merged block elaborates to the same definitions as the two separate files.
