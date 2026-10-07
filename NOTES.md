# Lane q-s05-centre notes

## Current state (2026-10-07)

- Read `../../BRIEF-COMMON-LUNA.md`; worktree branch is `lane/q-s05-centre`.
- Owned proof holes: `L5_1j`, `L5_1g_rows`, `L5_1k_rows`, `L5_1l3` in `S05/Centres.lean`, and `L5_1g_common_high_law` in `S05/Stages.lean`.
- The common-high-law proof now handles the direct failure bound, empty-reference case, and singleton-reference case. Four center theorems and the multi-reference separation step remain open.
- Acceptance was rerun after the final proof edit and is summarized in `ACCEPTANCE.md`; exit status 1 with only these five own `sorryAx` failures.
- Next: resume with the finite separation proof in the high-law theorem, then the four center constructions. Frozen statements/definitions must remain untouched.

## Dependency audit (2026-10-07)

- The older Section 5 lane reported an `Empty`-reference counterexample to its former `L5_1g_common_high_law`, but that does **not** refute this frozen s05v2 statement: current `HighRowModel5` has `capped_feasible` (Stages.lean:37–42), which supplies the cap/support law even when `Ref` is empty. Raw current source confirmed this difference.
- Current `L5_1g_common_high_law` still needs the simultaneous-cost/separation argument when `Ref` is nonempty; no reusable minimax lemma was found in the imported Mathlib/OAI sources.
- `L5_1g_rows`, `L5_1j`, `L5_1k_rows`, and `L5_1l3` remain unproved. No frozen statement is yet established false.
- Resume by formalizing the substantive constructions while preserving the frozen signatures.

## Partial proof and acceptance (2026-10-07)

- `Stages.lean` now proves the failure-bound conjunct of `L5_1g_common_high_law` by `M.failure_bound`, handles `IsEmpty Ref` from `M.capped_feasible`, and uses `price_feasible` for a singleton reference; the remaining `sorry` is the multi-reference simultaneous-cost/separation argument (line 81).
- `lake env lean HypercubeRamsey/S05/Stages.lean` succeeded after the latest proof edit (warnings include the remaining `sorry`).
- Required acceptance rerun after the edit: exit status 1. All 129 frozen declarations retained their types, and `other_errors` was empty. The only failures are the five owned proof holes: `L5_1g_rows`, `L5_1j`, `L5_1k_rows`, `L5_1l3`, `L5_1g_common_high_law`; each prints `sorryAx` in addition to `propext`, `Classical.choice`, `Quot.sound`. No false-statement counterexample was established for these current s05v2 contracts.
- The four `Centres.lean` target bodies remain at lines 239, 313, 371, 419. They need, respectively, the centre marking/height success construction; high row selection and its support/cost/locality transfer; low posterior-selection row construction; and the odd-column load concentration argument.
- Before finalizing: commit the latest `Stages.lean` edit and updated acceptance/state records; then write `REPORT.md` as the final file action.
