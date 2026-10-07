# Lane q-s05-centre notes

## Current state (2026-10-07)

- Read `../../BRIEF-COMMON-LUNA.md`; worktree is clean on `lane/q-s05-centre` at `824b28c`.
- Owned proof holes found: `L5_1j`, `L5_1g_rows`, `L5_1k_rows`, `L5_1l3` in `S05/Centres.lean`, and `L5_1g_common_high_law` in `S05/Stages.lean`.
- No `NOTES.md` or `LOG.md` existed at start; created this note and initialized the heartbeat log.
- Next: inspect parameter requirements and imported theorem dependencies for a sound proof path; then attempt the most reusable theorem (`L5_1g_common_high_law`) and evaluate feasibility of the other claims. Frozen statements/definitions must remain untouched.
- Not yet proved or verified. Acceptance command has not been run.

## Dependency audit (2026-10-07)

- The older Section 5 lane reported an `Empty`-reference counterexample to its former `L5_1g_common_high_law`, but that does **not** refute this frozen s05v2 statement: current `HighRowModel5` has `capped_feasible` (Stages.lean:37–42), which supplies the cap/support law even when `Ref` is empty. Raw current source confirmed this difference.
- Current `L5_1g_common_high_law` still needs the simultaneous-cost/separation argument when `Ref` is nonempty; no reusable minimax lemma was found in the imported Mathlib/OAI sources.
- `L5_1g_rows`, `L5_1j`, `L5_1k_rows`, and `L5_1l3` remain unproved. No frozen statement is yet established false. No proof edits made; acceptance remains outstanding.
- Resume by formalizing one of the substantive constructions, preserving the frozen signatures. The required acceptance must still be run before the final report.

## Partial proof and acceptance (2026-10-07)

- `Stages.lean` now proves the failure-bound conjunct of `L5_1g_common_high_law` by `M.failure_bound` and handles `IsEmpty Ref` from `M.capped_feasible`; the remaining `sorry` is only the nonempty-reference simultaneous-cost/separation argument (line 69).
- `lake env lean HypercubeRamsey/S05/Stages.lean` succeeded after that edit (warnings include the remaining `sorry`).
- Required acceptance rerun after the edit: exit status 1. All 129 frozen declarations retained their types, and `other_errors` was empty. The only failures are the five owned proof holes: `L5_1g_rows`, `L5_1j`, `L5_1k_rows`, `L5_1l3`, `L5_1g_common_high_law`; each prints `sorryAx` in addition to `propext`, `Classical.choice`, `Quot.sound`. No false-statement counterexample was established for these current s05v2 contracts.
- The four `Centres.lean` target bodies remain at lines 239, 313, 371, 419. They need, respectively, the centre marking/height success construction; high row selection and its support/cost/locality transfer; low posterior-selection row construction; and the odd-column load concentration argument.
- Before finalizing: commit `Stages.lean`, `NOTES.md`, and `LOG.md` on this branch; write `REPORT.md` only after commit and line-reference check.
