# Acceptance record

The exact 129-declaration command from the lane `BRIEF.md` was run against `runs/frozen/s05v2.json` after the `Stages.lean` proof edit.

Command:

```sh
cd wt && python3 "tools/leancheck.py" accept . \
  "runs/frozen/s05v2.json" \
  [all 129 declaration names listed in the lane BRIEF.md]
```

Exit status: **1**.

All 129 declarations kept their frozen types. `other_errors` was empty. Five declarations failed only their axiom check, each printing `[propext, sorryAx, Classical.choice, Quot.sound]`:

- `HypercubeRamsey.Setup5.L5_1g_rows`
- `HypercubeRamsey.Setup5.L5_1j`
- `HypercubeRamsey.Setup5.L5_1k_rows`
- `HypercubeRamsey.Setup5.L5_1l3`
- `HypercubeRamsey.L5_1g_common_high_law`

For the first four, `sorryAx` comes from the proof body at `Centres.lean:239`, `:313`, `:371`, and `:419`, respectively. For the common high-law theorem, the remaining own `sorry` is at `Stages.lean:69`; its failure-bound conjunct and empty-reference case are proved at lines 64–74.
