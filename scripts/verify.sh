#!/usr/bin/env bash
# Build Erdos181.erdos_181, check its statement against Challenge.lean, and check its axioms.
#
# Exit 0: every check passed. Exit 2: the proof still depends on sorryAx. Exit 1: any other failure, including
# an axiom outside propext, Classical.choice and Quot.sound.
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

lake build HypercubeRamsey.Main || exit 1

# The copied Formal Conjectures definitions are identical in Challenge.lean and the proof.
python3 scripts/check_target.py defs
# The statement and the definitions it uses elaborate identically in both (pp.all).
python3 scripts/check_target.py statement

result_dir=.lake/verification-results
mkdir -p "$result_dir"
axiom_log="$result_dir/axioms.log"
if ! lake env lean --trust=0 scripts/Axioms.lean >"$axiom_log" 2>&1; then
  cat "$axiom_log"
  exit 1
fi
cat "$axiom_log"
python3 scripts/check_axioms.py "$axiom_log"
