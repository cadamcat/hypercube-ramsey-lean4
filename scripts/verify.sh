#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

lake build HypercubeRamsey.Main Challenge

result_dir=.lake/verification-results
mkdir -p "$result_dir"
axiom_source="$result_dir/Axioms.lean"
axiom_log="$result_dir/axioms.log"
cat > "$axiom_source" <<'LEAN'
import HypercubeRamsey.Main

#print axioms Erdos181.erdos_181
LEAN

if ! lake env lean --trust=0 "$axiom_source" >"$axiom_log" 2>&1; then
  cat "$axiom_log"
  exit 1
fi
cat "$axiom_log"
python3 scripts/check_axioms.py "$axiom_log"
