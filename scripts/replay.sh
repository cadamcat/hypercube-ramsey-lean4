#!/usr/bin/env bash
# Replay HypercubeRamsey.Main and every module it imports, Mathlib and OpenAI's library included, in a fresh
# Lean kernel environment. This takes much longer than scripts/verify.sh.
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
mkdir -p .lake/verification-results

lake build HypercubeRamsey.Main
lake env leanchecker --fresh HypercubeRamsey.Main 2>&1 | tee .lake/verification-results/replay.log
