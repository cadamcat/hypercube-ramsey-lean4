#!/usr/bin/env bash
# Apply OpenAI's Lean 4.34.1 compatibility patches to the dependencies that Lake fetched.
#
# OpenAI's `lake update` hook applies these patches only when its own package is the Lake root, so in this
# project they must be applied separately. Run from anywhere after `lake update`; running it again is safe:
# a patch that is already applied is skipped.
#
# Environment: OAI_PATCHES overrides the patch directory (default .lake/packages/OAI/lean/patches).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
packages="$root/.lake/packages"
patches="${OAI_PATCHES:-$packages/OAI/lean/patches}"
if [ ! -d "$patches" ]; then
  echo "error: no patch directory at $patches; run 'lake update' first" >&2
  exit 1
fi
status=0
for patch in "$patches"/*-lean4341.patch; do
  name="$(basename "$patch" -lean4341.patch)"
  dir="$packages/$name"
  if [ ! -d "$dir" ]; then
    echo "skip    $name (package not fetched)"
  elif git -C "$dir" apply --check --reverse "$patch" 2>/dev/null; then
    echo "present $name"
  elif git -C "$dir" apply --check "$patch" 2>/dev/null; then
    git -C "$dir" apply --whitespace=nowarn "$patch"
    git -C "$dir" apply --check --reverse "$patch"
    echo "applied $name"
  else
    echo "error: $name: the patch neither applies nor is already applied" >&2
    status=1
  fi
done
exit "$status"
