#!/usr/bin/env python3
"""Check the axiom report of Erdos181.erdos_181 in a captured `#print axioms` log.

Exit 0 when the theorem depends only on propext, Classical.choice and Quot.sound; 2 when it also
depends on sorryAx (an open proof) and on nothing else outside that set; 1 otherwise, including a
missing, repeated or unparsable report.
"""

from pathlib import Path
import re
import sys


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
OPEN = "sorryAx"
TARGET = "Erdos181.erdos_181"
# Lean may wrap a long axiom list over several lines.
REPORT = re.compile(r"'(?P<name>[^'\n]+)' depends on axioms:\s*\[(?P<axioms>[^\]]*)\]")
NO_AXIOMS = re.compile(r"'(?P<name>[^'\n]+)' does not depend on any axioms")


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} AXIOM_LOG", file=sys.stderr)
        return 1

    log = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
    reports = [(m.group("name"), m.group("axioms")) for m in REPORT.finditer(log)]
    reports += [(m.group("name"), "") for m in NO_AXIOMS.finditer(log)]
    if len(reports) != 1:
        print(f"FAIL: expected one axiom report, found {len(reports)}", file=sys.stderr)
        return 1

    name, listed = reports[0]
    if name != TARGET:
        print(f"FAIL: the axiom report is for {name}, not {TARGET}", file=sys.stderr)
        return 1

    axioms = {item.strip() for item in listed.split(",") if item.strip()}
    print(f"Axioms for {TARGET}: {', '.join(sorted(axioms)) or '(none)'}")
    unexpected = axioms - ALLOWED - {OPEN}
    if unexpected:
        print(f"FAIL: axioms outside the permitted set: {', '.join(sorted(unexpected))}", file=sys.stderr)
        return 1
    if OPEN in axioms:
        print(f"OPEN: {TARGET} depends on sorryAx; the proof is incomplete.")
        return 2

    print("PASS: all axioms are in the permitted set.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
