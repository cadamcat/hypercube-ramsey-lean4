#!/usr/bin/env python3
"""List public declaration names defined in more than one HypercubeRamsey source file (they break the root build).

Approximate: parses `namespace`/`end` blocks and declaration keywords; skips `private` declarations. Exit 1 if any.
"""
import collections, re, subprocess, sys
files = subprocess.run('git ls-files | grep "^HypercubeRamsey.*\\.lean$"', shell=True, capture_output=True,
                       text=True).stdout.split()
KW = (r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?'
      r'(?:theorem|lemma|def|structure|abbrev|inductive|class|instance|opaque)\s+([^\s(:{\[]+)')
seen = collections.defaultdict(set)
for f in files:
    ns = []
    for line in open(f):
        m = re.match(r'\s*namespace\s+(\S+)', line)
        if m:
            ns.append(m.group(1)); continue
        m = re.match(r'\s*end\s+(\S+)', line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop(); continue
        if re.match(r'\s*private\s', line):
            continue
        m = re.match(KW, line)
        if m and not m.group(1).startswith('_'):
            seen['.'.join(ns + [m.group(1)])].add(f)
dups = {k: sorted(v) for k, v in seen.items() if len(v) > 1}
for k, v in dups.items():
    print(k, ' '.join(v))
sys.exit(1 if dups else 0)
