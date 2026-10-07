#!/usr/bin/env python3
"""Resolve a lane's FREEZE.txt into `Module:FullName` items for leancheck.

  freeze_list.py FREEZE.txt FILE...   FILEs are the lane's Lean sources (paths relative to the repo root)

Entries may be `Module:Name`, `FullName` or a short name. The declaration is located in FILEs by its last name
component; the full name is built from the enclosing `namespace` blocks. Prints one `Module:FullName` per line and
lists unresolved entries on stderr (exit 1 if any).
"""
import re, sys
from pathlib import Path

KW = r'(?:noncomputable\s+)?(?:protected\s+)?(?:def|theorem|lemma|structure|abbrev|inductive|class|instance|opaque)'


def decls(path):
    out, ns = {}, []
    for line in Path(path).read_text().splitlines():
        m = re.match(r'\s*namespace\s+(\S+)', line)
        if m:
            ns.append(m.group(1)); continue
        m = re.match(r'\s*end\s+(\S+)\s*$', line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop(); continue
        m = re.match(r'\s*(?:@\[[^\]]*\]\s*)?' + KW + r'\s+([^\s(:{\[]+)', line)
        if m:
            name = m.group(1)
            full = '.'.join(ns + [name]) if not name.startswith('_root_.') else name[7:]
            out.setdefault(name.split('.')[-1], []).append((full, path))
    return out


def main():
    entries = [l.strip() for l in Path(sys.argv[1]).read_text().splitlines() if l.strip() and not l.startswith('#')]
    table = {}
    for f in sys.argv[2:]:
        for k, v in decls(f).items():
            table.setdefault(k, []).extend(v)
    bad = 0
    for e in entries:
        name = e.split(':', 1)[1] if ':' in e else e
        short = name.split('.')[-1]
        cands = [c for c in table.get(short, []) if c[0].endswith(name) or name.endswith(c[0]) or c[0] == name]
        if not cands:
            cands = table.get(short, [])
        if len(cands) != 1:
            # structure fields and constructors: use the given module, or the module of the enclosing declaration
            if ':' in e and len(cands) == 0:
                print(e); continue
            pre = [c for k, cs in table.items() for c in cs if name.startswith(c[0] + '.')] if not cands else []
            if len(pre) >= 1 and len({c[1] for c in pre}) == 1:
                print(f"{pre[0][1][:-5].replace('/', '.')}:{name}"); continue
            print(f'unresolved: {e} ({len(cands)} candidates)', file=sys.stderr); bad += 1; continue
        full, path = cands[0]
        print(f"{path[:-5].replace('/', '.')}:{full}")
    sys.exit(1 if bad else 0)


main()
