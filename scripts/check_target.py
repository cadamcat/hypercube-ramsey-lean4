#!/usr/bin/env python3
"""Check that the proof's target matches Challenge.lean.

  check_target.py defs [FC_CHECKOUT]   definitions block of Challenge.lean equals that of
                                       HypercubeRamsey/FormalConjectures.lean; with FC_CHECKOUT, each
                                       definition also appears verbatim in Formal Conjectures' sources
  check_target.py types                elaborated statement of Erdos181.erdos_181 and the definitions it
                                       uses, printed with pp.all, agree between Challenge.lean and
                                       HypercubeRamsey.Main (run after `lake build HypercubeRamsey.Main`)
Exit 0 only when every check passes.
"""
import re, subprocess, sys, tempfile, os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BEGIN, END = '-- BEGIN FORMAL CONJECTURES DEFINITIONS', '-- END FORMAL CONJECTURES DEFINITIONS'
NAMES = ['Erdos181.erdos_181', 'SimpleGraph.hypercube', 'SimpleGraph.graphRamsey',
         'SimpleGraph.diagonalGraphRamsey', 'SimpleGraph.IsContained', 'SimpleGraph.Copy']
FC_FILES = ['FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Hypercube.lean',
            'FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean']


def block(path):
    s = path.read_text()
    return s[s.index(BEGIN):s.index(END)]


def defs(fc):
    a, b = block(ROOT / 'Challenge.lean'), block(ROOT / 'HypercubeRamsey/FormalConjectures.lean')
    ok = a == b
    print(f'definitions block identical: {ok}')
    if fc:
        src = '\n'.join((Path(fc) / f).read_text() for f in FC_FILES)
        # each top-level declaration with its docstring, as one chunk
        a = re.sub(r'\n\s*end SimpleGraph\s*$', '', a.rstrip())
        chunks = [c.strip() for c in re.split(r'\n(?=/--|@\[simp\]\n|noncomputable def|def |theorem )', a)
                  if re.match(r'(/--|@\[simp\]|noncomputable def|def |theorem )', c.strip())]
        for c in chunks:
            hit = c in src
            print(f'verbatim in Formal Conjectures: {hit}: {c.splitlines()[0][:70]}')
            ok = ok and hit
        ok = ok and len(chunks) >= 4
    return ok


def printed(header_lines):
    body = header_lines + ['set_option pp.all true'] + \
        [f'#check @{NAMES[0]}'] + [f'#print {n}' for n in NAMES[1:]]
    fd, p = tempfile.mkstemp(prefix='.check_target_', suffix='.lean', dir=ROOT)
    with os.fdopen(fd, 'w') as f:
        f.write('\n'.join(body) + '\n')
    try:
        r = subprocess.run(['lake', 'env', 'lean', p], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(p)
    out = re.sub(r'^.*?:\d+:\d+: ', '', r.stdout, flags=re.M)
    return r.returncode, out


def types():
    ch = (ROOT / 'Challenge.lean').read_text()
    ch_imports = [l for l in ch.splitlines() if l.startswith('import ')]
    ch_body = [l for l in ch.splitlines() if not l.startswith('import ')]
    rc1, a = printed(ch_imports + ch_body)
    rc2, b = printed(['import HypercubeRamsey.Main'])
    a = a.replace("declaration uses 'sorry'", '').replace('declaration uses `sorry`', '')
    a = '\n'.join(l for l in a.splitlines() if not l.startswith('warning'))
    b = '\n'.join(l for l in b.splitlines() if not l.startswith('warning'))
    ok = rc1 == 0 and rc2 == 0 and a.strip() == b.strip() and 'erdos_181' in a
    print(f'challenge exit {rc1}, main exit {rc2}, pp.all outputs identical: {a.strip() == b.strip()}')
    if not ok:
        print('--- challenge\n' + a[-3000:] + '\n--- main\n' + b[-3000:])
    return ok


if __name__ == '__main__':
    if len(sys.argv) >= 2 and sys.argv[1] == 'defs':
        sys.exit(0 if defs(sys.argv[2] if len(sys.argv) > 2 else None) else 1)
    if len(sys.argv) == 2 and sys.argv[1] == 'types':
        sys.exit(0 if types() else 1)
    sys.exit(__doc__)
