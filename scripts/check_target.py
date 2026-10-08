#!/usr/bin/env python3
"""Check that the proof's target matches Challenge.lean.

  check_target.py defs [FC_CHECKOUT]   definitions block of Challenge.lean equals that of
                                       HypercubeRamsey/FormalConjectures.lean and holds nothing besides the
                                       copied declarations; with FC_CHECKOUT, each declaration (with its
                                       docstring and attribute) appears verbatim in Formal Conjectures'
                                       sources, and Challenge.lean's `namespace Erdos181` section equals
                                       FC's 181.lean section minus its attribute and TODO lines
  check_target.py types                builds HypercubeRamsey.Main; the elaborated statement of
                                       Erdos181.erdos_181 and the definitions it uses, printed with pp.all,
                                       agree between Challenge.lean and HypercubeRamsey.Main; and the
                                       proof's axioms are within propext, Classical.choice, Quot.sound
  check_target.py statement            as `types`, without the axiom check (scripts/verify.sh checks the
                                       axioms separately and reports an open proof with its own exit status)
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


PRE, POST = 'namespace SimpleGraph\n\nopen scoped Finset\n', '\nend SimpleGraph'


def erdos_section(text):
    s = text[text.index('namespace Erdos181'):text.index('end Erdos181') + len('end Erdos181')]
    lines = [l for l in s.splitlines() if not l.startswith('@[category') and not l.startswith('-- TODO')]
    return re.sub(r'\n{2,}', '\n\n', '\n'.join(lines)).strip()


def defs(fc):
    a, b = block(ROOT / 'Challenge.lean'), block(ROOT / 'HypercubeRamsey/FormalConjectures.lean')
    ok = a == b
    print(f'definitions block identical: {ok}')
    body = a[len(BEGIN):].strip('\n')
    framed = body.startswith(PRE) and body.rstrip().endswith(POST)
    print(f'block is exactly the SimpleGraph preamble, the declarations and the closing: {framed}')
    ok = ok and framed
    if fc:
        src = '\n'.join((Path(fc) / f).read_text() for f in FC_FILES)
        same = erdos_section((ROOT / 'Challenge.lean').read_text()) == \
            erdos_section((Path(fc) / 'FormalConjectures/ErdosProblems/181.lean').read_text())
        print(f'Erdos181 section equals Formal Conjectures 181.lean (attribute and TODO lines removed): {same}')
        ok = ok and same
        # each declaration with its docstring or attribute is one chunk; text between declarations would make a
        # chunk fail to match
        a = body[len(PRE):].rstrip()[:-len(POST)] if framed else body
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


ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def axioms_of_main():
    fd, p = tempfile.mkstemp(prefix='.check_target_', suffix='.lean', dir=ROOT)
    with os.fdopen(fd, 'w') as f:
        f.write('import HypercubeRamsey.Main\n#print axioms Erdos181.erdos_181\n')
    try:
        r = subprocess.run(['lake', 'env', 'lean', p], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(p)
    out = re.sub(r'\s+', ' ', r.stdout)
    if 'does not depend on any axioms' in out:
        return r.returncode, set()
    m = re.search(r'depends on axioms: \[(.*?)\]', out)
    return r.returncode, ({x.strip() for x in m.group(1).split(',')} if m else None)


def build_main():
    b0 = subprocess.run(['lake', 'build', 'HypercubeRamsey.Main'], cwd=ROOT, capture_output=True, text=True)
    print(f'lake build HypercubeRamsey.Main exit {b0.returncode}')
    if b0.returncode != 0:
        print((b0.stdout + b0.stderr)[-3000:])
    return b0.returncode == 0


def compare_printed(ch):
    """Print the statement and definitions with pp.all from the challenge text `ch` and from HypercubeRamsey.Main."""
    ch_imports = [l for l in ch.splitlines() if l.startswith('import ')]
    ch_body = [l for l in ch.splitlines() if not l.startswith('import ')]
    rc1, a = printed(ch_imports + ch_body)
    rc2, b = printed(['import HypercubeRamsey.Main'])
    a = a.replace("declaration uses 'sorry'", '').replace('declaration uses `sorry`', '')
    a = '\n'.join(l for l in a.splitlines() if not l.startswith('warning'))
    b = '\n'.join(l for l in b.splitlines() if not l.startswith('warning'))
    same = rc1 == 0 and rc2 == 0 and a.strip() == b.strip() and 'erdos_181' in a
    print(f'challenge exit {rc1}, main exit {rc2}, pp.all outputs identical: {a.strip() == b.strip()}')
    return same, a, b


def types():
    if not build_main():
        return False
    rc0, ax = axioms_of_main()
    ax_ok = rc0 == 0 and ax is not None and ax <= ALLOWED
    print(f'axioms of Erdos181.erdos_181: {sorted(ax) if ax is not None else "unparsed"}; allowed: {ax_ok}')
    same, a, b = compare_printed((ROOT / 'Challenge.lean').read_text())
    ok = ax_ok and same
    if not ok:
        print('--- challenge\n' + a[-3000:] + '\n--- main\n' + b[-3000:])
    return ok


def statement():
    if not build_main():
        return False
    same, a, b = compare_printed((ROOT / 'Challenge.lean').read_text())
    if not same:
        print('--- challenge\n' + a[-3000:] + '\n--- main\n' + b[-3000:])
    return same


if __name__ == '__main__':
    if len(sys.argv) >= 2 and sys.argv[1] == 'defs':
        sys.exit(0 if defs(sys.argv[2] if len(sys.argv) > 2 else None) else 1)
    if len(sys.argv) == 2 and sys.argv[1] == 'types':
        sys.exit(0 if types() else 1)
    if len(sys.argv) == 2 and sys.argv[1] == 'statement':
        sys.exit(0 if statement() else 1)
    sys.exit(__doc__)
