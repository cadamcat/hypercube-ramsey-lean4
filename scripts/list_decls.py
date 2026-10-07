#!/usr/bin/env python3
"""List the declarations of a module prefix as `Module:Name`, from the compiled environment.

  list_decls.py PREFIX MODULE...   import MODULEs (built), print every constant whose module starts with PREFIX,
                                   skipping auxiliary recursors, no-confusion and internal names
"""
import os, subprocess, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
prefix, mods = sys.argv[1], sys.argv[2:]
src = '\n'.join(f'import {m}' for m in mods) + f'''
open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let skip := ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn", "binductionOn",
    "ibelow", "injEq", "inj", "sizeOf_spec", "ctorIdx", "toCtorIdx", "ext_iff", "eq_def", "eq_1", "eq_2"]
  for (n, _) in env.constants.toList do
    if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n then continue
    if skip.contains (n.getString!) then continue
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (`{prefix}).isPrefixOf m then IO.println s!"{{m}}:{{n}}"
'''
fd, p = tempfile.mkstemp(prefix='.list_decls_', suffix='.lean', dir=ROOT)
os.write(fd, src.encode()); os.close(fd)
try:
    r = subprocess.run(['lake', 'env', 'lean', p], cwd=ROOT, capture_output=True, text=True)
finally:
    os.unlink(p)
lines = sorted({l for l in r.stdout.splitlines() if ':' in l and not l.startswith(p)})
print('\n'.join(lines))
if r.returncode != 0:
    print(r.stdout[-1500:] + r.stderr[-1500:], file=sys.stderr); sys.exit(1)
