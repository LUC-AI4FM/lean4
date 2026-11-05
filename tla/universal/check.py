#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Check universal semantics and generated modules without compiling on the coordinator."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
os.chdir(root)
sys.path.insert(0, str(root.parent))
from universal_compile import compile_file

lake = os.environ.get('LAKE', 'lake')
subprocess.run([lake, 'build'], check=True)
fixtures = ['Counter.tla', 'fixtures/Collections.tla', 'fixtures/Records.tla',
            'fixtures/Binders.tla', 'fixtures/Universal.tla', 'fixtures/Claims.tla', 'fixtures/Temporal.tla', 'fixtures/ValueForms.tla', 'fixtures/Strings.tla', 'fixtures/Finite.tla', 'fixtures/Recursive.tla', 'fixtures/StructuredClaims.tla']
fixtures += [str(p.relative_to(root.parent / 'tests')) for p in sorted((root.parent / 'tests' / 'corpus').glob('*.tla'))]
with tempfile.TemporaryDirectory(prefix='universal-check-', dir='.') as directory:
    for fixture in fixtures:
        source = root.parent / 'tests' / fixture
        target = Path(directory) / source.with_suffix('.lean').name
        code = compile_file(source, includes=[root.parent / 'tests' / 'corpus' / 'tlaps'])
        if source.name == 'Counter.tla':
            code += (root / 'CounterProof.txt').read_text()
        if source.name == 'StructuredClaims.tla':
            code += "\nexample (c : StructuredClaims.Constants) : StructuredClaims.Certificate c := by\n  constructor <;> intros <;> simp [StructuredClaims.TLAProofClaim0, StructuredClaims.TLAProofClaim1, truth_boolean]\n"
        target.write_text(code)
        subprocess.run([lake, 'env', 'lean', str(target)], check=True, timeout=120)
    target = Path(directory) / 'Negative.lean'
    target.write_text('module\nimport TLAUniversal\nexample : TLAUniversal.truth (TLAUniversal.boolean False) := by simp [TLAUniversal.truth_boolean]\n')
    result = subprocess.run([lake, 'env', 'lean', str(target)], capture_output=True, text=True)
    if result.returncode == 0 or 'error:' not in result.stdout:
        raise RuntimeError('false universal-value proof was not rejected')
print('Universal definitions, generated modules and negative proof checks passed.')
