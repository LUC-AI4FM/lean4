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
            'fixtures/Binders.tla', 'fixtures/Universal.tla', 'fixtures/Claims.tla', 'fixtures/Temporal.tla', 'fixtures/ValueForms.tla', 'fixtures/Strings.tla', 'fixtures/Finite.tla', 'fixtures/Recursive.tla', 'fixtures/StructuredClaims.tla', 'fixtures/Mutual.tla', 'fixtures/RealNumbers.tla', 'fixtures/StandardLibrary.tla', 'fixtures/Labels.tla', 'fixtures/HigherOrder.tla', 'fixtures/LevelClaims.tla']
fixtures += [str(p.relative_to(root.parent / 'tests')) for p in sorted((root.parent / 'tests' / 'corpus').glob('*.tla'))]
failures = []
with tempfile.TemporaryDirectory(prefix='universal-check-', dir='.') as directory:
    for fixture in fixtures:
        source = root.parent / 'tests' / fixture
        target = Path(directory) / source.with_suffix('.lean').name
        code = compile_file(source, includes=[root.parent / 'tests' / 'corpus' / 'tlaps'])
        if source.name == 'Counter.tla':
            code += (root / 'CounterProof.txt').read_text()
        if source.name == 'LevelClaims.tla':
            code += "\nexample (c : LevelClaims.Constants) : LevelClaims.Certificate c := by\n  constructor <;> intros <;> simp [LevelClaims.TLAProofClaim0, LevelClaims.TLAProofClaim1, LevelClaims.TLAProofClaim2, LevelClaims.TLAProofClaim3, LevelClaims.TLAProofClaim4, LevelClaims.TLAProofClaim5, truth_boolean]\n"
        if source.name == 'HigherOrder.tla':
            code += "\nexample (c : HigherOrder.Constants) (b : Behavior) (n : Nat) : HigherOrder.Answer c b n = integer 3 := by simp only [HigherOrder.Answer, intBinary_integer]; rfl\nexample (c : HigherOrder.Constants) (b : Behavior) (n : Nat) : HigherOrder.ConstantCall c b n = c.F (integer 2) := rfl\n"
        if source.name == 'Labels.tla':
            code += "\nexample (c : Labels.Constants) (b : Behavior) (n : Nat) : truth (Labels.B c b n) := by simp [Labels.B, truth_boolean]\n"
        if source.name == 'Recursive.tla':
            code += (root / 'RecursiveProof.txt').read_text()
        if source.name == 'RealNumbers.tla':
            code = code.replace('import TLAUniversal', 'import TLAUniversal\nimport Mathlib.Tactic.NormNum')
            code += (root / 'RealProof.txt').read_text()
        if source.name == 'StructuredClaims.tla':
            code += "\nexample (c : StructuredClaims.Constants) : StructuredClaims.Certificate c := by\n  constructor <;> intros <;> simp [StructuredClaims.TLAProofClaim0, StructuredClaims.TLAProofClaim1, truth_boolean]\n"
        target.write_text(code)
        result = subprocess.run([lake, 'env', 'lean', str(target)], capture_output=True, text=True, timeout=120)
        if result.returncode:
            failures.append(fixture)
            print(result.stdout + result.stderr, flush=True)
        print(('FAIL ' if result.returncode else 'PASS ') + fixture, flush=True)
    target = Path(directory) / 'Negative.lean'
    target.write_text('module\nimport TLAUniversal\nexample : TLAUniversal.truth (TLAUniversal.boolean False) := by simp [TLAUniversal.truth_boolean]\n')
    result = subprocess.run([lake, 'env', 'lean', str(target)], capture_output=True, text=True)
    if result.returncode == 0 or 'error:' not in result.stdout:
        raise RuntimeError('false universal-value proof was not rejected')
if failures:
    raise RuntimeError('Universal checks failed: ' + ', '.join(failures))
print('Universal definitions, generated modules and negative proof checks passed.')
