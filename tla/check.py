#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Build the library, run translator tests, and check both proof entry points."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
from translate import translate

os.chdir(Path(__file__).resolve().parent)
lake = os.environ.get('LAKE', 'lake')

def run(*args):
    subprocess.run(args, check=True)

run(lake, 'build')
run(sys.executable, '-m', 'unittest', 'discover', '-s', 'tests')
run(lake, 'env', 'lean', 'tests/Native.lean')
run(lake, 'env', 'lean', 'tests/Data.lean')
run(lake, 'env', 'lean', 'tests/Temporal.lean')
source = translate(Path('tests/Counter.tla').read_text(), backend='typed')
proof = Path('tests/CounterProof.txt').read_text()
with tempfile.TemporaryDirectory(prefix='check-', dir='.') as directory:
    generated = Path(directory) / 'Counter.lean'
    generated.write_text(source + '\n' + proof)
    run(lake, 'env', 'lean', str(generated))
    # A false invariant must fail in Lean, even when parsing succeeds.
    generated.write_text(source + '\nexample : Counter.Init ⟨⟩ (fun _ => ⟨1⟩) 0 := by rfl\n')
    negative = subprocess.run([lake, 'env', 'lean', str(generated)], capture_output=True, text=True)
    if negative.returncode == 0 or 'error:' not in negative.stdout:
        raise RuntimeError('negative proof was not rejected with a Lean diagnostic')
print('Native and translated proofs passed; false proof rejected.')
