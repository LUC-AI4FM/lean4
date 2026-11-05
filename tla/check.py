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
run(sys.executable, 'audit_standard.py')
run(lake, 'env', 'lean', 'tests/Native.lean')
run(lake, 'env', 'lean', 'tests/Data.lean')
run(lake, 'env', 'lean', 'tests/Temporal.lean')
source = translate(Path('tests/Counter.tla').read_text(), backend='typed')
proof = Path('tests/CounterProof.txt').read_text()
with tempfile.TemporaryDirectory(prefix='check-', dir='.') as directory:
    generated = Path(directory) / 'Counter.lean'
    generated.write_text(source + '\n' + proof)
    run(lake, 'env', 'lean', str(generated))
    # Compile and import in another file: same-file proofs cannot detect
    # accidentally private generated declarations under Lean's module system.
    run(lake, 'env', 'lean', '--root=' + directory, '-o', str(generated.with_suffix('.olean')), str(generated))
    consumer = Path(directory) / 'Consumer.lean'
    consumer.write_text('module\nimport Counter\n' + proof)
    import_env = dict(os.environ)
    import_env['LEAN_PATH'] = str(Path(directory).resolve()) + os.pathsep + import_env.get('LEAN_PATH', '')
    subprocess.run([lake, 'env', 'lean', str(consumer)], env=import_env, check=True)
    # A false invariant must fail in Lean, even when parsing succeeds.
    generated.write_text(source + '\nexample : TLAImported.Counter.Init ⟨⟩ (fun _ => ⟨1⟩) 0 := by rfl\n')
    negative = subprocess.run([lake, 'env', 'lean', str(generated)], capture_output=True, text=True)
    if negative.returncode == 0 or 'error:' not in negative.stdout:
        raise RuntimeError('negative proof was not rejected with a Lean diagnostic')
print('Native and translated proofs passed; false proof rejected.')
