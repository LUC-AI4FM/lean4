#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Translate an unchanged TLA+ proof script and check the generated proof in Lean."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile
from compiler import CompileError
from proofs import compile_proofs
from sany import SanyError


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('-o', '--output', type=Path, required=True)
    parser.add_argument('-I', '--include', type=Path, action='append', default=[])
    parser.add_argument('--timeout', type=int, default=120)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error('timeout must be positive')
    root = Path(__file__).resolve().parent
    try:
        code = compile_proofs(args.source, includes=args.include)
        with tempfile.TemporaryDirectory(prefix='proof-check-', dir=root / 'universal') as directory:
            target = Path(directory) / 'Proof.lean'
            target.write_text(code)
            result = subprocess.run([os.environ.get('LAKE', 'lake'), 'env', 'lean', str(target)],
                                    cwd=root / 'universal', capture_output=True, text=True, timeout=args.timeout)
            if result.returncode:
                parser.exit(1, 'tla-proof: Lean rejected the generated proof:\n' + result.stdout + result.stderr)
        # Preserve existing output when translation or checking fails.
        args.output.write_text(code)
    except (CompileError, SanyError, OSError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f'tla-proof: {error}\n')
    print(f'Lean checked {args.source.name}; wrote {args.output}')


if __name__ == '__main__':
    main()
