#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Translate an existing TLA+ module through SANY to Lean definitions."""
import argparse
from pathlib import Path
import re
import tempfile
from compiler import compile_file as compile_typed, CompileError
from universal_compile import compile_file

TranslationError = CompileError

def translate(source, *, backend="universal"):
    """Translate a self-contained module string; use compile_file for local imports."""
    match = re.search(r'-{4,}\s*MODULE\s+([A-Za-z_][A-Za-z_0-9]*)\s*-{4,}', source)
    if not match:
        raise TranslationError('expected a TLA+ MODULE header')
    with tempfile.TemporaryDirectory(prefix='tla-source-') as directory:
        path = Path(directory) / (match.group(1) + '.tla')
        path.write_text(source)
        if backend not in ("universal", "typed"):
            raise TranslationError(f"unknown backend: {backend}")
        return (compile_typed if backend == "typed" else compile_file)(path)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('-o', '--output', type=Path, required=True)
    parser.add_argument('-I', '--include', type=Path, action='append', default=[])
    parser.add_argument("--backend", choices=("universal", "typed"), default="universal")
    args = parser.parse_args()
    try:
        compile = compile_typed if args.backend == "typed" else compile_file
        output = compile(args.source, includes=args.include)
        args.output.write_text(output)
    except (CompileError, OSError) as error:
        parser.exit(1, f'tla: {error}\n')

if __name__ == '__main__':
    main()
