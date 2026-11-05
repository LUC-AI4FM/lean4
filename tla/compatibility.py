#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Check unchanged upstream modules, retaining every failure in a JSON report."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
from sany import parse_file, SanyError
from universal_compile import UniversalCompiler


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference_root', type=Path)
    parser.add_argument('-I', '--include', action='append', type=Path, default=[])
    parser.add_argument('--shard', type=int, default=0)
    parser.add_argument('--shards', type=int, default=1)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    if not 0 <= args.shard < args.shards:
        parser.error('shard must be between zero and shards minus one')
    root = Path(__file__).resolve().parent
    reference = args.reference_root.resolve()
    includes = [p.resolve() for p in args.include]
    sources = sorted(reference.rglob('*.tla'))[args.shard::args.shards]
    if not sources:
        parser.error('no source modules selected')
    lake = os.environ.get('LAKE', 'lake')
    results = []
    with tempfile.TemporaryDirectory(prefix='compatibility-', dir=root / 'universal') as directory:
        target = Path(directory) / 'Generated.lean'
        for source in sources:
            item = {'source': str(source.relative_to(reference))}
            try:
                graph = parse_file(source, includes=includes)
            except SanyError as error:
                item.update(status='frontend_rejected', diagnostic=str(error))
            else:
                try:
                    target.write_text(UniversalCompiler(graph).compile())
                except Exception as error:
                    item.update(status='translation_failed', diagnostic=f'{type(error).__name__}: {error}')
                else:
                    try:
                        checked = subprocess.run([lake, 'env', 'lean', str(target)], cwd=root / 'universal',
                                                 capture_output=True, text=True, timeout=120)
                        item.update(status='pass' if checked.returncode == 0 else 'lean_failed')
                        if checked.returncode:
                            item['diagnostic'] = checked.stdout + checked.stderr
                    except subprocess.TimeoutExpired:
                        item.update(status='lean_timeout', diagnostic='Lean exceeded 120 seconds')
            results.append(item)
            print(item['status'].upper(), item['source'], flush=True)
            # Persist progress even when the overall CI time limit is reached.
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps({'selected': len(sources), 'results': results}, indent=2))
    failed = sum(item['status'] != 'pass' for item in results)
    print(f'{len(results) - failed}/{len(results)} modules passed; {failed} need investigation.', flush=True)
    return 1 if failed else 0


if __name__ == '__main__':
    raise SystemExit(main())
