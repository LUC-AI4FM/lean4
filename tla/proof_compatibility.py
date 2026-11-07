#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Audit unchanged TLAPS sources; retain failures and never count absent proofs."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
from prover_process import run_prover
from proofs import compile_proofs
from sany import parse_file


def audit(task):
    source, reference, includes, manifest = task
    root = Path(__file__).resolve().parent
    item = {'source': str(source.relative_to(reference)),
            'expected_false': source.name.endswith('_stest.tla')}
    if manifest:
        if item['source'] not in manifest:
            raise ValueError('source absent from reference manifest: ' + item['source'])
        item['reference_positive'] = manifest[item['source']]['positive']
    with tempfile.TemporaryDirectory(prefix='proof-audit-', dir=root / 'universal') as directory:
        target = Path(directory) / 'Proof.lean'
        start = time.monotonic()
        try:
            graph = parse_file(source, includes=includes)
            item['claims'] = len(graph.proof_claims())
            if not item['claims']:
                item['status'] = 'no_claims'
            else:
                target.write_text(compile_proofs(source, includes=includes))
                result = run_prover([os.environ.get('LAKE', 'lake'), 'env', 'lean', str(target)],
                                    cwd=root / 'universal', timeout=float(os.environ.get('TLA_AUDIT_TIMEOUT', '60')))
                item['status'] = 'checked' if result.returncode == 0 else 'lean_rejected'
                if result.returncode:
                    item['diagnostic'] = result.stdout + result.stderr
                elif item['expected_false']:
                    item['status'] = 'UNSOUND_ACCEPTANCE'
        except subprocess.TimeoutExpired:
            item.update(status='timeout', diagnostic='proof reconstruction exceeded time limit')
        except Exception as error:
            item.update(status='translation_rejected', diagnostic=f'{type(error).__name__}: {error}')
        item['seconds'] = round(time.monotonic() - start, 1)
    return item


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference_root', type=Path)
    parser.add_argument('-I', '--include', type=Path, action='append', default=[])
    parser.add_argument('--shard', type=int, default=0)
    parser.add_argument('--shards', type=int, default=1)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--reference-manifest', type=Path)
    parser.add_argument('--sources', nargs='+', help='only these paths relative to the reference root (local runs)')
    parser.add_argument('--jobs', type=int, default=1, help='parallel workers (local runs)')
    args = parser.parse_args()
    if not 0 <= args.shard < args.shards:
        parser.error('invalid shard')
    root = Path(__file__).resolve().parent
    reference = args.reference_root.resolve()
    sources = sorted(reference.rglob('*.tla'))[args.shard::args.shards]
    if args.sources:
        sources = [s for s in sources if str(s.relative_to(reference)) in args.sources]
    if not sources:
        parser.error('empty reference corpus')
    includes = [reference / 'library', *[p.resolve() for p in args.include], root / 'tests/corpus/tlaps']
    manifest = {x['source']: x for x in json.loads(args.reference_manifest.read_text())['results']} if args.reference_manifest else {}
    tasks = [(source, reference, includes, manifest) for source in sources]
    results = []
    report = lambda: args.report.write_text(json.dumps({'selected': len(sources), 'results': results}, indent=2))
    args.report.parent.mkdir(parents=True, exist_ok=True)
    if args.jobs > 1:
        # Local use: each source in its own worker; the result for every
        # source is identical to the sequential run's.
        with ProcessPoolExecutor(args.jobs) as pool:
            for item in pool.map(audit, tasks):
                results.append(item)
                print(item['status'], item['source'], flush=True)
                report()
    else:
        for task in tasks:
            item = audit(task)
            results.append(item)
            print(item['status'], item['source'], flush=True)
            report()
    # Rejection of a negative is not evidence that its intended backend test ran.
    # Unknown and unsupported cases remain explicit, never promoted to passes.
    if manifest:
        return int(any(x['status'] == 'UNSOUND_ACCEPTANCE'
                       or (x['reference_positive'] and x['status'] != 'checked') for x in results))
    return int(any(x['status'] not in ('checked', 'no_claims')
                   and not (x['expected_false'] and x['status'] != 'UNSOUND_ACCEPTANCE')
                   for x in results))


if __name__ == '__main__':
    raise SystemExit(main())
