#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Run the CI TLA checks locally in parallel, with the same commands and budgets.

Runs the `TLA port` workflow (native/source check and the universal shards)
and the unchanged-proof audit (`tla-proof-compatibility.yml`) concurrently,
then compares the audit with tests/proofs/lean-baseline.json. A script that
the baseline records as checked and that fails under load is re-run alone
before it counts as a regression. Exit status is nonzero on any failed
check, expected-false acceptance or confirmed regression.

  python3 local_suite.py [--jobs N] [--only audit|port] [--sources examples/Euclid.tla ...]
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root = Path(__file__).resolve().parent


def spawn(command, cwd, log, env=None):
    return subprocess.Popen(command, cwd=cwd, env={**os.environ, **(env or {})},
                            stdout=open(log, 'w'), stderr=subprocess.STDOUT)


def audit_command(args, report, jobs, sources=None):
    command = [sys.executable, 'proof_compatibility.py', str(args.tlapm),
               '--reference-manifest', 'tests/proofs/reference-baseline.json',
               '-I', str(args.community / 'modules'), '--report', str(report), '--jobs', str(jobs)]
    return command + (['--sources', *sources] if sources else [])


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--tlapm', type=Path, default=Path(os.environ.get('TLAPM_REFERENCE', '/private/tmp/tlapm-proof-reference')))
    parser.add_argument('--community', type=Path, default=Path(os.environ.get('COMMUNITY_REFERENCE', '/private/tmp/lean4-tla-community-reference')))
    parser.add_argument('--jobs', type=int, default=max(1, (os.cpu_count() or 2) - 2))
    parser.add_argument('--universal-shards', type=int, default=4)
    parser.add_argument('--only', choices=['audit', 'port'])
    parser.add_argument('--sources', nargs='+', help='audit only these reference paths')
    parser.add_argument('--logs', type=Path, default=root / '.local-suite')
    parser.add_argument('--write-baseline', metavar='RUN', help='after a full passing audit, rewrite '
                        'tests/proofs/lean-baseline.json from it, recording RUN (a CI run URL or "local")')
    args = parser.parse_args()
    args.logs.mkdir(exist_ok=True)
    start = time.time()
    subprocess.run(['lake', 'build'], cwd=root / 'universal', check=True, stdout=subprocess.DEVNULL)
    jobs = []
    if args.only != 'audit' and not args.sources:
        jobs.append(('port-check', spawn([sys.executable, 'check.py'], root, args.logs / 'port-check.log')))
        for shard in range(args.universal_shards):
            jobs.append((f'universal-{shard}', spawn(
                [sys.executable, 'check.py'], root / 'universal', args.logs / f'universal-{shard}.log',
                env={'TLA_PROOF_SHARDS': str(args.universal_shards), 'TLA_PROOF_SHARD': str(shard)})))
    report = args.logs / 'audit.json'
    if args.only != 'port':
        report.unlink(missing_ok=True)
        jobs.append(('audit', spawn(audit_command(args, report, args.jobs, args.sources), root, args.logs / 'audit.log')))
    failed = []
    for name, process in jobs:
        code = process.wait()
        print(('ok   ' if code == 0 or name == 'audit' else 'FAIL ') + name, f'({time.time() - start:.0f}s)', flush=True)
        if code and name != 'audit':
            failed.append(name)
    if args.only != 'port':
        results = json.loads(report.read_text())['results']
        baseline = {r['source']: r['status'] for r in json.loads((root / 'tests/proofs/lean-baseline.json').read_text())['results']}
        suspect = [r['source'] for r in results if baseline.get(r['source']) == 'checked' and r['status'] != 'checked']
        if suspect:
            # Re-run alone: a 60 s budget under full load is not a CI result.
            print('re-running alone:', ', '.join(suspect), flush=True)
            retry = args.logs / 'audit-retry.json'
            subprocess.run(audit_command(args, retry, 1, suspect), cwd=root, stdout=subprocess.DEVNULL)
            again = {r['source']: r for r in json.loads(retry.read_text())['results']}
            results = [again.get(r['source'], r) for r in results]
            report.write_text(json.dumps({'selected': len(results), 'results': results}, indent=2))
        positive = [r for r in results if r.get('reference_positive')]
        checked = sum(r['status'] == 'checked' for r in positive)
        unsound = [r['source'] for r in results if r['status'] == 'UNSOUND_ACCEPTANCE']
        regressed = [r['source'] for r in results if baseline.get(r['source']) == 'checked' and r['status'] != 'checked']
        gained = [r['source'] for r in positive if r['status'] == 'checked' and baseline.get(r['source']) != 'checked']
        print(f'audit: {checked}/{len(positive)} reference-positive checked of {len(results)} inputs')
        seconds = {r['source']: r.get('seconds') for r in results}
        for label, items in (('UNSOUND', unsound), ('REGRESSED', regressed), ('newly checked', gained)):
            for item in items:
                print(f'  {label}: {item} ({seconds[item]} s)')
        if unsound or regressed:
            failed.append('audit')
        elif args.write_baseline and not args.sources:
            path = root / 'tests/proofs/lean-baseline.json'
            old = json.loads(path.read_text())
            kept = ('source', 'expected_false', 'reference_positive', 'claims', 'status')
            rows = [{k: r[k] for k in kept if k in r} for r in results]
            counts = {}
            for r in rows:
                counts[r['status']] = counts.get(r['status'], 0) + 1
            commit = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=root, capture_output=True, text=True).stdout.strip()
            path.write_text(json.dumps({'run': args.write_baseline, 'commit': commit,
                                        'reference_commit': old['reference_commit'], 'note': old['note'],
                                        'counts': counts, 'results': rows}, indent=2) + '\n')
            print(f'wrote {path.name}: {checked}/{len(positive)}; update its note')
    print(f'total {time.time() - start:.0f}s;', 'FAILED: ' + ', '.join(failed) if failed else 'all passed')
    return int(bool(failed))


if __name__ == '__main__':
    raise SystemExit(main())
