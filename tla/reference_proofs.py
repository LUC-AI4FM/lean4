#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Record strict TLAPS outcomes without treating absent proofs as successes."""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess


def toolbox_status(output, returncode):
    records, current = [], None
    for line in output.splitlines():
        if line == '@!!BEGIN':
            current = {}
        elif line == '@!!END' and current is not None:
            records.append(current)
            current = None
        elif current is not None and line.startswith('@!!') and ':' in line:
            key, value = line[3:].split(':', 1)
            current[key] = value
    obligations = {}
    counts = []
    for record in records:
        if record.get('type') == 'obligation' and 'id' in record:
            obligations[record['id']] = record.get('status', 'unknown')
        if record.get('type') == 'obligationsnumber':
            counts.append(int(record['count']))
    # Require strict exit success, complete protocol accounting and an actual
    # obligation. A successful parser invocation is not a successful proof.
    expected = counts[-1] if len(counts) == 1 else None
    proved = (returncode == 0 and expected is not None and expected > 0
              and len(obligations) == expected
              and all(s in ('proved', 'trivial') for s in obligations.values()))
    return {'status': 'reference_proved' if proved else 'reference_unproved',
            'returncode': returncode, 'expected_obligations': expected,
            'obligations': obligations}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference_root', type=Path)
    parser.add_argument('--prover', type=Path, required=True)
    parser.add_argument('-I', '--include', type=Path, action='append', default=[])
    parser.add_argument('--shard', type=int, default=0)
    parser.add_argument('--shards', type=int, default=1)
    parser.add_argument('--timeout', type=int, default=60)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    if not 0 <= args.shard < args.shards or args.timeout <= 0:
        parser.error('invalid shard or timeout')
    root = args.reference_root.resolve()
    prover = str(args.prover.resolve(strict=True))
    version = subprocess.run([prover, '--version'], capture_output=True, text=True, check=True).stdout.strip()
    sources = sorted(root.rglob('*.tla'))[args.shard::args.shards]
    if not sources:
        parser.error('empty corpus')
    results = []
    for source in sources:
        command = [prover, '--strict', '--toolbox', '0', '0', '--nofp']
        for include in [root / 'library', *args.include]:
            command.extend(['-I', str(include.resolve())])
        command.append(str(source))
        process = subprocess.Popen(command, cwd=source.parent, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True, start_new_session=True)
        try:
            output, _ = process.communicate(timeout=args.timeout)
            item = toolbox_status(output, process.returncode)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            output, _ = process.communicate()
            item = {'status': 'reference_timeout'}
        item.update(source=str(source.relative_to(root)), diagnostic=output)
        results.append(item)
        print(item['status'], item['source'], flush=True)
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps({'prover_version': version, 'selected': len(sources),
                                          'results': results}, indent=2))
    return 0  # This measures a mixed corpus, not a positive-only test suite.


if __name__ == '__main__':
    raise SystemExit(main())
