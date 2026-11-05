#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Compare fixture call coverage with exports of every pinned standard module."""
from pathlib import Path
import tempfile
from sany import parse_file

MODULES = ('Naturals', 'Integers', 'Reals', 'Sequences', 'FiniteSets', 'Bags',
           'RealTime', 'TLC', 'Randomization', 'Toolbox')

def identity(symbol):
    body = symbol.body
    while body.tag in ('SubstInNode', 'APSubstInNode'):
        body = body.find('body')[0]
    return body.findtext('location/filename', symbol.location), symbol.name.rsplit('!', 1)[-1]

def audit():
    expected, covered = set(), set()
    with tempfile.TemporaryDirectory(prefix='tla-library-audit-') as directory:
        source = Path(directory) / 'Audit.tla'
        for module in MODULES:
            source.write_text('---- MODULE Audit ----\nEXTENDS ' + module + '\n====')
            graph = parse_file(source)
            expected.update(identity(graph.resolve(ref)) for ref in graph.root.node.findall('UserDefinedOpKindRef'))
    for source in sorted((Path(__file__).parent / 'tests' / 'fixtures').glob('*.tla')):
        graph = parse_file(source)
        seen = set()
        def visit(symbol):
            if symbol.uid in seen or symbol.node.tag != 'UserDefinedOpKind':
                return
            seen.add(symbol.uid)
            covered.add(identity(symbol))
            for ref in symbol.body.iter('UserDefinedOpKindRef'):
                visit(graph.resolve(ref))
        for definition in graph.definitions():
            visit(definition)
        for kind in ('AssumeNode', 'TheoremNode'):
            for claim in graph.claims(kind):
                for ref in claim.body.iter('UserDefinedOpKindRef'):
                    visit(graph.resolve(ref))
    return expected, covered

if __name__ == '__main__':
    expected, covered = audit()
    missing = sorted(expected - covered)
    if missing:
        raise SystemExit('Uncovered standard exports: ' + repr(missing))
    print(f'All {len(expected)} standard-module exports have reachable fixture calls.')
