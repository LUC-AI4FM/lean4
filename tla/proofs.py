# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Reconstruct source proof scripts as Lean terms; no source fact is an axiom."""
from compiler import CompileError, ident
from sany import parse_file
from universal_compile import UniversalCompiler


class ProofError(CompileError):
    pass


def proof_node(theorem):
    nodes = [node for node in theorem.node if node.tag in ('obvious', 'by', 'omitted', 'steps')]
    if len(nodes) != 1:
        raise ProofError(f'{theorem.location}:{theorem.node.findtext("location/line/begin")}: '
                         'theorem has no explicit proof')
    if nodes[0].tag == 'omitted':
        raise ProofError(f'{theorem.location}: OMITTED is not a checked proof')
    return nodes[0]


def compile_proofs(source, **kwargs):
    graph = parse_file(source, **kwargs)
    compiler = UniversalCompiler(graph)
    code = compiler.compile()
    exports = compiler.proof_exports
    theorems = graph.claims('TheoremNode')
    if not theorems:
        return code
    code = code.replace('public import TLAUniversal', 'public import TLAUniversal\nimport Aesop', 1)
    lines = [f'namespace {exports["namespace"]}', '@[expose] public noncomputable section']
    names = exports['proof_names']
    for index, theorem in enumerate(theorems):
        proof = proof_node(theorem)
        if proof.tag == 'steps':
            raise ProofError(f'{theorem.location}: hierarchical proof reconstruction is not implemented yet')
        unfold = [exports['assumptions'], exports['claims'][index], '_root_.TLAUniversal.truth_boolean']
        for reference in proof.findall('defs/*'):
            symbol = graph.resolve(reference)
            if symbol.uid in compiler.emitted:
                unfold.append(compiler.emitted[symbol.uid][0])
        lines += [f'theorem {names[index]} (c : {exports["constants"]}) '
                  f'(b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) '
                  f'(source_assumptions : {exports["assumptions"]} c b n) : '
                  f'{exports["claims"][index]} c b n := by', '  classical']
        # Only already checked theorems enter the context. A BY reference is
        # never converted to an assumed proposition merely because SANY resolved it.
        for previous in range(index):
            lines.append(f'  have prior_{previous} := {names[previous]} c b n source_assumptions')
            unfold.append(exports['claims'][previous])
        lines += ['  simp_all only [' + ', '.join(unfold) + ']', '  all_goals aesop']
    lines += [f'def {exports["certificate_proof"]} (c : {exports["constants"]}) : '
              f'{exports["certificate"]} c :=',
              '  ⟨' + ', '.join(name + ' c' for name in names) + '⟩',
              'end', f'end {exports["namespace"]}', '']
    return code + '\n' + '\n'.join(lines)
