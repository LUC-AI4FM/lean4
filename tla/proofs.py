# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Reconstruct source proof scripts as Lean terms; no source fact is an axiom."""
import xml.etree.ElementTree as ET
from compiler import CompileError
from sany import parse_file
from universal_compile import UniversalCompiler, OperatorBinding, ValueBinding, LevelBinding, ExpressionBinding, qualify


class ProofError(CompileError):
    pass


def proof_node(theorem, *, implicit=False):
    nodes = [node for node in theorem.node if node.tag in ('obvious', 'by', 'omitted', 'steps')]
    if not nodes and implicit:
        return ET.Element('obvious')
    if len(nodes) != 1:
        raise ProofError(f'{theorem.location}:{theorem.node.findtext("location/line/begin")}: '
                         'theorem has no explicit proof')
    if nodes[0].tag == 'omitted':
        raise ProofError(f'{theorem.location}: OMITTED is not a checked proof')
    return nodes[0]


class Renderer:
    def __init__(self, compiler, unfold):
        self.compiler = compiler
        self.graph = compiler.g
        self.unfold = unfold

    def proposition(self, node, env):
        return '_root_.TLAUniversal.truth ' + qualify(self.compiler.expr(node, env))

    def leaf(self, proof, indent):
        unfold = list(self.unfold) + [
            '_root_.TLAUniversal.truth_true',
            '_root_.TLAUniversal.not_truth_false',
            '_root_.TLAUniversal.realBinary_add_integer',
            '_root_.TLAUniversal.realBinary_mul_integer',
            '_root_.TLAUniversal.realNegate_integer',
            '_root_.TLAUniversal.realLessEqual_integer',
            '_root_.TLAUniversal.integer_injective.eq_iff',
            '_root_.TLAUniversal.integer_mem_naturals',
            '_root_.TLAUniversal.integer_mem',
            '_root_.TLAUniversal.numberInterval_integer',
            '_root_.TLAUniversal.integer_mem_interval',
            '_root_.TLAUniversal.mem_enumerate',
        ]
        for reference in proof.findall('defs/*'):
            symbol = self.graph.resolve(reference)
            if symbol.uid in self.compiler.emitted:
                unfold.append(self.compiler.emitted[symbol.uid][0])
        return [indent + 'simp_all only [' + ', '.join(dict.fromkeys(unfold)) + ']',
                indent + 'all_goals first | omega | (solve | norm_num) | aesop']

    def open_statement(self, node, env, indent):
        env = dict(env)
        if node.tag != 'AssumeProveNode':
            return [], env
        lines = [indent + 'apply (_root_.TLAUniversal.truth_boolean _).2']
        for i, assumption in enumerate(node.find('assumes')):
            if assumption.tag != 'NewSymbNode':
                lines.append(indent + f'intro premise_{i}')
                continue
            symbol = self.graph.resolve(assumption.find('OpDeclNodeRef'))
            name = 'new_' + symbol.uid
            lines.append(indent + 'intro ' + name)
            if symbol.node.findtext('kind') == '25':
                env[symbol.uid] = ExpressionBinding(f'(fun (_ : _root_.TLAUniversal.Behavior) (k : _root_.Nat) => {name} k)')
            elif symbol.level and symbol.arity:
                env[symbol.uid] = ExpressionBinding(name, symbol.arity)
            elif symbol.level:
                env[symbol.uid] = LevelBinding(name, symbol.level)
            else:
                env[symbol.uid] = OperatorBinding(name, symbol.arity)
            bounds = [x for x in assumption if x.tag not in ('location', 'level', 'OpDeclNodeRef')]
            if bounds:
                lines.append(indent + 'intro bound_' + symbol.uid)
            if (symbol.level and symbol.arity) or symbol.level == 3:
                lines.append(indent + 'intro locality_' + symbol.uid)
        return lines, env

    def render(self, proof, env, indent='  '):
        if proof.tag in ('obvious', 'by'):
            return self.leaf(proof, indent)
        if proof.tag != 'steps':
            raise ProofError('unsupported proof node: ' + proof.tag)
        refs = [x for x in proof if x.tag not in ('location', 'level')]
        # Definition visibility is local to this proof, including nested proofs.
        saved = self.unfold
        self.unfold = list(saved)
        try:
            return self.steps(refs, dict(env), indent)
        finally:
            self.unfold = saved

    def steps(self, references, env, indent):
        lines = []
        for index, reference in enumerate(references):
            if reference.tag == 'DefStepNode':
                # SANY resolves references to these definitions by UID. The
                # expression compiler expands their bodies in the current
                # binder environment, including parameters and substitutions.
                for definition in reference:
                    if definition.tag.endswith('Ref'):
                        self.graph.resolve(definition)
                continue
            if reference.tag == 'UseOrHideNode':
                hiding = reference.find('hide') is not None
                for definition in reference.findall('defs/*'):
                    symbol = self.graph.resolve(definition)
                    if symbol.uid in self.compiler.emitted:
                        emitted = self.compiler.emitted[symbol.uid][0]
                        if hiding:
                            self.unfold = [x for x in self.unfold if x != emitted]
                        elif emitted not in self.unfold:
                            self.unfold.append(emitted)
                # USE facts are obligations, not assumptions. Reconstruct each
                # before making it available to subsequent source steps.
                for fact_index, fact in enumerate(reference.findall('facts/*')):
                    if hiding:
                        raise ProofError('HIDE facts requires scoped fact visibility')
                    lines.append(indent + f'have used_{index}_{fact_index} : '
                                 + self.proposition(fact, env) + ' := by')
                    lines += self.leaf(ET.Element('obvious'), indent + '  ')
                continue
            if reference.tag != 'TheoremNodeRef':
                raise ProofError('unsupported proof step: ' + reference.tag)
            step = self.graph.resolve(reference)
            body = step.body
            name = self.graph.operator(body).name if body.tag == 'OpApplNode' else None
            args = list(body.find('operands')) if body.tag == 'OpApplNode' else []
            label = 'step_' + step.uid
            if name == '$Qed':
                if index != len(references) - 1:
                    raise ProofError('QED must terminate its proof scope')
                return lines + self.render(proof_node(step, implicit=True), env, indent)
            if name == '$Take':
                lines.append(indent + 'first | apply (_root_.TLAUniversal.truth_boolean _).2 | skip')
                for group in body.find('boundSymbols'):
                    if group.find('tuple') is not None:
                        refs = group.findall('FormalParamNodeRef')
                        variable = 'taken_tuple_' + refs[0].findtext('UID')
                        lines.append(indent + 'intro ' + variable)
                        for component, ref in enumerate(refs, 1):
                            env[ref.findtext('UID')] = ValueBinding(
                                f'(_root_.TLAUniversal.apply {variable} (_root_.TLAUniversal.integer {component}))')
                        if group.tag != 'unbound':
                            lines.append(indent + 'intro bound_' + variable)
                        continue
                    for ref in group.findall('FormalParamNodeRef'):
                        uid = ref.findtext('UID')
                        variable = 'taken_' + uid
                        lines.append(indent + 'intro ' + variable)
                        env[uid] = ValueBinding(variable)
                        if group.tag != 'unbound':
                            lines.append(indent + 'intro bound_' + uid)
                continue
            if name == '$Witness':
                lines.append(indent + 'first | apply (_root_.TLAUniversal.truth_boolean _).2 | skip')
                for argument in args:
                    value = qualify(self.compiler.expr(argument, env))
                    lines.append(indent + 'first')
                    lines.append(indent + f'| refine Exists.intro {value} ?_')
                    lines.append(indent + '| refine And.intro ?_ ?_')
                    lines.append(indent + '  ·')
                    lines += self.leaf(ET.Element('obvious'), indent + '    ')
                    lines.append(indent + f'  · refine Exists.intro {value} ?_')
                continue
            if name == '$Pick':
                existential = self.compiler.expr(body, env, operator_override='$UnboundedExists')
                proposition = '_root_.TLAUniversal.truth ' + qualify(existential)
                lines.append(indent + f'have {label} : {proposition} := by')
                lines += self.render(proof_node(step, implicit=True), env, indent + '  ')
                fields = []
                for group in body.find('boundSymbols'):
                    if group.find('tuple') is not None:
                        refs = group.findall('FormalParamNodeRef')
                        variable = 'picked_tuple_' + refs[0].findtext('UID')
                        fields.append(variable)
                        for component, ref in enumerate(refs, 1):
                            env[ref.findtext('UID')] = ValueBinding(
                                f'(_root_.TLAUniversal.apply {variable} (_root_.TLAUniversal.integer {component}))')
                        if group.tag != 'unbound':
                            fields.append('bound_' + variable)
                        continue
                    for ref in group.findall('FormalParamNodeRef'):
                        uid = ref.findtext('UID')
                        variable = 'picked_' + uid
                        fields.append(variable)
                        env[uid] = ValueBinding(variable)
                        if group.tag != 'unbound':
                            fields.append('bound_' + uid)
                fields.append('picked_fact_' + step.uid)
                lines.append(indent + 'obtain ⟨' + ', '.join(fields) + '⟩ := '
                             f'(_root_.TLAUniversal.truth_boolean _).1 {label}')
                continue
            if name == '$Pfcase':
                lines.append(indent + f'by_cases {label} : {self.proposition(args[0], env)}')
                lines.append(indent + '·')
                lines += self.render(proof_node(step, implicit=True), dict(env), indent + '  ')
                lines.append(indent + '·')
                return lines + self.steps(references[index + 1:], dict(env), indent + '  ')
            if name == '$Have':
                lines.append(indent + f'have {label} : {self.proposition(args[0], env)} := by')
                lines += self.leaf(ET.Element('obvious'), indent + '  ')
                continue
            if step.node.find('suffices') is not None:
                if name == '$Suffices':
                    body = args[0]
                lines.append(indent + f'suffices {label} : {self.proposition(body, env)} by')
                lines += self.render(proof_node(step, implicit=True), dict(env), indent + '  ')
                opened, env = self.open_statement(body, env, indent)
                lines += opened
                continue
            lines.append(indent + f'have {label} : {self.proposition(body, env)} := by')
            opened, child_env = self.open_statement(body, env, indent + '  ')
            lines += opened + self.render(proof_node(step, implicit=True), child_env, indent + '  ')
        raise ProofError('hierarchical proof has no final QED')


def compile_proofs(source, **kwargs):
    graph = parse_file(source, **kwargs)
    compiler = UniversalCompiler(graph)
    code = compiler.compile()
    exports = compiler.proof_exports
    theorems = graph.claims('TheoremNode')
    if not theorems:
        return code
    code = code.replace('public import TLAUniversal', 'public import TLAUniversal\nimport Aesop\nimport Mathlib.Tactic.NormNum', 1)
    lines = [f'namespace {exports["namespace"]}', '@[expose] public noncomputable section']
    names = exports['proof_names']
    for index, theorem in enumerate(theorems):
        proof = proof_node(theorem)
        unfold = [exports['assumptions'], exports['claims'][index], '_root_.TLAUniversal.truth_boolean']
        lines += [f'theorem {names[index]} (c : {exports["constants"]}) '
                  f'(b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) '
                  f'(source_assumptions : {exports["assumptions"]} c b n) : '
                  f'{exports["claims"][index]} c b n := by', '  classical',
                  '  have set_not_universal := _root_.TLAUniversal.not_universal']
        # Only already checked theorems enter the context. A BY reference is
        # never converted to an assumed proposition merely because SANY resolved it.
        for previous in range(index):
            lines.append(f'  have prior_{previous} := {names[previous]} c')
            unfold.append(exports['claims'][previous])
        renderer = Renderer(compiler, unfold)
        opened, environment = renderer.open_statement(theorem.body, {}, '  ')
        lines += opened + renderer.render(proof, environment)
    lines += [f'def {exports["certificate_proof"]} (c : {exports["constants"]}) : '
              f'{exports["certificate"]} c :=',
              '  ⟨' + ', '.join(name + ' c' for name in names) + '⟩',
              'end', f'end {exports["namespace"]}', '']
    return code + '\n' + '\n'.join(lines)
