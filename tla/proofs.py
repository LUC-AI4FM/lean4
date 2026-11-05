# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Reconstruct source proof scripts as Lean terms; no source fact is an axiom."""
import copy
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
            '_root_.eq_self_iff_true',
            '_root_.not_true_eq_false',
            '_root_.imp_self',
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
            '_root_.ZFSet.mem_sep',
        ]
        for reference in proof.findall('defs/*'):
            symbol = self.graph.resolve(reference)
            if symbol.uid in self.compiler.emitted:
                unfold.append(self.compiler.emitted[symbol.uid][0])
        simplifiers = ', '.join(dict.fromkeys(unfold))
        return [indent + 'try (solve | trivial)',
                indent + 'try (solve | simp (config := { maxSteps := 10000 }) [' + simplifiers + '])',
                indent + 'all_goals first | simp_all only [' + simplifiers + '] | simp only [' + simplifiers + '] at *',
                indent + 'all_goals first | (solve | intro fair; exact _root_.TLA.strong_implies_weak _ _ _ _ fair) | (solve | rintro ⟨fair, available⟩; exact _root_.TLA.weak_fairness_continuously_enabled _ _ _ _ fair available) | (solve | apply _root_.TLAUniversal.diagonal_ne <;> assumption) | omega | (solve | norm_num) | (solve | aesop (config := { maxRuleApplicationDepth := 128, maxRuleApplications := 50, useSimpAll := false }) (add safe (by omega), norm (by tla_choice))) | (solve | tla_temporal_induction <;> aesop (config := { maxRuleApplicationDepth := 128 }) (add safe (by omega), norm (by tla_choice))) | (solve | tla_natural_induction <;> aesop (config := { maxRuleApplicationDepth := 128 }) (add safe (by omega), norm (by tla_choice))) | aesop (config := { maxRuleApplicationDepth := 128 }) (add safe (by omega), norm (by tla_choice))']

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

    def goal_body(self, goal):
        seen = set()
        while goal is not None:
            if goal.tag == 'AssumeProveNode':
                goal = goal.find('prove')[0]
            elif goal.tag in ('LetInNode', 'LabelNode'):
                goal = goal.find('body')[0]
            elif goal.tag == 'OpApplNode':
                symbol = self.graph.operator(goal)
                if symbol.uid in seen or symbol.node.tag != 'UserDefinedOpKind' or len(goal.find('operands')):
                    break
                seen.add(symbol.uid)
                goal = symbol.body
            else:
                break
        return goal

    def binder_refs(self, goal):
        goal = self.goal_body(goal)
        if goal is None or goal.tag != 'OpApplNode' or goal.find('boundSymbols') is None:
            return []
        group = goal.find('boundSymbols')[0]
        refs = [x.findtext('UID') for x in group.findall('FormalParamNodeRef')]
        return refs if group.find('tuple') is not None else refs[:1]

    def consume_binder(self, goal):
        goal = self.goal_body(goal)
        if goal is None or goal.tag != 'OpApplNode' or goal.find('boundSymbols') is None:
            return None, None
        goal = copy.deepcopy(goal)
        groups = goal.find('boundSymbols')
        group = groups[0]
        bounded = group.tag != 'unbound'
        refs = group.findall('FormalParamNodeRef')
        if group.find('tuple') is not None or len(refs) == 1:
            groups.remove(group)
        else:
            group.remove(refs[0])
        return bounded, goal if len(groups) else goal.find('operands')[0]

    def render(self, proof, env, indent='  ', goal=None):
        if proof.tag in ('obvious', 'by'):
            return self.leaf(proof, indent)
        if proof.tag != 'steps':
            raise ProofError('unsupported proof node: ' + proof.tag)
        refs = [x for x in proof if x.tag not in ('location', 'level')]
        # Definition visibility is local to this proof, including nested proofs.
        saved = self.unfold
        self.unfold = list(saved)
        try:
            return self.steps(refs, dict(env), indent, self.goal_body(goal))
        finally:
            self.unfold = saved

    def steps(self, references, env, indent, goal):
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
                return lines + self.render(proof_node(step, implicit=True), env, indent, goal)
            if name == '$Take':
                lines.append(indent + 'first | apply (_root_.TLAUniversal.truth_boolean _).2 | skip')
                for group in body.find('boundSymbols'):
                    if group.find('tuple') is not None:
                        refs = group.findall('FormalParamNodeRef')
                        goal_refs = self.binder_refs(goal)
                        _, goal = self.consume_binder(goal)
                        variable = 'taken_tuple_' + refs[0].findtext('UID')
                        lines.append(indent + 'intro ' + variable)
                        for component, ref in enumerate(refs, 1):
                            env[ref.findtext('UID')] = ValueBinding(
                                f'(_root_.TLAUniversal.apply {variable} (_root_.TLAUniversal.integer {component}))')
                        for original, ref in zip(goal_refs, refs):
                            env[original] = env[ref.findtext('UID')]
                        if group.tag != 'unbound':
                            lines.append(indent + 'intro bound_' + variable)
                        continue
                    for ref in group.findall('FormalParamNodeRef'):
                        uid = ref.findtext('UID')
                        goal_refs = self.binder_refs(goal)
                        _, goal = self.consume_binder(goal)
                        variable = 'taken_' + uid
                        lines.append(indent + 'intro ' + variable)
                        env[uid] = ValueBinding(variable)
                        for original in goal_refs:
                            env[original] = env[uid]
                        if group.tag != 'unbound':
                            lines.append(indent + 'intro bound_' + uid)
                continue
            if name == '$Witness':
                lines.append(indent + 'first | apply (_root_.TLAUniversal.truth_boolean _).2 | skip')
                for argument in args:
                    goal_refs = self.binder_refs(goal)
                    binder = self.goal_body(goal)
                    tuple_binder = bool(goal_refs) and binder.find('boundSymbols')[0].find('tuple') is not None
                    bounded, goal = self.consume_binder(goal)
                    if bounded and argument.tag == 'OpApplNode' and self.graph.operator(argument).name == '\\in':
                        lines.append(indent + f'have witness_bound_{index} : '
                                     + self.proposition(argument, env) + ' := by')
                        lines += self.leaf(ET.Element('obvious'), indent + '  ')
                        argument = argument.find('operands')[0]
                    value = qualify(self.compiler.expr(argument, env))
                    lines.append(indent + 'first')
                    lines.append(indent + f'| refine Exists.intro {value} ?_')
                    lines.append(indent + '| refine And.intro (by')
                    lines += self.leaf(ET.Element('obvious'), indent + '    ')
                    lines.append(indent + f'    ) (Exists.intro {value} ?_)')
                    if bounded:
                        lines.append(indent + 'refine And.intro (by')
                        lines += self.leaf(ET.Element('obvious'), indent + '  ')
                        lines.append(indent + '  ) ?_')
                    for component, original in enumerate(goal_refs, 1):
                        env[original] = ValueBinding(
                            f'(_root_.TLAUniversal.apply {value} (_root_.TLAUniversal.integer {component}))'
                            if tuple_binder else value)
                continue
            if name == '$Pick':
                existential = self.compiler.expr(body, env, operator_override='$UnboundedExists')
                proposition = '_root_.TLAUniversal.truth ' + qualify(existential)
                lines.append(indent + f'have {label} : {proposition} := by')
                lines += self.render(proof_node(step, implicit=True), env, indent + '  ', body)
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
                case_env = dict(env)
                later_env = dict(env)
                definition = step.node.find('definition/TheoremDefRef/UID')
                if definition is not None:
                    # Inside CASE its name denotes the condition; outside it
                    # denotes the assertion condition => enclosing goal.
                    case_env[definition.text] = ValueBinding(self.compiler.expr(args[0], env))
                    if goal is None:
                        raise ProofError('CASE reference requires its enclosing goal')
                    later_env[definition.text] = ValueBinding(
                        '(_root_.TLAUniversal.boolean (' + self.proposition(args[0], env)
                        + ' → ' + self.proposition(goal, env) + '))')
                lines += self.render(proof_node(step, implicit=True), case_env, indent + '  ', goal)
                lines.append(indent + '·')
                return lines + self.steps(references[index + 1:], later_env, indent + '  ', goal)
            if name == '$Have':
                implication = self.goal_body(goal)
                if implication is None or implication.tag != 'OpApplNode' or self.graph.operator(implication).name != '=>':
                    raise ProofError('HAVE requires an implication goal')
                consequent = implication.find('operands')[1]
                lines.append(indent + 'first | apply (_root_.TLAUniversal.truth_boolean _).2 | skip')
                lines.append(indent + f'suffices {label} : {self.proposition(args[0], env)} → '
                             + self.proposition(consequent, env) + ' by')
                lines.append(indent + '  intro have_antecedent')
                lines.append(indent + f'  apply {label}')
                lines += self.leaf(ET.Element('obvious'), indent + '  ')
                lines.append(indent + 'intro have_' + step.uid)
                definition = step.node.find('definition/TheoremDefRef/UID')
                if definition is not None:
                    env[definition.text] = ValueBinding(self.compiler.expr(args[0], env))
                goal = consequent
                continue
            if step.node.find('suffices') is not None:
                if name == '$Suffices':
                    body = args[0]
                lines.append(indent + f'suffices {label} : {self.proposition(body, env)} by')
                lines += self.render(proof_node(step, implicit=True), dict(env), indent + '  ', goal)
                goal = self.goal_body(body)
                opened, env = self.open_statement(body, env, indent)
                lines += opened
                continue
            proposition = self.proposition(body, env)
            step_proof = proof_node(step, implicit=True)
            opened, child_env = self.open_statement(body, env, indent + '  ')
            proof_lines = opened + self.render(step_proof, child_env, indent + '  ', body)
            if step.level in (1, 2) and step_proof.tag in ('obvious', 'by'):
                # Generalization is attempted with a fresh behavior/time, but
                # existing assumptions retain their original types. Lean must
                # prove this stronger statement; a local premise cannot become
                # a universally valid state fact merely by being cited.
                general = label + '_general'
                lines.append(indent + 'first')
                lines.append(indent + f'| have {general} : ∀ (b : _root_.TLAUniversal.Behavior) '
                             + f'(n : _root_.Nat), {proposition} := by')
                lines.append(indent + '    intro b n')
                lines += ['  ' + line for line in proof_lines]
                lines.append(indent + f'  have {label} : {proposition} := {general} b n')
                lines.append(indent + f'| have {label} : {proposition} := by')
                lines += ['  ' + line for line in proof_lines]
            else:
                lines.append(indent + f'have {label} : {proposition} := by')
                lines += proof_lines
        raise ProofError('hierarchical proof has no final QED')


def compile_proofs(source, **kwargs):
    graph = parse_file(source, **kwargs)
    compiler = UniversalCompiler(graph)
    code = compiler.compile()
    exports = compiler.proof_exports
    theorems = graph.proof_claims()
    if not theorems:
        return code
    code = code.replace('public import TLAUniversal', 'public import TLAUniversal\nimport Aesop\nimport Mathlib.Tactic.NormNum', 1)
    lines = [f'namespace {exports["namespace"]}', '@[expose] public noncomputable section']
    # Re-run semantic normalization inside proof search after quantified
    # domain witnesses are introduced, not only before the search begins.
    normalized = ('truth_boolean truth_true not_truth_false false_ne_true integer_eq_iff '
                  'mem_naturals mem_integers integer_mem_naturals integer_mem '
                  'realBinary_add_integer realBinary_mul_integer realNegate_integer '
                  'realSubtract_integer realLessEqual_integer realLess_integer realPower_integer_nonnegative '
                  'intBinary_integer numberInterval_integer integer_mem_interval '
                  'enumerate_nil mem_enumerate mem_image caseValue apply_function domain_function function_isFunc_iff '
                  'domain_update domain_updatePath_cons update_same update_other updatePath '
                  'domain_tuple apply_tuple_at tuple_eq_iff length_tuple '
                  'prepend_tuple mem_cartesian_cons mem_cartesian_nil '
                  'string_eq_iff string_mem domain_record apply_record_lookup record_eq_iff mem_recordSpace mem_interval_iff mem_union_enumerate').split()
    lines.append('attribute [local simp] ' + ' '.join(
        '_root_.TLAUniversal.' + name for name in normalized)
        + ' _root_.ZFSet.zftrue_ne_zffalse _root_.ZFSet.pair_inj _root_.List.lookup_cons')
    lines.append('attribute [local simp] _root_.TLA.weakFairness _root_.TLA.strongFairness '
                 '_root_.TLA.always _root_.TLA.eventually _root_.TLA.state '
                 '_root_.TLA.action _root_.TLA.enabled _root_.TLA.angle _root_.TLA.unchanged')
    lines.append('attribute [local simp ↓] _root_.TLAUniversal.apply_updatePath_other '
                 '_root_.TLAUniversal.apply_updatePath_single '
                 '_root_.TLAUniversal.update_other _root_.TLAUniversal.update_same '
                 '_root_.TLAUniversal.domain_updatePath_cons '
                 '_root_.TLAUniversal.domain_update _root_.TLAUniversal.domain_record')
    lines.append('attribute [local aesop safe apply] _root_.TLAUniversal.remainder_nonnegative '
                 '_root_.TLAUniversal.remainder_upper _root_.Int.emod_lt_of_pos '
                 '_root_.TLAUniversal.realPower_integer_mem '
                 '_root_.TLAUniversal.exists_state_pair '
                 '_root_.TLAUniversal.separation_subset '
                 '_root_.TLAUniversal.exists_container '
                 '_root_.TLAUniversal.diagonal_ne '
                 '_root_.TLAUniversal.exists_nat_of_nonneg')
    lines.append('attribute [local aesop safe forward] _root_.TLAUniversal.domain_isFunc '
                 '_root_.TLAUniversal.apply_mem '
                 '_root_.TLAUniversal.diagonal_contradiction '
                 '_root_.TLAUniversal.record_eq_keys '
                 '_root_.TLAUniversal.universal_set_contradiction '
                 '_root_.TLAUniversal.powerset_subset_contradiction '
                 '_root_.TLAUniversal.function_range_mono')
    lines.append('attribute [local aesop unsafe 50% apply] _root_.TLAUniversal.function_ext '
                 '_root_.TLAUniversal.apply_record '
                 '_root_.TLAUniversal.record_isFunc_of_domain '
                 '_root_.TLAUniversal.record_eta')
    names = exports['proof_names']
    for index, theorem in enumerate(theorems):
        # Imported library declarations may omit a source proof. Reconstruct
        # their statements in Lean before exposing them to later claims; never
        # turn an imported declaration into an axiom. Root omissions still fail.
        imported = bool(theorem.location) and theorem.location != graph.root.name
        proof = proof_node(theorem, implicit=imported)
        unfold = [exports['assumptions'], exports['claims'][index], '_root_.TLAUniversal.truth_boolean',
                  *exports['instance_helpers']]
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
        lines += opened + renderer.render(proof, environment, goal=theorem.body)
    lines += [f'def {exports["certificate_proof"]} (c : {exports["constants"]}) : '
              f'{exports["certificate"]} c :=',
              '  ⟨' + ', '.join(name + ' c' for name in names) + '⟩',
              'end', f'end {exports["namespace"]}', '']
    return code + '\n' + '\n'.join(lines)
