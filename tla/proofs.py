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
    def __init__(self, compiler, unfold, trace=False, claim=0, facts=None, assumptions=(), used=()):
        self.compiler = compiler
        self.graph = compiler.g
        self.unfold = unfold
        self.trace = trace
        self.claim = claim
        self.leaves = 0
        # Hypotheses about the current behavior/time (HAVE, CASE, PICK,
        # state-level ASSUME premises) make a fresh-behavior generalization
        # unprovable; attempting it only doubles proof search.
        self.local_state = False
        # Step/theorem definition UID -> [(hypothesis, certainly present)].
        self.facts = dict(facts or {})
        # Earlier theorems are, like steps, usable only when cited or USEd.
        self.prior_theorems = list(self.facts)
        # Facts removed from the default context by HIDE, still citable by BY.
        self.hidden = {}
        self.uses_hidden = False
        # Assertion steps in scope, and those made usable by USE. As in TLAPS,
        # a source leaf sees an earlier step only when it cites or USEs it.
        self.scope_steps = []
        self.used_steps = set(used)
        # Named module assumptions are usable only when cited or USEd.
        self.assumptions = list(assumptions)
        # Steps cited by a `BY PTL` leaf. PTL uses facts at every time, so
        # such a step is also attempted in fresh-behavior form at any depth.
        self.ptl_cited = set()

    @staticmethod
    def level(node):
        return int(node.findtext('level') or 0) if node is not None else 0

    def state_premises(self, node):
        return node.tag == 'AssumeProveNode' and any(
            assumption.tag != 'NewSymbNode' and self.level(assumption) >= 1
            for assumption in node.find('assumes'))

    @staticmethod
    def fact_reference(fact):
        if fact.tag != 'OpApplNode' or len(fact.find('operands')):
            return None, None
        operator = fact.find('operator')[0]
        return operator.tag, operator.findtext('UID')

    def reveal(self, uid, indent):
        """Restore hidden hypotheses for a USE, or locally for a BY citation."""
        lines = []
        for name, certain in self.hidden.get(uid, []):
            restore = f'have {name} := hidden_{name}.val'
            lines.append(indent + (restore if certain else f'try {restore}'))
        return lines

    def ptl_citations(self, proof):
        """Step UIDs that some `BY ... PTL` leaf below `proof` cites."""
        found = set()
        if proof.tag == 'by':
            names = set()
            uids = set()
            for fact in proof.findall('facts/*'):
                kind, uid = self.fact_reference(fact)
                if kind == 'TheoremDefRef':
                    uids.add(uid)
                elif fact.tag == 'OpApplNode' and not len(fact.find('operands')):
                    try:
                        names.add(self.graph.operator(fact).name)
                    except Exception:
                        pass
            if 'PTL' in names:
                found |= uids
        elif proof.tag == 'steps':
            for reference in proof:
                if reference.tag == 'TheoremNodeRef':
                    step = self.graph.resolve(reference)
                    try:
                        found |= self.ptl_citations(proof_node(step, implicit=True))
                    except ProofError:
                        pass
        return found

    def proposition(self, node, env):
        return '_root_.TLAUniversal.truth ' + qualify(self.compiler.expr(node, env))

    def leaf(self, proof, indent, restrict=False):
        unfold = list(self.unfold) + [
            '_root_.eq_self_iff_true',
            '_root_.not_true_eq_false',
            '_root_.ne_eq',
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
        # TLAPS's AutoUSE expands the definitions the obligation mentions.
        # Unfolding every emitted root definition is the same expansion.
        temporal = False
        everything = [self.compiler.emitted[symbol.uid][0] for symbol in self.graph.definitions()
                      if symbol.uid in self.compiler.emitted]
        for fact in proof.findall('facts/*'):
            if fact.tag == 'OpApplNode' and not len(fact.find('operands')):
                try:
                    named = self.graph.operator(fact).name
                except Exception:
                    named = None
                if named == 'AutoUSE':
                    unfold += everything
                # PTL is a backend hint, not a fact: it selects the checked
                # fairness rules (TLAUniversal.PTL) for this leaf.
                temporal = temporal or named == 'PTL'
        for reference in proof.findall('defs/*'):
            symbol = self.graph.resolve(reference)
            if symbol.uid in self.compiler.emitted:
                unfold.append(self.compiler.emitted[symbol.uid][0])
        simplifiers = ', '.join(dict.fromkeys(unfold))
        direct_simplifiers = ', '.join(dict.fromkeys(self.unfold + ['_root_.TLAUniversal.truth_boolean']))
        self.leaves += 1
        cited = []
        citations = set()
        for fact in proof.findall('facts/*'):
            kind, uid = self.fact_reference(fact)
            if kind in ('TheoremDefRef', 'AssumeDefRef'):
                citations.add(uid)
            if kind == 'TheoremDefRef':
                cited += self.reveal(uid, indent)
        if restrict:
            # Removing facts can only make Lean's search harder, never
            # unsound; it matches TLAPS's cited-facts proof context.
            for uid in self.prior_theorems + self.scope_steps:
                if uid in citations or uid in self.used_steps or uid in self.hidden:
                    continue
                for name, certain in self.facts.get(uid, []):
                    cited.append(indent + (f'clear {name}' if certain else f'try clear {name}'))
            for uid, name in self.assumptions:
                if uid and uid not in citations and uid not in self.used_steps:
                    cited.append(indent + f'clear {name}')
        tracing = cited + ([indent + f'trace \"TLA claim {self.claim} leaf {self.leaves}\"',
                    indent + 'trace_state'] if self.trace else [])
        # Single-time premises of a fairness rule need the definitions
        # TLAPS's PTL treats as atoms; unfolding a definition is always sound.
        definitions = ', '.join(dict.fromkeys(everything))
        helpers = ', '.join(dict.fromkeys(everything + list(self.compiler.proof_exports.get('instance_helpers', []))))
        fairness = (f'(solve | tla_iff_rewrite [{helpers}]) | (solve | tla_ptl_invariant [{definitions}]) | (solve | tla_wf_rank [{definitions}]) | (solve | tla_ptl_saturate [{definitions}]) | '
                    if temporal else '')
        return tracing + [indent + 'try (solve | trivial)',
                indent + 'try (solve | simp only [' + direct_simplifiers + ']; apply _root_.TLAUniversal.record_mem_singletonSpace; decide)',
                indent + 'try (solve | simp (config := { maxSteps := 10000 }) [' + simplifiers + '])',
                indent + 'all_goals simp only [' + simplifiers + '] at *',
                indent + 'all_goals tla_guard first | ' + fairness + '(solve | tla_chain) | (solve | tla_structural) | (solve | exact _root_.TLAUniversal.record_two_ne_iff _ _ _ _ _ _ (by decide)) | (solve | intro fair; exact _root_.TLA.strong_implies_weak _ _ _ _ fair) | (solve | rintro ⟨fair, available⟩; apply _root_.TLA.weak_fairness_continuously_enabled _ _ _ _ fair; simpa [_root_.TLA.always, _root_.TLA.state, _root_.TLA.enabled, _root_.TLA.angle, _root_.TLA.unchanged, _root_.TLA.action] using available) | (solve | apply _root_.TLAUniversal.diagonal_ne <;> assumption) | tla_omega | (solve | norm_num) | (solve | tla_natural_induction <;> (first | assumption | simp_all)) | (solve | tla_state_witness) | (solve | tla_except_step) | (solve | tla_temporal_induction <;> aesop (config := { maxRuleApplicationDepth := 128, maxRuleApplications := 50, useSimpAll := false }) (add safe (by tla_omega), norm (by tla_choice))) | (solve | aesop (config := { maxRuleApplicationDepth := 128, maxRuleApplications := 50 }) (simp_config := { maxSteps := 20000 }) (add safe (by tla_omega), norm (by tla_choice))) | (solve | aesop (config := { maxRuleApplicationDepth := 128, maxRuleApplications := 50, useSimpAll := false }) (add safe (by tla_omega), norm (by tla_choice))) | (solve | tla_temporal_induction <;> aesop (config := { maxRuleApplicationDepth := 128 }) (add safe (by tla_omega), norm (by tla_choice))) | (solve | tla_natural_induction <;> aesop (config := { maxRuleApplicationDepth := 128 }) (add safe (by tla_omega), norm (by tla_choice))) | aesop (config := { maxRuleApplicationDepth := 128 }) (add safe (by tla_omega), safe (by tla_instantiate), unsafe 50% (by tla_state_witness), norm (by tla_choice))']

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
            return self.leaf(proof, indent, restrict=True)
        if proof.tag != 'steps':
            raise ProofError('unsupported proof node: ' + proof.tag)
        refs = [x for x in proof if x.tag not in ('location', 'level')]
        # Definition visibility is local to this proof, including nested proofs.
        saved = self.unfold, self.local_state, self.hidden, self.scope_steps, self.used_steps
        self.unfold = list(saved[0])
        self.hidden = dict(saved[2])
        self.scope_steps = list(saved[3])
        self.used_steps = set(saved[4])
        try:
            return self.steps(refs, dict(env), indent, self.goal_body(goal))
        finally:
            self.unfold, self.local_state, self.hidden, self.scope_steps, self.used_steps = saved

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
                # HIDE removes named facts from the default context for the
                # rest of this scope. They are wrapped, not discarded, so a
                # later USE or an explicit BY citation can restore them.
                for fact in reference.findall('facts/*'):
                    kind, uid = self.fact_reference(fact)
                    if hiding:
                        if kind != 'TheoremDefRef' or uid not in self.facts:
                            raise ProofError('HIDE supports step and theorem names; unsupported fact: '
                                             + (kind or fact.tag))
                        self.used_steps.discard(uid)
                        if uid in self.hidden:
                            continue
                        self.uses_hidden = True
                        for name, certain in self.facts[uid]:
                            wrap = (f'have hidden_{name} : TLAHiddenFact _ := ⟨{name}⟩; clear {name}')
                            lines.append(indent + (wrap if certain else f'try ({wrap})'))
                        self.hidden[uid] = self.facts[uid]
                    elif kind == 'TheoremDefRef' and uid in self.hidden:
                        lines += self.reveal(uid, indent)
                        del self.hidden[uid]
                    if kind in ('TheoremDefRef', 'AssumeDefRef') and not hiding:
                        self.used_steps.add(uid)
                if hiding:
                    continue
                # USE facts are obligations, not assumptions. Reconstruct each
                # before making it available to subsequent source steps.
                for fact_index, fact in enumerate(reference.findall('facts/*')):
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
            definition_uid = step.node.findtext('definition/TheoremDefRef/UID')
            if name == '$Qed':
                if index != len(references) - 1:
                    raise ProofError('QED must terminate its proof scope')
                return lines + self.render(proof_node(step, implicit=True), env, indent, goal)
            if name == '$Take':
                lines.append(indent + 'first | apply (_root_.TLAUniversal.truth_boolean _).2 | skip')
                if self.level(goal) >= 1 and any(group.tag != 'unbound' for group in body.find('boundSymbols')):
                    self.local_state = True
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
                if definition_uid:
                    self.facts[definition_uid] = [('picked_fact_' + step.uid, True)]
                if self.level(body) >= 1:
                    self.local_state = True
                continue
            if name == '$Pfcase':
                if self.level(args[0]) >= 1:
                    self.local_state = True
                lines.append(indent + f'by_cases {label} : {self.proposition(args[0], env)}')
                lines.append(indent + '·')
                if definition_uid:
                    self.facts[definition_uid] = [(label, True)]
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
                if definition_uid:
                    self.facts[definition_uid] = [('have_' + step.uid, True)]
                if self.level(args[0]) >= 1:
                    self.local_state = True
                definition = step.node.find('definition/TheoremDefRef/UID')
                if definition is not None:
                    env[definition.text] = ValueBinding(self.compiler.expr(args[0], env))
                goal = consequent
                continue
            if step.node.find('suffices') is not None:
                if name == '$Suffices':
                    body = args[0]
                lines.append(indent + f'suffices {label} : {self.proposition(body, env)} by')
                outer = self.local_state
                self.local_state = outer or self.level(body) >= 1
                lines += self.render(proof_node(step, implicit=True), dict(env), indent + '  ', goal)
                self.local_state = outer or self.state_premises(body)
                goal = self.goal_body(body)
                opened, env = self.open_statement(body, env, indent)
                lines += opened
                continue
            proposition = self.proposition(body, env)
            step_proof = proof_node(step, implicit=True)
            opened, child_env = self.open_statement(body, env, indent + '  ')
            outer = self.local_state
            self.local_state = outer or self.state_premises(body)
            proof_lines = opened + self.render(step_proof, child_env, indent + '  ', body)
            self.local_state = outer
            generalize = (step.level in (1, 2) or definition_uid in self.ptl_cited) and not outer
            if definition_uid:
                self.facts[definition_uid] = [(label, True)] + ([(label + '_general', False)] if generalize else [])
                self.scope_steps.append(definition_uid)
            if generalize:
                # Generalization is attempted with a fresh behavior/time, but
                # existing assumptions retain their original types. Lean must
                # prove this stronger statement; a local premise cannot become
                # a universally valid state fact merely by being cited.
                general = label + '_general'
                lines.append(indent + 'first')
                lines.append(indent + f'| have {general} : ∀ (b : _root_.TLAUniversal.Behavior) '
                             + f'(n : _root_.Nat), {proposition} := by')
                lines.append(indent + '    intro b n')
                lines.append(indent + '    tla_rebase b n')
                lines += ['  ' + line for line in proof_lines]
                lines.append(indent + f'  have {label} : {proposition} := {general} b n')
                lines.append(indent + f'| have {label} : {proposition} := by')
                lines += ['  ' + line for line in proof_lines]
            else:
                lines.append(indent + f'have {label} : {proposition} := by')
                lines += proof_lines
        raise ProofError('hierarchical proof has no final QED')


def compile_proofs(source, *, trace=False, **kwargs):
    graph = parse_file(source, **kwargs)
    compiler = UniversalCompiler(graph)
    code = compiler.compile()
    exports = compiler.proof_exports
    theorems = graph.proof_claims()
    if not theorems:
        return code
    code = code.replace('public import TLAUniversal', 'public import TLAUniversal\nimport Aesop\nimport Mathlib.Tactic.NormNum', 1)
    lines = [f'namespace {exports["namespace"]}', '@[expose] public noncomputable section',
             'set_option maxHeartbeats 4000000',
             'set_option linter.unusedSimpArgs false',
             # Linters re-run proof-search tactics after the proof is done
             # (doubling search time); they never affect what is checked.
             'set_option linter.all false',
             'set_option linter.tacticAnalysis false']
    # Re-run semantic normalization inside proof search after quantified
    # domain witnesses are introduced, not only before the search begins.
    normalized = ('truth_boolean truth_true not_truth_false false_ne_true integer_eq_iff '
                  'boolean_eq_true_iff boolean_eq_false_iff '
                  'integer_mem_naturals integer_mem '
                  'realBinary_add_integer realBinary_mul_integer realNegate_integer '
                  'realSubtract_integer realLessEqual_integer realLess_integer realPower_integer_nonnegative '
                  'intBinary_integer numberInterval_integer integer_mem_interval '
                  'enumerate_nil enumerate_subset_iff union_subset_iff mem_enumerate mem_image caseValue apply_function domain_function function_isFunc_iff '
                  'domain_update domain_updatePath_cons update_same update_other updatePath selectPath '
                  'domain_tuple apply_tuple_at tuple_eq_iff length_tuple '
                  'prepend_tuple mem_cartesian_cons mem_cartesian_nil '
                  'string_eq_iff string_mem domain_record apply_record_lookup record_isFunc_iff record_eq_iff record_two_eq_iff mem_recordSpace mem_recordSpace_two mem_interval_iff mem_union_enumerate').split()
    # Membership in Nat/Int names the value as `v = integer k`, so simp_all
    # substitutes it everywhere; existential naturals reduce to `0 ≤ z`.
    lines += [
        'theorem tla_mem_naturals_eq (v : _root_.TLAUniversal.Value) : v ∈ _root_.TLAUniversal.naturals ↔ '
        '∃ k : _root_.Nat, v = _root_.TLAUniversal.integer k := by',
        '  rw [_root_.TLAUniversal.mem_naturals]; exact exists_congr fun _ => eq_comm',
        'theorem tla_mem_integers_eq (v : _root_.TLAUniversal.Value) : v ∈ _root_.TLAUniversal.integers ↔ '
        '∃ k : _root_.Int, v = _root_.TLAUniversal.integer k := by',
        '  rw [_root_.TLAUniversal.mem_integers]; exact exists_congr fun _ => eq_comm',
        'theorem tla_exists_nat_eq (z : _root_.Int) : (∃ k : _root_.Nat, z = (k : _root_.Int)) ↔ 0 ≤ z :=',
        '  ⟨fun ⟨k, h⟩ => h ▸ Int.natCast_nonneg k, fun h => ⟨z.toNat, (Int.toNat_of_nonneg h).symm⟩⟩',
        "theorem tla_exists_nat_eq' (z : _root_.Int) : (∃ k : _root_.Nat, (k : _root_.Int) = z) ↔ 0 ≤ z :=",
        '  ⟨fun ⟨k, h⟩ => h ▸ Int.natCast_nonneg k, fun h => ⟨z.toNat, Int.toNat_of_nonneg h⟩⟩',
        "attribute [local simp] tla_mem_naturals_eq tla_mem_integers_eq tla_exists_nat_eq tla_exists_nat_eq'"]
    lines.append('attribute [local simp] ' + ' '.join(
        '_root_.TLAUniversal.' + name for name in normalized)
        + ' _root_.ZFSet.zftrue_ne_zffalse _root_.ZFSet.pair_inj _root_.not_and_or _root_.List.lookup_cons')
    lines.append('attribute [local simp] _root_.TLA.weakFairness _root_.TLA.strongFairness '
                 '_root_.TLA.always _root_.TLA.eventually _root_.TLA.state '
                 '_root_.TLA.action _root_.TLA.enabled _root_.TLA.angle _root_.TLA.unchanged')
    lines.append('attribute [local simp ↓] _root_.TLAUniversal.record_mem_singletonSpace _root_.TLAUniversal.mem_recordSpace_two '
                 '_root_.TLAUniversal.record_two_eq_iff '
                 '_root_.TLAUniversal.apply_updatePath_other '
                 '_root_.TLAUniversal.apply_updatePath_single '
                 '_root_.TLAUniversal.update_other _root_.TLAUniversal.update_same '
                 '_root_.TLAUniversal.domain_updatePath_cons '
                 '_root_.TLAUniversal.domain_update _root_.TLAUniversal.domain_record')
    # Boolean range inference is useful only when the emitted source uses BOOLEAN.
    if 'integers' in code:
        lines += [
            'private theorem tla_integer_function_apply {D f x : _root_.TLAUniversal.Value} '
            '(hf : _root_.ZFSet.IsFunc D _root_.TLAUniversal.integers f) (hx : x ∈ D) : '
            '∃ n : _root_.Int, _root_.TLAUniversal.apply f x = _root_.TLAUniversal.integer n := '
            '(tla_mem_integers_eq _).mp (_root_.TLAUniversal.apply_mem hf hx)',
            'attribute [local aesop safe apply] tla_integer_function_apply']
    if 'ZFSet.𝔹' in code:
        lines.append('attribute [local aesop safe apply] _root_.TLAUniversal.boolean_function_apply')
    lines.append('attribute [local aesop safe apply] _root_.TLAUniversal.remainder_nonnegative '
                 '_root_.TLAUniversal.remainder_upper _root_.Int.emod_lt_of_pos '
                 '_root_.TLAUniversal.realPower_integer_mem '
                 '_root_.TLAUniversal.update_isFunc _root_.TLAUniversal.record_isFunc _root_.TLAUniversal.subset_intro '
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
                 '_root_.TLAUniversal.function_range_mono '
                 '_root_.TLAUniversal.singleton_range_isFunc '
                 '_root_.TLAUniversal.subset_member')
    lines.append('attribute [local aesop unsafe 50% apply] _root_.TLAUniversal.function_ext '
                 '_root_.TLAUniversal.apply_record '
                 '_root_.TLAUniversal.record_isFunc_of_domain '
                 '_root_.TLAUniversal.function_range_of_values '
                 '_root_.TLAUniversal.record_eta')
    # TLA+ operators are Leibniz: equal arguments give equal results. For
    # operators that evaluate their arguments in the current state, Lean
    # checks the congruence lemma by unfolding; tla_try drops any operator
    # for which it does not hold, so no unproved fact is ever added.
    for symbol in graph.definitions(include_imported=True):
        entry = compiler.emitted.get(symbol.uid)
        if not entry or not entry[1] or any(entry[1]) or (symbol.level or 0) > 1:
            continue
        name, arities = entry
        k = len(arities)
        ps = [f'p{i}' for i in range(k)]
        qs = [f'q{i}' for i in range(k)]
        hyps = ' '.join(f'(h{i} : p{i} b n = q{i} b n)' for i in range(k))
        const = lambda xs: ' '.join(f'(fun _ _ => {x} b n)' for x in xs)
        lines += [f'tla_try @[local aesop unsafe 30% apply] theorem tla_leibniz_{symbol.uid} '
                  f'({" ".join(ps + qs)} : _root_.TLAUniversal.Expression) (c : {exports["constants"]}) '
                  f'(b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) {hyps} : '
                  f'{name} {" ".join(ps)} c b n = {name} {" ".join(qs)} c b n := by',
                  f'  show {name} {const(ps)} c b n = {name} {const(qs)} c b n',
                  '  rw [' + ', '.join(f'h{i}' for i in range(k)) + ']',
                  # Normal form: arguments as current-state constants, so
                  # simp can rewrite inside them with state equations.
                  f'tla_try @[local simp] theorem tla_leibniz_normal_{symbol.uid} '
                  f'({" ".join(ps)} : _root_.TLAUniversal.Expression) (c : {exports["constants"]}) '
                  f'(b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) : '
                  f'{name} {" ".join(ps)} c b n = {name} {const(ps)} c b n := by rfl']
    names = exports['proof_names']
    hidden_definition = len(lines)
    uses_hidden = False
    theorem_facts = {}
    # Module-level USE/HIDE apply to later theorems in source order.
    module_context = {}
    module_unfold, module_used = [], set()
    for child in graph.root.node:
        if child.tag == 'TheoremNodeRef':
            module_context[child.findtext('UID')] = (list(module_unfold), set(module_used))
        if child.tag != 'UseOrHideNode':
            continue
        hiding = child.find('hide') is not None
        for definition in child.findall('defs/*'):
            symbol = graph.resolve(definition)
            if symbol.uid in compiler.emitted:
                emitted = compiler.emitted[symbol.uid][0]
                if hiding:
                    module_unfold = [x for x in module_unfold if x != emitted]
                elif emitted not in module_unfold:
                    module_unfold.append(emitted)
        for fact in child.findall('facts/*'):
            kind, uid = Renderer.fact_reference(fact)
            if kind in ('TheoremDefRef', 'AssumeDefRef'):
                (module_used.discard if hiding else module_used.add)(uid)
    assumptions = [(symbol.node.findtext('definition/AssumeDefRef/UID'), f'assume_{i}')
                   for i, symbol in enumerate(graph.claims('AssumeNode'))]
    if len(assumptions) == 1:
        split = ['  have assume_0 := source_assumptions', '  clear source_assumptions']
    elif assumptions:
        split = ['  obtain ⟨' + ', '.join(name for _, name in assumptions) + '⟩ := source_assumptions']
    else:
        split = []
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
        context_unfold, context_used = module_context.get(theorem.uid, ([], set()))
        if str(theorem.uid).startswith('module_use_'):
            # A module-level USE fact is itself an obligation over the whole module context.
            context_used = {uid for uid, _ in assumptions if uid}
        unfold += context_unfold
        # Only already checked theorems enter the context. A BY reference is
        # never converted to an assumed proposition merely because SANY resolved it.
        # ASSUME is constant-level, so the module assumptions discharge an
        # earlier theorem's premise at every behavior and time.
        for previous in range(index):
            lines.append(f'  have prior_{previous} := by first '
                         f'| exact (fun b n => {names[previous]} c b n source_assumptions : '
                         f'∀ (b : _root_.TLAUniversal.Behavior) (n : _root_.Nat), {exports["claims"][previous]} c b n) '
                         f'| exact {names[previous]} c')
            unfold.append(exports['claims'][previous])
        lines += split
        renderer = Renderer(compiler, unfold, trace=trace, claim=index, facts=theorem_facts,
                            assumptions=assumptions, used=context_used)
        opened, environment = renderer.open_statement(theorem.body, {}, '  ')
        renderer.local_state = renderer.state_premises(theorem.body)
        renderer.ptl_cited = renderer.ptl_citations(proof)
        lines += opened + renderer.render(proof, environment, goal=theorem.body)
        uses_hidden = uses_hidden or renderer.uses_hidden
        definition = theorem.node.findtext('definition/TheoremDefRef/UID')
        if definition:
            theorem_facts[definition] = [(f'prior_{index}', True)]
    if uses_hidden:
        # An opaque wrapper: simp, aesop and assumption do not look inside it.
        lines[hidden_definition:hidden_definition] = [
            'structure TLAHiddenFact (p : Prop) : Prop where', '  val : p']
    lines += [f'def {exports["certificate_proof"]} (c : {exports["constants"]}) : '
              f'{exports["certificate"]} c :=',
              '  ⟨' + ', '.join(name + ' c' for name in names) + '⟩',
              'end', f'end {exports["namespace"]}', '']
    return code + '\n' + '\n'.join(lines)
