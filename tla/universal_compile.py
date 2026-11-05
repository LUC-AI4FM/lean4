#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Compile SANY expressions over the common ZFC value universe."""
import argparse
from dataclasses import dataclass
import json
import re
from pathlib import Path
import xml.etree.ElementTree as ET
from compiler import CompileError, ident, lean_string
from sany import parse_file, SanyError

SEMANTIC_NAMES = set("""Value State Behavior Expression truth boolean integer integers toInt naturals interval real reals realUnary realBinary realDivide realPower realLess realLessEqual infinity
    enumerate image choose function apply domain update undefined intUnary intBinary intCompare
    tuple length sequences append prepend cartesian caseValue concatenate subsequence string strings
    record recordSpace selectPath updatePath finite cardinality intPower recursiveOperator expressionLevel""".split())

def qualify(code):
    # Keep source identifiers and string literals intact while qualifying library names.
    def token(match):
        name = match[0]
        if name in SEMANTIC_NAMES:
            return '_root_.TLAUniversal.' + name
        if name.split('.')[0] in {'TLA', 'ZFSet', 'Nat', 'Int', 'Real', 'String'}:
            return '_root_.' + name
        return name
    return re.sub(r'"(?:\\.|[^"\\])*"|«[^»]*»|[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', token, code)

@dataclass
class ValueBinding:
    code: str

@dataclass
class OperatorBinding:
    name: str
    arity: int

@dataclass
class RecursiveBinding:
    graph: str
    arity: int
    tag: int | None = None

@dataclass
class LevelBinding:
    name: str
    level: int

@dataclass
class StateBinding:
    key: str

@dataclass
class ExpressionBinding:
    name: str
    arity: int = 0

@dataclass
class SyntaxBinding:
    node: object
    env: dict

class UniversalCompiler:
    def __init__(self, graph):
        self.g = graph
        self.real_arithmetic = any(s.location == "Reals" for s in graph.symbols.values())
        self.vars = {s.uid for s in graph.variables()}
        self.consts = {s.uid for s in graph.constants()}
        self.active = []
        self.emitted = {}
        self.serial = 0
        recursive = {uid: symbol for uid, symbol in graph.symbols.items()
                     if symbol.node.tag == 'UserDefinedOpKind' and symbol.node.find('recursive') is not None}
        def reachable(uid, seen=None):
            seen = set() if seen is None else seen
            if uid in seen:
                return seen
            seen.add(uid)
            symbol = graph.symbols[uid]
            if symbol.node.tag == 'UserDefinedOpKind':
                for ref in symbol.body.iter('UserDefinedOpKindRef'):
                    reachable(ref.findtext('UID'), seen)
            return seen
        reach = {uid: reachable(uid) for uid in recursive}
        self.recursive_groups = {
            uid: [recursive[other] for other in sorted(recursive, key=int)
                  if other in reach[uid] and uid in reach[other]] for uid in recursive}


    def fresh(self):
        self.serial += 1
        return f'z{self.serial}'

    @staticmethod
    def app(symbol, args=()):
        node = ET.Element('OpApplNode')
        op = ET.SubElement(node, 'operator')
        ref = ET.SubElement(op, symbol.node.tag + 'Ref')
        ET.SubElement(ref, 'UID').text = symbol.uid
        operands = ET.SubElement(node, 'operands')
        operands.extend(args)
        return node

    def expr(self, node, env=None, b='b', n='n', *, operator_override=None):
        env = {} if env is None else env
        if node.tag == 'NumeralNode':
            number = node.findtext('IntValue') or node.findtext('BigIntValue')
            if number is None or not number.lstrip('-').isdigit():
                raise CompileError('invalid numeral')
            return f'(integer {number})'
        if node.tag == 'DecimalNode':
            mantissa, exponent = int(node.findtext('mantissa')), int(node.findtext('exponent'))
            if abs(exponent) > 10000:
                raise CompileError('decimal exponent exceeds the translation resource limit')
            return f'(real (({mantissa} : _root_.Real) * (10 : _root_.Real) ^ ({exponent} : Int)))'
        if node.tag == 'StringNode':
            return '(string ' + lean_string(node.findtext('StringValue', '')) + ')'
        if node.tag == 'AssumeProveNode':
            def obligation(items, context, trace):
                if not items:
                    return 'truth ' + self.expr(node.find('prove')[0], context, trace, n)
                head, *tail = items
                if head.tag != 'NewSymbNode':
                    premise = self.expr(head, context, trace, n)
                    return f'(truth {premise} → {obligation(tail, context, trace)})'
                declaration = self.g.resolve(head.find('OpDeclNodeRef'))
                variable = self.fresh()
                extended = dict(context)
                level = declaration.level or 0

                locality = None
                if level and declaration.arity:
                    extended[declaration.uid] = ExpressionBinding(variable, declaration.arity)
                    ty = ' → '.join(['Expression'] * (declaration.arity + 1))
                    parameters = [self.fresh() for _ in range(declaration.arity)]
                    signature = ' '.join(f'({p} : Expression)' for p in parameters)
                    premises = ' → '.join(f'expressionLevel {level} {p}' for p in parameters)
                    application = '(' + ' '.join([variable, *parameters]) + ')'
                    locality = f'(∀ {signature}, {premises} → expressionLevel {level} {application})'
                elif declaration.node.findtext('kind') == '25':
                    key, time, field = '$new:' + declaration.uid, self.fresh(), self.fresh()
                    extended[declaration.uid] = StateBinding(key)
                    trace = f'(fun {time} {field} => if {field} = {lean_string(key)} then {variable} {time} else ({trace}) {time} {field})'
                    ty = 'Nat → Value'
                elif level:
                    extended[declaration.uid] = LevelBinding(variable, level)
                    ty = {1: 'State → Value', 2: 'State → State → Value', 3: 'Behavior → Value'}[level]
                else:
                    extended[declaration.uid] = OperatorBinding(variable, declaration.arity)
                    ty = ' → '.join(['Value'] * (declaration.arity + 1))
                body = obligation(tail, extended, trace)
                if locality:
                    body = f'({locality} → {body})'
                elif level == 3:
                    left, right = self.fresh(), self.fresh()
                    body = f'((∀ ({left} {right} : Behavior), TLA.stutteringEquivalent {left} {right} → {variable} {left} = {variable} {right}) → {body})'
                bounds = [x for x in head if x.tag not in ('location', 'level', 'OpDeclNodeRef')]
                if bounds:
                    if len(bounds) != 1 or declaration.arity:
                        raise CompileError('invalid NEW symbol bound')
                    domain = self.expr(bounds[0], context, trace, n)
                    value = self.expr(self.app(declaration), extended, trace, n)
                    body = f'({value} ∈ {domain} → {body})'
                return f'(∀ ({variable} : {ty}), {body})'
            return '(boolean ' + obligation(list(node.find('assumes')), env, b) + ')'
        if node.tag in ('LetInNode', 'LabelNode'):
            return self.expr(node.find('body')[0], env, b, n)
        if node.tag in ('SubstInNode', 'APSubstInNode'):
            substituted = dict(env)
            for subst in node.findall('substs/Subst'):
                parts = [x for x in subst if x.tag not in ('location', 'level')]
                if len(parts) != 2:
                    raise CompileError('malformed module substitution')
                substituted[parts[0].findtext('UID')] = SyntaxBinding(parts[1], env)
            return self.expr(node.find('body')[0], substituted, b, n)
        if node.tag == 'AtNode':
            parts = [x for x in node if x.tag not in ('location', 'level')]
            value = env['@except'].code if '@except' in env else self.expr(parts[0], env, b, n)
            keys = [self.expr(x, env, b, n) for x in parts[1].find('operands')]
            return f'(selectPath {value} [{", ".join(keys)}])'
        if node.tag != 'OpApplNode':
            raise CompileError(f'unimplemented universal semantic node: {node.tag}')
        symbol = self.g.operator(node)
        args = list(node.find('operands'))
        if symbol.uid in env:
            binding = env[symbol.uid]
            if isinstance(binding, LevelBinding):
                if args:
                    raise CompileError('level-specific expression used as an operator')
                if binding.level == 1:
                    return f'({binding.name} (({b}) ({n})))'
                if binding.level == 2:
                    return f'({binding.name} (({b}) ({n})) (({b}) (({n}) + 1)))'
                return f'({binding.name} (fun k => ({b}) (({n}) + k)))'
            if isinstance(binding, OperatorBinding):
                if len(args) != binding.arity:
                    raise CompileError('operator arity mismatch')
                values = [self.expr(a, env, b, n) for a in args]
                return '(' + ' '.join([binding.name, *values]) + ')'
            if isinstance(binding, RecursiveBinding):
                if len(args) != binding.arity:
                    raise CompileError('recursive operator arity mismatch')
                actuals = [self.expr(a, env, b, n) for a in args]
                key = actuals[0] if len(actuals) == 1 else f'(tuple [{", ".join(actuals)}])'
                if binding.tag is not None:
                    key = f'(tuple [(integer {binding.tag}), {key}])'
                return f'(apply {binding.graph} {key})'
            if isinstance(binding, StateBinding):
                if args:
                    raise CompileError('flexible variable used as an operator')
                return f'(({b}) ({n}) {json.dumps(binding.key)})'
            if isinstance(binding, ValueBinding):
                if args:
                    raise CompileError('value used as an operator')
                return binding.code
            if isinstance(binding, ExpressionBinding):
                if len(args) != binding.arity:
                    raise CompileError('operator parameter arity mismatch')
                actuals = [f'(fun b n => {self.expr(a, env)})' for a in args]
                return f'({binding.name} {" ".join(actuals)} ({b}) ({n}))'
            if binding.node.tag == 'OpArgNode':
                return self.operator_argument(binding.node, args, env, binding.env, b, n)
            if args:
                raise CompileError('nonoperator syntax argument applied')
            return self.expr(binding.node, binding.env, b, n)
        if symbol.uid in self.vars:
            return f'(({b}) ({n}) {json.dumps(symbol.name)})'
        if symbol.uid in self.consts:
            values = [self.expr(a, env, b, n) for a in args]
            return f'(c.{ident(symbol.name)} {" ".join(values)})'
        if symbol.uid in self.emitted:
            name, arities = self.emitted[symbol.uid]
            if len(args) == len(arities) and not any(arities):
                actuals = []
                for argument in args:
                    trace, time = self.fresh(), self.fresh()
                    body = self.expr(argument, env, trace, time)
                    actuals.append(f'(fun ({trace} : Behavior) ({time} : Nat) => {body})')
                return '(' + ' '.join([name, *actuals, 'c', f'({b})', f'({n})']) + ')'
        name, origin = operator_override or symbol.name, symbol.location
        name = {'\\union': '\\cup', '\\intersect': '\\cap', '$NonRecursiveFcnSpec': '$FcnConstructor'}.get(name, name)
        body = symbol.node.find('body')
        if body is not None and len(body) == 1:
            original = body[0]
            while original.tag in ('SubstInNode', 'APSubstInNode'):
                original = original.find('body')[0]
            # LOCAL INSTANCE copies the declaration location into the importing
            # module, while the expression retains its defining source location.
            origin = original.findtext('location/filename', origin)
        standard = origin in ('Naturals', 'Integers', 'Reals', 'Sequences', 'FiniteSets')
        if standard:
            name = name.rsplit('!', 1)[-1]
        if standard:
            standard = name in {
                'Nat', 'Int', 'Real', 'Infinity', '+', '-', '*', '/', '\\div', '%', '^', '-.',
                '<', '>', '\\leq', '\\geq', '..', 'Seq', 'Len', 'Append', '\\o',
                'SubSeq', 'Head', 'Tail', 'IsFiniteSet', 'Cardinality'}
        if symbol.node.tag != 'BuiltInKind' and not standard:
            if symbol.node.tag in ('AssumeDef', 'TheoremDefNode'):
                return self.expr(symbol.body, env, b, n)
            if symbol.node.tag != 'UserDefinedOpKind':
                raise CompileError(f'unsupported universal symbol: {name}')
            if symbol.uid in self.active:
                raise CompileError(f'recursive operator needs a fixed-point obligation: {name}')
            params = symbol.node.findall('params/leibnizparam/FormalParamNodeRef')
            if len(params) != len(args):
                raise CompileError(f'arity mismatch: {name}')
            if symbol.node.find('recursive') is not None:
                return self.recursive(symbol, params, args, env, b, n)
            extended = dict(env)
            extended.update({p.findtext('UID'): SyntaxBinding(a, env) for p, a in zip(params, args)})
            self.active.append(symbol.uid)
            try:
                return self.expr(symbol.body, extended, b, n)
            finally:
                self.active.pop()
        if name == '$Nop' and len(args) == 1:
            return self.expr(args[0], env, b, n)
        if name == '$RecursiveFcnSpec':
            copy = ET.fromstring(ET.tostring(node))
            unbound = copy.find('boundSymbols/unbound')
            variable = self.fresh()
            extended = dict(env)
            extended[unbound[0].findtext('UID')] = ValueBinding(variable)
            copy.find('boundSymbols').remove(unbound)
            body = self.expr(copy, extended, b, n, operator_override='$FcnConstructor')
            return f'(choose (fun ({variable} : Value) => {variable} = {body}))'
        if name in ('$TemporalExists', '$TemporalForall'):
            refs = node.findall('boundSymbols/unbound/FormalParamNodeRef')
            if not refs:
                raise CompileError('missing flexible variable')
            def quantify(remaining, context, trace, index):
                if not remaining:
                    return self.expr(args[0], context, trace, index)
                ref, *rest = remaining
                history, sampled, time, keyvar = self.fresh(), self.fresh(), self.fresh(), self.fresh()
                key = '$bound:' + ref.findtext('UID')
                extended = dict(context); extended[ref.findtext('UID')] = StateBinding(key)
                lifted = f'(fun t {keyvar} => if {keyvar} = {json.dumps(key)} then {history} t else {sampled} t {keyvar})'
                inner = quantify(rest, extended, lifted, time)
                fn = 'existsFlexible' if name == '$TemporalExists' else 'forallFlexible'
                return f'(boolean (TLA.{fn} (fun ({history} : Nat → Value) ({sampled} : Behavior) {time} => truth {inner}) ({trace}) ({index})))'
            return quantify(refs, env, b, n)
        if name == '-+->':
            trace, time = self.fresh(), self.fresh()
            left = self.expr(args[0], env, trace, time)
            right = self.expr(args[1], env, trace, time)
            return f'(boolean (TLA.guarantees (fun ({trace} : Behavior) ({time} : Nat) => truth {left}) (fun ({trace} : Behavior) ({time} : Nat) => truth {right}) ({b}) ({n})))'
        if name == '~>':
            start, end = self.fresh(), self.fresh()
            left = self.expr(args[0], env, b, start)
            right = self.expr(args[1], env, b, end)
            return f'(boolean (∀ {start} : Nat, ({n}) ≤ {start} → truth {left} → ∃ {end} : Nat, {start} ≤ {end} ∧ truth {right}))'
        if name == '\\cdot':
            middle, time = self.fresh(), self.fresh()
            left_trace = f'(fun {time} => if {time} = ({n}) + 1 then {middle} else ({b}) {time})'
            right_trace = f'(fun {time} => if {time} = ({n}) then {middle} else ({b}) {time})'
            left = self.expr(args[0], env, left_trace, n)
            right = self.expr(args[1], env, right_trace, n)
            return f'(boolean (∃ {middle} : State, truth {left} ∧ truth {right}))'
        if name == "'":
            return self.expr(args[0], env, b, f'({n}) + 1')
        if name in ('[]', '<>'):
            k = self.fresh(); formula = self.expr(args[0], env, b, k)
            quantifier, connective = ('∀', '→') if name == '[]' else ('∃', '∧')
            return f'(boolean ({quantifier} {k} : Nat, ({n}) ≤ {k} {connective} truth {formula}))'
        if name in ('UNCHANGED', '$SquareAct', '$AngleAct'):
            frame = args[0] if name == 'UNCHANGED' else args[1]
            current = self.expr(frame, env, b, n)
            nxt = self.expr(frame, env, b, f'({n}) + 1')
            equality = f'({nxt} = {current})'
            if name == 'UNCHANGED': return f'(boolean {equality})'
            action = self.expr(args[0], env, b, n)
            connective = '∨' if name == '$SquareAct' else '∧ ¬'
            return f'(boolean (truth {action} {connective} {equality}))'
        if name == 'ENABLED':
            state, k = self.fresh(), self.fresh()
            trace = f'(fun {k} => if {k} = ({n}) + 1 then {state} else ({b}) {k})'
            return f'(boolean (∃ {state} : State, truth {self.expr(args[0], env, trace, n)}))'
        if name in ('$WF', '$SF'):
            s, t, k = self.fresh(), self.fresh(), self.fresh()
            trace = f'(fun {k} => if {k} = 0 then {s} else {t})'
            frame = self.expr(args[0], env, f'(fun _ => {s})', '0')
            action = self.expr(args[1], env, trace, '0')
            fn = 'weakFairness' if name == '$WF' else 'strongFairness'
            return f'(boolean (TLA.{fn} (fun ({s} {t} : State) => truth {action}) (fun ({s} : State) => {frame}) ({b}) ({n})))'
        if name in ('$BoundedForall', '$BoundedExists', '$UnboundedForall', '$UnboundedExists',
                    '$BoundedChoose', '$UnboundedChoose', '$SubsetOf', '$SetOfAll', '$FcnConstructor'):
            extended, bindings = dict(env), []
            for group in node.find('boundSymbols'):
                refs = group.findall('FormalParamNodeRef')
                domains = [x for x in group if x.tag not in ('FormalParamNodeRef', 'tuple')]
                if group.tag == 'unbound':
                    domain = None
                elif len(domains) == 1:
                    domain = self.expr(domains[0], extended, b, n)
                else:
                    raise CompileError('tuple-pattern binder not implemented')
                if group.find('tuple') is not None:
                    v = self.fresh(); bindings.append((v, domain))
                    for i, ref in enumerate(refs):
                        extended[ref.findtext('UID')] = ValueBinding(f'(apply {v} (integer {i + 1}))')
                else:
                    for ref in refs:
                        v = self.fresh(); bindings.append((v, domain))
                        extended[ref.findtext('UID')] = ValueBinding(v)
            formula = self.expr(args[0], extended, b, n)
            if name in ('$SubsetOf', '$BoundedChoose', '$UnboundedChoose'):
                if len(bindings) != 1:
                    raise CompileError('invalid CHOOSE/subset binder count')
                v, domain = bindings[0]
                if name == '$SubsetOf':
                    return f'({domain}.sep (fun {v} => truth {formula}))'
                guard = f'{v} ∈ {domain} ∧ ' if domain else ''
                return f'(choose (fun {v} => {guard}truth {formula}))'
            if name == '$FcnConstructor':
                if len(bindings) == 1:
                    v, domain = bindings[0]
                    return f'(function {domain} (fun {v} => {formula}))'
                key = self.fresh()
                domains = ', '.join(domain for _, domain in bindings)
                body = formula
                for i, (v, _) in reversed(list(enumerate(bindings))):
                    body = f'(let {v} := apply {key} (integer {i + 1}); {body})'
                return f'(function (cartesian [{domains}]) (fun {key} => {body}))'
            if name == '$SetOfAll':
                value = formula
                for v, domain in reversed(bindings):
                    value = f'(image {domain} (fun {v} => {value}))'
                    if (v, domain) != bindings[-1]:
                        value = f'(ZFSet.sUnion {value})'
                return value
            universal = name in ('$BoundedForall', '$UnboundedForall')
            quantifier, connective = ('∀', '→') if universal else ('∃', '∧')
            value = f'truth {formula}'
            for v, domain in reversed(bindings):
                guard = f'{v} ∈ {domain} {connective} ' if domain else ''
                value = f'({quantifier} {v} : Value, {guard}{value})'
            return f'(boolean {value})'
        if name == '$Case':
            clauses, fallback = [], 'undefined'
            for pair in args:
                guard, value = list(pair.find('operands'))
                rhs = self.expr(value, env, b, n)
                if guard.tag == 'StringNode' and guard.text == '$Other':
                    fallback = rhs
                else:
                    clauses.append(f'({self.expr(guard, env, b, n)}, {rhs})')
            return f'(caseValue [{", ".join(clauses)}] {fallback})'
        if name in ('$RcdConstructor', '$SetOfRcds'):
            fields = []
            for pair in args:
                key, value = list(pair.find('operands'))
                if key.tag != 'StringNode': raise CompileError('invalid record label')
                fields.append(f'({json.dumps(key.findtext("StringValue"))}, {self.expr(value, env, b, n)})')
            fn = 'record' if name == '$RcdConstructor' else 'recordSpace'
            return f'({fn} [{", ".join(fields)}])'
        if name == '$Except':
            value = self.expr(args[0], env, b, n)
            for pair in args[1:]:
                path, rhs = list(pair.find('operands'))
                keys = [self.expr(k, env, b, n) for k in path.find('operands')]
                updated = dict(env); updated['@except'] = ValueBinding(value)
                replacement = self.expr(rhs, updated, b, n)
                value = f'(updatePath {value} [{", ".join(keys)}] {replacement})'
            return value
        values = [self.expr(a, env, b, n) for a in args]
        def call(fn): return '(' + ' '.join([fn, *values]) + ')'
        if name in ('TRUE', 'FALSE'): return '(ZFSet.zftrue : Value)' if name == 'TRUE' else '(ZFSet.zffalse : Value)'
        if name == 'BOOLEAN': return '(ZFSet.𝔹 : Value)'
        if name == 'STRING': return 'strings'
        if name in ('=', '/='):
            return f'(boolean ({values[0]} {"=" if name == "=" else "≠"} {values[1]}))'
        if name in ('\\land', '\\lor', '=>', '\\equiv'):
            op = {'\\land': '∧', '\\lor': '∨', '=>': '→', '\\equiv': '↔'}[name]
            return f'(boolean (truth {values[0]} {op} truth {values[1]}))'
        if name == '\\lnot': return f'(boolean (¬ truth {values[0]}))'
        if name in ('$ConjList', '$DisjList'):
            op = ' ∧ ' if name == '$ConjList' else ' ∨ '
            return '(boolean (' + op.join('truth ' + v for v in values) + '))'
        if self.real_arithmetic:
            if name in ('+', '-', '*'):
                return f'(realBinary (fun x y => x {name} y) {values[0]} {values[1]})'
            if name == '-.': return f'(realUnary (fun x => -x) {values[0]})'
            if name == '/': return call('realDivide')
            if name == '^': return call('realPower')
            if name == 'Real': return 'reals'
            if name == 'Infinity': return 'infinity'
            if name in ('<', '>', '\\leq', '\\geq'):
                fn = 'realLess' if name in ('<', '>') else 'realLessEqual'
                left, right = values if name in ('<', '\\leq') else reversed(values)
                return f'({fn} {left} {right})'
        if name in ('+', '-', '*', '\\div', '%'):
            op = {'\\div': '/'}.get(name, name)
            return f'(intBinary (fun x y => x {op} y) {values[0]} {values[1]})'
        if name == '^': return call('intPower')
        if standard and name == 'IsFiniteSet': return call('finite')
        if standard and name == 'Cardinality': return call('cardinality')
        if name == '-.': return f'(intUnary (fun x => -x) {values[0]})'
        if name in ('<', '>', '\\leq', '\\geq'):
            op = {'\\leq': '≤', '\\geq': '≥'}.get(name, name)
            return f'(intCompare (fun x y => x {op} y) {values[0]} {values[1]})'
        if name == '$IfThenElse': return f'(if truth {values[0]} then {values[1]} else {values[2]})'
        if name == 'Nat': return 'naturals'
        if name == 'Int': return 'integers'
        if name == '..': return call('interval')
        if name in ('\\in', '\\notin', '\\subseteq'):
            op = {'\\in': '∈', '\\notin': '∉', '\\subseteq': '⊆'}[name]
            return f'(boolean ({values[0]} {op} {values[1]}))'
        if name in ('\\cup', '\\cap', '\\setminus', '\\'):
            op = {'\\cup': '∪', '\\cap': '∩', '\\setminus': '\\', '\\': '\\'}[name]
            return f'({values[0]} {op} {values[1]})'
        if name in ('$SetEnumerate', '$Tuple'):
            fn = 'enumerate' if name == '$SetEnumerate' else 'tuple'
            return f'({fn} [{", ".join(values)}])'
        if name == 'SUBSET': return f'({values[0]}).powerset'
        if name == 'UNION': return call('ZFSet.sUnion')
        if name in ('$FcnApply', '$RcdSelect'): return call('apply')
        if name == '$SetOfFcns': return call('ZFSet.funs')
        if name == '$CartesianProd': return f'(cartesian [{", ".join(values)}])'
        if name == 'DOMAIN': return call('domain')
        sequence_ops = {'Seq': 'sequences', 'Len': 'length', 'Append': 'append', '\\o': 'concatenate', 'SubSeq': 'subsequence'}
        if standard and name in sequence_ops: return call(sequence_ops[name])
        if standard and name == 'Head': return f'(apply {values[0]} (integer 1))'
        if standard and name == 'Tail': return f'(subsequence {values[0]} (integer 2) (length {values[0]}))'
        raise CompileError(f'unsupported universal operator {name!r} from {origin}')

    def operator_argument(self, argument, args, caller, context, b, n):
        target = self.g.resolve(argument.find('argument')[0])
        binding = context.get(target.uid)
        if isinstance(binding, SyntaxBinding) and binding.node.tag == 'OpArgNode':
            return self.operator_argument(binding.node, args, caller, binding.env, b, n)
        if isinstance(binding, ExpressionBinding):
            if len(args) != binding.arity:
                raise CompileError('operator argument arity mismatch')
            actuals = []
            for arg in args:
                trace, time = self.fresh(), self.fresh()
                actuals.append(f'(fun ({trace} : Behavior) ({time} : Nat) => {self.expr(arg, caller, trace, time)})')
            return '(' + ' '.join([binding.name, *actuals, f'({b})', f'({n})']) + ')'
        if isinstance(binding, OperatorBinding) or target.uid in self.consts:
            expected = binding.arity if isinstance(binding, OperatorBinding) else target.arity
            if len(args) != expected:
                raise CompileError('constant operator argument arity mismatch')
            name = binding.name if isinstance(binding, OperatorBinding) else f'c.{ident(target.name)}'
            return '(' + ' '.join([name, *(self.expr(arg, caller, b, n) for arg in args)]) + ')'
        if target.node.tag == 'UserDefinedOpKind':
            params = target.node.findall('params/leibnizparam/FormalParamNodeRef')
            if len(params) != len(args):
                raise CompileError('defined operator argument arity mismatch')
            if target.node.find('recursive') is not None:
                return self.recursive(target, params, args, context, b, n, argument_env=caller)
            extended = dict(context)
            extended.update({p.findtext('UID'): SyntaxBinding(a, caller) for p, a in zip(params, args)})
            return self.expr(target.body, extended, b, n)
        raise CompileError(f'unsupported operator argument target: {target.name}')

    def recursive(self, symbol, params, args, env, b, n, *, argument_env=None):
        members = self.recursive_groups.get(symbol.uid, [symbol])
        mutual = len(members) > 1
        actuals = [self.expr(a, env if argument_env is None else argument_env, b, n) for a in args]
        key = actuals[0] if len(actuals) == 1 else f'(tuple [{", ".join(actuals)}])'
        if mutual:
            tag = next(i for i, member in enumerate(members) if member.uid == symbol.uid)
            key = f'(tuple [(integer {tag}), {key}])'
        point, graph = self.fresh(), self.fresh()
        context = dict(env)
        for i, member in enumerate(members):
            context[member.uid] = RecursiveBinding(graph, member.arity, i if mutual else None)
        point_args = f'(apply {point} (integer 2))' if mutual else point
        bodies = []
        for member in members:
            member_params = member.node.findall('params/leibnizparam/FormalParamNodeRef')
            if any(self.g.resolve(p).arity for p in member_params):
                raise CompileError('recursive higher-order parameters need operator semantics')
            extended = dict(context)
            for i, parameter in enumerate(member_params):
                value = point_args if len(member_params) == 1 else f'(apply {point_args} (integer {i + 1}))'
                extended[parameter.findtext('UID')] = ValueBinding(value)
            self.active.append(member.uid)
            try:
                bodies.append(self.expr(member.body, extended, b, n))
            finally:
                self.active.pop()
        body = bodies[0]
        if mutual:
            body = 'undefined'
            for i, member_body in reversed(list(enumerate(bodies))):
                body = f'(if apply {point} (integer 1) = integer {i} then {member_body} else {body})'
        return f'(recursiveOperator (fun ({point} {graph} : Value) => {body}) {key})'

    def compile(self):
        definitions = self.g.definitions(include_imported=True)
        occupied = {definition.name for definition in definitions}
        def declaration_name(base):
            while base in occupied:
                base += '_'
            occupied.add(base)
            return base
        constants_type = declaration_name('Constants')
        assumptions_name = declaration_name('TLAProofAssumptions')
        certificate_name = declaration_name('Certificate')
        namespace = self.g.root.name
        if namespace in {'TLA', 'TLAUniversal', 'Nat', 'Int', 'Real', 'String', 'List', 'Classical', 'ZFSet'}:
            namespace = 'Source_' + namespace
        lines = ['module', 'import TLAUniversal', '', 'open TLAUniversal Classical',
                 'set_option autoImplicit false', f'namespace {ident(namespace)}', 'noncomputable section', f'structure {constants_type} where']
        for constant in self.g.constants():
            ty = ' → '.join(['_root_.TLAUniversal.Value'] * (constant.arity + 1))
            lines.append(f'  {ident(constant.name)} : {ty}')
        for definition in definitions:
            parameters, environment = [], {}
            for ref in definition.node.findall('params/leibnizparam/FormalParamNodeRef'):
                parameter = self.g.resolve(ref)
                name = 'parameter_' + parameter.uid
                ty = ' → '.join(['_root_.TLAUniversal.Expression'] * (parameter.arity + 1))
                parameters.append(f'({name} : {ty})')
                environment[parameter.uid] = ExpressionBinding(name, parameter.arity)
            if parameters and definition.node.find('recursive') is not None:
                refs = definition.node.findall('params/leibnizparam/FormalParamNodeRef')
                actuals = [self.app(self.g.resolve(ref)) for ref in refs]
                code = self.recursive(definition, refs, actuals, environment, 'b', 'n')
            else:
                code = self.expr(definition.body, environment) if parameters else self.expr(self.app(definition))
            signature = (' '.join(parameters) + ' ') if parameters else ''
            code = qualify(code)
            context, trace, index = 'c', 'b', 'n'
            lines.extend([f'def {ident(definition.name)} {signature}({context} : {constants_type}) ({trace} : _root_.TLAUniversal.Behavior) ({index} : _root_.Nat) : _root_.TLAUniversal.Value :=', '  ' + code])
            refs = definition.node.findall('params/leibnizparam/FormalParamNodeRef')
            self.emitted[definition.uid] = (ident(definition.name), [self.g.resolve(r).arity for r in refs])
        assumptions = [qualify(self.expr(s.body)) for s in self.g.claims('AssumeNode')]
        obligations = [qualify(self.expr(s.body)) for s in self.g.claims('TheoremNode')]
        if assumptions or obligations:
            condition = ' ∧ '.join(f'_root_.TLAUniversal.truth {a}' for a in assumptions) or 'True'
            lines += [f'def {assumptions_name} (c : {constants_type}) (b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) : Prop := {condition}']
            claim_names = [declaration_name(f'TLAProofClaim{i}') for i in range(len(obligations))]
            for name, claim in zip(claim_names, obligations):
                lines += [f'def {name} (c : {constants_type}) (b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) : Prop := _root_.TLAUniversal.truth {claim}']
        if obligations:
            lines += [f'structure {certificate_name} (c : {constants_type}) : Prop where']
            for i in range(len(obligations)):
                lines += [f'  obligation_{i} : ∀ (b : _root_.TLAUniversal.Behavior) (n : _root_.Nat), {assumptions_name} c b n → {claim_names[i]} c b n']
        lines.extend(['end', f'end {ident(namespace)}', ''])
        return '\n'.join(lines)

def compile_file(source, **kwargs):
    try:
        return UniversalCompiler(parse_file(source, **kwargs)).compile()
    except SanyError as error:
        raise CompileError(str(error)) from error

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('-o', '--output', type=Path, required=True)
    parser.add_argument('-I', '--include', type=Path, action='append', default=[])
    args = parser.parse_args()
    try:
        args.output.write_text(compile_file(args.source, includes=args.include))
    except (CompileError, OSError) as error:
        parser.exit(1, f'tla-universal: {error}\n')
