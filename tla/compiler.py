# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Compile resolved SANY expressions to Lean; reject every unmapped construct."""
from dataclasses import dataclass
import json
import xml.etree.ElementTree as ET
from pathlib import Path
from sany import parse_file, SanyError

class CompileError(ValueError):
    pass

class Ty:
    def __init__(self, name=None, *args):
        self.name, self.args, self.link = name, args, None
    def root(self):
        if self.link is not None:
            self.link = self.link.root()
            return self.link
        return self
    def contains(self, other):
        r = self.root()
        return r is other or any(a.contains(other) for a in r.args)
    def unify(self, other):
        a, b = self.root(), other.root()
        if a is b:
            return
        if a.name is None:
            if b.contains(a):
                raise CompileError('recursive type constraint')
            a.link = b
        elif b.name is None:
            b.unify(a)
        elif a.name != b.name or len(a.args) != len(b.args):
            raise CompileError(f'incompatible value types: {a.name} and {b.name}')
        else:
            for x, y in zip(a.args, b.args):
                x.unify(y)
    def lean(self):
        r = self.root()
        if r.name is None:
            raise CompileError('unconstrained value type: universal value semantics are not implemented yet')
        names = {'Set': 'TLA.Data.Set', 'Function': 'TLA.Data.Function', 'Seq': 'List'}
        name = names.get(r.name, r.name)
        if r.name.startswith('Record:'):
            name = ident('TLARecord_' + r.name[7:].replace(',', '_'))
        return '(' + ' '.join([name, *(a.lean() for a in r.args)]) + ')' if r.args else name

INT, PROP, STRING = Ty('Int'), Ty('Prop'), Ty('String')

def ident(name):
    if any(c in name for c in ('«', '»', '\n', '\r')):
        raise CompileError('invalid Lean identifier')
    return f'«{name}»'

@dataclass
class Term:
    code: str
    ty: Ty

@dataclass
class Bound:
    term: Term

@dataclass
class Closure:
    node: object
    env: dict

class Compiler:
    def __init__(self, graph):
        self.g = graph
        self.vars = {x.uid: Ty() for x in graph.variables()}
        self.consts = {x.uid: Ty() for x in graph.constants()}
        self.counter = 0
        self.active = []
        self.types = []

    def fresh(self):
        self.counter += 1
        return f'v{self.counter}'

    def select(self, value, key):
        root = value.ty.root()
        if root.name and root.name.startswith('Record:'):
            key.ty.unify(STRING)
            try:
                field = json.loads(key.code)
                index = root.name[7:].split(',').index(field)
            except (ValueError, TypeError):
                raise CompileError('record selection requires a known field name')
            return Term(f'({value.code}).{ident(field)}', root.args[index])
        if root.name == 'Seq':
            key.ty.unify(INT)
            return Term(f'(TLA.Data.Seq.get {value.code} {key.code})', root.args[0])
        result = Ty()
        value.ty.unify(Ty('Function', key.ty, result))
        return Term(f'(TLA.Data.Function.apply {value.code} {key.code})', result)

    def update(self, value, keys, replacement):
        if not keys:
            value.ty.unify(replacement.ty)
            return replacement
        key, *rest = keys
        selected = self.select(value, key)
        changed = self.update(selected, rest, replacement)
        root = value.ty.root()
        if root.name.startswith('Record:'):
            field = json.loads(key.code)
            return Term(f'({{ {value.code} with {ident(field)} := {changed.code} }})', value.ty)
        fn = 'Seq.update' if root.name == 'Seq' else 'Function.update'
        return Term(f'(TLA.Data.{fn} {value.code} {key.code} {changed.code})', value.ty)

    def term(self, node, env=None, b='b', n='n'):
        result = self._term(node, env, b, n)
        self.types.append(result.ty)
        return result

    def _term(self, node, env=None, b='b', n='n'):
        env = {} if env is None else env
        if node.tag == 'NumeralNode':
            value = node.findtext('IntValue') or node.findtext('BigIntValue')
            if value is None or not value.lstrip('-').isdigit():
                raise CompileError('invalid integer literal')
            return Term(f'({value} : Int)', INT)
        if node.tag == 'StringNode':
            return Term(json.dumps(node.findtext('StringValue', ''), ensure_ascii=False), STRING)
        if node.tag == 'AtNode':
            parts = [x for x in node if x.tag not in ('location', 'level')]
            if len(parts) != 2:
                raise CompileError('malformed EXCEPT @ expression')
            current = env.get('@except')
            value = current.term if current is not None else self.term(parts[0], env, b, n)
            for selector in parts[1].find('operands'):
                value = self.select(value, self.term(selector, env, b, n))
            return value
        if node.tag == 'SubstInNode':
            extended = dict(env)
            for subst in node.findall('substs/Subst'):
                parts = [x for x in subst if x.tag not in ('location', 'level')]
                if len(parts) != 2 or not parts[0].tag.endswith('Ref'):
                    raise CompileError('malformed module substitution')
                extended[parts[0].findtext('UID')] = Closure(parts[1], env)
            return self.term(node.find('body')[0], extended, b, n)
        if node.tag == 'LetInNode':
            return self.term(node.find('body')[0], env, b, n)
        if node.tag != 'OpApplNode':
            raise CompileError(f'unimplemented semantic node: {node.tag}')
        op = self.g.operator(node)
        args = list(node.find('operands'))
        name = op.name
        if op.uid in env:
            value = env[op.uid]
            if args:
                raise CompileError('operator-valued parameters are not implemented')
            if isinstance(value, Bound):
                return value.term
            return self.term(value.node, value.env, b, n)
        if op.uid in self.vars:
            if args:
                raise CompileError('variable cannot take operator arguments')
            return Term(f'(({b}) ({n})).{ident(name)}', self.vars[op.uid])
        if op.uid in self.consts:
            if args or op.arity:
                raise CompileError('operator-valued constants are not implemented')
            return Term(f'c.{ident(name)}', self.consts[op.uid])
        origin = op.location
        original = op.node.find('body')
        if original is not None and len(original) == 1 and original[0].tag == 'SubstInNode':
            original_body = original[0].find('body')
            if original_body is not None and len(original_body) == 1:
                origin = original_body[0].findtext('location/filename', origin)
        standard = origin in ('Naturals', 'Integers', 'Sequences', 'FiniteSets')
        if standard:
            name = name.rsplit('!', 1)[-1]
        builtin = op.node.tag == 'BuiltInKind'
        if not builtin and not standard:
            if op.node.tag != 'UserDefinedOpKind':
                raise CompileError(f'unsupported symbol: {name}')
            if op.uid in self.active:
                raise CompileError(f'recursive operator requires fixed-point semantics: {name}')
            params = list(op.node.findall('params/leibnizparam/FormalParamNodeRef'))
            if len(params) != len(args):
                raise CompileError(f'arity mismatch for {name}')
            extended = dict(env)
            for parameter, argument in zip(params, args):
                extended[parameter.findtext('UID')] = Closure(argument, env)
            self.active.append(op.uid)
            try:
                return self.term(op.body, extended, b, n)
            finally:
                self.active.pop()
        if name == "'":
            return self.term(args[0], env, b, f'({n}) + 1')
        if name in ('[]', '<>'):
            k = self.fresh()
            value = self.term(args[0], env, b, k)
            value.ty.unify(PROP)
            text = f'∀ {k} : Nat, ({n}) ≤ {k} → {value.code}' if name == '[]' else f'∃ {k} : Nat, ({n}) ≤ {k} ∧ {value.code}'
            return Term(f'({text})', PROP)
        if name in ('UNCHANGED', '$SquareAct', '$AngleAct'):
            frame = args[0] if name == 'UNCHANGED' else args[1]
            left = self.term(frame, env, b, n)
            right = self.term(frame, env, b, f'({n}) + 1')
            left.ty.unify(right.ty)
            same = f'({right.code} = {left.code})'
            if name == 'UNCHANGED':
                return Term(same, PROP)
            action = self.term(args[0], env, b, n)
            action.ty.unify(PROP)
            return Term(f'({action.code} {"∨" if name == "$SquareAct" else "∧ ¬"} {same})', PROP)
        if name == 'ENABLED':
            nxt, k = self.fresh(), self.fresh()
            trace = f'(fun {k} => if {k} = ({n}) + 1 then {nxt} else ({b}) {k})'
            value = self.term(args[0], env, trace, n)
            value.ty.unify(PROP)
            return Term(f'(∃ {nxt} : State, {value.code})', PROP)
        if name in ('$WF', '$SF'):
            # SANY's fairness operands are frame first, action second.
            s, t, k = self.fresh(), self.fresh(), self.fresh()
            trace = f'(fun {k} => if {k} = 0 then {s} else {t})'
            frame = self.term(args[0], env, f'(fun _ => {s})', '0')
            act = self.term(args[1], env, trace, '0')
            act.ty.unify(PROP)
            fn = 'weakFairness' if name == '$WF' else 'strongFairness'
            return Term(f'(TLA.{fn} (fun {s} {t} => {act.code}) (fun {s} => {frame.code}) ({b}) ({n}))', PROP)
        if name in ('$BoundedForall', '$BoundedExists', '$SetOfAll'):
            bounds = node.findall('boundSymbols/bound')
            bindings = []
            extended = dict(env)
            for bound in bounds:
                refs = bound.findall('FormalParamNodeRef')
                domains = [x for x in bound if x.tag != 'FormalParamNodeRef']
                if len(domains) != 1:
                    raise CompileError('tuple-pattern binders require universal value semantics')
                domain = self.term(domains[0], extended, b, n)
                element = Ty(); domain.ty.unify(Ty('Set', element))
                for ref in refs:
                    v = self.fresh()
                    bindings.append((v, domain))
                    extended[ref.findtext('UID')] = Bound(Term(v, element))
            if not bindings:
                raise CompileError('missing bounded variables')
            body = self.term(args[0], extended, b, n)
            if name == '$SetOfAll':
                result = self.fresh()
                code = f'{body.code} = {result}'
            else:
                body.ty.unify(PROP)
                code = body.code
            for v, domain in reversed(bindings):
                if name == '$BoundedForall':
                    code = f'(∀ {v}, ({domain.code}) {v} → {code})'
                else:
                    code = f'(∃ {v}, ({domain.code}) {v} ∧ {code})'
            if name == '$SetOfAll':
                return Term(f'(fun {result} => {code})', Ty('Set', body.ty))
            return Term(code, PROP)
        if name in ('$BoundedForall', '$BoundedExists', '$BoundedChoose', '$SubsetOf', '$SetOfAll', '$FcnConstructor'):
            bounds = node.findall('boundSymbols/bound')
            if len(bounds) != 1:
                raise CompileError('multiple binding groups are not implemented yet')
            refs = bounds[0].findall('FormalParamNodeRef')
            domains = [x for x in bounds[0] if x.tag != 'FormalParamNodeRef']
            if len(refs) != 1 or len(domains) != 1:
                raise CompileError('tuple and multiple binders are not implemented yet')
            domain = self.term(domains[0], env, b, n)
            element = Ty()
            domain.ty.unify(Ty('Set', element))
            v = self.fresh()
            extended = dict(env)
            extended[refs[0].findtext('UID')] = Bound(Term(v, element))
            body = self.term(args[0], extended, b, n)
            if name in ('$BoundedForall', '$BoundedExists', '$BoundedChoose', '$SubsetOf'):
                body.ty.unify(PROP)
            if name == '$BoundedForall':
                return Term(f'(∀ {v}, ({domain.code}) {v} → {body.code})', PROP)
            if name == '$BoundedExists':
                return Term(f'(∃ {v}, ({domain.code}) {v} ∧ {body.code})', PROP)
            if name == '$BoundedChoose':
                return Term(f'(TLA.Data.Set.choose (fun {v} => ({domain.code}) {v} ∧ {body.code}))', element)
            if name == '$SubsetOf':
                return Term(f'(TLA.Data.Set.filter {domain.code} (fun {v} => {body.code}))', Ty('Set', element))
            if name == '$SetOfAll':
                return Term(f'(TLA.Data.Set.image {domain.code} (fun {v} => {body.code}))', Ty('Set', body.ty))
            return Term(f'(TLA.Data.Function.make {domain.code} (fun {v} => {body.code}))', Ty('Function', element, body.ty))
        if name in ('$RcdConstructor', '$SetOfRcds'):
            fields = {}
            for pair in args:
                parts = list(pair.find('operands'))
                if len(parts) != 2 or parts[0].tag != 'StringNode':
                    raise CompileError('malformed record field')
                label = parts[0].findtext('StringValue')
                if label in fields:
                    raise CompileError('duplicate record field')
                fields[label] = self.term(parts[1], env, b, n)
            labels = sorted(fields)
            types = []
            for label in labels:
                ty = fields[label].ty
                if name == '$SetOfRcds':
                    element = Ty(); ty.unify(Ty('Set', element)); ty = element
                types.append(ty)
            record_type = Ty('Record:' + ','.join(labels), *types)
            record_name = ident('TLARecord_' + '_'.join(labels))
            if name == '$RcdConstructor':
                body = ', '.join(f'{ident(label)} := {fields[label].code}' for label in labels)
                placeholders = ' '.join('_' for _ in labels)
                return Term(f'({{ {body} }} : {record_name} {placeholders})', record_type)
            v = self.fresh()
            body = ' ∧ '.join(f'({fields[label].code}) {v}.{ident(label)}' for label in labels) or 'True'
            placeholders = ' '.join('_' for _ in labels)
            return Term(f'(fun ({v} : {record_name} {placeholders}) => {body})', Ty('Set', record_type))
        if name == '$Except':
            value = self.term(args[0], env, b, n)
            for pair in args[1:]:
                parts = list(pair.find('operands'))
                keys = [self.term(key, env, b, n) for key in parts[0].find('operands')]
                updated_env = dict(env)
                updated_env['@except'] = Bound(value)
                replacement = self.term(parts[1], updated_env, b, n)
                value = self.update(value, keys, replacement)
            return value
        values = [self.term(arg, env, b, n) for arg in args]
        codes = [v.code for v in values]
        def binary(result, expected=None):
            if len(values) != 2:
                raise CompileError(f'expected two operands for {name}')
            values[0].ty.unify(values[1].ty)
            if expected is not None:
                values[0].ty.unify(expected)
            return Term(f'({codes[0]} {result} {codes[1]})', PROP if expected is PROP or name in ('=', '/=', '<', '>', '<=', '>=', '\\leq', '\\geq') else INT)
        if name in ('TRUE', 'FALSE'):
            return Term('True' if name == 'TRUE' else 'False', PROP)
        if name in ('=', '/='):
            return binary('=' if name == '=' else '≠')
        if name in ('+', '-', '*', '%', '\\div', '^'):
            if name == '^':
                for v in values: v.ty.unify(INT)
                return Term(f'({codes[0]} ^ Int.toNat {codes[1]})', INT)
            return binary({'\\div': '/'}.get(name, name), INT)
        if name in ('<', '>', '<=', '>=', '\\leq', '\\geq'):
            return binary({'\\leq': '≤', '\\geq': '≥'}.get(name, name), INT)
        if name in ('\\land', '\\lor', '=>', '\\equiv'):
            return binary({'\\land': '∧', '\\lor': '∨', '=>': '→', '\\equiv': '↔'}[name], PROP)
        if name in ('$ConjList', '$DisjList'):
            for v in values: v.ty.unify(PROP)
            return Term('(' + (' ∧ ' if name == '$ConjList' else ' ∨ ').join(codes) + ')', PROP)
        if name in ('\\lnot', '-.'):
            values[0].ty.unify(PROP if name == '\\lnot' else INT)
            prefix = "¬" if name == "\\lnot" else "-"
            return Term(f'({prefix} {codes[0]})', values[0].ty)
        if name == '$IfThenElse':
            values[0].ty.unify(PROP)
            values[1].ty.unify(values[2].ty)
            return Term(f'(if {codes[0]} then {codes[1]} else {codes[2]})', values[1].ty)
        if name in ('Nat', 'Int') and standard:
            return Term('TLA.Data.Set.' + ('naturals' if name == 'Nat' else 'integers'), Ty('Set', INT))
        if name == '..':
            for v in values: v.ty.unify(INT)
            return Term(f'(TLA.Data.Set.interval {codes[0]} {codes[1]})', Ty('Set', INT))
        if name in ('\\in', '\\notin'):
            values[1].ty.unify(Ty('Set', values[0].ty))
            prefix = "¬ " if name == "\\notin" else ""
            return Term(f'({prefix}({codes[1]}) {codes[0]})', PROP)
        if name in ('\\cup', '\\cap', '\\setminus', '\\subseteq'):
            element = Ty()
            for v in values: v.ty.unify(Ty('Set', element))
            fn = {'\\cup': 'union', '\\cap': 'inter', '\\setminus': 'diff', '\\subseteq': 'subset'}[name]
            return Term(f'(TLA.Data.Set.{fn} {codes[0]} {codes[1]})', PROP if name == '\\subseteq' else values[0].ty)
        if name == '$SetEnumerate':
            element = Ty()
            for v in values: v.ty.unify(element)
            return Term(f'(TLA.Data.Set.enumerate [{", ".join(codes)}])', Ty('Set', element))
        if name == '$Tuple':
            element = Ty()
            for v in values: v.ty.unify(element)
            return Term(f'[{", ".join(codes)}]', Ty('Seq', element))
        if name == 'SUBSET':
            element = Ty()
            values[0].ty.unify(Ty('Set', element))
            return Term(f'(TLA.Data.Set.power {codes[0]})', Ty('Set', Ty('Set', element)))
        if name == 'UNION':
            element = Ty()
            values[0].ty.unify(Ty('Set', Ty('Set', element)))
            return Term(f'(TLA.Data.Set.bigUnion {codes[0]})', Ty('Set', element))
        if name == '$SetOfFcns':
            a, z = Ty(), Ty()
            values[0].ty.unify(Ty('Set', a)); values[1].ty.unify(Ty('Set', z))
            return Term(f'(TLA.Data.Function.space {codes[0]} {codes[1]})', Ty('Set', Ty('Function', a, z)))
        if name in ('$FcnApply', '$RcdSelect'):
            return self.select(values[0], values[1])
        if name == 'DOMAIN':
            root = values[0].ty.root()
            if root.name == 'Seq':
                return Term(f'(TLA.Data.Set.interval 1 (TLA.Data.Seq.len {codes[0]}))', Ty('Set', INT))
            if root.name and root.name.startswith('Record:'):
                fields = ', '.join(json.dumps(label) for label in root.name[7:].split(','))
                return Term(f'(TLA.Data.Set.enumerate [{fields}])', Ty('Set', STRING))
            a, z = Ty(), Ty()
            values[0].ty.unify(Ty('Function', a, z))
            return Term(f'({codes[0]}).domain', Ty('Set', a))
        if name in ('Len', 'Append', 'Head', 'Tail', 'SubSeq', '\\o') and standard:
            element = Ty()
            values[0].ty.unify(Ty('Seq', element))
            if name == 'Len': return Term(f'(TLA.Data.Seq.len {codes[0]})', INT)
            if name == 'Head': return Term(f'(TLA.Data.Seq.get {codes[0]} 1)', element)
            if name == 'Tail': return Term(f'({codes[0]}).drop 1', values[0].ty)
            if name == 'Append':
                values[1].ty.unify(element)
                return Term(f'({codes[0]} ++ [{codes[1]}])', values[0].ty)
            if name == '\\o':
                values[1].ty.unify(values[0].ty)
                return Term(f'({codes[0]} ++ {codes[1]})', values[0].ty)
            values[1].ty.unify(INT); values[2].ty.unify(INT)
            return Term(f'(TLA.Data.Seq.subseq {codes[0]} {codes[1]} {codes[2]})', values[0].ty)
        if name == 'Seq' and standard:
            element = Ty(); values[0].ty.unify(Ty('Set', element))
            return Term(f'(TLA.Data.Seq.space {codes[0]})', Ty('Set', Ty('Seq', element)))
        raise CompileError(f'unsupported resolved operator {name!r} from {op.location}')

    def compile(self):
        for ref in self.g.root.node:
            if ref.tag in ('AssumeNodeRef', 'TheoremNodeRef'):
                raise CompileError('proof/assumption declarations require the pending obligation pipeline')
        reserved = {'State', 'Constants'}
        if any(d.name in reserved for d in self.g.definitions()):
            raise CompileError('source name collides with generated State or Constants type')
        rendered = []
        for definition in self.g.definitions():
            if definition.arity:
                # Parameterized definitions are expanded at each resolved application.
                continue
            call = ET.Element('OpApplNode')
            operator = ET.SubElement(call, 'operator')
            ref = ET.SubElement(operator, definition.node.tag + 'Ref')
            ET.SubElement(ref, 'UID').text = definition.uid
            ET.SubElement(call, 'operands')
            value = self.term(call)
            rendered.append((definition, value))
        free = []
        records = {}
        def collect(ty):
            root = ty.root()
            if root.name and root.name.startswith('Record:'):
                records[root.name] = root.name[7:].split(',')
            if root.name is None and root not in free:
                free.append(root)
            for arg in root.args:
                collect(arg)
        for ty in [*self.vars.values(), *self.consts.values(), *self.types]:
            collect(ty)
        for i, ty in enumerate(free):
            ty.name = f'TLAValue{i}'
        parameters = ' '.join(ty.name for ty in free)
        binders = ' '.join(f'({ty.name} : Type)' for ty in free)
        state_type = f'(State {parameters})' if free else 'State'
        constants_type = f'(Constants {parameters})' if free else 'Constants'
        lines = ['/- Generated from the SANY semantic graph; inspect before proving source claims. -/',
                 'module', 'import TLA', '', f'namespace {ident(self.g.root.name)}',
                 'noncomputable section', 'open Classical']
        for labels in records.values():
            name = ident('TLARecord_' + '_'.join(labels))
            params = ' '.join(f'(A{i} : Type)' for i in range(len(labels)))
            lines += [f'structure {name} {params} where']
            lines += [f'  {ident(label)} : A{i}' for i, label in enumerate(labels)]
            lines += ['  deriving Inhabited']
        lines += [f'structure Constants {binders} where']
        lines += [f'  {ident(self.g.symbols[uid].name)} : {ty.lean()}' for uid, ty in self.consts.items()]
        lines += [f'structure State {binders} where']
        lines += [f'  {ident(self.g.symbols[uid].name)} : {ty.lean()}' for uid, ty in self.vars.items()]
        for ty in free:
            lines += [f'variable {{{ty.name} : Type}} [Inhabited {ty.name}]']
        for definition, term in rendered:
            context_name = 'c' if 'c.' in term.code else '_c'
            trace_name = 'b' if '(b)' in term.code else '_b'
            index_name = 'n' if '(n)' in term.code else '_n'
            code = term.code.replace(': State,', f': {state_type},')
            lines += [f'def {ident(definition.name)} ({context_name} : {constants_type}) ({trace_name} : TLA.Behavior {state_type}) ({index_name} : Nat) : {term.ty.lean()} :=',
                      '  ' + code]
        lines += ['end', f'end {ident(self.g.root.name)}', '']
        return '\n'.join(lines)

def compile_file(path, **kwargs):
    try:
        return Compiler(parse_file(path, **kwargs)).compile()
    except SanyError as error:
        raise CompileError(str(error)) from error
