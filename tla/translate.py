#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Translate the documented integer/action fragment of TLA+ to inspectable Lean."""
import argparse
import re
from pathlib import Path

class TranslationError(ValueError):
    pass

TOKEN = re.compile(r"\s*(<=>|=>|/\\|\\/|/=|<=|>=|\[\]|<>|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[()'=+*<>~,-])")
OPS = {'<=>': (1, '↔'), '=>': (2, '→'), '\\/': (3, '∨'), '/\\': (4, '∧'),
       '=': (5, '='), '/=': (5, '≠'), '<': (5, '<'), '>': (5, '>'),
       '<=': (5, '≤'), '>=': (5, '≥'), '+': (6, '+'), '-': (6, '-'), '*': (7, '*')}

def ident(name):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name):
        raise TranslationError(f'invalid identifier: {name}')
    return '«' + name + '»'

class Expression:
    def __init__(self, source, variables, definitions):
        self.tokens = []
        pos = 0
        while source[pos:].strip():
            match = TOKEN.match(source, pos)
            if not match:
                raise TranslationError(f'unsupported syntax near {source[pos:pos+40]!r}')
            self.tokens.append(match.group(1))
            pos = match.end()
        self.i = 0
        self.variables = variables
        self.definitions = definitions
        self.action = False

    def pop(self):
        if self.i == len(self.tokens):
            raise TranslationError('unexpected end of expression')
        t = self.tokens[self.i]
        self.i += 1
        return t

    def peek(self):
        return self.tokens[self.i] if self.i < len(self.tokens) else None

    def expr(self, precedence=0):
        t = self.pop()
        if t == '(':
            left, typ = self.expr()
            if self.pop() != ')':
                raise TranslationError('expected closing parenthesis')
        elif t in ('~', '-'):
            value, typ = self.expr(8)
            expected = 'Prop' if t == '~' else 'Int'
            if typ != expected:
                raise TranslationError('invalid unary operand')
            left = f'({"¬" if t == "~" else "-"} {value})'
        elif t == 'UNCHANGED':
            name = self.pop()
            if name not in self.variables:
                raise TranslationError('UNCHANGED requires a declared variable')
            self.action = True
            left, typ = f'(t.{ident(name)} = s.{ident(name)})', 'Prop'
        elif t.isdigit():
            left, typ = f'({t} : Int)', 'Int'
        elif t in ('TRUE', 'FALSE'):
            left, typ = ('True' if t == 'TRUE' else 'False'), 'Prop'
        elif t in self.variables:
            primed = self.peek() == "'"
            if primed:
                self.pop()
                self.action = True
            left, typ = f'({"t" if primed else "s"}.{ident(t)})', 'Int'
        elif t in self.definitions:
            kind = self.definitions[t]
            if kind != 'Predicate':
                raise TranslationError('action/temporal references require an explicit action or Spec form')
            left, typ = f'({ident(t)} s)', 'Prop'
        else:
            raise TranslationError(f'unsupported or undeclared name: {t}')
        while self.peek() in OPS and OPS[self.peek()][0] >= precedence:
            op = self.pop()
            rank, target = OPS[op]
            right, rtyp = self.expr(rank + 1)
            expected = 'Prop' if rank < 5 else 'Int'
            if typ != expected or rtyp != expected:
                raise TranslationError(f'{op} requires {expected} operands')
            left = f'({left} {target} {right})'
            typ = 'Int' if rank >= 6 else 'Prop'
        return left, typ

    def parse(self):
        value, typ = self.expr()
        if self.peek() is not None:
            raise TranslationError(f'unconsumed token: {self.peek()}')
        if typ != 'Prop':
            raise TranslationError('a definition must be a predicate or action')
        return value

def translate(source):
    # Nested block comments are stripped without interpreting their contents.
    out, i, depth = [], 0, 0
    while i < len(source):
        pair = source[i:i+2]
        if pair == '(*':
            depth += 1
            i += 2
        elif pair == '*)':
            if depth == 0:
                raise TranslationError('unmatched comment terminator')
            depth -= 1
            out.append(' ')
            i += 2
        elif depth:
            out.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif pair == '\\*':
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise TranslationError('unterminated comment')
    source = ''.join(out)
    m = re.fullmatch(r'\s*-{4,}\s*MODULE\s+(\w+)\s*-{4,}\s*(.*?)\s*={4,}\s*', source, re.S)
    if not m:
        raise TranslationError('expected exactly one MODULE with a closing ====')
    name, body = m.groups()
    variables, definitions, chunks = [], {}, []
    for line in body.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith('EXTENDS '):
            if chunks or any(x.strip() not in ('Integers', 'Naturals') for x in line[8:].split(',')):
                raise TranslationError('only EXTENDS Integers, Naturals is supported')
        elif re.match(r'VARIABLES?\s', line):
            if chunks:
                raise TranslationError('variables must precede definitions')
            vs = re.sub(r'^VARIABLES?\s+', '', line).split(',')
            for v in vs:
                v = v.strip()
                ident(v)
                if v in variables:
                    raise TranslationError('duplicate variable')
                variables.append(v)
        elif re.match(r'\w+\s*==', line):
            chunks.append(line)
        elif chunks:
            chunks[-1] += ' ' + line
        else:
            raise TranslationError(f'unsupported declaration: {line}')
    if not variables or not chunks:
        raise TranslationError('module requires variables and definitions')
    result = ['module', 'import TLA', '', f'namespace {ident(name)}',
              'structure State where']
    result += [f'  {ident(v)} : Int' for v in variables]
    for chunk in chunks:
        name, expression = map(str.strip, chunk.split('==', 1))
        ident(name)
        if name in definitions or name in variables or name == 'State':
            raise TranslationError(f'duplicate or reserved name: {name}')
        spec = re.fullmatch(r'(\w+)\s*/\\\s*\[\]\[(\w+)\]_(\w+|<<.*?>>)', expression)
        if spec:
            init, nxt, frame = spec.groups()
            frames = [v.strip() for v in frame.removeprefix('<<').removesuffix('>>').split(',')]
            if frames != variables:
                raise TranslationError('Spec frame must list every variable in declaration order')
            if definitions.get(init) != 'Predicate' or definitions.get(nxt) != 'Action':
                raise TranslationError('Spec requires an earlier state predicate and action')
            result.append(f'def {ident(name)} : TLA.Formula State := TLA.spec {ident(init)} {ident(nxt)}')
            definitions[name] = 'Formula'
        else:
            parser = Expression(expression, variables, definitions)
            value = parser.parse()
            kind = 'Action' if parser.action else 'Predicate'
            definitions[name] = kind
            result.append(f'def {ident(name)} : TLA.{kind} State := fun s{" t" if parser.action else ""} => {value}')
    result += ['end ' + ident(m.group(1)), '']
    return '\n'.join(result)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('-o', '--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        output = translate(args.source.read_text())
    except (TranslationError, OSError) as error:
        parser.exit(1, f'tla: {error}\n')
    args.output.write_text(output)

if __name__ == '__main__':
    main()
