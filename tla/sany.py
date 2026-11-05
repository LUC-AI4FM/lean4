# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Validated access to the official SANY semantic graph, including resolved UIDs."""
from dataclasses import dataclass
import base64
import os
import re
import tempfile
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET
from tools import DEFAULT_JAR, verify

class SanyError(ValueError):
    pass

@dataclass(frozen=True)
class Symbol:
    uid: str
    node: ET.Element

    @property
    def name(self):
        return self.node.findtext('uniquename', '')

    @property
    def level(self):
        value = self.node.findtext('level')
        return int(value) if value is not None else None

    @property
    def body(self):
        body = self.node.find('body')
        if body is None and self.node.tag in ('AssumeDef', 'TheoremDefNode'):
            expressions = [n for n in self.node if n.tag in ('OpApplNode', 'AssumeProveNode', 'LetInNode', 'SubstInNode', 'APSubstInNode', 'LabelNode')]
            if len(expressions) == 1:
                return expressions[0]
        if body is None or len(body) != 1:
            raise SanyError(f'{self.name}: expected one operator body')
        return body[0]

    @property
    def location(self):
        return self.node.findtext('location/filename', '')

    @property
    def arity(self):
        return int(self.node.findtext('arity', '0'))

class Graph:
    STANDARD_MODULES = {'Naturals', 'Integers', 'Reals', 'Sequences', 'FiniteSets', 'Bags',
                        'TLC', 'Randomization', 'RealTime', 'Toolbox', 'TLAPS', 'Json'}

    def __init__(self, document):
        self.document = document
        self.standard_overrides = set()
        self.symbols = {}
        for entry in document.findall('context/entry'):
            uid = entry.findtext('UID')
            payload = [n for n in entry if n.tag != 'UID']
            if uid is None or uid in self.symbols or len(payload) != 1:
                raise SanyError('malformed or duplicate context entry')
            self.symbols[uid] = Symbol(uid, payload[0])
        root_name = document.findtext('RootModule')
        roots = [n for n in self.symbols.values() if n.node.tag == 'ModuleNode' and n.name == root_name]
        if len(roots) != 1:
            raise SanyError('missing or ambiguous root module')
        self.root = roots[0]
        for node in document.iter():
            if node.tag.endswith('Ref'):
                self.resolve(node)

    @classmethod
    def from_xml(cls, xml):
        if '<!DOCTYPE' in xml or '<!ENTITY' in xml:
            raise SanyError('DTD and entities are not allowed in semantic XML')
        try:
            document = ET.fromstring(xml)
        except ET.ParseError as error:
            raise SanyError(f'invalid semantic XML: {error}') from error
        for string in document.iter('StringValue'):
            if string.get('encoding') == 'base64-utf8':
                try:
                    string.text = base64.b64decode(string.text or '', validate=True).decode('utf-8')
                except (ValueError, UnicodeError) as error:
                    raise SanyError('invalid encoded string payload') from error
        if document.tag != 'modules':
            raise SanyError('expected modules XML document')
        return cls(document)

    def resolve(self, ref):
        uid = ref.findtext('UID')
        if uid not in self.symbols:
            raise SanyError(f'unresolved symbol UID: {uid}')
        symbol = self.symbols[uid]
        expected = 'TheoremDefRef' if symbol.node.tag == 'TheoremDefNode' else symbol.node.tag + 'Ref'
        if ref.tag != expected:
            raise SanyError(f'symbol reference kind mismatch for {uid}')
        return symbol

    def operator(self, application):
        container = application.find('operator')
        if container is None or len(container) != 1:
            raise SanyError('expected exactly one operator reference')
        return self.resolve(container[0])

    def definitions(self, *, include_imported=False):
        standard = self.STANDARD_MODULES - self.standard_overrides
        return [self.resolve(ref) for ref in self.root.node.findall('UserDefinedOpKindRef')
                if self.resolve(ref).location == self.root.name or
                (include_imported and self.resolve(ref).location not in standard)]

    def variables(self):
        return [self.resolve(ref) for ref in self.root.node.findall('OpDeclNodeRef')
                if self.resolve(ref).node.findtext('kind') == '3']

    def claims(self, kind):
        return [self.resolve(ref) for ref in self.root.node.findall(kind + 'Ref')]

    def constants(self):
        return [self.resolve(ref) for ref in self.root.node.findall('OpDeclNodeRef')
                if self.resolve(ref).node.findtext('kind') == '2']

def source_modules(text):
    """Locate concatenated top-level modules, ignoring comments and strings.

    Nested MODULE declarations remain in their enclosing module. This only
    supplies file names to SANY; SANY still parses and validates all syntax.
    """
    masked = list(text)
    i, comment, string = 0, 0, False
    while i < len(text):
        if comment:
            if text.startswith('(*', i):
                masked[i:i+2] = '  '; comment += 1; i += 2
            elif text.startswith('*)', i):
                masked[i:i+2] = '  '; comment -= 1; i += 2
            else:
                if text[i] != '\n': masked[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\':
                masked[i:i+2] = '  '; i += 2
            else:
                if text[i] == '"': string = False
                if text[i] != '\n': masked[i] = ' '
                i += 1
        elif text.startswith('(*', i):
            masked[i:i+2] = '  '; comment = 1; i += 2
        elif text.startswith('\\*', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            masked[i:end] = ' ' * (end - i); i = end
        elif text[i] == '"':
            masked[i] = ' '; string = True; i += 1
        else:
            i += 1
    tokens = re.finditer(r'(?m)^[ \t]*(?:-{4,}[ \t]*MODULE[ \t]+([A-Za-z_][A-Za-z_0-9]*)\b[^\n]*|={4,}[ \t]*$)', ''.join(masked))
    depth, start, name, modules = 0, 0, None, []
    for token in tokens:
        if token[1]:
            if depth == 0: start, name = token.start(), token[1]
            depth += 1
        elif depth:
            depth -= 1
            if depth == 0:
                modules.append((name, '\n' * text.count('\n', 0, start) + text[start:token.end()] + '\n'))
    return modules


def parse_file(source, *, jar=None, includes=(), timeout=30):
    source = Path(source).resolve(strict=True)
    modules = source_modules(source.read_text())
    if len(modules) <= 1:
        return _parse_file(source, jar=jar, includes=includes, timeout=timeout)
    names = [name for name, _ in modules]
    if len(names) != len(set(names)):
        raise SanyError('duplicate top-level module names in source file')
    with tempfile.TemporaryDirectory(prefix='tla-source-modules-') as directory:
        for name, content in modules:
            (Path(directory) / (name + '.tla')).write_text(content)
        return _parse_file(source, jar=jar, includes=[*includes, directory], timeout=timeout)


def _parse_file(source, *, jar=None, includes=(), timeout=30):
    source = Path(source).resolve(strict=True)
    jar = Path(jar or os.environ.get('TLA2TOOLS', DEFAULT_JAR)).resolve()
    if not jar.is_file():
        raise SanyError('reference tools missing; run python3 tools.py or set TLA2TOOLS')
    try:
        verify(jar)
    except ValueError as error:
        raise SanyError(str(error)) from error
    # Local modules may legally reuse standard names. Never apply trusted
    # standard-module overrides to their user-defined operator bodies.
    overrides = {name for directory in [source.parent, *includes]
                 for name in Graph.STANDARD_MODULES
                 if (Path(directory) / (name + '.tla')).exists()}
    command = ['java', '-Xmx512m', '-cp', str(jar), 'tla2sany.xml.XMLExporter', '-o']
    for directory in [source.parent, *includes]:
        command.extend(['-I', str(Path(directory).resolve())])
    command.append(str(source))
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout, cwd=source.parent)
        if result.returncode and 'An invalid XML character' in result.stderr:
            adapter = Path(__file__).parent / 'java' / 'SemanticExport.java'
            fallback = ['java', '-Xmx512m', '-cp', str(jar), str(adapter), str(source),
                        str(source.parent), *(str(Path(p).resolve()) for p in includes)]
            result = subprocess.run(fallback, capture_output=True, text=True, timeout=timeout, cwd=source.parent)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise SanyError(f'reference parser failed: {error}') from error
    # The pinned exporter can exit zero and emit XML after a level error.
    failed = any(marker in result.stderr for marker in ('*** Errors:', '*** Abort messages:'))
    if result.returncode or failed or not result.stdout.lstrip().startswith('<?xml'):
        diagnostics = (result.stderr + ('' if result.stdout.lstrip().startswith('<?xml') else result.stdout)).strip()
        raise SanyError(f'SANY rejected {source.name}:\n{diagnostics}')
    graph = Graph.from_xml(result.stdout)
    # SANY's stock XML omits parameters of theorem/assumption definitions.
    # Ask the lossless adapter when an application needs those bindings.
    missing_parameters = any(
        app.find('operands') is not None and len(app.find('operands')) > 0 and
        any(ref.tag in ('TheoremDefRef', 'AssumeDefRef') and
            graph.resolve(ref).node.find('params') is None for ref in app.find('operator'))
        for app in graph.document.iter('OpApplNode'))
    if missing_parameters:
        adapter = Path(__file__).parent / 'java' / 'SemanticExport.java'
        fallback = ['java', '-Xmx512m', '-cp', str(jar), str(adapter), str(source),
                    str(source.parent), *(str(Path(p).resolve()) for p in includes)]
        try:
            result = subprocess.run(fallback, capture_output=True, text=True, timeout=timeout, cwd=source.parent)
        except (OSError, subprocess.TimeoutExpired) as error:
            raise SanyError(f'reference adapter failed: {error}') from error
        if result.returncode:
            raise SanyError(f'SANY adapter rejected {source.name}:\n{result.stderr}')
        graph = Graph.from_xml(result.stdout)
    graph.standard_overrides = overrides
    return graph
