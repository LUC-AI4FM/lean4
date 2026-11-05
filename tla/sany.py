# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Validated access to the official SANY semantic graph, including resolved UIDs."""
from dataclasses import dataclass
import base64
import os
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
            expressions = [n for n in self.node if n.tag in ('OpApplNode', 'AssumeProveNode', 'LetInNode')]
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
    def __init__(self, document):
        self.document = document
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

    def definitions(self):
        return [self.resolve(ref) for ref in self.root.node.findall('UserDefinedOpKindRef')
                if self.resolve(ref).location == self.root.name]

    def variables(self):
        return [self.resolve(ref) for ref in self.root.node.findall('OpDeclNodeRef')
                if self.resolve(ref).node.findtext('kind') == '3']

    def claims(self, kind):
        return [self.resolve(ref) for ref in self.root.node.findall(kind + 'Ref')]

    def constants(self):
        return [self.resolve(ref) for ref in self.root.node.findall('OpDeclNodeRef')
                if self.resolve(ref).node.findtext('kind') == '2']

def parse_file(source, *, jar=None, includes=(), timeout=30):
    source = Path(source).resolve(strict=True)
    jar = Path(jar or os.environ.get('TLA2TOOLS', DEFAULT_JAR)).resolve()
    if not jar.is_file():
        raise SanyError('reference tools missing; run python3 tools.py or set TLA2TOOLS')
    try:
        verify(jar)
    except ValueError as error:
        raise SanyError(str(error)) from error
    standard_names = ('Naturals', 'Integers', 'Reals', 'Sequences', 'FiniteSets')
    for directory in [source.parent, *includes]:
        for name in standard_names:
            if (Path(directory) / (name + '.tla')).exists():
                raise SanyError(f'local module shadows trusted standard module {name}')
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
    failed = any(marker in result.stderr for marker in ('Semantic errors:', '*** Errors:', '*** Abort messages:'))
    if result.returncode or failed or not result.stdout.lstrip().startswith('<?xml'):
        diagnostics = (result.stderr + ('' if result.stdout.lstrip().startswith('<?xml') else result.stdout)).strip()
        raise SanyError(f'SANY rejected {source.name}:\n{diagnostics}')
    return Graph.from_xml(result.stdout)
