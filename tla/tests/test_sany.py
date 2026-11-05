"""Reference frontend grammar, binding and failure behavior."""
import os
from pathlib import Path
import tempfile
import unittest
from sany import Graph, SanyError, parse_file

JAR = Path(os.environ.get('TLA2TOOLS', '.tools/tla2tools-1.7.4.jar'))

@unittest.skipUnless(JAR.is_file(), 'run tools.py first or set TLA2TOOLS')
class SanyTests(unittest.TestCase):
    def parse(self, source, **dependencies):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Test.tla').write_text(source)
            for name, content in dependencies.items():
                (root / f'{name}.tla').write_text(content)
            return parse_file(root / 'Test.tla', jar=JAR)

    def test_levels_and_bindings(self):
        graph = parse_file(Path('tests/Counter.tla'), jar=JAR)
        self.assertEqual(graph.root.name, 'Counter')
        defs = {n.name: n for n in graph.definitions()}
        self.assertEqual([defs[x].level for x in ('Init', 'Next', 'Spec')], [1, 2, 3])
        self.assertEqual(graph.variables()[0].name, 'x')
        self.assertTrue(graph.operator(defs['Next'].body).name == '=')

    def test_full_source_shapes(self):
        graph = self.parse(r'''---- MODULE Test ----
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N
VARIABLE x
Double(a) == a + a
Domain == {i \\in 1..N : i % 2 = 0}
Mapped == {Double(i) : i \\in Domain}
Func == [i \\in Domain |-> Double(i)]
Record == [a |-> 1, b |-> <<2, 3>>]
Update == [Func EXCEPT ![2] = @ + 1]
Bound == \\A i \\in Domain : i >= 0
Chosen == CHOOSE i \\in Domain : i > 0
Local == LET F(a) == a + 1 IN F(2)
Init == x = <<>>
Next == x' = Append(x, 1)
Spec == Init /\\ [][Next]_x /\\ WF_x(Next)
===='''.replace('\\\\', '\\'))
        names = {n.name for n in graph.definitions()}
        self.assertTrue({'Domain', 'Mapped', 'Func', 'Record', 'Update', 'Bound', 'Chosen', 'Local', 'Spec'} <= names)

    def test_instance_substitution(self):
        graph = self.parse('---- MODULE Test ----\nEXTENDS Integers\nI == INSTANCE Other WITH c <- 2\nAnswer == I!Twice\n====',
            Other='---- MODULE Other ----\nEXTENDS Integers\nCONSTANT c\nTwice == c + c\n====')
        self.assertIn('Answer', {n.name for n in graph.definitions()})

    def test_reject_parse_and_level_errors(self):
        for body in ["VARIABLE x\nBad == x'' = 0", 'Bad == Unknown', 'Bad == (']:
            with self.subTest(body=body), self.assertRaises(SanyError):
                self.parse('---- MODULE Test ----\n' + body + '\n====')

class GraphTests(unittest.TestCase):
    def test_reject_invalid_xml(self):
        for xml in ['garbage', '<modules/>', '<!DOCTYPE modules><modules/>']:
            with self.subTest(xml=xml), self.assertRaises(SanyError):
                Graph.from_xml(xml)
