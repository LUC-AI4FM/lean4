import unittest
from translate import translate, TranslationError
from pathlib import Path

class TranslationTests(unittest.TestCase):
    def test_counter(self):
        result = translate(Path('tests/Counter.tla').read_text())
        self.assertIn('namespace «Counter»', result)
        self.assertIn('TLA.spec «Init» «Next»', result)
        self.assertIn('(t.«x»)', result)
    def test_reject_unsupported(self):
        for expression in ['CHOOSE y : y = x', 'x \\in Nat', 'LET y == 1 IN y = x', 'Missing', 'x / 0 = 1']:
            with self.subTest(expression=expression), self.assertRaises(TranslationError):
                translate('---- MODULE Bad ----\nVARIABLE x\nInit == ' + expression + '\n====')
    def test_reject_temporal_misuse(self):
        with self.assertRaises(TranslationError):
            translate("---- MODULE Bad ----\nVARIABLE x\nNext == x' = x\nInit == Next\n====")
    def test_reject_trailing_input(self):
        with self.assertRaises(TranslationError):
            translate('---- MODULE Bad ----\nVARIABLE x\nInit == x = 0 garbage\n====')

    def test_comments_and_multiline(self):
        source = Path('tests/Counter.tla').read_text()
        source = source.replace('Init == x = 0', 'Init == (* outer (* inner *) *)\n x = 0 \\* comment')
        self.assertEqual(translate(source), translate(Path('tests/Counter.tla').read_text()))

    def test_reject_declarations_and_bad_frames(self):
        base = Path('tests/Counter.tla').read_text()
        cases = [base.replace('EXTENDS Integers', 'EXTENDS Sequences'),
                 base.replace('VARIABLE x', 'VARIABLE x, x'),
                 base.replace('VARIABLE x', 'CONSTANT x'),
                 base.replace('[Next]_x', '[Next]_other'),
                 base.replace('Next ==', 'Init =='),
                 base.replace('====', '==== trailing'),
                 base + '(* unterminated',
                 base.replace('x = 0', 'x + TRUE = 0')]
        for source in cases:
            with self.subTest(source=source), self.assertRaises(TranslationError):
                translate(source)

    def test_multiple_variables(self):
        result = translate("---- MODULE Pair ----\nVARIABLES x, y\nInit == (x = 0) /\\ (y = 0)\nNext == (x' = x + 1) /\\ UNCHANGED y\nSpec == Init /\\ [][Next]_<<x, y>>\n====")
        self.assertIn('t.«y» = s.«y»', result)
        self.assertIn('TLA.spec', result)

if __name__ == '__main__':
    unittest.main()
