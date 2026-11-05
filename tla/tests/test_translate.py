"""CLI/API failures leave no misleading output; source names remain bound."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from translate import translate, TranslationError, compile_file

class TranslationTests(unittest.TestCase):
    def test_counter(self):
        result = translate(Path('tests/Counter.tla').read_text())
        self.assertIn('import TLAUniversal', result)
        self.assertIn('namespace «Counter»', result)
        self.assertIn('def «Spec»', result)
        self.assertNotIn('sorry', result)

    def test_inherited_user_operator_is_exported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Base.tla').write_text('---- MODULE Base ----\nAnswer == 42\n====')
            (root / 'Derived.tla').write_text('---- MODULE Derived ----\nEXTENDS Base\n====')
            self.assertIn('def «Answer»', compile_file(root / 'Derived.tla'))

    def test_standard_library_source_definitions(self):
        result = translate(Path('tests/fixtures/StandardLibrary.tla').read_text())
        self.assertIn('def «Selected»', result)
        self.assertIn('def «Joined»', result)

    def test_typed_backend_is_explicit(self):
        result = translate(Path('tests/Counter.tla').read_text(), backend='typed')
        self.assertIn('import TLA\n', result)
        self.assertNotIn('import TLAUniversal', result)

    def test_mixed_source_uses_universal_values(self):
        result = translate(Path('tests/fixtures/Universal.tla').read_text())
        self.assertIn('Value', result)
        self.assertIn('def «Mixed»', result)

    def test_reject_undeclared_and_invalid_levels(self):
        for expression in ['Missing', "x'' = 0", 'x = 0 garbage']:
            with self.subTest(expression=expression), self.assertRaises(TranslationError):
                translate('---- MODULE Bad ----\nVARIABLE x\nInit == ' + expression + '\n====')

    def test_comments_preserve_meaning(self):
        source = Path('tests/Counter.tla').read_text()
        source = source.replace('Init == x = 0', 'Init == (* outer (* inner *) *)\n x = 0 \\* comment')
        self.assertEqual(translate(source), translate(Path('tests/Counter.tla').read_text()))

    def test_failed_cli_preserves_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            source, target = Path(directory) / 'Bad.tla', Path(directory) / 'Bad.lean'
            source.write_text('---- MODULE Bad ----\nA == Missing\n====')
            target.write_text('existing')
            result = subprocess.run([sys.executable, 'translate.py', str(source), '-o', str(target)],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(target.read_text(), 'existing')
            self.assertIn('SANY rejected', result.stderr)

    def test_standard_module_shadowing_rejected(self):
        with self.assertRaises(TranslationError):
            translate('---- MODULE Integers ----\nFake == TRUE\n====')
