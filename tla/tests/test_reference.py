"""One-state differential checks against pinned TLC; never a proof substitute."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from tools import DEFAULT_JAR, verify

class ReferenceTests(unittest.TestCase):
    def check_records(self, invariant):
        verify(DEFAULT_JAR)
        source = Path('tests/fixtures/Records.tla').read_text().replace(
            '====', 'VARIABLE tick\nInit == tick = 0\nNext == tick\' = tick\nChecks == ' + invariant + '\n====')
        with tempfile.TemporaryDirectory(prefix='tla-reference-') as directory:
            root = Path(directory)
            (root / 'Records.tla').write_text(source)
            (root / 'Records.cfg').write_text('INIT Init\nNEXT Next\nINVARIANT Checks\nCHECK_DEADLOCK FALSE\n')
            return subprocess.run(['java', '-XX:+UseParallelGC', '-Xmx256m', '-cp', str(DEFAULT_JAR), 'tlc2.TLC',
                                   '-workers', '1', '-seed', '1', '-config', 'Records.cfg', 'Records.tla'],
                                  cwd=root, capture_output=True, text=True, timeout=30)

    def test_reference_agrees_with_lean_record_proofs(self):
        result = self.check_records('Good /\\ Included /\\ UpdateGood')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('No error has been found', result.stdout)

    def test_reference_rejects_negated_property(self):
        result = self.check_records('~Good')
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue('Invariant Checks is violated' in result.stdout or 'invariant of Checks is equal to FALSE' in result.stdout, result.stdout + result.stderr)
