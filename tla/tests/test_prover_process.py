"""A timeout must also stop descendants of the Lake launcher."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from prover_process import run_prover


class ProverProcessTests(unittest.TestCase):
    def test_preserves_output_and_return_code(self):
        result = run_prover([sys.executable, '-c',
                            'import sys; print("out"); print("err", file=sys.stderr); sys.exit(3)'],
                           cwd=None, timeout=5)
        self.assertEqual((result.returncode, result.stdout, result.stderr), (3, 'out\n', 'err\n'))

    @unittest.skipUnless(os.name == 'posix', 'process-group cleanup is POSIX-specific')
    def test_timeout_kills_launcher_children(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'orphan-ran'
            child = 'import time,pathlib; time.sleep(0.8); pathlib.Path(%r).touch()' % str(marker)
            parent = ('import subprocess,sys,time; '
                      'subprocess.Popen([sys.executable,"-c",%r]); '
                      'print("started",flush=True); time.sleep(10)') % child
            with self.assertRaises(subprocess.TimeoutExpired) as caught:
                run_prover([sys.executable, '-c', parent], cwd=directory, timeout=0.3)
            self.assertIn('started', caught.exception.output)
            time.sleep(0.8)
            self.assertFalse(marker.exists())
