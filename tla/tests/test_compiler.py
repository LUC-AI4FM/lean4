"""End-to-end source compilation through resolved SANY bindings."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from compiler import compile_file, CompileError

class CompilerTests(unittest.TestCase):
    def check(self, source, extra=''):
        code = compile_file(source)
        with tempfile.TemporaryDirectory(dir='.') as directory:
            target = Path(directory) / 'Generated.lean'
            target.write_text(code + '\n' + extra)
            result = subprocess.run([os.environ.get('LAKE', 'lake'), 'env', 'lean', str(target)],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, code + '\n' + result.stdout + result.stderr)
        return code

    def test_counter(self):
        self.check(Path('tests/Counter.tla'))

    def test_collections(self):
        self.check(Path('tests/fixtures/Collections.tla'))

    def test_unknown_operator_not_assumed(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'Unknown.tla'
            path.write_text('---- MODULE Unknown ----\nCONSTANT F(_)\nA == F(1)\n====')
            with self.assertRaises(CompileError):
                compile_file(path)

    def test_instance_substitution(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'Other.tla').write_text('---- MODULE Other ----\nEXTENDS Integers\nCONSTANT c\nTwice == c + c\n====')
            (root / 'Main.tla').write_text('---- MODULE Main ----\nEXTENDS Integers\nI == INSTANCE Other WITH c <- 2\nAnswer == I!Twice\n====')
            self.check(root / 'Main.tla', 'example (c : Main.Constants) (b : TLA.Behavior Main.State) (n : Nat) : Main.Answer c b n = 4 := rfl')

    def test_collection_semantics(self):
        self.check(Path('tests/fixtures/Collections.tla'), r"""
example (c : Collections.Constants) (b : TLA.Behavior Collections.State) (n : Nat) :
    Collections.Local c b n = c.N + 1 := rfl
example (c : Collections.Constants) (b : TLA.Behavior Collections.State) (n : Nat) :
    Collections.Bound c b n := by
  intro i hi
  have h := hi.1.1
  omega
""")

    def test_generic_sets(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'Generic.tla'
            path.write_text(r"""---- MODULE Generic ----
CONSTANT S
VARIABLE x
Empty == {}
Init == x \in S
Next == UNCHANGED x
Spec == Init /\ [][Next]_x
====""")
            self.check(path)

    def test_unproved_theorem_not_dropped(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'FalseClaim.tla'
            path.write_text('---- MODULE FalseClaim ----\nA == TRUE\nTHEOREM FALSE\n====')
            with self.assertRaises(CompileError):
                compile_file(path)

    def test_records_and_nested_updates(self):
        self.check(Path('tests/fixtures/Records.tla'), r"""
example (c : Records.Constants) (b : TLA.Behavior Records.State) (n : Nat) :
    Records.Good c b n := by
  simp [Records.Good, TLA.Data.Seq.get, TLA.Data.Seq.update]
example (c : Records.Constants) (b : TLA.Behavior Records.State) (n : Nat) :
    Records.Included c b n := by
  simp [Records.Included, TLA.Data.Set.enumerate]
example (c : Records.Constants) (b : TLA.Behavior Records.State) (n : Nat) :
    Records.UpdateGood c b n := by
  simp [Records.UpdateGood, TLA.Data.Function.apply, TLA.Data.Function.update,
        TLA.Data.Function.make, TLA.Data.Set.interval]
""")
