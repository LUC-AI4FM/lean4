"""Proof reconstruction must produce terms, never assume cited theorems."""
from pathlib import Path
import unittest
from proofs import compile_proofs, ProofError


class ProofTests(unittest.TestCase):
    def test_leaf_proofs_generate_checked_declarations(self):
        code = compile_proofs(Path('tests/proofs/Leaves.tla'))
        self.assertEqual(code.count('theorem TLACheckedProof'), 5)
        self.assertIn('def TLACheckedCertificate', code)
        self.assertNotIn('sorry', code)
        self.assertNotIn('axiom ', code)

    def test_omitted_is_not_a_proof(self):
        with self.assertRaisesRegex(ProofError, 'OMITTED'):
            compile_proofs(Path('tests/proofs/Omitted.tla'))

    def test_false_leaf_is_left_for_lean_to_reject(self):
        code = compile_proofs(Path('tests/proofs/FalseLeaf.tla'))
        self.assertIn('theorem TLACheckedProof0', code)
        self.assertNotIn('sorry', code)
        self.assertNotIn('axiom ', code)
