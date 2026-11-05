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

    def test_hierarchical_proof_preserves_assertions_and_binders(self):
        code = compile_proofs(Path('tests/proofs/ProofShapes.tla'))
        for instruction in ('intro taken_', 'refine Exists.intro', 'suffices step_', 'obtain ⟨picked_', 'by_cases step_'):
            self.assertIn(instruction, code)

    def test_false_intermediate_step_is_not_dropped(self):
        code = compile_proofs(Path('tests/proofs/FalseStep.tla'))
        self.assertIn('have step_', code)
        self.assertIn('ZFSet.zffalse', code)

    def test_scoped_definitions(self):
        code = compile_proofs(Path('tests/proofs/DefinitionScope.tla'))
        self.assertIn('«DefinitionScope».«A»', code)

    def test_bounded_witness_annotations_are_proved(self):
        code = compile_proofs(Path('tests/proofs/BoundedWitness.tla'))
        self.assertIn('have witness_bound_', code)
        self.assertIn('refine Exists.intro (_root_.TLAUniversal.integer 1)', code)
        self.assertIn('refine Exists.intro (_root_.TLAUniversal.boolean', code)
