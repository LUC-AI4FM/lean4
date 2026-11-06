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

    def test_hidden_facts_leave_the_default_context(self):
        code = compile_proofs(Path('tests/proofs/FactScope.tla'))
        self.assertIn('structure TLAHiddenFact', code)
        self.assertIn('clear step_', code)
        self.assertIn('clear prior_0', code)
        self.assertIn(':= hidden_step_', code)
        self.assertIn(':= hidden_prior_0.val', code)
        false_code = compile_proofs(Path('tests/proofs/FalseFactScope.tla'))
        self.assertIn('clear step_', false_code)
        self.assertNotIn(':= hidden_step_', false_code)

    def test_leaves_see_only_cited_or_used_steps(self):
        code = compile_proofs(Path('tests/proofs/FalseUncitedStep.tla'))
        self.assertIn('clear step_', code)
        code = compile_proofs(Path('tests/proofs/CitedStep.tla'))
        self.assertEqual(code.count('clear step_'), 1)

    def test_module_use_and_assumption_citations(self):
        code = compile_proofs(Path('tests/proofs/ModuleContext.tla'))
        self.assertIn('«ModuleContext».«D»', code.split('theorem TLACheckedProof0')[1])
        third = code.split('theorem TLACheckedProof2')[1].split('theorem ')[0]
        self.assertNotIn('clear assume_0', third)
        code = compile_proofs(Path('tests/proofs/FalseUncitedAssumption.tla'))
        self.assertIn('clear assume_0', code)

    def test_leibniz_congruence_lemmas_are_checked_optionally(self):
        code = compile_proofs(Path('tests/proofs/Leibniz.tla'))
        self.assertIn('tla_try @[local aesop unsafe 30% apply] theorem tla_leibniz_', code)
        self.assertIn('show ', code)

    def test_generalization_is_not_attempted_under_state_hypotheses(self):
        code = compile_proofs(Path('tests/proofs/upstream/test_decompose_naive_bcast.tla'),
                              includes=[Path('tests/corpus/tlaps')])
        # Only the four constant-context steps are generalized; steps proved
        # after HAVE/CASE/PICK state facts cannot hold for a fresh behavior.
        self.assertEqual(code.count('_general : ∀ (b :'), 4)

    def test_bounded_witness_annotations_are_proved(self):
        code = compile_proofs(Path('tests/proofs/BoundedWitness.tla'))
        self.assertIn('have witness_bound_', code)
        self.assertIn('refine Exists.intro (_root_.TLAUniversal.integer 1)', code)
        self.assertIn('refine Exists.intro (_root_.TLAUniversal.boolean', code)

    def test_module_use_fact_is_a_checked_obligation(self):
        code = compile_proofs(Path('tests/proofs/ModuleUse.tla'))
        self.assertIn('theorem TLACheckedProof0', code)
        self.assertIn('def TLACheckedCertificate', code)

    def test_case_references_use_scoped_condition_and_later_implication(self):
        code = compile_proofs(Path('tests/proofs/CaseReferences.tla'))
        self.assertIn('have used_', code)
        self.assertIn(' → ', code)
        self.assertNotIn('$Pfcase', code)

    def test_have_introduces_implication_premise(self):
        code = compile_proofs(Path('tests/proofs/upstream/test_proof_steps.tla'))
        self.assertIn('intro have_antecedent', code)
        self.assertIn('suffices step_', code)
        with self.assertRaisesRegex(ProofError, 'HAVE requires an implication'):
            compile_proofs(Path('tests/proofs/FalseHave.tla'))

    def test_state_generalization_requires_a_separate_lean_proof(self):
        code = compile_proofs(Path('tests/proofs/StateGeneralization.tla'))
        self.assertIn('_general : ∀ (b :', code)
        self.assertIn('intro b n', code)
        self.assertIn('| have step_', code)
        # A step proved from a state-level premise is never generalized.
        code = compile_proofs(Path('tests/proofs/FalseStateGeneralization.tla'))
        self.assertNotIn('_general : ∀ (b :', code)

    def test_imported_declarations_are_proof_obligations(self):
        for source in ('ImportedLaw', 'FalseImportedLaw'):
            code = compile_proofs(Path('tests/proofs/imported') / (source + '.tla'))
            self.assertEqual(code.count('theorem TLACheckedProof'), 2)
            self.assertNotIn('axiom ', code)
            self.assertNotIn('sorry', code)
        with self.assertRaisesRegex(ProofError, 'no explicit proof'):
            compile_proofs(Path('tests/proofs/imported/ImportedProofLibrary.tla'))
