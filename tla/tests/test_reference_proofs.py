import unittest
from reference_proofs import toolbox_status


def record(kind, **fields):
    return '@!!BEGIN\n@!!type:' + kind + '\n' + ''.join(
        '@!!' + key + ':' + str(value) + '\n' for key, value in fields.items()) + '@!!END\n'


class ReferenceProofTests(unittest.TestCase):
    def test_last_backend_result_counts(self):
        output = record('obligationsnumber', count=1)
        output += record('obligation', id=1, status='failed')
        output += record('obligation', id=1, status='proved')
        self.assertEqual(toolbox_status(output, 0)['status'], 'reference_proved')

    def test_missing_omitted_or_failed_exit_is_not_proved(self):
        output = record('obligationsnumber', count=1) + record('obligation', id=1, status='proved')
        self.assertEqual(toolbox_status(output, 11)['status'], 'reference_unproved')
        self.assertEqual(toolbox_status(record('obligationsnumber', count=0), 0)['status'], 'reference_unproved')

    def test_incomplete_protocol_is_not_proved(self):
        output = record('obligationsnumber', count=2) + record('obligation', id=1, status='proved')
        self.assertEqual(toolbox_status(output, 0)['status'], 'reference_unproved')
        self.assertEqual(toolbox_status('', 0)['status'], 'reference_unproved')

    def test_trivial_is_checked(self):
        output = record('obligationsnumber', count=1) + record('obligation', id=1, status='trivial')
        self.assertEqual(toolbox_status(output, 0)['status'], 'reference_proved')
