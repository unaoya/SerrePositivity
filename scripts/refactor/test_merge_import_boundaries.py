"""Import rewrites must leave following audit commands untouched."""
import unittest
from merge_modules import import_commands, rewrite_imports


class AuditCommandBoundaryTests(unittest.TestCase):
    def test_assertions_after_imports_are_not_import_tokens(self):
        source = ('import Demo.Old\nimport Mathlib.Util.AssertNoSorry\n\n'
                  'assert_no_sorry Demo.first\n'
                  'assert_no_sorry Demo.second\n'
                  'assert_no_sorry Demo.first\n')
        tokens = [name for _, _, _, values in import_commands(source) for _, _, name in values]
        self.assertEqual(tokens, ['Demo.Old', 'Mathlib.Util.AssertNoSorry'])
        self.assertEqual(rewrite_imports(source, {'Demo.Old': 'Demo.New'}),
                         source.replace('import Demo.Old', 'import Demo.New'))

    def test_other_audit_command_boundaries(self):
        for command in ['assert_not_exists', 'assert_not_imported', 'run_cmd', 'run_elab']:
            with self.subTest(command=command):
                source = 'import Demo.Old\n'+command+' Demo.first\n'+command+' Demo.second\n'
                self.assertEqual(rewrite_imports(source, {'Demo.Old': 'Demo.New'}),
                                 source.replace('import Demo.Old', 'import Demo.New'))


if __name__ == '__main__':
    unittest.main()
