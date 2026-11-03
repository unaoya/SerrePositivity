#!/usr/bin/env python3
"""Archive importer exclusions are opt-in and do not hide production consumers."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

VALIDATOR = Path(__file__).with_name('validate_targets.py')


class ArchiveImporterTests(unittest.TestCase):
    def test_opt_in_audit_prefixes_preserve_production_consumer_check(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = 'SerrePositivity.Unused'
            def put(name, text):
                path = root / (name.replace('.', '/') + '.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            put(module, 'def unused : Nat := 1\n')
            for name in ('scripts.audit.area', 'scripts.audit_example', 'scripts.checks.example'):
                put(name, 'import ' + module + '\n')
            plan = root / 'targets.json'
            plan.write_text(json.dumps([{'module': module, 'action': 'archive',
                'dest': 'SerrePositivity.Archive.Unused', 'moved': [], 'keep': [],
                'attributes': {}, 'candidate': 'test', 'note': 'archive fixture'}]))
            def run(flags=()):
                return subprocess.run([sys.executable, str(VALIDATOR), str(plan),
                    '--root', str(root), *flags], capture_output=True, text=True)
            default = run()
            self.assertEqual(default.returncode, 1)
            self.assertIn('archive still has outside importers', default.stderr)
            flags = [part for prefix in ('scripts.audit', 'scripts.audit_', 'scripts.checks')
                     for part in ('--ignore-importer-prefix', prefix)]
            ignored = run(flags)
            self.assertEqual(ignored.returncode, 0, ignored.stderr)
            self.assertEqual(json.loads(ignored.stdout)['status'], 'PASS')
            put('SerrePositivity.Consumer', 'import ' + module + '\n')
            production = run(flags)
            self.assertEqual(production.returncode, 1)
            self.assertIn('SerrePositivity.Consumer', production.stderr)
            self.assertNotIn('scripts.audit', production.stderr)


if __name__ == '__main__':
    unittest.main()
