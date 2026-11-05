"""No-build regression tests for audit preparation and runtime-import cache keys."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from audit_imports import audit_imports, audit_build_targets
from verify_runner import cache_key

ROOT = Path(__file__).resolve().parents[2]

class AuditImportsTests(unittest.TestCase):
    def test_static_imports_and_checks(self):
        self.assertEqual(audit_imports('module\npublic import all SerrePositivity.A\nimport Lean X.Y\nassert_no_sorry SerrePositivity.fake\n#check SerrePositivity.fake\n'), {'SerrePositivity.A','Lean','X.Y'})

    def test_runtime_multiple_calls_and_records(self):
        source = '''import Lean
run_cmd do
  let env ← Lean.importModules (#[{ module := `SerrePositivity.宇宙.A, importAll := true },
    { module := `Lean.Util.CollectAxioms }]) {}
  let env ← importModules #[{ module := `SerrePositivity.B }] {}
  let expected := #[`SerrePositivity.NotAnImport]
'''
        self.assertEqual(audit_build_targets([source, source]), ['SerrePositivity.B','SerrePositivity.宇宙.A'])

    def test_comments_strings_and_unrelated_module_fields(self):
        source = '''/- importModules #[{ module := `SerrePositivity.Fake }]
/- nested -/ -/
-- import SerrePositivity.Fake
#eval "importModules #[{ module := `SerrePositivity.Fake }]"
#eval "escaped \\" import SerrePositivity.Fake"
def unrelated := { module := `SerrePositivity.Fake }
import SerrePositivity.Real
'''
        self.assertEqual(audit_imports(source), {'SerrePositivity.Real'})

    def test_empty_runtime_array(self):
        self.assertEqual(audit_imports('run_cmd do let env ← importModules #[] {}'), set())

    def test_unsupported_runtime_calls_fail_closed(self):
        for expression in ['modules','#[{ module := candidate }]', '#[mkImport `SerrePositivity.X]', '#[{module := `SerrePositivity.X}']:
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                audit_imports('run_cmd do let env ← importModules '+expression+' {}')

    def test_repository_audits(self):
        paths = sorted(ROOT.glob('scripts/audit_*.lean')) + sorted(ROOT.glob('scripts/audit/*.lean'))
        targets = audit_build_targets(p.read_text() for p in paths)
        self.assertIn('SerrePositivity.InfinityCategories.F1.Diagrams.CocartesianKanWeightedUnit', targets)
        self.assertTrue(all((ROOT/(n.replace('.','/')+'.lean')).exists() for n in targets))

    def test_cache_tracks_runtime_import_and_transitive_dependencies(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td); (root/'scripts/refactor').mkdir(parents=True)
            for n in ['lean-toolchain','lake-manifest.json']: (root/n).write_text('fixture')
            p=root/'scripts/audit.lean'; p.write_text('import Lean\nrun_cmd do let env ← importModules #[{module := `SerrePositivity.Leaf}] {}\n')
            for n in ['Leaf','Dependency']:
                q=root/('.lake/build/lib/lean/SerrePositivity/'+n+'.olean.hash');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(n)
            graph={'SerrePositivity.Leaf':{'SerrePositivity.Dependency'},'SerrePositivity.Dependency':set()}
            first=cache_key(root,'scripts/audit.lean',graph)
            (root/'.lake/build/lib/lean/SerrePositivity/Dependency.olean.hash').write_text('changed')
            self.assertNotEqual(first,cache_key(root,'scripts/audit.lean',graph))
            (root/'.lake/build/lib/lean/SerrePositivity/Leaf.olean.hash').unlink()
            with self.assertRaises(FileNotFoundError):cache_key(root,'scripts/audit.lean',graph)

    def preparation(self,source):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);(root/'.lake/verify').mkdir(parents=True);(root/'scripts/refactor').mkdir(parents=True)
            for n in ['audit_imports.py','layer_check.py']:(root/'scripts/refactor'/n).write_bytes((ROOT/'scripts/refactor'/n).read_bytes())
            (root/'scripts/audit_fixture.lean').write_text(source)
            (root/'scripts/refactor/audit_manifest.txt').write_text('scripts/audit_fixture.lean\n')
            script=(ROOT/'scripts/refactor/verify.sh').read_text().split("run_stage preparation manifest-and-targets python3 - <<'PY'\n",1)[1].split('\nPY\n',1)[0]
            # Run only preparation, never verify.sh, lake, Lean, or any build.
            run=subprocess.run([sys.executable,'-B','-c',script],cwd=root,capture_output=True,text=True,env={'PATH':__import__('os').environ['PATH']})
            prep=json.loads((root/'.lake/verify/preparation.json').read_text())
            targets=(root/'.lake/verify/audit_targets.txt').read_text().splitlines() if (root/'.lake/verify/audit_targets.txt').exists() else []
            return run.returncode,prep,targets

    def test_clean_preparation_collects_runtime_only_module(self):
        rc,prep,targets=self.preparation('import Lean\nrun_cmd do let env ← importModules #[{module := `SerrePositivity.RuntimeOnly}] {}\n')
        self.assertEqual(rc,0,prep);self.assertEqual(targets,['SerrePositivity.RuntimeOnly'])

    def test_preparation_rejects_computed_runtime_imports(self):
        rc,prep,_=self.preparation('import Lean\nrun_cmd do let env ← importModules computedModules {}\n')
        self.assertNotEqual(rc,0);self.assertTrue(prep['errors'])

if __name__ == '__main__':unittest.main()
