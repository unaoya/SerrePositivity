#!/usr/bin/env python3
"""§10.37: real Lean fixtures, isolated olean directory; no project lake build."""
import json
import os
import re
from pathlib import Path
import subprocess
import time
import unittest
from compare_snapshots import compare

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / '.lake/verify/proof-irrelevant-tests'

def definitions(name):
    return f"""
namespace ProofFixture
def {name} (n : Nat) : {{k : Nat // k ≤ n + 1}} := ⟨n, by omega⟩
def {name}Match (a b : Nat) : Nat :=
  match a, b with
  | 0, _ => b
  | a+1, 0 => a
  | a+1, b+1 => a+b
end ProofFixture
"""

class ProofIrrelevantIntegration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        OUT.mkdir(parents=True, exist_ok=True)
        cls.commands = []
        search = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
        cls.env = {**os.environ, 'LEAN_PATH': str(OUT) + ':' + search}
        cls.write('Before.A', 'import Lean\n' + definitions('f'))
        cls.write('Before.B', 'import Lean\n' + definitions('g'))
        cls.write('After', 'import Lean\n' + definitions('f') + definitions('g'))
        cls.write('References', """import Lean
namespace ProofFixture
class Witness (n : Nat) : Prop where
  eq_self : n = n
instance routeA : Witness 0 := ⟨rfl⟩
instance routeB : Witness 0 := ⟨rfl⟩
def chooseA : {n : Nat // n = 0} := ⟨0, @Witness.eq_self 0 routeA⟩
def chooseB : {n : Nat // n = 0} := ⟨0, @Witness.eq_self 0 routeB⟩
def valueA : Nat := 1
def valueB : Nat := 1
def pickA : Nat := valueA
def pickB : Nat := valueB
def match_900 : Nat := 1
def match_901 : Nat := 1
def userMatchA : Nat := match_900
def userMatchB : Nat := match_901
end ProofFixture
""")
        cls.before = cls.snapshot('before', 'Before.A,Before.B')
        cls.after = cls.snapshot('after', 'After')
        cls.legacy_before = cls.snapshot('legacy-before', 'Before.A,Before.B', '--no-proof-irrelevant')
        cls.legacy_after = cls.snapshot('legacy-after', 'After', '--no-proof-irrelevant')
        cls.refs = cls.snapshot('references', 'References', '--proof-irrelevant')
        cls.module_map = {'modules': {'Before.A': 'After', 'Before.B': 'After'}}
        compiled = OUT/'scripts/refactor/decl_snapshot.olean'
        compiled.parent.mkdir(parents=True, exist_ok=True)
        cls.run_cmd('compile-hash-tool', ['lean', '-o', str(compiled),
                     'scripts/refactor/decl_snapshot.lean'], cwd=ROOT)
        cls.run_cmd('dag-sharing', ['lean', 'scripts/refactor/test_dag_hash.lean'], cwd=ROOT)
        cls.run_cmd('hash-recursion', ['lean', 'scripts/refactor/test_proof_irrelevant_hash.lean'], cwd=ROOT)

    @classmethod
    def run_cmd(cls, label, args, cwd=OUT):
        start = time.monotonic()
        with (OUT/(label+'.log')).open('w') as log:
            rc = subprocess.call(args, cwd=cwd, env=cls.env, stdout=log, stderr=subprocess.STDOUT)
        cls.commands.append(dict(label=label, command=args, exit_code=rc, seconds=round(time.monotonic()-start, 3)))
        (OUT/'commands.json').write_text(json.dumps(cls.commands, indent=2)+'\n')
        text = (OUT/(label+'.log')).read_text()
        if rc or re.search(r'(?m)^PANIC\b|\berror(?:\([^)]*\))?:', text):
            raise RuntimeError(f'{label}: exit {rc}, failed diagnostics\n'+text)

    @classmethod
    def write(cls, module, source):
        path = OUT/(module.replace('.', '/')+'.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        cls.run_cmd('compile-'+module, ['lean', '-o', str(path.with_suffix('.olean')), str(path)])

    @classmethod
    def snapshot(cls, label, modules, *flags):
        cls.run_cmd(label, ['lean', '-M', '40000', '--run', str(ROOT/'scripts/refactor/decl_snapshot.lean'),
                            '--modules', modules, *flags, '--output', str(OUT/(label+'.json'))])
        return json.loads((OUT/(label+'.json')).read_text())

    def test_two_files_and_merged_file_preserve_hashes(self):
        result = compare(self.before, self.after, module_map=self.module_map)
        (OUT/'comparison.json').write_text(json.dumps(result, indent=2)+'\n')
        self.assertEqual(result['changes'], [])
        before = {r['name']: r for r in self.before['declarations']}
        after = {r['name']: r for r in self.after['declarations']}
        for n in ['f', 'g', 'fMatch', 'gMatch']:
            for field in ['type_hash', 'body_hash']:
                self.assertEqual(before['ProofFixture.'+n][field], after['ProofFixture.'+n][field])
        old = compare(self.legacy_before, self.legacy_after, module_map=self.module_map)
        self.assertEqual(old['status'], 'FAIL')
        helpers = [r for r in self.before['declarations'] if r.get('reference_kind') == 'generated']
        self.assertTrue(helpers, 'fixture did not produce a registered matcher')
        proofs = [r for r in self.before['declarations'] if '._proof_' in r['name']]
        self.assertTrue(proofs, 'fixture did not produce extracted proofs')
        for token in ['._proof_', '.match_']:
            self.assertTrue(any(token in c for r in before.values() for c in r['used_constants']))
        self.assertNotEqual(set(before), set(after), 'fixture did not share helpers on merge')
        for parent, token in [('g', '._proof_'), ('gMatch', '.match_')]:
            old_refs = {c for c in before['ProofFixture.'+parent]['used_constants'] if token in c}
            new_refs = {c for c in after['ProofFixture.'+parent]['used_constants'] if token in c}
            self.assertTrue(old_refs and new_refs)
            self.assertNotEqual(old_refs, new_refs, 'fixture failed to share '+token)

    def test_prop_instances_compare_by_type(self):
        rows = {r['name']: r for r in self.refs['declarations']}
        for n in ['routeA', 'routeB']:
            self.assertEqual(rows['ProofFixture.'+n]['reference_kind'], 'proof')
        self.assertEqual(rows['ProofFixture.chooseA']['body_hash'], rows['ProofFixture.chooseB']['body_hash'])

    def test_non_prop_definition_references_still_differ(self):
        rows = {r['name']: r for r in self.refs['declarations']}
        self.assertEqual(rows['ProofFixture.valueA']['body_hash'], rows['ProofFixture.valueB']['body_hash'])
        self.assertNotEqual(rows['ProofFixture.pickA']['body_hash'], rows['ProofFixture.pickB']['body_hash'])
        self.assertNotEqual(rows['ProofFixture.userMatchA']['body_hash'], rows['ProofFixture.userMatchB']['body_hash'])

    def test_changed_definition_body_is_rejected(self):
        import copy
        changed = copy.deepcopy(self.after)
        row = next(r for r in changed['declarations'] if r['name'] == 'ProofFixture.gMatch')
        row['body_hash'] = 'deliberately changed'
        result = compare(self.before, changed, module_map=self.module_map)
        self.assertTrue(any(r['name'] == 'ProofFixture.gMatch' and r['change'] == 'body' for r in result['changes']))

    def test_hash_modes_must_match(self):
        with self.assertRaisesRegex(ValueError, 'hash algorithms differ'):
            compare(self.before, self.legacy_after, module_map=self.module_map)

if __name__ == '__main__':
    unittest.main(verbosity=2)
