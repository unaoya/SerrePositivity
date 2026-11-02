"""Parent identity and false-positive guards for proof-irrelevant snapshots."""
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import unittest
from compare_snapshots import compare

def row(name, parent=None, body='1'):
    return dict(name=name, parent=parent or name, module='M', kind='def',
                type_hash='nat', body_hash=body, axioms=[], attributes={},
                reference_kind='named')

def snapshot(rows, source=None):
    return dict(schema_version=2, hash_algorithm='normalized Expr DAG mixHash proof-irrelevant v3 (term-level)',
                name_map={}, proof_irrelevant=True, declarations=rows,
                sources=[] if source is None else [dict(module='M',source=source)])

class ParentGroups(unittest.TestCase):
    def test_auxiliary_names_and_duplicate_count_do_not_matter(self):
        before=snapshot([row('N.f'),row('N.f.match_1','N.f'),row('N.f.match_2','N.f')])
        after=snapshot([row('N.f'),row('N.f.match_99','N.f')])
        result=compare(before,after)
        self.assertEqual(result['status'],'PASS')
        self.assertEqual(result['auxiliary_groups']['before'][0]['parent'],'N.f')
        self.assertEqual(len(result['auxiliary_groups']['before'][0]['names']),2)

    def test_non_inlined_auxiliary_value_and_attributes_are_checked(self):
        before=snapshot([row('N.f'),row('N.f.child','N.f')])
        for field,value in [('body_hash','2'),('attributes',{'simp':True})]:
            after=copy.deepcopy(before)
            after['declarations'][1][field]=value
            self.assertEqual(compare(before,after)['status'],'FAIL')

    def test_authored_generated_looking_declaration_is_not_discarded(self):
        source='namespace N\ndef f : Nat := 0\ndef f._proof_1 : Nat := 0\nend N\n'
        before=snapshot([row('N.f'),row('N.f._proof_1','N.f')],source)
        before['declarations'][1]['reference_kind']='generated'
        after=copy.deepcopy(before)
        after['declarations'][1]['body_hash']='changed'
        result=compare(before,after)
        self.assertEqual(result['status'],'FAIL')
        self.assertTrue(any(c['name']=='N.f._proof_1' for c in result['changes']))

    def test_inlined_helpers_are_recorded_under_parent(self):
        before=snapshot([row('N.f'),{**row('N.f.match_1','N.f'),'reference_kind':'generated'}])
        after=snapshot([row('N.f')])
        result=compare(before,after)
        self.assertEqual(result['status'],'PASS')
        self.assertEqual(result['auxiliary_groups']['before'],
                         [{'parent':'N.f','module':'M','names':['N.f.match_1']}])

class TermProofErasure(unittest.TestCase):
    """Real Lean terms: application arguments and proofs below local binders."""

    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[2]
        out = root / '.lake/verify/proof-irrelevant-v3-tests'
        out.mkdir(parents=True, exist_ok=True)
        search = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                         cwd=root, text=True).strip()
        env = {**os.environ, 'LEAN_PATH': str(out) + ':' + search}
        source = out / 'TermProofFixture.lean'
        source.write_text("""import Lean
namespace TermProofFixture
class Witness (n : Nat) : Prop where
  eq_self : n = n
theorem routeA (n : Nat) : Witness n := ⟨rfl⟩
theorem routeB (n : Nat) (_ : Unit) : Witness n := routeA n
def value (n : Nat) [Witness n] : Nat := n
def chooseA : Nat := @value 7 (routeA 7)
def chooseB : Nat := @value 7 (routeB 7 ())
def changedData : Nat := @value 8 (routeA 8)
def underA : (n : Nat) → Witness n → Nat := fun n h => @value n h
def underB : (n : Nat) → Witness n → Nat := fun n _ => @value n (routeB n ())
end TermProofFixture
""")
        commands = [
            ('compile', ['lean', '-o', str(source.with_suffix('.olean')), str(source)]),
            ('snapshot', ['lean', '--run', str(root / 'scripts/refactor/decl_snapshot.lean'),
                          '--modules', 'TermProofFixture', '--output', str(out / 'snapshot.json')]),
        ]
        for label, command in commands:
            result = subprocess.run(command, cwd=out, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (out / (label + '.log')).write_text(result.stdout)
            if result.returncode or re.search(r'(?m)^PANIC\b|\berror(?:\([^)]*\))?:', result.stdout):
                raise RuntimeError(label + ': ' + result.stdout)
        snap = json.loads((out / 'snapshot.json').read_text())
        if snap['hash_algorithm'] != 'normalized Expr DAG mixHash proof-irrelevant v3 (term-level)':
            raise AssertionError('term-level snapshot mode was not used')
        cls.rows = {r['name'].split('.')[-1]: r for r in snap['declarations']}

    def test_same_proposition_different_instance_derivations(self):
        self.assertEqual(self.rows['chooseA']['body_hash'], self.rows['chooseB']['body_hash'])

    def test_data_arguments_are_not_erased(self):
        self.assertNotEqual(self.rows['chooseA']['body_hash'], self.rows['changedData']['body_hash'])

    def test_proofs_under_binders_are_erased(self):
        self.assertEqual(self.rows['underA']['type_hash'], self.rows['underB']['type_hash'])
        self.assertEqual(self.rows['underA']['body_hash'], self.rows['underB']['body_hash'])

if __name__=='__main__':
    unittest.main()
