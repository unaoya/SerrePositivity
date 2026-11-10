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
    return dict(schema_version=2, hash_algorithm='normalized Expr DAG mixHash proof-irrelevant v3b (term-level, proof marker)',
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

    def test_single_name_export_preserves_generated_proof_attribution(self):
        source = "namespace N\ndef f : Nat := 0\nend N\n"
        export = "with_weak_namespace _root_.Q export _root_.N (f)\n"
        equation = {**row("N.f.eq_1"), "kind": "theorem", "reference_kind": "proof",
                    "environment_parent": "N.f", "parent_module": "M"}
        before = snapshot([row("N.f"), equation], source)
        after = snapshot([row("N.f"), equation], source.replace("end N", export + "end N"))
        result = compare(before, after)
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["auxiliary_groups"]["after"],
                         [{"parent": "N.f", "module": "M", "names": ["N.f.eq_1"]}])

    def test_deprecated_alias_remains_a_source_declaration(self):
        source = ("namespace N\ndef f : Nat := 0\n"
                  "deprecated_alias _root_.Old.f := _root_.N.f\nend N\n")
        parent = {**row("N.f"), "source_range": {"start_line": 2, "end_line": 2, "selection_start_line": 2}}
        legacy = {**row("Old.f"), "parent_module": "Other", "environment_parent": "Old",
                  "source_range": {"start_line": 3, "end_line": 3, "selection_start_line": 3}}
        before = snapshot([parent, legacy], source)
        after = copy.deepcopy(before)
        after["declarations"][1]["body_hash"] = "changed alias body"
        result = compare(before, after)
        self.assertEqual(result["status"], "FAIL")
        self.assertEqual(result["changes"][0]["name"], "Old.f")

    def test_inlined_helpers_are_recorded_under_parent(self):
        before=snapshot([row('N.f'),{**row('N.f.match_1','N.f'),'reference_kind':'generated'}])
        after=snapshot([row('N.f')])
        result=compare(before,after)
        self.assertEqual(result['status'],'PASS')
        self.assertEqual(result['auxiliary_groups']['before'],
                         [{'parent':'N.f','module':'M','names':['N.f.match_1']}])

    def test_matching_data_parent_suppresses_generated_proof_type(self):
        for kind in ['def', 'abbrev', 'instance']:
            with self.subTest(kind=kind):
                parent = {**row('N.f'), 'kind': kind}
                proof = {**row('N.f._proof_1', 'N.f', None),
                         'kind': 'theorem', 'reference_kind': 'proof'}
                before = snapshot([parent, proof])
                after = copy.deepcopy(before)
                after['declarations'][1]['type_hash'] = 'different proof proposition syntax'
                self.assertEqual(compare(before, after)['status'], 'PASS')

    def test_changed_parent_reports_its_generated_proof_too(self):
        for kind in ['theorem', 'def', 'abbrev', 'instance']:
            with self.subTest(kind=kind):
                parent = {**row('N.f'), 'kind': kind}
                proof = {**row('N.f._proof_1', 'N.f', None),
                         'kind': 'theorem', 'reference_kind': 'proof'}
                before = snapshot([parent, proof])
                after = copy.deepcopy(before)
                after['declarations'][0]['type_hash'] = 'changed parent type'
                after['declarations'][1]['type_hash'] = 'changed helper type'
                result = compare(before, after)
                self.assertEqual(result['status'], 'FAIL')
                self.assertEqual({r['name'] for r in result['changes']},
                                 {'N.f', 'N.f._proof_1'})

class TermProofErasure(unittest.TestCase):
    """Real Lean terms: application arguments and proofs below local binders."""

    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[2]
        out = root / '.lake/verify/proof-irrelevant-v3b-tests'
        out.mkdir(parents=True, exist_ok=True)
        search = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                         cwd=root, text=True).strip()
        env = {**os.environ, 'LEAN_PATH': str(out) + ':' + search}
        source = out / 'TermProofFixture.lean'
        source.write_text("""import Mathlib.AlgebraicTopology.SimplicialSet.Basic
open CategoryTheory
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
class HasValue (A : Type 1) : Prop where
  witness : True
theorem aliasWitness : HasValue SSet.{0} := ⟨True.intro⟩
theorem expandedWitness : HasValue (SimplexCategoryᵒᵖ ⥤ Type) := ⟨True.intro⟩
def pickAlias (_ : HasValue SSet.{0}) : Nat := 7
def fromAlias : Nat := pickAlias aliasWitness
def fromExpanded : Nat := pickAlias expandedWitness
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
        if snap['hash_algorithm'] != 'normalized Expr DAG mixHash proof-irrelevant v3b (term-level, proof marker)':
            raise AssertionError('term-level snapshot mode was not used')
        cls.rows = {r['name'].split('.')[-1]: r for r in snap['declarations']}

    def test_same_proposition_different_instance_derivations(self):
        self.assertEqual(self.rows['chooseA']['body_hash'], self.rows['chooseB']['body_hash'])

    def test_data_arguments_are_not_erased(self):
        self.assertNotEqual(self.rows['chooseA']['body_hash'], self.rows['changedData']['body_hash'])

    def test_definitionally_equal_propositions_use_same_marker(self):
        # The witness propositions really have different syntax before erasure.
        self.assertNotEqual(self.rows['aliasWitness']['type_hash'],
                            self.rows['expandedWitness']['type_hash'])
        self.assertEqual(self.rows['fromAlias']['body_hash'],
                         self.rows['fromExpanded']['body_hash'])

    def test_proofs_under_binders_are_erased(self):
        self.assertEqual(self.rows['underA']['type_hash'], self.rows['underB']['type_hash'])
        self.assertEqual(self.rows['underA']['body_hash'], self.rows['underB']['body_hash'])

if __name__=='__main__':
    unittest.main()
