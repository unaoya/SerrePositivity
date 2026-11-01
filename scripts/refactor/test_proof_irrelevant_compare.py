"""Parent identity and false-positive guards for proof-irrelevant snapshots."""
import copy
import unittest
from compare_snapshots import compare

def row(name, parent=None, body='1'):
    return dict(name=name, parent=parent or name, module='M', kind='def',
                type_hash='nat', body_hash=body, axioms=[], attributes={},
                reference_kind='named')

def snapshot(rows, source=None):
    return dict(schema_version=2, hash_algorithm='normalized Expr DAG mixHash proof-irrelevant v2',
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

if __name__=='__main__':
    unittest.main()
