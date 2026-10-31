import copy,unittest
from lean_source import declaration_owner,transient_names,GENERATED_SUFFIXES
from compare_snapshots import compare

def row(name,module='Test',line=None,parent=None,parent_module=None):
    return dict(name=name,module=module,parent=name,environment_parent=parent,parent_module=parent_module,
                source_range=None if line is None else dict(start_line=line,end_line=line,selection_start_line=line,selection_end_line=line),
                kind='theorem',type=['const','True',[]],body=None,axioms=[],attributes={},used_constants=[])

class AttributionTests(unittest.TestCase):
    def test_position_before_external_parent(self):
        a=row('N.a',line=3);a['source_range']['end_line']=6
        g=row('External.a.eq_1',line=3,parent='External.a',parent_module='Mathlib.Other')
        self.assertEqual(declaration_owner(g,{'N.a'},{a['name']:a,g['name']:g}),'N.a')
        s={'sources':[{'module':'Test','source':'namespace N\n\n@[simp]\ntheorem a : True := by\n  trivial\n\nend N\n'}],'declarations':[a,g]}
        self.assertEqual(transient_names(s),[])
    def test_position_in_other_module_not_used(self):
        a=row('N.a',module='Other',line=3);g=row('unknown',line=3)
        self.assertIsNone(declaration_owner(g,{'N.a'},{'N.a':a}))
    def test_ambiguous_position_stops(self):
        from lean_source import Unsupported
        a=row('a',line=1);b=row('b',line=1);g=row('unknown',line=1)
        with self.assertRaisesRegex(Unsupported,'ambiguous'):declaration_owner(g,{'a','b'},{'a':a,'b':b})
    def test_private_normalized_prefix(self):
        a=row('N.a');g=row('_private.Test.0.N.a._proof_1_1')
        self.assertEqual(declaration_owner(g,{'N.a'},{'N.a':a}), 'N.a')
    def test_longest_prefix(self):
        a=row('N.a');b=row('N.a.f');g=row('N.a.f.eq_1')
        self.assertEqual(declaration_owner(g,{'N.a','N.a.f'},{'N.a':a,'N.a.f':b}),'N.a.f')
    def test_allowed_suffixes_only_and_same_module(self):
        for suffix in GENERATED_SUFFIXES:
            g=row('N.a_'+suffix)
            self.assertEqual(declaration_owner(g,{'N.a'},{'N.a':row('N.a')}),'N.a')
            self.assertIsNone(declaration_owner(g,{'N.a'},{'N.a':row('N.a',module='Other')}))
        self.assertIsNone(declaration_owner(row('N.a_other'),{'N.a'},{'N.a':row('N.a')}))
    def test_ambiguous_suffix_stops(self):
        from lean_source import Unsupported
        with self.assertRaisesRegex(Unsupported,'ambiguous generated declaration suffix'):
            declaration_owner(row('N.a_symm_apply'),{'N.a','N.a_symm'},
                              {'N.a':row('N.a'),'N.a_symm':row('N.a_symm')})
    def test_reassoc_comparison_checks_generated_type(self):
        a=row('a');g=row('a_assoc');s={'schema_version':1,'sources':[{'module':'Test','source':'theorem a : True := True.intro\n'}],'declarations':[a,g]}
        self.assertEqual(compare(s,copy.deepcopy(s))['status'],'PASS')
        changed=copy.deepcopy(s);changed['declarations'][1]['type']=['const','False',[]]
        self.assertEqual(compare(s,changed)['status'],'FAIL')

if __name__=='__main__':unittest.main()
