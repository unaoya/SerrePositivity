"""Environment parent metadata, external transients, and fail-closed splitting."""
import unittest
from lean_source import parse_source, dependency_directions, transient_names, Unsupported
from compare_snapshots import compare

class GeneratedTests(unittest.TestCase):
    def snapshot(self, parent='External.f', parent_module='Mathlib.Test'):
        source='def kept := 1\ndef moved := 2\n'
        row={'parent':'kept','kind':'def','type':['nat',1],'body':['nat',1],'axioms':[],
             'attributes':{},'module':'Test','used_constants':[]}
        rows=[dict(row,name=n,parent=n,environment_parent=None,parent_module=None) for n in ('kept','moved')]
        rows.append(dict(row,name=parent+'.eq_1',parent=parent,environment_parent=parent,parent_module=parent_module))
        return {'schema_version':1,'sources':[{'module':'Test','source':source}],'declarations':rows}
    def test_mathlib_external_is_transient(self):
        s=self.snapshot();self.assertEqual(transient_names(s),['External.f.eq_1'])
        self.assertEqual(dependency_directions(parse_source(s['sources'][0]['source']),{'moved'},s),([],[]))
        after={**s,'declarations':s['declarations'][:2]};r=compare(s,after)
        self.assertEqual(r['status'],'PASS');self.assertEqual(r['transient']['before'],['External.f.eq_1'])
    def test_project_external(self):
        self.assertEqual(transient_names(self.snapshot(parent_module='SerrePositivity.Other')),['External.f.eq_1'])
    def test_local_auxiliary_keeps_dependency(self):
        s=self.snapshot('moved','Test');s['declarations'][-1]['used_constants']=['kept']
        self.assertEqual(transient_names(s),[])
        self.assertEqual(dependency_directions(parse_source(s['sources'][0]['source']),{'moved'},s),([('moved','kept')],[]))
    def test_longest_parent_chain(self):
        s=self.snapshot('moved','Test');r=s['declarations'][-1]
        s['declarations'].append(dict(r,name='moved.eq_1.match_1',environment_parent='moved.eq_1',used_constants=['kept']))
        self.assertEqual(dependency_directions(parse_source(s['sources'][0]['source']),{'moved'},s),([('moved','kept')],[]))
    def test_no_parent_stops(self):
        s=self.snapshot();s['declarations'][-1].update(environment_parent=None,parent_module=None)
        with self.assertRaisesRegex(Unsupported,'cannot associate'):dependency_directions(parse_source(s['sources'][0]['source']),{'moved'},s)
    def test_explicit_source_declaration_is_preserved(self):
        s=self.snapshot();s['sources'][0]['source']+='theorem External.f.eq_1 : True := True.intro\n'
        self.assertEqual(transient_names(s),[])
        self.assertEqual(compare(s,{**s,'declarations':s['declarations'][:2]})['status'],'FAIL')
    def test_other_namespace_same_short_name_is_not_explicit(self):
        s=self.snapshot();s['sources'][0]['source']+='namespace Other\ndef eq_1 := 0\nend Other\n'
        self.assertEqual(transient_names(s),['External.f.eq_1'])
    def test_underscore_is_not_name_prefix(self):
        s=self.snapshot('moved','Test');s['declarations'][-1].update(name='moved_other',environment_parent=None)
        with self.assertRaises(Unsupported):dependency_directions(parse_source(s['sources'][0]['source']),{'moved'},s)

if __name__=='__main__':unittest.main()
