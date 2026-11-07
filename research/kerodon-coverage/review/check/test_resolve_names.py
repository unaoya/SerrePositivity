import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
import resolve_names as r


class ScopeTests(unittest.TestCase):
    def names(self, source, name, line=1):
        return r.candidates(dict(declaration=name, source_line=str(line)), source)[0]

    def test_nested_namespace_and_sections(self):
        source = 'namespace A\nsection S\nnamespace B\nopen C\ndef foo := 1\nend B\nend S\ndef bar := 2\nend A\n'
        scopes, decls = r.scopes(source)
        self.assertEqual(decls[0]['context'],dict(namespace='A.B',opens=['C']))
        self.assertEqual(decls[1]['context'],dict(namespace='A',opens=[]))
        self.assertIn('A.B.foo', self.names(source,'Bad.foo',5))

    def test_nested_comments_and_strings(self):
        source = '/- namespace Bad\n/- end -/\n-/\nnamespace Good\ndef s := "namespace Fake"\ndef foo := 1 -- end\nend Good\n'
        _, decls = r.scopes(source)
        self.assertEqual(decls[-1]['context']['namespace'],'Good')
        self.assertNotIn('Bad.foo',self.names(source,'foo',6))
        self.assertEqual(source.count('\n'),r.mask(source).count('\n'))

    def test_open_in_is_local(self):
        source='namespace A\nopen B in\nlemma foo : True := by trivial\nlemma bar : True := by trivial\nend A\n'
        _, decls=r.scopes(source)
        self.assertEqual(decls[0]['context']['opens'],['B'])
        self.assertEqual(decls[1]['context']['opens'],[])
        self.assertIn('B.foo',self.names(source,'foo',3))
        self.assertNotIn('B.bar',self.names(source,'bar',4))

    def test_open_in_wrapper_and_instance(self):
        source='open B in\nset_option maxRecDepth 100 in\nnoncomputable instance : Inhabited Nat := inferInstance\ndef foo := 1\n'
        _,d=r.scopes(source)
        self.assertEqual(d[0]['context']['opens'],[])

    def test_section_open_expires(self):
        source='namespace A\nsection\nopen X\ndef foo := 0\nend\ndef bar := 1\nend A\n'
        _,d=r.scopes(source)
        self.assertEqual(d[0]['context']['opens'],['X'])
        self.assertEqual(d[1]['context']['opens'],[])

    def test_absolute_namespace_and_attributes(self):
        source='namespace A\nnamespace _root_.B\n@[simp] def foo := 0\nend B\ndef bar := 1\nend A\n'
        _,d=r.scopes(source)
        self.assertEqual(d[0]['context']['namespace'],'B')
        self.assertEqual(d[1]['context']['namespace'],'A')

    def test_line_drift_finds_matching_declaration(self):
        source='namespace A\n/- doc -/\n\ndef foo := 1\nend A\n'
        self.assertIn('A.foo',self.names(source,'Wrong.foo',2))

    def test_qualified_suffix_does_not_mix_dual_namespaces(self):
        source='namespace CategoryTheory\nnamespace SimplicialObject\ndef δ := 0\nend SimplicialObject\nnamespace CosimplicialObject\ndef δ := 1\nend CosimplicialObject\nend CategoryTheory\n'
        names=self.names(source,'SimplicialObject.δ',3)
        self.assertIn('CategoryTheory.SimplicialObject.δ',names)
        self.assertNotIn('CategoryTheory.CosimplicialObject.δ',names)

    def test_private_is_not_replaced_by_imported_namesake(self):
        self.assertEqual(self.names('namespace A\nnoncomputable private def foo := 0\nend A','foo',2),[])

    def test_no_guess_for_descriptions(self):
        self.assertEqual(self.names('namespace A\ndef foo := 0\nend A','instance Foo X'),[])
        self.assertEqual(self.names('namespace A\ndef foo := 0\nend A','foo / bar'),[])

    def test_abbreviated_paths(self):
        x=r.locate('foo @ IC/F2/Presentable/Accessible.lean:41')
        self.assertEqual(x['source'],'SerrePositivity/InfinityCategories/F2/Presentable/Accessible.lean')
        self.assertEqual(x['declaration'],'foo')
        x=r.locate('Foo.bar @ HomotopicalAlgebra/Smith/Basic.lean:12')
        self.assertEqual(x['source'],'SerrePositivity/HomotopicalAlgebra/Smith/Basic.lean')

    def test_source_does_not_execute(self):
        self.assertEqual(self.names('namespace A\n#eval bad\ndef foo := 0\nend A','foo',3)[0],'A.foo')


class ResolutionTests(unittest.TestCase):
    def test_unique_requires_all_candidates_checked(self):
        good={'state':'found'}; bad={'state':'not_found'}
        self.assertEqual(r.resolution_state('not_found',['a','b'],{'a':good})[0],'pending')
        self.assertEqual(r.resolution_state('not_found',['a','b'],{'a':good,'b':bad})[0],'renamed')
        self.assertEqual(r.resolution_state('not_found',['a','b'],{'a':good,'b':good})[0],'ambiguous')
        self.assertEqual(r.resolution_state('unresolved_reference',[],{})[0],'manual')
        self.assertEqual(r.resolution_state('found',[],{})[0],'found')
        self.assertEqual(r.resolution_state('not_found',['a','b'],{'a':good,'b':{'state':'check_failed','diagnostics':''}})[0],'pending')
        self.assertEqual(r.resolution_state('not_found',['a','b'],{'a':good,'b':{'state':'output_invalid'}})[0],'pending')

    def test_frontend_error_limit_and_command_positions(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); directory=root/'runs/test'
            ref=r.audit.reference('Nat.add @ Mathlib/Dummy.lean')
            plan=dict(provenance={},resolver_sha256='hash',source_hashes={},probes=[ref],jobs=[dict(id='one',modules=['Mathlib.Dummy'],references=[ref['id']])])
            calls=[]
            def call(root,command,out,err):
                calls.append(command);out.write_text('');err.write_text('');return 0
            with patch.object(r,'ROOT',root), patch.object(r.audit,'provenance',return_value={}), patch.object(r.audit,'digest',return_value='hash'), patch.object(r.audit,'inspect_builds',return_value='ready'), patch.object(r.audit,'call',side_effect=call):
                r.run(directory,plan)
            self.assertIn('-DmaxErrors=0',calls[-1])
            import json
            commands=json.loads((directory/'modules/one/commands.json').read_text())
            lines=(directory/'modules/one/Check.lean').read_text().splitlines()
            self.assertEqual(lines[commands[ref['id']]['check_line']-1],'#check @Nat.add')
            self.assertEqual(lines[commands[ref['id']]['axioms_line']-1],'#print axioms Nat.add')

    def test_inline_open(self):
        _, ds=r.scopes('namespace A\nopen B in lemma foo : True := by trivial\nlemma bar : True := by trivial\nend A\n')
        self.assertEqual(ds[0]['context']['opens'],['B'])
        self.assertEqual(ds[1]['context']['opens'],[])


if __name__=='__main__': unittest.main()
