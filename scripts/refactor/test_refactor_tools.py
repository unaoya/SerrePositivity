"""分割の文字列保存・依存方向・拒否と、比較の名前対応を検証する。"""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from lean_source import parse_source, render, Unsupported, dependency_directions, add_import
from split_module import prepare
from compare_snapshots import compare
from validate_targets import simulated_model_mentions

SOURCE='''module
public import Lean
@[expose] public section
namespace Outer
namespace Inner
universe u
variable (n : Nat)
/-- A preserved docstring with /- a nested comment -/. -/
@[simp] theorem keep : n = n := rfl
section Local
variable (b : Bool)
include b in
/-- Move this declaration unchanged. -/
def moved : Bool := b
end Local
end Inner
end Outer
'''


class RefactorTests(unittest.TestCase):
    def test_model_mentions_use_destination_prefix(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            outside='SerrePositivity.Other.Model'
            inside='SerrePositivity.HomotopicalAlgebra.Model'
            for name in [outside,inside]:
                path=root/(name.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True)
                path.write_text('variable [ModelCategory C]\n')
            config={'model_category_rule':{'prefix':'SerrePositivity.HomotopicalAlgebra','code_contains':'ModelCategory'}}
            self.assertEqual(simulated_model_mentions(root,{inside},{inside:outside},{},config),set())
            self.assertEqual(simulated_model_mentions(root,set(),{outside:inside},{},config),{inside})

    def test_scopes_docstrings_attributes_are_unchanged(self):
        p=parse_source(SOURCE)
        self.assertEqual(set(p.declarations),{'Outer.Inner.keep','Outer.Inner.moved'})
        out=render(p,{'Outer.Inner.moved'})
        self.assertEqual(set(parse_source(out).declarations),{'Outer.Inner.moved'})
        self.assertIn(p.commands[p.declarations['Outer.Inner.moved']].text,out)
        self.assertIn('namespace Outer\nnamespace Inner\n',out)
        self.assertIn('variable (b : Bool)',out)
        kept=render(p,{'Outer.Inner.keep'})
        self.assertNotIn('variable (b : Bool)',kept)
        self.assertIn('/-- A preserved docstring with /- a nested comment -/. -/\n@[simp]',kept)

    def test_reject_mutual_local_variable_and_unnamed_instance(self):
        for source in ['mutual\ndef a := 1\nend\n', 'instance : Inhabited Bool := ⟨false⟩\n']:
            with self.assertRaises(Unsupported): parse_source(source)

    def test_dependency_directions_include_proof_dependencies(self):
        p=parse_source('def a := 1\ntheorem b : a = 1 := rfl\n')
        forward,backward=dependency_directions(p,{'b'},{'declarations':[
            {'name':'a','used_constants':[]},{'name':'b','used_constants':['a']}]})
        self.assertEqual(forward,[('b','a')]);self.assertEqual(backward,[])

    def test_indented_commands_are_not_silently_copied(self):
        for source in ['namespace N\n  def hidden := 1\ndef visible := 2\nend N\n',
                       'def first := 1\n  @[simp] theorem hidden : True := trivial\ndef second := 2\n',
                       'namespace N\ndef visible := 1\n  end N\n']:
            with self.assertRaisesRegex(Unsupported, 'indented command'):
                parse_source(source)

    def test_generated_simp_declaration_does_not_add_consumer_import(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);src=root/'SerrePositivity/A.lean';src.parent.mkdir()
            text='def kept := 1\ndef moved := 2\n';src.write_text(text)
            consumer=root/'SerrePositivity/C.lean'
            consumer.write_text('import SerrePositivity.A\nexample : True := by simp\n')
            attrs={'simp':False,'instance_priority':None}
            snap={'sources':[{'module':'SerrePositivity.A','source':text}], 'declarations':[
                {'name':n,'module':'SerrePositivity.A','used_constants':[],
                 'attributes':{**attrs,'simp':n=='moved.generated'}} for n in ['kept','moved','moved.generated']]}
            plan=prepare(root,'SerrePositivity.A','SerrePositivity.B',{'moved'},snap,
                         {'SerrePositivity.A':set(),'SerrePositivity.C':{'SerrePositivity.A'}})
            self.assertEqual(set(plan['changes']),{'SerrePositivity.A','SerrePositivity.B'})
            self.assertEqual(consumer.read_text(),'import SerrePositivity.A\nexample : True := by simp\n')

    def test_prepare_bidirectional_refusal_is_read_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);src=root/'SerrePositivity/A.lean';src.parent.mkdir()
            text='def a : Nat := 1\ndef b : Nat := 2\n';src.write_text(text)
            snap={'sources':[{'module':'SerrePositivity.A','source':text}], 'declarations':[
                {'name':'a','module':'SerrePositivity.A','used_constants':['b']},
                {'name':'b','module':'SerrePositivity.A','used_constants':['a']}]}
            with self.assertRaisesRegex(Unsupported,'bidirectional'):
                prepare(root,'SerrePositivity.A','SerrePositivity.B',{'b'},snap,{'SerrePositivity.A':set()})
            self.assertEqual(src.read_text(),text);self.assertFalse((root/'SerrePositivity/B.lean').exists())

    def test_import_insertion_preserves_existing_bytes(self):
        out=add_import(SOURCE,'SerrePositivity.New')
        self.assertEqual(out.replace('public import SerrePositivity.New\n','',1),SOURCE)
        self.assertEqual(add_import(out,'SerrePositivity.New'),out)

    def test_crlf_declarations_are_preserved(self):
        original=SOURCE.replace('\n','\r\n')
        parsed=parse_source(original)
        selected={'Outer.Inner.moved'}
        out=add_import(render(parsed,selected),'SerrePositivity.New')
        self.assertIn(parsed.commands[parsed.declarations['Outer.Inner.moved']].text,out)
        self.assertIn('public import SerrePositivity.New\r\n',out)

    def test_proof_auxiliaries_are_grouped_but_definition_auxiliaries_checked(self):
        root={'name':'f','parent':'f','kind':'theorem','type':['const','True',[]],
              'body':None,'axioms':[],'attributes':{}}
        aux={**root,'name':'f._proof_1','parent':'f'}
        self.assertEqual(compare({'schema_version':1,'declarations':[root,aux]},
                                 {'schema_version':1,'declarations':[root]})['status'],'PASS')
        root={**root,'kind':'def','body':['nat',1]}
        self.assertEqual(compare({'schema_version':1,'declarations':[root,aux]},
                                 {'schema_version':1,'declarations':[root]})['status'],'FAIL')

    def test_comparison_does_not_rename_string_literals(self):
        row={'name':'Old.f','parent':'Old.f','kind':'def','type':['const','Old.T',[]],
             'body':['string','Old.literal'],'axioms':[],'attributes':{}}
        before={'schema_version':1,'declarations':[row]}
        other=copy.deepcopy(row);other.update(name='New.f',parent='New.f',type=['const','New.T',[]])
        self.assertEqual(compare(before,{'schema_version':1,'declarations':[other]},{'Old':'New'})['status'],'PASS')
        other['body']=['string','New.literal']
        self.assertEqual(compare(before,{'schema_version':1,'declarations':[other]},{'Old':'New'})['changes'][0]['change'],'body')


if __name__=='__main__': unittest.main(verbosity=2)
