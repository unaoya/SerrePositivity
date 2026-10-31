"""§10.10: position-backed names, attribute routing, and local command wrappers."""
import tempfile
from pathlib import Path
import unittest
from lean_source import parse_source,render,check_attribute_dependencies,Unsupported
from split_module import prepare

MODULE='SerrePositivity.Sample'

def snapshot(text, names):
    return {'sources':[{'module':MODULE,'source':text}], 'declarations':[
        {'name':name,'module':MODULE,'environment_parent':parent,'parent_module':MODULE if parent else None,
         'source_range':{'start_line':line,'end_line':line,'selection_start_line':line,'selection_end_line':line},
         'attributes':{'simp':False,'instance_priority':None},'used_constants':[]}
        for name,line,parent in names]}

class PositionTests(unittest.TestCase):
    def test_anonymous_environment_name_and_auxiliary(self):
        text='namespace N\nlocal instance : Inhabited Nat := ⟨0⟩\ndef keep := 1\nend N\n'
        snap=snapshot(text,[('N.instInhabitedNat',2,None),('N.instInhabitedNat._proof_1',2,'N.instInhabitedNat'),('N.keep',3,None)])
        src=parse_source(text,snapshot=snap,module=MODULE)
        self.assertEqual(set(src.declarations),{'N.instInhabitedNat','N.keep'})
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);p=root/'SerrePositivity/Sample.lean';p.parent.mkdir();p.write_text(text)
            plan=prepare(root,MODULE,'SerrePositivity.Dest',{'N.instInhabitedNat'},snap,{MODULE:set()})
            self.assertIn('local instance : Inhabited Nat',plan['changes']['SerrePositivity.Dest']['after'])
            self.assertNotIn('local instance',plan['changes'][MODULE]['after'])
            self.assertEqual(p.read_text(),text)
    def test_anonymous_ambiguous_or_missing_position_stops(self):
        text='instance : Inhabited Nat := ⟨0⟩\n'
        for rows in [[],[('instA',1,None),('instB',1,None)],[('instA',5,None)]]:
            with self.assertRaisesRegex(Unsupported,'source position'):
                parse_source(text,snapshot=snapshot(text,rows),module=MODULE)
    def test_named_position_mismatch_stops(self):
        with self.assertRaisesRegex(Unsupported,'disagrees'):
            parse_source('def a := 1\n',snapshot=snapshot('def a := 1\n',[('b',1,None)]),module=MODULE)
    def test_internal_attributes_follow_target_and_keep_order(self):
        text='namespace N\nclass C where\n  x : Nat\ndef kept := 1\nattribute [instance] C.x\nattribute [-simp] C.x\nend N\n'
        src=parse_source(text);moved=render(src,{'N.C'},side='moved');kept=render(src,{'N.kept'})
        self.assertIn('  x : Nat\nattribute [instance] C.x\nattribute [-simp] C.x\n',moved)
        self.assertNotIn('attribute',kept)
    def test_attribute_targets_are_partitioned(self):
        src=parse_source('def a := 1\ndef b := 2\nattribute [simp] a b\n')
        self.assertIn('attribute [simp] a',render(src,{'a'}));self.assertNotIn('attribute [simp] b',render(src,{'a'}))
    def test_external_local_and_scoped_preserve_section(self):
        for kind in ('local','scoped'):
            text=f'section Local\nattribute [{kind} simp] External.f\ndef a := 1\ndef b := 2\nend Local\n'
            src=parse_source(text);check_attribute_dependencies(src,{'b'})
            for selected,side in [({'a'},'keep'),({'b'},'moved')]:
                result=render(src,selected,side=side)
                self.assertIn(f'section Local\nattribute [{kind} simp] External.f\n',result)
                self.assertTrue(result.endswith('end Local\n'))
    def test_external_global_stops_before_any_write(self):
        for spec in ('instance','-simp'):
            text=f'attribute [{spec}] External.f\ndef keep := 1\ndef moved := 2\n'
            snap=snapshot(text,[('keep',2,None),('moved',3,None)])
            with tempfile.TemporaryDirectory() as td:
                root=Path(td);p=root/'SerrePositivity/Sample.lean';p.parent.mkdir();p.write_text(text)
                with self.assertRaisesRegex(Unsupported,'external global attribute'):
                    prepare(root,MODULE,'SerrePositivity.Dest',{'moved'},snap,{MODULE:set()})
                self.assertEqual(p.read_text(),text);self.assertFalse((root/'SerrePositivity/Dest.lean').exists())
    def test_external_global_persists_past_section(self):
        src=parse_source('section S\nattribute [instance] External.f\nend S\ndef moved := 1\n')
        with self.assertRaisesRegex(Unsupported,'external global attribute'):
            check_attribute_dependencies(src,{'moved'})
    def test_mixed_attribute_specs_refused(self):
        with self.assertRaisesRegex(Unsupported,'multiple attribute'):
            parse_source('attribute [local simp, instance] External.f\ndef a := 1\n')
    def test_external_global_after_moved_stays_keep_only(self):
        src=parse_source('def moved := 1\nattribute [instance] External.f\ndef kept := 2\n')
        check_attribute_dependencies(src,{'moved'})
        self.assertNotIn('attribute',render(src,{'moved'},side='moved'))
        self.assertIn('attribute [instance]',render(src,{'kept'},side='keep'))
    def test_internal_attribute_different_scope_stops(self):
        with self.assertRaisesRegex(Unsupported,'different scopes'):
            parse_source('def a := 1\nsection S\nattribute [local simp] a\nend S\n')
    def test_prefix_wrappers_follow_declaration(self):
        for prefix in ('open Nat in','set_option pp.universes true in','variable (n : Nat) in'):
            for sep in ('\n',' '):
                text='def keep := 0\n'+prefix+sep+'def moved := 1\n'
                src=parse_source(text)
                self.assertIn(prefix+sep+'def moved := 1',render(src,{'moved'},side='moved'))
                self.assertNotIn(prefix,render(src,{'keep'}))
    def test_include_context_stays_in_section(self):
        src=parse_source('section S\nvariable (h : True)\ninclude h\ntheorem a : True := h\ntheorem b : True := h\nend S\n')
        for name in ('a','b'):self.assertIn('include h\n',render(src,{name}))

if __name__=='__main__':unittest.main()
