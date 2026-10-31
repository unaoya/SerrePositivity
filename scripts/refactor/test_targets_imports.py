"""IF-W0-3: imports の型、依存方向、閉包模擬を独立した小さいグラフで検査。"""
import copy
from pathlib import Path
import tempfile
import unittest
from validate_targets import validate, split_imports

A='SerrePositivity.DerivedInput.A'
B='SerrePositivity.InfinityCategories.Core.SplitA'
DG='SerrePositivity.DifferentialGraded.Dependency'

class ImportsTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.source='module\npublic import '+DG+'\n@[expose] public section\ndef a : Nat := 1\ndef b : Nat := 2\n'
        for m,text in [(A,self.source),(DG,'def dep : Nat := 0\n')]:
            p=self.root/(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
        self.snapshot={'sources':[{'module':A,'source':self.source}], 'declarations':[
            {'name':n,'module':A,'used_constants':[], 'attributes':{'simp':False,'instance_priority':None}} for n in ('a','b')]}
        self.entry=dict(module=A,dest=B,action='split',moved=['b'],keep=['a'],attributes={},candidate='test',note='synthetic graph; not Lean compilation evidence')
    def check(self,entry=None):return validate(self.root,[entry or self.entry],{A:self.snapshot})
    def imports(self,a=None,b=None):
        self.entry['imports']={A:['Mathlib.Data.Nat.Basic'] if a is None else a,B:['Mathlib.Data.Nat.Basic'] if b is None else b}
    def test_optional_omission_preserves_old_forbidden_import(self):
        self.assertEqual(self.check()['status'],'FAIL')
    def test_exact_override_removes_banned_edge_without_source_edit(self):
        self.imports();r=self.check();self.assertEqual(r['status'],'PASS')
        self.assertEqual(r['after']['closure']['W1'],0)
        self.assertEqual(r['after']['entry_edges']['W1'],[])
        self.assertEqual((self.root/(A.replace('.','/')+'.lean')).read_text(),self.source)
    def test_missing_key(self):
        self.imports();del self.entry['imports'][A]
        with self.assertRaisesRegex(ValueError,'exactly'):self.check()
    def test_extra_key(self):
        self.imports();self.entry['imports'][DG]=[]
        with self.assertRaisesRegex(ValueError,'exactly'):self.check()
    def test_non_dictionary(self):
        self.entry['imports']=[]
        with self.assertRaisesRegex(ValueError,'exactly'):self.check()
    def test_string_not_array(self):
        self.imports();self.entry['imports'][A]='Mathlib'
        with self.assertRaisesRegex(ValueError,'arrays'):self.check()
    def test_bad_name(self):
        self.imports(b=['Mathlib; bad'])
        with self.assertRaisesRegex(ValueError,'arrays'):self.check()
    def test_duplicates(self):
        self.imports(b=['Mathlib','Mathlib'])
        with self.assertRaisesRegex(ValueError,'duplicate import'):self.check()
    def test_self_import(self):
        self.imports(b=[B])
        with self.assertRaisesRegex(ValueError,'self import'):self.check()
    def test_missing_module(self):
        self.imports(b=['SerrePositivity.NoSuchModule'])
        with self.assertRaisesRegex(ValueError,'missing project'):self.check()
    def test_import_cycle(self):
        self.imports(a=[B],b=[A])
        with self.assertRaisesRegex(ValueError,'import cycle'):self.check()
    def test_moved_to_keep_must_remain(self):
        self.snapshot['declarations'][1]['used_constants']=['a'];self.imports()
        with self.assertRaisesRegex(ValueError,'moved-to-keep'):self.check()
    def test_keep_to_moved_must_remain(self):
        self.snapshot['declarations'][0]['used_constants']=['b'];self.imports()
        with self.assertRaisesRegex(ValueError,'keep-to-moved'):self.check()
    def test_move_override(self):
        self.entry.update(action='move',moved=[],keep=[],imports={B:['Mathlib.Data.Nat.Basic']})
        result,before,after,_,_=validate(self.root,[self.entry],return_graph=True)
        self.assertEqual(result['status'],'PASS')
        self.assertNotIn(A,after)
        self.assertEqual(after[B],{'Mathlib.Data.Nat.Basic'})
        self.assertIn(DG,before[A])
    def test_move_only_destination_key(self):
        self.imports();self.entry.update(action='move',moved=[],keep=[])
        with self.assertRaisesRegex(ValueError,'exactly the destination'):self.check()
    def test_move_old_name_self_reference(self):
        self.entry.update(action='move',moved=[],keep=[],imports={B:[A]})
        with self.assertRaisesRegex(ValueError,'self import'):self.check()
    def test_move_import_cycle(self):
        path=self.root/(A.replace('.','/')+'.lean');path.write_text('import Mathlib\ndef a := 1\n')
        (self.root/(DG.replace('.','/')+'.lean')).write_text('import '+A+'\ndef dep := 0\n')
        self.entry.update(action='move',moved=[],keep=[],imports={B:[DG]})
        with self.assertRaisesRegex(ValueError,'import cycle'):self.check()
    def test_archive_rejects_imports(self):
        self.entry.update(action='archive',moved=[],keep=[],imports={B:[]})
        with self.assertRaisesRegex(ValueError,'only valid'):self.check()
    def test_consumer_addition_composes_with_another_split_body(self):
        c='SerrePositivity.DerivedInput.C';d='SerrePositivity.InfinityCategories.Core.SplitC'
        source='module\npublic import '+A+'\n@[expose] public section\ndef c : Nat := 3\ndef d : Nat := 4\n'
        path=self.root/(c.replace('.','/')+'.lean');path.write_text(source)
        snap={'sources':[{'module':c,'source':source}], 'declarations':[
            {'name':n,'module':c,'used_constants':[], 'attributes':{'simp':False,'instance_priority':None}} for n in ('c','d')]}
        other=dict(module=c,dest=d,action='split',moved=['c'],keep=['d'],attributes={},candidate='test',note='test',imports={c:[A],d:['Mathlib']})
        self.imports()
        result,_,after,_,_=validate(self.root,[self.entry,other],{A:self.snapshot,c:snap},return_graph=True)
        self.assertEqual(result['status'],'PASS')
        self.assertEqual(after[c],{A,B})
        self.assertEqual(result['consumer_import_additions'][c],[B])
        self.assertEqual(path.read_text(),source)
    def test_unknown_field(self):
        self.entry['improts']={}
        with self.assertRaisesRegex(ValueError,'required fields'):self.check()
    def test_rename_after_import_override(self):
        self.imports(b=[DG]);move=dict(module=DG,dest='SerrePositivity.InfinityCategories.Core.Dependency',action='move',moved=[],keep=[],attributes={},candidate='test',note='test')
        r=validate(self.root,[self.entry,move],{A:self.snapshot})
        self.assertEqual(r['status'],'PASS')

class DownstreamImportsTests(unittest.TestCase):
    check=ImportsTests.check
    def setUp(self):
        ImportsTests.setUp(self)
        self.entry.update(action='move',moved=[],keep=[],imports={B:['Mathlib']})
        self.user='SerrePositivity.DerivedInput.User'
        path=self.root/(self.user.replace('.','/')+'.lean');path.write_text('import '+A+'\n')
    # Only additional tests are defined here; inherited split-specific cases stay in ImportsTests.
    def test_downstream_addition_survives_rename(self):
        self.entry['downstream_imports']={self.user:[DG]}
        result,_,after,_,_=validate(self.root,[self.entry],return_graph=True)
        self.assertEqual(after[self.user],{B,DG})
        self.assertEqual(result['downstream_imports'],{self.user:[DG]})
    def test_bad_downstream_map(self):
        self.entry['downstream_imports']=[]
        with self.assertRaisesRegex(ValueError,'module map'):self.check()
    def test_missing_downstream_consumer(self):
        self.entry['downstream_imports']={'SerrePositivity.Missing':[DG]}
        with self.assertRaisesRegex(ValueError,'missing downstream'):self.check()
    def test_missing_downstream_dependency(self):
        self.entry['downstream_imports']={self.user:['SerrePositivity.Missing']}
        with self.assertRaisesRegex(ValueError,'missing project'):self.check()
    def test_downstream_cycle_rejected(self):
        self.entry['downstream_imports']={DG:[self.user],self.user:[DG]}
        with self.assertRaisesRegex(ValueError,'cycle'):self.check()
    def test_downstream_self_reference(self):
        self.entry['downstream_imports']={self.user:[self.user]}
        with self.assertRaisesRegex(ValueError,'self downstream'):self.check()
    def test_archive_rejects_downstream_field(self):
        self.entry.update(action='archive',downstream_imports={})
        self.entry.pop('imports')
        with self.assertRaisesRegex(ValueError,'requires move, split or reimport'):self.check()
    def test_downstream_duplicate(self):
        self.entry['downstream_imports']={self.user:[DG,DG]}
        with self.assertRaisesRegex(ValueError,'duplicate'):self.check()

class ReimportTests(unittest.TestCase):
    def setUp(self):
        ImportsTests.setUp(self)
        self.entry.update(action='reimport',dest=A,moved=[],keep=[],imports={A:['Mathlib']})
    check=ImportsTests.check
    def test_replaces_without_rename_or_snapshot(self):
        r,b,a,_,_=validate(self.root,[self.entry],return_graph=True)
        self.assertEqual(r['status'],'PASS');self.assertEqual(a[A],{'Mathlib'})
        self.assertIn(DG,b[A]);self.assertNotIn(B,a)
    def test_requires_imports(self):
        self.entry.pop('imports')
        with self.assertRaisesRegex(ValueError,'requires imports'):self.check()
    def test_requires_same_destination(self):
        self.entry.update(dest=B,imports={B:[]})
        with self.assertRaisesRegex(ValueError,'dest equal'):self.check()
    def test_empty_declarations(self):
        self.entry['moved']=['a']
        with self.assertRaisesRegex(ValueError,'empty moved'):self.check()
    def test_duplicate_module(self):
        with self.assertRaisesRegex(ValueError,'duplicate module'):validate(self.root,[self.entry,self.entry])
    def test_cycle(self):
        self.entry['imports']={A:[DG]};self.entry['downstream_imports']={DG:[A]}
        with self.assertRaisesRegex(ValueError,'cycle'):self.check()
    def test_downstream_and_move_composition(self):
        self.entry['downstream_imports']={DG:['Mathlib.Order.Basic']}
        move=dict(module=DG,action='move',dest=B,moved=[],keep=[],attributes={},candidate='test',note='test')
        self.entry['imports']={A:[DG]}
        _,_,a,_,_=validate(self.root,[self.entry,move],return_graph=True)
        self.assertEqual(a[A],{B});self.assertIn('Mathlib.Order.Basic',a[B])
    def test_root_reimport(self):
        (self.root/'SerrePositivity.lean').write_text('import '+A+'\n')
        self.entry.update(module='SerrePositivity',dest='SerrePositivity',imports={'SerrePositivity':[DG]})
        _,_,a,_,_=validate(self.root,[self.entry],return_graph=True)
        self.assertEqual(a['SerrePositivity'],{DG})

if __name__=='__main__':unittest.main()
