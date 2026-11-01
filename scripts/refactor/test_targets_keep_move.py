"""§10.30: allow only split then keep move, preserving simulated dependencies."""
import copy
from pathlib import Path
import tempfile
import unittest
from validate_targets import validate

A='SerrePositivity.Input.A'
B='SerrePositivity.ModelOutput.B'
K='SerrePositivity.InfinityCategories.Core.Keep'
C='SerrePositivity.Input.Consumer'

class KeepMoveTests(unittest.TestCase):
    def setUp(self):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup)
        self.root=Path(tmp.name)
        source='module\npublic import Mathlib\n@[expose] public section\ndef a : Nat := 1\ndef b : Nat := a\n'
        for module,text in [(A,source),(C,'import '+A+'\n')]:
            p=self.root/(module.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
        self.snapshot={'sources':[{'module':A,'source':source}], 'declarations':[
            {'name':n,'module':A,'used_constants':uses,'attributes':{'simp':False,'instance_priority':None}}
            for n,uses in [('a',[]),('b',['a'])]]}
        self.split=dict(module=A,action='split',dest=B,moved=['b'],keep=['a'],attributes={},candidate='test',note='synthetic graph',imports={A:[],B:[A]})
        self.move=dict(module=A,action='move',dest=K,moved=[],keep=[],attributes={},candidate='test',note='keep side',imports={K:['Mathlib.Data.Nat.Basic']})
    def test_split_then_keep_move_composes_graph(self):
        result,before,after,_,_=validate(self.root,[self.split,self.move],{A:self.snapshot},return_graph=True)
        self.assertEqual(result['status'],'PASS')
        self.assertEqual(result['target_count'],2)
        self.assertEqual(before[C],{A})
        self.assertNotIn(A,after)
        self.assertEqual(after[K],{'Mathlib.Data.Nat.Basic'})
        self.assertEqual(after[B],{K})
        self.assertEqual(after[C],{K})
        self.assertTrue(result['split_directions'][0]['moved_to_keep'])
        self.assertTrue((self.root/(A.replace('.','/')+'.lean')).exists())
        self.assertFalse((self.root/(K.replace('.','/')+'.lean')).exists())
    def test_other_duplicate_combinations_rejected(self):
        for actions in [('move','move'),('split','split'),('move','split'),('split','move','move'),('split','archive'),('split','reimport')]:
            with self.subTest(actions=actions):
                entries=[]
                for i,action in enumerate(actions):
                    e=copy.deepcopy(self.split if action=='split' else self.move)
                    e['action']=action
                    if action=='reimport':e.update(dest=A,imports={A:[]})
                    elif action=='archive':e.pop('imports')
                    entries.append(e)
                with self.assertRaisesRegex(ValueError,'duplicate module'):
                    validate(self.root,entries,{A:self.snapshot})
