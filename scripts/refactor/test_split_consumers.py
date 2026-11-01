"""§10.14: consumer imports require failed-build evidence; core repairs stop."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import layer_check as lc
from split_module import ROOT, prepare, downstream_repair_snapshot
from prune_imports import prune_plan
from lean_source import Unsupported
from validate_targets import validate

CONFIG=json.loads((ROOT/'scripts/refactor/layers.json').read_text())
A='SerrePositivity.HomotopicalAlgebra.Sample'
B='SerrePositivity.InfinityCategories.ModelBridge.Sample'
CORE='SerrePositivity.InfinityCategories.F2.Consumer'
NONCORE='SerrePositivity.HomotopicalAlgebra.Consumer'

class ConsumerTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.source='module\npublic import Mathlib\n@[expose] public section\ndef kept : Nat := 1\ndef moved : Nat := 2\n'
        self.write(A,self.source)
        self.snap={'sources':[{'module':A,'source':self.source}], 'declarations':[
            {'name':n,'module':A,'used_constants':[], 'used_modules':['Mathlib'],
             'attributes':{'simp':False,'instance_priority':None}} for n in ('kept','moved')]}
    def write(self,module,text):
        p=self.root/(module.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text);return p
    def test_core_public_export_and_explicit_use_are_not_auto_repaired(self):
        source='module\npublic import '+A+'\n@[expose] public section\ndef use : Nat := moved\n'
        path=self.write(CORE,source)
        plan=prepare(self.root,A,B,['moved'],self.snap,{CORE:{A},A:{'Mathlib'}})
        self.assertEqual(set(plan['changes']),{A,B})
        entry=dict(module=A,dest=B,action='split',moved=['moved'],keep=['kept'],attributes={},candidate='test',note='synthetic')
        result,_,after,_,_=validate(self.root,[entry],{A:self.snap},return_graph=True)
        self.assertEqual(after[CORE],{A});self.assertEqual(result['consumer_import_additions'],{})
        self.assertEqual(path.read_text(),source)
    def run_failed_repair(self,consumer):
        source='import '+A+'\ndef use : Nat := moved\n'
        path=self.write(consumer,source)
        baseline={'declarations':[{'name':'use','module':consumer,'used_constants':['moved'],
            'used_modules':[A],'source_range':{'start_line':2,'end_line':2}}]}
        plan=prepare(self.root,A,B,['moved'],self.snap,{})
        # Exercise the real downstream build/repair/restoration control flow,
        # with pruning already done and every Lean invocation replaced by a fake.
        plan['prune_modules']=[]
        (self.root/'.lake/verify').mkdir(parents=True)
        cfg=self.root/'scripts/refactor/layers.json';cfg.parent.mkdir(parents=True);cfg.write_text(json.dumps(CONFIG))
        error='error: '+consumer.replace('.','/')+'.lean:2:18: Unknown identifier `moved`\n'
        commands=[];attempts=[]
        def invoke(args,**kwargs):
            commands.append(args)
            if '--output' in args: Path(args[args.index('--output')+1]).write_text(json.dumps(baseline))
            return 0
        class Process:
            def __init__(self,args,**kwargs):
                commands.append(args);self.rc=1 if not attempts else 0;attempts.append(self.rc)
                if self.rc: kwargs['stdout'].write(error)
            def poll(self):return self.rc
            def wait(self):return self.rc
        graph={A:{'Mathlib'},consumer:{A}}
        with patch('prune_imports.lc.read_graph',return_value=(graph,set())), \
             patch('prune_imports.affected_modules',return_value=[consumer]), \
             patch('prune_imports.subprocess.call',side_effect=invoke), \
             patch('prune_imports.subprocess.Popen',side_effect=Process), \
             patch('prune_imports.compare',return_value={'status':'PASS'}):
            if lc.classify(consumer,CONFIG) in CONFIG['core']:
                with self.assertRaisesRegex(Unsupported,'core downstream repair forbidden') as exc:
                    prune_plan(self.root,plan,self.snap)
                detail=json.loads(str(exc.exception).split(': ',1)[1])
                self.assertEqual(detail['consumer'],consumer)
                self.assertEqual(detail['failed_declarations'][0]['declarations'],['use'])
                self.assertEqual(detail['used_moved_declarations'],{'use':['moved']})
                self.assertNotIn(consumer,plan['changes']);self.assertEqual(attempts,[1])
            else:
                result=prune_plan(self.root,plan,self.snap)
                self.assertEqual(result['downstream_imports'],{consumer:[B]})
                self.assertEqual(attempts,[1,0])
        self.assertEqual(path.read_text(),source)
        self.assertEqual((self.root/(A.replace('.','/')+'.lean')).read_text(),self.source)
        self.assertFalse((self.root/(B.replace('.','/')+'.lean')).exists())
        report=json.loads(next((self.root/'.lake/verify').glob('prune-*/results.json')).read_text())
        self.assertTrue(report['sources_restored'])
        return report
    def test_failed_build_stops_before_core_import_write_and_restores(self):
        report=self.run_failed_repair(CORE)
        self.assertEqual(report['status'],'FAIL');self.assertEqual(report['downstream_imports'],{})
    def test_failed_noncore_build_repairs_only_used_destination_and_restores(self):
        self.assertEqual(self.run_failed_repair(NONCORE)['status'],'PASS')
    def test_every_core_layer_stops(self):
        for layer in CONFIG['layers']:
            if layer['name'] not in CONFIG['core']:continue
            with self.subTest(layer=layer['name']), self.assertRaisesRegex(Unsupported,'core downstream'):
                downstream_repair_snapshot(layer['prefixes'][0]+'.Consumer',{'declarations':[]},
                    {'moved':[]},self.snap,'unlocated diagnostic',CONFIG)
    def test_unused_moved_constant_does_not_require_destination(self):
        baseline={'declarations':[{'name':'use','used_constants':['kept'],'used_modules':[A]}]}
        result=downstream_repair_snapshot(NONCORE,baseline,prepare(self.root,A,B,['moved'],self.snap,{}),self.snap,'',CONFIG)
        self.assertEqual(result,baseline)

if __name__=='__main__':unittest.main()
