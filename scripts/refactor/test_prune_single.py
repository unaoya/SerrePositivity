"""Single-module pruning plans reject stale sources and unrelated declarations."""
import tempfile
from pathlib import Path
import unittest
from prune_imports import single_module_plan, missing_direct_imports, failed_modules

class SinglePruneTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.module='SerrePositivity.A'
        p=self.root/'SerrePositivity/A.lean';p.parent.mkdir();p.write_text('import Lean\n')
        self.snapshot={'sources':[{'module':self.module,'source':'import Lean\n'}], 'declarations':[]}
    def test_empty_module_is_supported(self):
        plan=single_module_plan(self.root,self.module,self.snapshot)
        self.assertEqual(plan['prune_modules'],[self.module])
        self.assertEqual(plan['declaration_modules'],{})
        self.assertEqual(plan['changes'][self.module]['before'],plan['changes'][self.module]['after'])
    def test_stale_source_rejected(self):
        self.snapshot['sources'][0]['source']='import Init\n'
        with self.assertRaisesRegex(ValueError,'source does not match'):
            single_module_plan(self.root,self.module,self.snapshot)
    def test_unrelated_declaration_rejected(self):
        self.snapshot['declarations']=[{'module':'SerrePositivity.B','name':'b'}]
        with self.assertRaisesRegex(ValueError,'another module'):
            single_module_plan(self.root,self.module,self.snapshot)

class DownstreamTests(unittest.TestCase):
    def test_only_missing_used_modules_are_added(self):
        p='SerrePositivity.'
        graph={p+'User':{p+'Pruned'},p+'Pruned':{p+'Core'},p+'Core':set(),p+'Lost':{p+'Nested'},p+'Nested':set()}
        snap={'declarations':[{'used_modules':[p+'User',p+'Core',p+'Lost',p+'Nested']}]}
        self.assertEqual(missing_direct_imports(graph,p+'User',snap),{p+'Lost'})
    def test_no_missing_dependency(self):
        self.assertEqual(missing_direct_imports({'A':{'B'}},'A',{'declarations':[{'used_modules':['A','B']}]}),set())
    def test_cycle_is_rejected(self):
        with self.assertRaisesRegex(ValueError,'cycle'):
            missing_direct_imports({'A':set(),'SerrePositivity.B':{'A'}},'A',{'declarations':[{'used_modules':['SerrePositivity.B']}]})
    def test_entire_log_failure_detection(self):
        text='error: SerrePositivity/X/Y.lean:20:3: Unknown identifier `x`\n'+'build succeeded\n'*100
        self.assertEqual(failed_modules(text),['SerrePositivity.X.Y'])

class CandidateFallbackTests(unittest.TestCase):
    def test_underestimated_minimports_is_checked_then_original_imports_minimized(self):
        import json
        from unittest.mock import patch
        from prune_imports import prune_plan
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); module='SerrePositivity.A'
            source='import Mathlib.Required\nimport Mathlib.Redundant\n'
            path=root/'SerrePositivity/A.lean';path.parent.mkdir();path.write_text(source)
            (root/'.lake/verify').mkdir(parents=True)
            (root/'scripts/refactor').mkdir(parents=True)
            (root/'scripts/refactor/layers.json').write_text('{}')
            snap={'count':0,'declarations':[],'sources':[{'module':module,'source':source}]}
            plan=single_module_plan(root,module,snap)
            graph={module:{'Mathlib.Required','Mathlib.Redundant'}}
            def invoke(args,**kwargs):
                if '--output' in args:
                    Path(args[args.index('--output')+1]).write_text(json.dumps(snap));return 0
                if args[:3]==['lake','env','lean']:
                    text=path.read_text()
                    if '#min_imports' in text:
                        kwargs['stdout'].write("Counting imports from here.\nunneeded import 'Mathlib.Required'\n")
                        return 0
                    return 0 if 'import Mathlib.Required\n' in text else 1
                return 0
            with patch('prune_imports.lc.read_graph',return_value=(graph,set())), \
                 patch('prune_imports.affected_modules',return_value=[]), \
                 patch('prune_imports.subprocess.call',side_effect=invoke), \
                 patch('prune_imports.compare',return_value={'status':'PASS'}):
                result=prune_plan(root,plan,snap)
            report=result['pruning']
            self.assertEqual(report['status'],'PASS')
            self.assertTrue(report['modules'][module]['min_imports_fallback'])
            self.assertEqual(report['modules'][module]['after'],['Mathlib.Required'])
            self.assertEqual(path.read_text(),source)
            labels={c['label']:c for c in report['commands']}
            self.assertEqual(labels['candidate']['exit_code'],1)
            self.assertEqual(labels['candidate-original-imports']['exit_code'],0)
            self.assertTrue(report['sources_restored'])

if __name__=='__main__':unittest.main()
