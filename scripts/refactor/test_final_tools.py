"""Regression tests for import-only rebasing, split documentation, and cache invalidation."""
import json
import contextlib
import io
import os
import threading
import time
from unittest.mock import patch
import verify_runner
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from rebase_helper import dirty_lean_files, rewrite
from split_module import module_doc
from prune_imports import replace_imports, affected_modules, preservation_dependencies
from verify_runner import cache_key, read_cache


class FinalToolsTests(unittest.TestCase):
    def test_preservation_dependencies_include_auxiliary_proofs(self):
        snapshot={'declarations':[
            {'name':'N.obj','parent':'N.obj','used_modules':['Original','Mathlib.Base']},
            {'name':'N.obj._proof_1','parent':'N.obj','used_modules':['Mathlib.Pasting']},
            {'name':'N.other','parent':'N.other','used_modules':['Unrelated']}]}
        self.assertEqual(preservation_dependencies(snapshot,[{'name':'N.obj','change':'auxiliaries'}],'Original'),
                         {'Mathlib.Base','Mathlib.Pasting'})
        del snapshot['declarations'][1]['used_modules']
        with self.assertRaisesRegex(ValueError,'regenerate the snapshot'):
            preservation_dependencies(snapshot,[{'name':'N.obj'}],'Original')

    def test_documentation_default_and_override(self):
        text='module\nimport Lean\n/-!\nOld module description.\n-/\n/-- Decl doc. -/\ndef f := 1\n'
        result=module_doc(text)
        self.assertIn('分割で生成：docstring を書き直すこと\nOld module description.',result)
        result=module_doc(text,'New module description.')
        self.assertNotIn('Old module description.',result)
        self.assertTrue(result.endswith('/-- Decl doc. -/\ndef f := 1\n'))

    def test_import_replacement_preserves_body_and_crlf(self):
        text='module\r\npublic import A\r\npublic import B\r\n/-! documentation -/\r\ndef f := 1\r\n'
        result=replace_imports(text,{'C'})
        self.assertEqual(result,'module\r\npublic import C\r\n/-! documentation -/\r\ndef f := 1\r\n')

    def test_pruning_refuses_import_visibility_changes(self):
        for line in ['private import A','meta import A','import A','public meta import A']:
            with self.assertRaisesRegex(ValueError,'pruning requires'):
                replace_imports('module\n'+line+'\ndef f := 1\n',{'B'})

    def test_transitive_downstream(self):
        graph={'SerrePositivity.A':set(),'SerrePositivity.B':{'SerrePositivity.A'},
               'SerrePositivity.C':{'SerrePositivity.B'},'SerrePositivity.D':set()}
        self.assertEqual(affected_modules(graph,{'SerrePositivity.A'}),sorted(graph)[:3])

    def test_rebase_changes_imports_only(self):
        source='module\npublic import Old.Module\n-- Old.Module\nnamespace Old.Module\ndef f := New.decl\ndef s := "Old.Module"\nend Old.Module\n'
        result=rewrite(source,{'Old.Module':'New.Module'},{'New.decl':'New.Split'})
        self.assertEqual(result.replace('public import New.Split\n','').replace('public import New.Module','public import Old.Module'),source)

    def test_dirty_discovery_ignores_clean_and_deleted_files(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            subprocess.run(['git','init','-q',str(root)],check=True)
            (root/'clean.lean').write_text('import Lean\n')
            (root/'dirty.lean').write_text('import Lean\n')
            (root/'deleted.lean').write_text('import Lean\n')
            subprocess.run(['git','add','.'],cwd=root,check=True)
            subprocess.run(['git','-c','user.name=Test','-c','user.email=test@example.invalid','-c','core.hooksPath=/dev/null','commit','-qm','fixture'],cwd=root,check=True)
            (root/'dirty.lean').write_text('import Lean\n-- modified\n')
            (root/'deleted.lean').unlink();(root/'untracked.lean').write_text('import Lean\n')
            self.assertEqual([p.name for p in dirty_lean_files(root)],['dirty.lean','untracked.lean'])

    def test_rebase_cli_dry_run_then_apply(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);subprocess.run(['git','init','-q',str(root)],check=True)
            source=root/'dirty.lean';source.write_text('import Old.Module\nexample := New.decl\n')
            moves=root/'moves.json';moves.write_text(json.dumps({'moves':{'Old.Module':'New.Module'}}))
            split=root/'split.json';split.write_text(json.dumps({'declaration_modules':{'New.decl':'New.Split'}}))
            cli=[sys.executable,str(Path(__file__).with_name('rebase_helper.py')),'--worktree',str(root),'--moves',str(moves),'--split',str(split)]
            before=source.read_bytes()
            subprocess.run(cli+['--dry-run'],check=True,capture_output=True)
            self.assertEqual(source.read_bytes(),before)
            subprocess.run(cli+['--apply'],check=True,capture_output=True)
            self.assertEqual(source.read_text(),'import New.Split\nimport New.Module\nexample := New.decl\n')

    def test_cache_key_tracks_transitive_hashes_and_implementation(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            files={'lean-toolchain':'lean-test','lake-manifest.json':'{}','scripts/refactor/verify.sh':'original',
                   'scripts/audit_test.lean':'import SerrePositivity.A\n',
                   '.lake/build/lib/lean/SerrePositivity/A.olean.hash':'A',
                   '.lake/build/lib/lean/SerrePositivity/B.olean.hash':'B',
                   '.lake/build/lib/lean/SerrePositivity/C.olean.hash':'C'}
            for name,text in files.items():
                p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
            graph={'SerrePositivity.A':{'SerrePositivity.B'},'SerrePositivity.B':set(),'SerrePositivity.C':set()}
            key=lambda:cache_key(root,'scripts/audit_test.lean',graph)
            initial=key()
            (root/'.lake/build/lib/lean/SerrePositivity/C.olean.hash').write_text('unrelated')
            self.assertEqual(initial,key())
            for name in ['.lake/build/lib/lean/SerrePositivity/B.olean.hash','scripts/audit_test.lean','lean-toolchain','lake-manifest.json','scripts/refactor/verify.sh']:
                p=root/name;old=p.read_bytes();p.write_bytes(old+b'\n')
                self.assertNotEqual(initial,key(),name);p.write_bytes(old)
            (root/'.lake/build/lib/lean/SerrePositivity/B.olean.hash').unlink()
            with self.assertRaises(FileNotFoundError):key()

    def test_parallel_order_failure_and_success_only_cache(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            files={'lean-toolchain':'test','lake-manifest.json':'{}','scripts/refactor/layers.json':'{}',
                   'scripts/refactor/audit_sorries.lean':'import Lean\n',
                   '.lake/verify/audits.txt':'c.lean\na.lean\nb.lean\n'}
            files.update({n+'.lean':'import Lean\n' for n in 'abc'})
            for name,text in files.items():
                path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            lock=threading.Lock();active=maximum=0;calls=[]
            def lean(args,**kwargs):
                nonlocal active,maximum
                with lock:active+=1;maximum=max(maximum,active);calls.append(args[-1])
                time.sleep(0.03)
                kwargs['stdout'].write('fixture '+args[-1]+'\n')
                with lock:active-=1
                return 1 if args[-1]=='b.lean' else 0
            with patch.object(verify_runner,'ROOT',root), patch.object(verify_runner,'read_graph',return_value=({},set())), patch.object(verify_runner.subprocess,'call',side_effect=lean), patch.dict(os.environ,{'VERIFY_JOBS':'3'},clear=True), contextlib.redirect_stdout(io.StringIO()):
                verify_runner.main()
                self.assertGreaterEqual(maximum,2)
                result=json.loads((root/'.lake/verify/runner.json').read_text())
                self.assertEqual([r['name'] for r in result['stages'][:3]],['a.lean','b.lean','c.lean'])
                self.assertEqual([r['exit_code'] for r in result['stages'][:3]],[0,1,0])
                calls.clear();os.environ['VERIFY_CACHE']='1';verify_runner.main()
                self.assertEqual(calls,['b.lean'])
                result=json.loads((root/'.lake/verify/runner.json').read_text())
                self.assertEqual([r['cached'] for r in result['stages']],[True,False,True,True])

    def test_cache_rejects_failed_and_corrupt_records(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'cache.json'
            p.write_text(json.dumps({'key':'x','exit_code':1,'output':''}))
            self.assertIsNone(read_cache(p,'x'))
            p.write_text(json.dumps({'key':'x','exit_code':0,'output':'edited','output_sha256':'wrong'}))
            self.assertIsNone(read_cache(p,'x'))


if __name__=='__main__':unittest.main(verbosity=2)
