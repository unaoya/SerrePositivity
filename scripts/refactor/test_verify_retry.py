#!/usr/bin/env python3
"""§10.9: retry classification, serial scheduling, and actual verify summary assembly.

Temporary fixture workspaces use a fake lake executable; these are not repository audits.
"""
import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

import verify_runner as vr

ROOT = Path(__file__).resolve().parents[2]


class RetryClassification(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.log = self.root/'first.log'

    def reasons(self, text, rc=1):
        self.log.write_text(text)
        return vr.environment_failure(self.root, {'exit_code':rc, 'log':'first.log'})

    def test_open_file_and_enfile_diagnostics(self):
        for message, reason in [
            ('failed to open file \'x.ir\': Too many open files in system', 'too-many-open-files'),
            ('failed to open file \'x.olean\': Input/output error', 'failed-to-open-file'),
        ]:
            with self.subTest(message=message):
                self.assertEqual(self.reasons('a.lean:2:0: error: '+message+'\n'), [reason])
        self.assertEqual(self.reasons('[Errno 24] Too many open files\n'), ['too-many-open-files'])

    def test_object_file_must_exist_after_failure(self):
        message="a.lean:1:0: error: object file 'obj.olean' of module X does not exist\n"
        self.assertEqual(self.reasons(message), [])
        (self.root/'obj.olean').write_bytes(b'fixture')
        self.assertEqual(self.reasons(message), ['object-file-exists-after-failure'])
        absolute=message.replace('obj.olean',str(self.root/'obj.olean'))
        self.assertEqual(self.reasons(absolute), ['object-file-exists-after-failure'])
        (self.root/'obj.olean').unlink();(self.root/'obj.olean').mkdir()
        self.assertEqual(self.reasons(message), [])

    def test_semantic_mixed_and_success_never_retry(self):
        environmental='a.lean:1:0: error: failed to open file \'x\'\n'
        semantic='a.lean:3:2: error(lean.unknownIdentifier): Unknown identifier `oldName`\n'
        self.assertEqual(self.reasons(semantic), [])
        self.assertEqual(self.reasons(environmental+semantic), [])
        self.assertEqual(self.reasons('a.lean:1:0: error: unsolved goals\n⊢ False\n'), [])
        self.assertEqual(self.reasons(environmental,0), [])
        self.assertEqual(self.reasons(''), [])


class RetryScheduling(unittest.TestCase):
    def run_fixture(self, persistent=False, heavy_failure=False):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);out=root/'.lake/verify';(out/'cache').mkdir(parents=True)
            lock=threading.Lock();events=[];active=set();calls={};main_thread=threading.get_ident()
            def lean(args,**kwargs):
                name=args[-1]
                with lock:
                    n=calls.get(name,0)+1;calls[name]=n
                    serial=name in (vr.HEAVY_AUDIT,vr.SORRY) or n>1
                    if serial:
                        self.assertEqual(active,set())
                        self.assertEqual(threading.get_ident(),main_thread)
                    active.add(name);events.append(('start',name,n))
                time.sleep(0.03)
                failure=(name=='normal.lean' and (n==1 or persistent)) or (heavy_failure and name in (vr.HEAVY_AUDIT,vr.SORRY) and n==1)
                kwargs['stdout'].write("fixture.lean:1:0: error: failed to open file 'x': Too many open files in system\n" if failure else 'success\n')
                with lock:active.remove(name);events.append(('end',name,n))
                return int(failure)
            audits=['normal.lean','other.lean',vr.HEAVY_AUDIT]
            with patch.object(vr.subprocess,'call',side_effect=lean), contextlib.redirect_stdout(io.StringIO()):
                records,_,_=vr.run_checks(root,audits,{p:None for p in [*audits,vr.SORRY]},3,False)
            normal=next(r for r in records if r['name']=='normal.lean')
            self.assertEqual(calls['normal.lean'],2)
            self.assertTrue(normal['retried']);self.assertEqual(normal['exit_code'],int(persistent))
            self.assertEqual([r['exit_code'] for r in normal['attempts']],[1,int(persistent)])
            self.assertNotEqual(normal['attempts'][0]['log'],normal['attempts'][1]['log'])
            self.assertIn('Too many open files',(root/normal['attempts'][0]['log']).read_text())
            self.assertEqual(normal['seconds'],round(sum(r['seconds'] for r in normal['attempts']),3))
            self.assertLess(events.index(('end','other.lean',1)),events.index(('start','normal.lean',2)))
            self.assertLess(events.index(('end','normal.lean',2)),events.index(('start',vr.HEAVY_AUDIT,1)))
            self.assertEqual(json.loads((out/'audit-progress.json').read_text()),{'completed':3,'total':3})
            for name in [vr.HEAVY_AUDIT,vr.SORRY]:
                r=next(r for r in records if r['name']==name)
                self.assertEqual(calls[name],2 if heavy_failure else 1)
                self.assertEqual(r['retried'],heavy_failure)
                self.assertEqual(r['exit_code'],0)

    def test_pool_joins_before_retry_and_heavy_checks(self):
        self.run_fixture()

    def test_second_environment_failure_is_final(self):
        self.run_fixture(persistent=True)

    def test_heavy_and_sorry_retry_serially(self):
        self.run_fixture(heavy_failure=True)

    def test_retry_bypasses_cache(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'failed.log').write_text("a.lean:1:0: error: failed to open file 'x'\n")
            first=dict(kind='audit',name='a.lean',exit_code=1,seconds=1.0,log='failed.log',cached=False,cache_key='key')
            second={**first,'exit_code':0,'seconds':2.0,'log':'retry.log'}
            with patch.object(vr,'execute',return_value=second) as execute:
                result=vr.retry_environment_failure(root,first)
            execute.assert_called_once_with(root,'audit','a.lean','key',False,attempt=2)
            self.assertEqual(result['seconds'],3.0)


FAKE_LAKE = r'''
import json,sys
from pathlib import Path
root=Path.cwd()
if sys.argv[1]=='build':raise SystemExit(0)
assert sys.argv[1:3]==['env','lean']
name=sys.argv[3];spec=json.loads((root/'fixture.json').read_text()).get(name,{'kind':'success'})
marker=root/('.lake/verify/count-'+name.replace('/','_'));n=int(marker.read_text())+1 if marker.exists() else 1;marker.write_text(str(n))
mode=spec['kind'];fail=n==1 or spec.get('persistent',False)
if mode=='semantic':
 print(name+':1:0: error(lean.unknownIdentifier): Unknown identifier `oldName`');raise SystemExit(1)
if mode=='missing':
 print(name+":1:0: error: object file 'absent.olean' of module Absent does not exist");raise SystemExit(1)
if fail and mode=='object':
 obj=root/'available.olean';obj.write_bytes(b'fixture')
 print(name+":1:0: error: object file '"+str(obj)+"' of module Available does not exist");raise SystemExit(1)
if fail and mode=='environment':
 print(name+":1:0: error: failed to open file 'x.ir': Too many open files in system");raise SystemExit(1)
print('fixture success')
'''


class SummaryIntegration(unittest.TestCase):
    def fixture(self, spec, selected=False):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);scripts=root/'scripts/refactor';scripts.mkdir(parents=True)
            for name in ['verify.sh','verify_runner.py','layer_check.py','layers.json']:
                shutil.copyfile(ROOT/'scripts/refactor'/name,scripts/name)
            audits=sorted(p for p in spec if p!=vr.SORRY)
            for name in [*audits,vr.SORRY]:
                p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text('import SerrePositivity.RetryFixture\n')
            source=root/'SerrePositivity/RetryFixture.lean';source.parent.mkdir();source.write_text('-- fixture\n')
            hashed=root/'.lake/build/lib/lean/SerrePositivity/RetryFixture.olean.hash'
            hashed.parent.mkdir(parents=True);hashed.write_text('fixture-hash')
            (scripts/'audit_manifest.txt').write_text('\n'.join(audits)+'\n')
            (scripts/'verify_baseline.txt').write_text('# no known failures\n')
            (root/'lean-toolchain').write_text('fixture');(root/'lake-manifest.json').write_text('{}')
            (root/'fixture.json').write_text(json.dumps(spec))
            bins=root/'bin';bins.mkdir()
            for name,body in [('lake',FAKE_LAKE),('git',"print('0'*40)\n")]:
                p=bins/name;p.write_text('#!'+sys.executable+'\n'+body);p.chmod(0o755)
            env={k:v for k,v in os.environ.items() if not k.startswith(('VERIFY_','SORRY_AUDIT_'))}
            env.update(PATH=str(bins)+os.pathsep+os.environ['PATH'],VERIFY_JOBS='3',VERIFY_CACHE='0',PYTHONDONTWRITEBYTECODE='1')
            if selected:env['VERIFY_ONLY_AUDITS']=' '.join(audits)
            p=subprocess.run(['zsh','scripts/refactor/verify.sh'],cwd=root,env=env,capture_output=True,text=True)
            path=root/'.lake/verify/summary.json'
            self.assertTrue(path.exists(),p.stdout+p.stderr)
            summary=json.loads(path.read_text())
            self.assertEqual(summary['gate'],not selected)
            self.assertEqual(summary['runner']['retried'],summary['retried'])
            self.assertEqual(len(summary['stages']),len(audits)+4) # prep, root, audit-targets, sorry
            self.assertEqual(summary['retried'],sum(r.get('retried',False) for r in summary['stages']))
            for record in summary['stages']:
                if 'attempts' in record:
                    self.assertEqual(len(record['attempts']),2 if record['retried'] else 1)
                    for attempt in record['attempts']:self.assertTrue((root/attempt['log']).exists())
            return p.returncode,summary

    def test_recovered_audit_is_success_and_gate_unchanged(self):
        rc,s=self.fixture({'scripts/audit_retry.lean':{'kind':'environment'}})
        self.assertEqual(rc,0);self.assertEqual(s['status'],'PASS');self.assertEqual(s['retried'],1)
        self.assertEqual(s['counts']['audit'],dict(success=1,failure=0,known=0))
        self.assertEqual(s['failures'],[])
        self.assertIn('retried=1',s['summary'])

    def test_object_exists_after_failure_and_selection_remains_non_gate(self):
        rc,s=self.fixture({'scripts/audit_retry.lean':{'kind':'object'}},selected=True)
        self.assertEqual(rc,0);self.assertEqual(s['retried'],1)

    def test_persistent_failure_retries_once_and_stays_fail(self):
        rc,s=self.fixture({'scripts/audit_retry.lean':{'kind':'environment','persistent':True}})
        self.assertEqual(rc,1);self.assertEqual(s['status'],'FAIL');self.assertEqual(s['retried'],1)
        self.assertEqual(s['counts']['audit'],dict(success=0,failure=1,known=0))
        r=next(r for r in s['stages'] if r['kind']=='audit')
        self.assertEqual([a['exit_code'] for a in r['attempts']],[1,1])
        self.assertIn('-retry-1.log',r['log']);self.assertEqual(r['signature']['error_count'],1)

    def test_semantic_and_genuinely_missing_object_do_not_retry(self):
        rc,s=self.fixture({'scripts/audit_old_name.lean':{'kind':'semantic'},'scripts/audit_missing.lean':{'kind':'missing'}})
        self.assertEqual(rc,1);self.assertEqual(s['retried'],0)
        self.assertEqual(s['counts']['audit'],dict(success=0,failure=2,known=0))

    def test_heavy_and_sorry_retries_are_counted(self):
        rc,s=self.fixture({vr.HEAVY_AUDIT:{'kind':'environment'},vr.SORRY:{'kind':'environment'}})
        self.assertEqual(rc,0);self.assertEqual(s['retried'],2)
        self.assertEqual(s['counts']['sorry'],dict(success=1,failure=0,known=0))


if __name__=='__main__':unittest.main(verbosity=2)
