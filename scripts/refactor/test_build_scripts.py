"""Isolated lock/rsync tests. No real lake command or production cache is used."""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

ROOT=Path(__file__).resolve().parents[2]
LOCK=ROOT/'scripts/refactor/with_build_lock.sh'
WARM=ROOT/'scripts/refactor/warm_build_dir.sh'


class BuildScriptTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='dg w2 ');self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.bin=self.root/'bin';self.bin.mkdir()
        self.env=dict(os.environ,TMPDIR=str(self.root),PYTHONDONTWRITEBYTECODE='1')
        self.env['PATH']=str(self.bin)+os.pathsep+self.env['PATH']
        self.fake('ps','')

    def fake(self,name,body):
        path=self.bin/name;path.write_text('#!'+sys.executable+'\n'+body+'\n');path.chmod(0o755)

    def lock(self,body,wait='0',**kw):
        return subprocess.run(['zsh',str(LOCK),'--wait',wait,'--',sys.executable,'-c',body],cwd=self.root,env=self.env,capture_output=True,text=True,**kw)

    def test_exit_status_and_owner_cleanup(self):
        result=self.lock('import sys;sys.exit(17)')
        self.assertEqual(result.returncode,17,result.stderr)
        self.assertFalse((self.root/'serre-lake-build.lock').exists())

    def test_stale_owner(self):
        folder=self.root/'serre-lake-build.lock';folder.mkdir()
        (folder/'owner.json').write_text(json.dumps({'pid':99999999}))
        self.assertEqual(self.lock('pass').returncode,0)
        self.assertFalse(folder.exists())

    def test_busy_immediate_defer(self):
        folder=self.root/'serre-lake-build.lock';folder.mkdir()
        (folder/'owner.json').write_text(json.dumps({'pid':os.getpid(),'token':'other'}))
        result=self.lock('raise RuntimeError("must not run")')
        self.assertEqual(result.returncode,75,result.stderr)
        self.assertTrue(folder.exists())

    def test_two_commands_are_serial(self):
        events=self.root/'events'
        code='from pathlib import Path;import time;p=Path('+repr(str(events))+');p.open("a").write("start1\\n");time.sleep(.3);p.open("a").write("end1\\n")'
        first=subprocess.Popen(['zsh',str(LOCK),'--','python3','-c',code],cwd=self.root,env=self.env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        self.addCleanup(lambda: first.kill() if first.poll() is None else None)
        deadline=time.monotonic()+5
        while not events.exists() and time.monotonic()<deadline:time.sleep(.01)
        self.assertTrue(events.exists())
        second=self.lock('from pathlib import Path;Path('+repr(str(events))+').open("a").write("start2\\n")',wait='1')
        out,err=first.communicate(timeout=5)
        self.assertEqual(first.returncode,0,out+err);self.assertEqual(second.returncode,0,second.stderr)
        self.assertEqual(events.read_text().splitlines(),['start1','end1','start2'])

    def test_signal_releases_lock_and_terminates_child(self):
        ready=self.root/'ready'
        code='from pathlib import Path;import os,time;Path('+repr(str(ready))+').write_text(str(os.getpid()));time.sleep(30)'
        child=subprocess.Popen(['zsh',str(LOCK),'--','python3','-c',code],cwd=self.root,env=self.env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        self.addCleanup(lambda:child.kill() if child.poll() is None else None)
        deadline=time.monotonic()+5
        while not ready.exists() and time.monotonic()<deadline:time.sleep(.01)
        self.assertTrue(ready.exists());child.send_signal(signal.SIGTERM)
        child.communicate(timeout=5)
        self.assertEqual(child.returncode,143)
        self.assertFalse((self.root/'serre-lake-build.lock').exists())
        with self.assertRaises(ProcessLookupError):os.kill(int(ready.read_text()),0)

    def fixture(self):
        self.source=self.root/'source';self.dest=self.root/'destination'
        for root in [self.source,self.dest]:
            (root/'.lake/build/lib/lean').mkdir(parents=True)
            (root/'lake-manifest.json').write_text('{}\n')
            (root/'.lake/packages').mkdir()
        (self.source/'.lake/build/lib/lean/A.olean').write_text('fixture')
        (self.dest/'.lake/build/stale').write_text('old')
        (self.dest/'.lake/packages/sentinel').write_text('keep')
        self.fake('lake','import sys\nassert sys.argv[1:]==["build","SerrePositivity","--no-build"]\nprint("error: build required for SerrePositivity.A (--no-build)")\nsys.exit(1)')

    def warm(self,*extra):
        return subprocess.run(['zsh',str(WARM),'--from',str(self.source),*extra],cwd=self.dest,env=self.env,capture_output=True,text=True)

    def test_real_rsync_copy_delete_and_no_build(self):
        self.fixture();result=self.warm()
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertEqual((self.dest/'.lake/build/lib/lean/A.olean').read_text(),'fixture')
        self.assertFalse((self.dest/'.lake/build/stale').exists())
        self.assertEqual((self.dest/'.lake/packages/sentinel').read_text(),'keep')
        self.assertIn('未ビルドの起点: 1',result.stdout)

    def vanished(self,paths,code=23,extra='',darwin=False):
        real=shutil.which('rsync')
        log='\n'.join(('rsync(123): error: '+str(p)+': open (2) in '+str(self.dest)+': No such file or directory') if darwin else ('file has vanished: "'+str(p)+'"') for p in paths)
        log+=('\n'+extra) if extra else ''
        self.fake('rsync','import subprocess,sys,os\nenv=dict(os.environ);env["PATH"]=os.pathsep.join(env["PATH"].split(os.pathsep)[1:])\nsubprocess.run(['+repr(real)+',*sys.argv[1:]],check=True,env=env)\nprint('+repr(log)+',file=sys.stderr)\nsys.exit('+str(code)+')')

    def test_vanished_output_accepts_23_and_24(self):
        self.fixture()
        for code in [23,24]:
            with self.subTest(code=code):
                self.vanished([self.source/'.lake/build/lib/lean/X.olean.private'],code)
                result=self.warm();self.assertEqual(result.returncode,0,result.stderr)
                self.assertIn('accepted rsync '+str(code),result.stdout)

    def test_darwin_vanished_output(self):
        self.fixture();self.vanished([self.source/'.lake/build/lib/lean/X.ir.sig'],darwin=True)
        result=self.warm();self.assertEqual(result.returncode,0,result.stderr)

    def test_unaccepted_rsync_failures(self):
        self.fixture()
        cases=[([self.source/'.lake/packages/X.olean'],23,''),
               ([self.source/'.lake/build/lib/lean/X.lean'],23,''),
               ([self.source/'.lake/build/lib/lean/X.olean'],23,'rsync: Permission denied'),
               ([self.source/'.lake/build/lib/lean'/f'{i}.olean' for i in range(50)],24,''),
               ([self.source/'.lake/build/ir/X.c'],23,''),([],23,''),
               ([self.source/'.lake/build/lib/lean/X.olean'],12,'')]
        for paths,rc,extra in cases:
            with self.subTest(paths=paths[:1],rc=rc,extra=extra):
                self.vanished(paths,rc,extra);result=self.warm()
                self.assertEqual(result.returncode,1,result.stdout+result.stderr)

    def test_manifest_mismatch_stops_before_copy(self):
        self.fixture();(self.dest/'lake-manifest.json').write_text('{"different":true}')
        result=self.warm();self.assertEqual(result.returncode,1)
        self.assertTrue((self.dest/'.lake/build/stale').exists())

    def test_source_build_stops_before_copy(self):
        self.fixture();self.fake('ps','print("123 lake lake build SerrePositivity")')
        self.fake('lsof','print('+repr('p123\nn'+str(self.source))+')')
        result=self.warm();self.assertEqual(result.returncode,1,result.stdout+result.stderr)
        self.assertTrue((self.dest/'.lake/build/stale').exists())

    def test_yes_waits_for_source_build(self):
        self.fixture();counter=self.root/'ps-count'
        self.fake('ps','from pathlib import Path\np=Path('+repr(str(counter))+')\nif not p.exists():\n p.write_text("1");print("123 lake lake build SerrePositivity")')
        self.fake('lsof','print('+repr('p123\nn'+str(self.source))+')')
        result=self.warm('--yes');self.assertEqual(result.returncode,0,result.stderr)
        self.assertIn('waiting for source lake build',result.stdout)

    def test_other_worktree_build_does_not_block(self):
        self.fixture();self.fake('ps','print("123 lake lake build SerrePositivity")')
        self.fake('lsof','print("p123\\nn/tmp/somewhere-else")')
        result=self.warm();self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_no_build_unknown_error_fails(self):
        self.fixture();self.fake('lake','import sys\nprint("error: invalid project")\nsys.exit(1)')
        result=self.warm();self.assertEqual(result.returncode,1)


if __name__=='__main__':unittest.main()
