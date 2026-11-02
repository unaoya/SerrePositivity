"""DG-W2 merge tests: ordinary discovery never invokes Lean.

DG_W2_LEAN_TEST=1 enables one two-source snapshot test. A busy build lock
skips it immediately (exit 75); all temporary sources, index entries and outputs
are removed. No production/root/downstream build is run.
"""
import copy
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import uuid

import merge_modules as mm

ROOT=Path(__file__).resolve().parents[2]
AREA='SerrePositivity.Fixture'


class MergeTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.git('init','-q')
        self.put('A','universe u\nnamespace Demo\n/-- keep this doc -/\ndef a : Nat := 1\nend Demo\n')
        self.put('B','noncomputable section\nuniverse u v\nnamespace Demo\ndef b : Nat := a + 1\nend Demo\n',imports=[AREA+'.A'])
        self.put('C','namespace Demo\ndef c : Nat := b + 1\nend Demo\n',imports=[AREA+'.B'])
        self.outside=self.root/'SerrePositivity/Consumer.lean'
        self.outside.write_text('module\npublic import '+AREA+'.A\npublic import '+AREA+'.B\n-- '+AREA+'.A\n/-! '+AREA+'.B -/\n#check "'+AREA+'.C"\n')
        self.git('add','.');self.git('-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-qm','fixture')
        self.plan=[{'module':AREA+'.Merged','action':'merge','sources':[AREA+'.'+n for n in ['A','B','C']],
                    'docstring':'# Combined\n\n## 概要\nfixture\n## 方針\nordered\n## 規約\nunchanged\n## 使われ方\ntest',
                    'private_renames':{},'deletes':[],'stubs':[],'candidate':'test','note':''}]

    def git(self,*args):
        return subprocess.run(['git',*args],cwd=self.root,check=True,capture_output=True)

    def put(self,name,body,imports=(),header='@[expose] public section'):
        path=self.root/mm.module_path(AREA+'.'+name);path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text('module\n'+''.join('public import '+n+'\n' for n in imports)+'\n/-! # '+name+' original\n\nuntouched docs\n-/\n'+header+'\n'+body)
        return path

    def analyze(self,plan=None,**kw):
        return mm.analyze(self.root,plan or self.plan,[AREA],[r'^SerrePositivity/.*\.lean$'],**kw)

    def test_render_and_import_only_rewrite(self):
        r=self.analyze();out=r['built'][AREA+'.Merged']
        self.assertTrue(out.startswith('module\n'))
        self.assertIn('universe u v',out)
        self.assertIn('@[expose] public section A',out)
        self.assertIn('noncomputable section',out)
        self.assertIn('end\n\nend B',out)
        self.assertIn('（旧 SerrePositivity/Fixture/A.lean）',out)
        self.assertIn('/-- keep this doc -/\ndef a : Nat := 1',out)
        self.assertIn('/-! # A original\n\nuntouched docs\n-/',out)
        self.assertNotIn('public import '+AREA+'.A',out)
        rewritten=r['edits']['SerrePositivity/Consumer.lean']
        self.assertEqual(rewritten.count('public import '+AREA+'.Merged'),1)
        self.assertIn('-- '+AREA+'.A',rewritten)
        self.assertIn('#check "'+AREA+'.C"',rewritten)
        self.assertGreater(r['rows'][0]['importers'],0)
        self.assertEqual(r['external_area_edges']['Consumer'],2)

    def test_apply_and_overwrite_source_destination(self):
        self.plan[0]['module']=AREA+'.A'
        r=self.analyze();mm.apply(self.root,r)
        self.assertTrue((self.root/mm.module_path(AREA+'.A')).exists())
        self.assertFalse((self.root/mm.module_path(AREA+'.B')).exists())
        self.assertIn('def c', (self.root/mm.module_path(AREA+'.A')).read_text())
        self.assertIn('D  SerrePositivity/Fixture/B.lean',self.git('status','--short').stdout.decode())

    def test_external_crlf_is_preserved(self):
        text=self.outside.read_text().replace('\n','\r\n')
        self.outside.write_bytes(text.encode())
        self.git('add','.');self.git('-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-qm','CRLF consumer')
        result=self.analyze();mm.apply(self.root,result)
        actual=self.outside.read_bytes().decode()
        self.assertEqual(actual.count('\r\n'),text.count('\r\n'))
        self.assertIn('-- '+AREA+'.A\r\n',actual)

    def test_dryrun_does_not_write(self):
        before={p:p.read_bytes() for p in self.root.rglob('*.lean')}
        self.analyze()
        self.assertEqual(before,{p:p.read_bytes() for p in self.root.rglob('*.lean')})

    def test_untracked_and_missing_sources_rejected(self):
        self.git('rm','--cached','--',mm.module_path(AREA+'.B'))
        with self.assertRaisesRegex(ValueError,'untracked source'):self.analyze()
        self.git('add',mm.module_path(AREA+'.B'))
        (self.root/mm.module_path(AREA+'.B')).unlink()
        with self.assertRaisesRegex(ValueError,'missing source'):self.analyze()

    def test_duplicate_source_and_destination(self):
        other=copy.deepcopy(self.plan[0]);other['module']=AREA+'.Other'
        with self.assertRaisesRegex(ValueError,'duplicate source'):self.analyze(self.plan+[other])
        with self.assertRaisesRegex(ValueError,'duplicate destination'):self.analyze(self.plan+self.plan)

    def test_import_order(self):
        self.plan[0]['sources'].reverse()
        with self.assertRaisesRegex(ValueError,'import order'):self.analyze()

    def test_private_collision_and_explicit_rename(self):
        for n in ['A','B']: self.put(n,'namespace Demo\nprivate def hidden := 1\ndef '+n.lower()+' := hidden\nend Demo\n')
        with self.assertRaisesRegex(ValueError,'private collision'):self.analyze()
        self.plan[0]['private_renames']={AREA+'.B':{'hidden':'hiddenB'}}
        out=self.analyze()['built'][AREA+'.Merged']
        self.assertIn('private def hiddenB',out);self.assertIn('def b := hiddenB',out)

    def test_private_names_in_different_namespaces(self):
        for n in ['A','B']: self.put(n,'namespace '+n+'\nprivate def hidden := 1\nend '+n+'\n')
        self.analyze()

    def test_option_conflict_is_scoped_warning(self):
        self.put('A','set_option maxRecDepth 100\ndef a := 1\n')
        self.put('B','set_option maxRecDepth 200\ndef b := 2\n')
        r=self.analyze();self.assertTrue(any('set_option maxRecDepth' in w for w in r['warnings']))
        out=r['built'][AREA+'.Merged']
        self.assertLess(out.index('section A'),out.index('set_option maxRecDepth 100'))
        self.assertLess(out.index('end A'),out.index('set_option maxRecDepth 200'))

    def test_unclosed_named_scope_and_mismatched_end(self):
        self.put('A','section Named\ndef a := 1\n')
        with self.assertRaisesRegex(ValueError,'unclosed named'):self.analyze()
        self.put('A','namespace Demo\ndef a := 1\nend Other\n')
        with self.assertRaisesRegex(ValueError,'mismatched end'):self.analyze()

    def test_explicit_outer_end_and_no_public_header(self):
        self.put('A','def a := 1\nend\n')
        self.put('B','def b := 2\n',header='')
        r=self.analyze();self.assertTrue(any('no public section' in w for w in r['warnings']))
        self.assertIn('\nsection B\n',r['built'][AREA+'.Merged'])

    def test_nested_comments_strings_and_multiline_imports(self):
        text='module\n/- nested /- import Bad -/ -/\npublic import\n  '+AREA+'.A\n  '+AREA+'.B\n-- keep\ndef s := "import '+AREA+'.A"\n'
        # import can be continued on following lines.
        out=mm.rewrite_imports(text,{AREA+'.A':AREA+'.X',AREA+'.B':AREA+'.X'})
        self.assertIn('  '+AREA+'.X',out);self.assertIn('"import '+AREA+'.A"',out)
        self.assertEqual(mm.imports(out),{AREA+'.X'})

    def test_dotted_namespace_can_close_in_parts(self):
        self.put('A','namespace Demo.Nested\ndef a := 1\nend Nested\ndef extra := 2\nend Demo\n')
        out=self.analyze()['built'][AREA+'.Merged']
        self.assertIn('end Nested\ndef extra := 2\nend Demo',out)

    def test_max_lines_report(self):
        r=self.analyze(max_lines=10)
        self.assertTrue(any('max-lines:' in w for w in r['warnings']))
        self.assertIn('生成行数',mm.report(r))

    def test_scope_stubs_and_deletes(self):
        with self.assertRaisesRegex(ValueError,'outside rewrite scope'):
            mm.analyze(self.root,self.plan,[AREA],[r'^SerrePositivity/Fixture/'])
        self.plan[0]['stubs']=[AREA+'.A',AREA+'.B']
        r=mm.analyze(self.root,self.plan,[AREA],[r'^SerrePositivity/Fixture/']);mm.apply(self.root,r)
        self.assertIn('public import '+AREA+'.Merged',(self.root/mm.module_path(AREA+'.A')).read_text())

    def test_live_delete_consumer_rejected(self):
        self.put('Unused','def d := 0\n');self.git('add','.')
        self.plan[0]['deletes']=[AREA+'.Unused']
        self.outside.write_text('import '+AREA+'.Unused\n')
        with self.assertRaisesRegex(ValueError,'deleted modules still imported'):self.analyze()

    def test_delete_removes_audit_import_and_tracked_file(self):
        self.put('Unused','def d := 0\n')
        audit=self.root/'scripts/audit_fixture.lean';audit.parent.mkdir()
        audit.write_text('import '+AREA+'.Unused\n-- retained audit comment\n')
        self.git('add','.');self.git('-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-qm','delete fixture')
        self.plan[0]['deletes']=[AREA+'.Unused']
        result=mm.analyze(self.root,self.plan,[AREA],[r'^(SerrePositivity|scripts)/.*\.lean$'])
        mm.apply(self.root,result)
        self.assertFalse((self.root/mm.module_path(AREA+'.Unused')).exists())
        self.assertNotIn('import ',audit.read_text());self.assertIn('-- retained audit comment',audit.read_text())

    def test_dirty_apply_rejected_without_writes(self):
        self.outside.write_text(self.outside.read_text()+'-- local edit\n')
        r=self.analyze()
        with self.assertRaisesRegex(ValueError,'dirty'):mm.apply(self.root,r)
        self.assertTrue((self.root/mm.module_path(AREA+'.B')).exists())

    def test_mixed_draft_cannot_apply(self):
        self.plan.append({'module':AREA+'.A','action':'move','dest':AREA+'.Moved'})
        r=self.analyze()
        with self.assertRaisesRegex(ValueError,'mixed move/split'):mm.apply(self.root,r)

    def test_snapshot_cli_delegates_with_explicit_module_map(self):
        row={'name':'Demo.a','parent':'Demo.a','kind':'def','type':['const','Nat',[]],'body':['lit',1],'axioms':[],'attributes':{},'module':'A'}
        a=self.root/'before.json';b=self.root/'after.json';mapping=self.root/'module-map.json'
        a.write_text(json.dumps({'schema_version':1,'declarations':[row]}))
        row['module']='Merged';b.write_text(json.dumps({'schema_version':1,'declarations':[row]}))
        args=['--snapshot-before',str(a),'--snapshot-after',str(b)]
        # Module identity is significant; an unapproved move must still fail.
        self.assertEqual(mm.main(args),1)
        mapping.write_text(json.dumps({'modules':{'A':'Merged'}}))
        args.extend(['--module-map',str(mapping)])
        self.assertEqual(mm.main(args),0)
        row['body']=['lit',2];b.write_text(json.dumps({'schema_version':1,'declarations':[row]}))
        self.assertEqual(mm.main(args),1)
        row['body']=['lit',1];row['type']=['const','Int',[]]
        b.write_text(json.dumps({'schema_version':1,'declarations':[row]}))
        self.assertEqual(mm.main(args),1)

    def test_module_map_requires_snapshots(self):
        error=io.StringIO()
        with contextlib.redirect_stderr(error):
            self.assertEqual(mm.main(['--module-map','unused.json']),1)
        self.assertIn('--module-map requires snapshots',error.getvalue())

    def cycle_fixture(self):
        # The original graph is a DAG: IHAdjunction -> ClosedStructure -> IHDef.
        # Contracting IHDef and IHAdjunction produces InternalHom <-> Closed.
        self.put('Mod.IHDef','def ih := 1\n')
        self.put('Mod.ClosedStructure','def closed := 2\n',imports=[AREA+'.Mod.IHDef'])
        self.put('Mod.IHAdjunction','def adj := 3\n',imports=[AREA+'.Mod.ClosedStructure'])
        self.git('add','.')
        return [dict(module=AREA+'.Mod.InternalHom',action='merge',
                     sources=[AREA+'.Mod.IHDef',AREA+'.Mod.IHAdjunction'],docstring='# InternalHom'),
                dict(module=AREA+'.Mod.Closed',action='merge',
                     sources=[AREA+'.Mod.ClosedStructure'],docstring='# Closed')]

    def test_check_rejects_target_cycle_and_reports_original_edges(self):
        plan=self.cycle_fixture()
        path=self.root/'plan.json';path.write_text(json.dumps(plan))
        before={p:p.read_bytes() for p in self.root.rglob('*.lean')}
        error=io.StringIO()
        with contextlib.redirect_stderr(error):
            rc=mm.main([str(path),'--root',str(self.root),'--area',AREA,'--check'])
        self.assertEqual(rc,1)
        for edge in [('Mod.InternalHom','Mod.Closed'),('Mod.Closed','Mod.InternalHom'),
                     ('Mod.IHAdjunction','Mod.ClosedStructure'),('Mod.ClosedStructure','Mod.IHDef')]:
            self.assertIn(AREA+'.'+edge[0]+' -> '+AREA+'.'+edge[1],error.getvalue())
        self.assertEqual(before,{p:p.read_bytes() for p in self.root.rglob('*.lean')})

    def test_acyclic_target_import_union_and_internal_edges(self):
        plan=self.cycle_fixture()
        self.put('Mod.IHAdjunction','def adj := 3\n',imports=[AREA+'.Mod.IHDef'])
        result=self.analyze(plan)
        self.assertNotIn('public import '+AREA+'.Mod.InternalHom',result['built'][AREA+'.Mod.InternalHom'])
        self.assertIn('public import '+AREA+'.Mod.InternalHom',result['built'][AREA+'.Mod.Closed'])
        self.assertNotIn('cycle',mm.report(result))

    def test_cycles_include_final_destination_imports(self):
        plan=self.cycle_fixture()
        self.put('Mod.IHAdjunction','def adj := 3\n',imports=[AREA+'.Mod.Closed'])
        with self.assertRaisesRegex(ValueError,'original: '+AREA+r'\.Mod.IHAdjunction -> '+AREA+r'\.Mod.Closed'):
            self.analyze(plan)

    def test_all_cyclic_components_and_edges_are_reported(self):
        edges={('A','B'),('B','C'),('C','A'),('A','C'),('D','E'),('E','D'),('Tail','A')}
        origins={edge:{('Old'+edge[0],'Old'+edge[1])} for edge in edges}
        with self.assertRaises(ValueError) as raised:
            mm.check_target_cycles({'A','B','C','D','E','Tail'},origins)
        message=str(raised.exception)
        self.assertIn('targets: A, B, C',message)
        self.assertIn('targets: D, E',message)
        self.assertNotIn('Tail',message)
        for a,b in edges-{('Tail','A')}:
            self.assertIn('original: Old'+a+' -> Old'+b,message)

    def test_long_acyclic_target_graph(self):
        nodes=[str(i) for i in range(1500)]
        mm.check_target_cycles(nodes,{(a,b):{(a,b)} for a,b in zip(nodes,nodes[1:])})


@unittest.skipUnless(os.environ.get('DG_W2_LEAN_TEST')=='1','opt-in: DG_W2_LEAN_TEST=1')
class LeanMergeTest(unittest.TestCase):
    def test_two_sources_snapshot(self):
        command=['zsh',str(ROOT/'scripts/refactor/with_build_lock.sh'),'--wait','0','--',sys.executable,'-B',str(Path(__file__).resolve()),'--lean-worker']
        result=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
        if result.returncode==75:self.skipTest('build lock busy; Lean preservation test deferred')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)


def lean_worker():
    suffix=uuid.uuid4().hex[:12];area='SerrePositivity.DGW2Fixture'+suffix
    mods=[area+'.A',area+'.B',area+'.Merged'];paths=[ROOT/mm.module_path(n) for n in mods]
    def run(args):subprocess.run(args,cwd=ROOT,check=True)
    with tempfile.TemporaryDirectory(prefix='dg-w2-snapshot-') as directory:
        out=Path(directory)
        try:
            paths[0].parent.mkdir()
            paths[0].write_text('module\npublic import Mathlib.Data.Nat.Basic\n@[expose] public section\nnamespace DGW2Fixture'+suffix+'\ndef value : Nat := 3\n@[simp] theorem value_eq : value = 3 := rfl\nend DGW2Fixture'+suffix+'\n')
            paths[1].write_text('module\npublic import '+mods[0]+'\n@[expose] public section\nnamespace DGW2Fixture'+suffix+'\ndef next : Nat := value + 1\nend DGW2Fixture'+suffix+'\n')
            run(['git','add','--',*[str(p.relative_to(ROOT)) for p in paths[:2]]])
            run(['lake','build',*mods[:2]])
            run(['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean','--modules',','.join(mods[:2]),'--output',str(out/'before.json')])
            entry={'module':mods[2],'action':'merge','sources':mods[:2],'docstring':'# Temporary preservation fixture'}
            result=mm.analyze(ROOT,[entry],[area],[r'^SerrePositivity/DGW2Fixture'+suffix+r'/.*\.lean$'])
            # Temporary sources are intentionally staged, so render the checked result
            # directly. --apply's git deletion path is covered by isolated Git tests.
            paths[2].write_text(result['built'][mods[2]])
            run(['lake','build',mods[2]])
            run(['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean','--modules',mods[2],'--output',str(out/'after.json')])
            mapping=out/'module-map.json'
            mapping.write_text(json.dumps({'modules':{m:mods[2] for m in mods[:2]}}))
            rc=mm.main(['--snapshot-before',str(out/'before.json'),'--snapshot-after',str(out/'after.json'),'--module-map',str(mapping)])
            if rc:raise RuntimeError('snapshot preservation failed')
        finally:
            subprocess.run(['git','rm','--cached','--ignore-unmatch','--',*[str(p.relative_to(ROOT)) for p in paths[:2]]],cwd=ROOT,check=True)
            for p in paths:p.unlink(missing_ok=True)
            if paths[0].parent.exists():paths[0].parent.rmdir()
            for base in [ROOT/'.lake/build/lib/lean',ROOT/'.lake/build/ir']:
                folder=base/area.replace('.','/')
                if folder.exists():
                    for p in folder.iterdir():
                        if p.is_file():p.unlink()
                    folder.rmdir()


if __name__=='__main__':
    if sys.argv[1:]==['--lean-worker']:lean_worker()
    else:unittest.main()
