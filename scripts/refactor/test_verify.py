#!/usr/bin/env python3
"""Staged verification acceptance: one full run, all other runs use two selected audits."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'.lake/verify/ifw0-2-acceptance'
SELECTED=['scripts/audit_homotopy_property_shared.lean','scripts/audit_euler_betti_finite_support.lean']


def run(label,overrides,expected=0):
    directory=OUT/label;directory.mkdir(parents=True,exist_ok=True)
    env={k:v for k,v in os.environ.items() if not k.startswith(('VERIFY_','SORRY_AUDIT_'))}
    env.update(overrides)
    started=time.time()
    (directory/'started.json').write_text(json.dumps({'command':['zsh','scripts/refactor/verify.sh'],'environment':overrides,'started_epoch':started})+'\n')
    with (directory/'run.log').open('w') as log:
        rc=subprocess.call(['zsh','scripts/refactor/verify.sh'],cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
    summary=json.loads((ROOT/'.lake/verify/summary.json').read_text())
    for record in summary['stages']:
        path=ROOT/record['log'];target=directory/path.name
        shutil.copyfile(path,target);record['log']=str(target.relative_to(ROOT))
    for record in summary.get('runner',{}).get('stages',[]):
        record['log']=str((directory/Path(record['log']).name).relative_to(ROOT))
    (directory/'summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
    result={'exit_code':rc,'expected':expected,'seconds':round(time.time()-started,3),'summary':summary['summary'],
            'gate':summary['gate'],'failures':summary['failures']}
    (directory/'result.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(label,json.dumps(result,ensure_ascii=False),flush=True)
    assert rc==expected,result
    assert summary['status']==('PASS' if expected==0 else 'FAIL'),result
    return summary


def main():
    parser=argparse.ArgumentParser();parser.add_argument('phase',choices=['preflight','full','cache'])
    args=parser.parse_args();OUT.mkdir(parents=True,exist_ok=True)
    selection={'VERIFY_ONLY_AUDITS':' '.join(SELECTED)}
    if args.phase=='preflight':
        result=run('preflight',{**selection,'VERIFY_JOBS':'1','VERIFY_SKIP_BUILD':'1'})
        assert not result['gate'] and result['executed_audit_count']==2
        assert [r['name'] for r in result['stages'] if r['kind']=='audit']==sorted(SELECTED)
    elif args.phase=='full':
        marker=OUT/'full-attempted'
        with marker.open('x') as handle:handle.write('The single authorized full run.\n')
        result=run('full',{'VERIFY_JOBS':'3'})
        assert result['gate'] and result['audit_count']==99 and result['executed_audit_count']==99
        assert result['counts']['audit']=={'success':99,'failure':0,'known':0}
        assert not any(r.get('cached') for r in result['stages'])
    else:
        env={**selection,'VERIFY_CACHE':'1','VERIFY_JOBS':'3'}
        result=run('cache',env)
        assert not result['gate']
        assert all(r['cached'] for r in result['stages'] if r['kind'] in ('audit','sorry'))
        path=ROOT/SELECTED[0];original=path.read_bytes()
        try:
            path.write_bytes(original+b'\n-- IF-W0-2 cache invalidation acceptance fixture\n')
            result=run('cache-invalidated',env)
            audits={r['name']:r for r in result['stages'] if r['kind']=='audit'}
            assert not audits[SELECTED[0]]['cached'] and audits[SELECTED[1]]['cached']
            assert next(r for r in result['stages'] if r['kind']=='sorry')['cached']
        finally:path.write_bytes(original)
        failure=ROOT/'.lake/verify/ifw0-2-intentional-failure.lean'
        try:
            failure.write_text('import Lean\nexample : False := by trivial\n')
            name=str(failure.relative_to(ROOT))
            result=run('intentional-failure',{'VERIFY_ONLY_AUDITS':name,'VERIFY_EXTRA_AUDITS':name,
                       'VERIFY_CACHE':'1','VERIFY_SKIP_BUILD':'1'},1)
            assert not result['gate'] and result['counts']['audit']['failure']==1
        finally:failure.unlink(missing_ok=True)
        result=run('invalid-selection',{'VERIFY_ONLY_AUDITS':'scripts/not-an-audit.lean'},1)
        assert not result['gate'] and result['counts']['preparation']['failure']>=1
    print('PASS phase='+args.phase,flush=True)



# Fast scheduler/measurement unit tests; no Lean builds or acceptance verify runs.
import tempfile
import threading
import unittest
from unittest.mock import patch
import verify_runner as vr


class MemoryRunnerTests(unittest.TestCase):
    def schedule(self, paths, stats, jobs=6, budget=40*vr.GB, exclusive=()):
        active = 0
        maximum = 0
        lock = threading.Lock()
        def action(name):
            nonlocal active, maximum
            with lock:
                active += 1; maximum = max(maximum, active)
            time.sleep(0.025)
            with lock: active -= 1
            return {'name': name}
        results, report = vr.schedule_checks(paths, action, stats, jobs, budget, exclusive_paths=exclusive)
        self.assertEqual({r['name'] for r in results}, set(paths))
        self.assertEqual(maximum, report['max_concurrent'])
        return report

    def test_longest_first(self):
        stats = {n: {'seconds': t, 'max_rss_bytes': vr.GB} for n,t in [('short',1),('long',9),('middle',4)]}
        report = self.schedule(['short','long','middle'],stats,jobs=1)
        self.assertEqual(report['start_order'], ['long','middle','short'])

    def test_memory_budget_waits_and_backfills_first_fitting(self):
        stats = {n: {'seconds': t, 'max_rss_bytes': rss*vr.GB}
                 for n,t,rss in [('large1',9,30),('large2',8,30),('small',1,10)]}
        report = self.schedule(['small','large2','large1'],stats)
        self.assertEqual(report['start_order'], ['large1','small','large2'])
        self.assertLessEqual(report['max_reserved_rss_bytes'],40*vr.GB)
        self.assertGreater(report['memory_wait_count'],0)
        self.assertGreater(report['memory_wait_seconds'],0)

    def test_unknown_first_and_twenty_gb_estimate(self):
        stats = {'known': {'seconds':1000, 'max_rss_bytes':vr.GB}}
        report = self.schedule(['known','u3','u1','u2'],stats)
        self.assertEqual(report['planned_order'],['u1','u2','u3','known'])
        starts = [e for e in report['events'] if e['event']=='start']
        self.assertEqual([e['estimated_rss_bytes'] for e in starts if e['name'].startswith('u')], [20*vr.GB]*3)
        self.assertLessEqual(report['max_reserved_rss_bytes'],40*vr.GB)

    def test_exclusive_audits_backfill_small_jobs_under_44_gb(self):
        stats = {n: {'seconds': t, 'max_rss_bytes': rss*vr.GB}
                 for n,t,rss in [('large1',9,14),('large2',8,13),('small',1,1)]}
        report = self.schedule(['small','large2','large1'], stats, jobs=6,
                               budget=44*vr.GB, exclusive=['large1','large2'])
        self.assertEqual(report['start_order'], ['large1','small','large2'])
        self.assertEqual(report['max_exclusive_concurrent'], 1)
        self.assertEqual(report['max_concurrent'], 2)
        self.assertLessEqual(report['max_reserved_rss_bytes'], 44*vr.GB)

    def test_exclusive_audits_apply_without_memory_budget_and_reject_typos(self):
        report = self.schedule(['a','b','small'], {}, jobs=6, budget=0,
                               exclusive=['a','b'])
        self.assertEqual(report['max_exclusive_concurrent'], 1)
        self.assertEqual(report['max_concurrent'], 2)
        with self.assertRaises(ValueError):
            self.schedule(['a'], {}, exclusive=['missing'])

    def test_jobs_one_is_serial(self):
        report = self.schedule(['a','b','c'],{},jobs=1)
        self.assertEqual(report['max_concurrent'],1)

    def test_budget_zero_preserves_three_workers(self):
        report = self.schedule(['a','b','c'],{},jobs=3,budget=0)
        self.assertEqual(report['max_concurrent'],3)
        self.assertEqual(report['memory_wait_count'],0)

    def test_oversize_runs_alone_without_deadlock(self):
        report = self.schedule(['large','small'],{'large':{'seconds':9,'max_rss_bytes':50*vr.GB},
                                                'small':{'seconds':1,'max_rss_bytes':vr.GB}})
        starts = [e for e in report['events'] if e['event']=='start']
        large = next(e for e in starts if e['name']=='large')
        self.assertTrue(large['oversize_alone'])
        self.assertEqual(large['concurrent'],1)

    def test_budget_validation_and_mac_rss_units(self):
        for value in ['-1','NaN','inf','oops']:
            with self.assertRaises(ValueError): vr.memory_budget(value)
        self.assertEqual(vr.memory_budget('0'),0)
        self.assertEqual(vr.memory_budget('1.5'),1_500_000_000)
        self.assertEqual(vr.parse_time_output('  1234567  maximum resident set size\n'),1234567)
        self.assertIsNone(vr.parse_time_output('no measurement'))

    def test_simultaneous_rss_excludes_unrelated_processes(self):
        table='100 1 999 Python\n101 100 3 /usr/bin/time\n102 101 4 lake\n103 102 5 lean\n104 100 100 ps\n201 200 999 lean\n'
        self.assertEqual(vr.timed_tree_rss(table,100),12*1024)

    def test_measurement_separate_from_output_and_cache_stats_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);out=root/'.lake/verify';(out/'cache').mkdir(parents=True)
            def fake_time(args,**kw):
                self.assertEqual(args[:3],['/usr/bin/time','-l','-o'])
                Path(args[3]).write_text(' 2345678 maximum resident set size\n')
                kw['stdout'].write('audit output only\n')
                return 0
            with patch.object(vr.subprocess,'call',side_effect=fake_time):
                first=vr.execute(root,'audit','a.lean','key',False)
            self.assertEqual(first['max_rss_bytes'],2345678)
            self.assertEqual((root/first['log']).read_text(),'audit output only\n')
            stats={};vr.save_stat(root,first,stats,'commit1')
            first_bytes=(out/'audit-stats.json').read_bytes()
            cached=vr.execute(root,'audit','a.lean','key',True)
            self.assertTrue(cached['cached']);self.assertEqual(cached['max_rss_bytes'],2345678)
            vr.save_stat(root,cached,stats,'commit2')
            self.assertEqual((out/'audit-stats.json').read_bytes(),first_bytes)
            larger={**first,'max_rss_bytes':3456789};vr.save_stat(root,larger,stats,'commit3')
            self.assertEqual(vr.read_stats(root)['a.lean']['max_rss_bytes'],3456789)
            self.assertEqual(vr.read_stats(root)['a.lean']['commit'],'commit3')

    def test_new_measurement_does_not_reuse_stale_time_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'.lake/verify/cache').mkdir(parents=True)
            with patch.object(vr.subprocess,'call',return_value=0):
                first=vr.execute(root,'audit','a.lean',None,False)
                (root/first['time_log']).write_text(' 999 maximum resident set size\n')
                second=vr.execute(root,'audit','a.lean',None,False)
            self.assertIsNone(second['max_rss_bytes'])


if __name__=='__main__':main()
