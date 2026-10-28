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


if __name__=='__main__':main()
