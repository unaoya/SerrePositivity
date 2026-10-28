#!/usr/bin/env python3
"""実 Lean snapshot と小さな import グラフで対象 JSON の受入条件を検証する。"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'.lake/verify/ifw0-2-targets'
MODULE='SerrePositivity.IFW0TargetsSplit'
SOURCE='import Lean\nnamespace IFW0Targets\ndef a : Nat := 1\ndef b : Nat := a + 1\nend IFW0Targets\n'


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    fixture=ROOT/(MODULE.replace('.','/')+'.lean')
    if fixture.exists(): raise RuntimeError('fixture already exists')
    results=[]
    def run(label,args,expected):
        start=time.monotonic()
        with (OUT/(label+'.log')).open('w') as log: rc=subprocess.call(args,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
        row={'label':label,'command':args,'exit_code':rc,'expected':expected,'seconds':round(time.monotonic()-start,3)}
        results.append(row);(OUT/'commands.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(row),flush=True)
        if rc!=expected: raise RuntimeError('unexpected result: '+label)
    def entry(module,action,dest,**kwargs):
        return {'module':module,'action':action,'dest':dest,'moved':[],'keep':[],
                'attributes':{},'candidate':'test','note':'temporary acceptance fixture',**kwargs}
    try:
        fixture.write_text(SOURCE)
        run('fixture-build',['lake','build',MODULE],0)
        snapshot=OUT/'snapshot.json'
        run('snapshot',['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean','--modules',MODULE,'--output',str(snapshot)],0)
        with tempfile.TemporaryDirectory(prefix='graph-',dir=OUT) as directory:
            root=Path(directory)
            def put(module,text):
                p=root/(module.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text);return p
            move='SerrePositivity.IFW0TargetsMove';archive='SerrePositivity.IFW0TargetsArchive'
            put(MODULE,SOURCE);put(move,'def moved : Bool := true\n');put(archive,'def archived : Nat := 1\n')
            plan=[entry(move,'move','SerrePositivity.InfinityCategories.Simplicial.IFW0TargetsMove'),
                  entry(MODULE,'split','SerrePositivity.InfinityCategories.Simplicial.IFW0TargetsSplit',moved=['IFW0Targets.b'],keep=['IFW0Targets.a']),
                  entry(archive,'archive','SerrePositivity.Archive.IFW0TargetsArchive')]
            def check(label,data,expected):
                path=OUT/(label+'-input.json');path.write_text(json.dumps(data,indent=2)+'\n')
                run(label,[sys.executable,'scripts/refactor/validate_targets.py',str(path),'--root',str(root),
                           '--snapshot',MODULE+'='+str(snapshot),'--output',str(OUT/(label+'-result.json'))],expected)
            check('valid',plan,0)
            bad=copy.deepcopy(plan);bad[1]['moved']=['IFW0Targets.missing'];check('unknown-declaration',bad,1)
            check('duplicate',plan+[plan[0]],1)
            outside=put('SerrePositivity.IFW0Outside','import '+archive+'\n')
            check('archive-consumer',plan,1);outside.unlink()
            put(move,'import SerrePositivity.DifferentialGraded.IFW0Bad\ndef moved : Bool := true\n')
            put('SerrePositivity.DifferentialGraded.IFW0Bad','def dependency : Nat := 1\n')
            check('layer-increase',plan,1)
        (OUT/'status.txt').write_text('PASS\n')
        print('PASS: valid move/split/archive; unknown, duplicate, archive consumer and layer increase rejected',flush=True)
    finally:
        fixture.unlink(missing_ok=True)
        for base in [ROOT/'.lake/build/lib/lean',ROOT/'.lake/build/ir']:
            stem=base/MODULE.replace('.','/')
            for p in stem.parent.glob(stem.name+'.*'):
                if p.is_file():p.unlink()


if __name__=='__main__':main()
