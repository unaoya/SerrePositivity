#!/usr/bin/env python3
"""§10.11: build a temporary reassoc lemma, split, compare, and remove all sources."""
import json,subprocess,sys,time,tempfile
from pathlib import Path
from split_module import ROOT,prepare,apply,module_path
from lean_source import parse_source,declaration_owner
from compare_snapshots import compare

A='SerrePositivity.InfinityCategories.ModelBridge.IFW0ReassocSource'
B='SerrePositivity.InfinityCategories.ModelBridge.IFW0ReassocMoved'
NAME='IFW0Reassoc.move'
TEXT='''module
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc
@[expose] public section
open CategoryTheory
namespace IFW0Reassoc
universe v u
variable {C : Type u} [Category.{v} C]
def keep : Nat := 1
@[reassoc]
theorem move {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := Category.id_comp f
end IFW0Reassoc
'''

def main():
    base=ROOT/'.lake/verify/ifw0-3-addendum11'
    base.mkdir(parents=True,exist_ok=True)
    out=Path(tempfile.mkdtemp(prefix='reassoc-test-',dir=base))
    print('OUTPUT',str(out),flush=True)
    paths=[module_path(ROOT,m) for m in (A,B)]
    if any(p.exists() for p in paths):raise RuntimeError('temporary module already exists')
    state={'status':'running','commands':[]}
    def save():(out/'results.json').write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n')
    def run(label,cmd):
        t=time.monotonic()
        with (out/(label+'.log')).open('w') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
        state['commands'].append(dict(label=label,command=cmd,exit_code=r.returncode,seconds=round(time.monotonic()-t,3)));save()
        if r.returncode:raise RuntimeError(label+' failed')
    def snap(label,mods):
        run(label,['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean','--modules',','.join(mods),'--output',str(out/(label+'.json'))])
        return json.loads((out/(label+'.json')).read_text())
    try:
        paths[0].parent.mkdir(parents=True,exist_ok=True);paths[0].write_text(TEXT)
        run('before-build',['lake','build',A]);before=snap('before',[A])
        source=parse_source(TEXT,snapshot=before,module=A);rows={r['name']:r for r in before['declarations']}
        assert declaration_owner(rows[NAME+'_assoc'],source.declarations,rows)==NAME
        plan=prepare(ROOT,A,B,{NAME},before,{A:set()});(out/'plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2))
        apply(ROOT,plan);run('split-build',['lake','build',A,B]);after=snap('after',[A,B])
        rows={r['name']:r for r in after['declarations']};assert rows[NAME]['module']==rows[NAME+'_assoc']['module']==B
        result=compare(before,after,module_map={'declarations':{A:plan['declaration_modules']}});(out/'comparison.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));assert result['status']=='PASS',result
        state['status']='PASS'
    except BaseException as e:state['status']='FAIL';state['error']=str(e);raise
    finally:
        for p in paths:p.unlink(missing_ok=True)
        for mod in (A,B):
            for base in [ROOT/'.lake/build/lib/lean',ROOT/'.lake/build/ir']:
                stem=base/mod.replace('.','/')
                for p in stem.parent.glob(stem.name+'.*'):
                    if p.is_file():p.unlink()
        state['sources_removed']=all(not p.exists() for p in paths);save()
        print(json.dumps(state,ensure_ascii=False),flush=True)

if __name__=='__main__':main()
