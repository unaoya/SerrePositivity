#!/usr/bin/env python3
from pathlib import Path
import os,subprocess,json,time,argparse,tempfile
parser=argparse.ArgumentParser(description="Kernel checks for cite attributes, persistence and original-declaration inspection")
parser.add_argument('--root',type=Path,default=Path.cwd())
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();V=args.root.resolve();T=args.output.resolve();T.mkdir(parents=True,exist_ok=True);start=time.monotonic();results=[]
setup=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,text=True).strip()
search=[]
for value in setup.split(os.pathsep):
 p=Path(value);search.append(str(p if p.is_absolute() else V/p))
env=dict(os.environ,LEAN_PATH=str(T)+os.pathsep+os.pathsep.join(search))
prefix=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=V,text=True).strip();lean=str(Path(prefix)/'bin/lean')
positive='''import SerrePositivity.Util.Citation
namespace Fixture
@[cite HTT "5.5.2.9"] def exactValue : Nat := 1
@[cite HA "1.1.1.1" (partial := special) "objects restricted"] theorem specialCase : True := trivial
@[cite HA "1.1.1.2" (partial := direction) "forward implication"] theorem forward : True := trivial
@[cite HA "1.1.1.3" (partial := stronger-hyp) "additional hypothesis"] theorem stronger : True := trivial
@[cite BS19 "Prop 7.10" (partial := component) "construction only"] theorem component : True := trivial
attribute [cite HTT "5.5.2.9"] exactValue
@[kerodon 0000] theorem nativeTag : True := trivial
end Fixture
#cite_tags HTT
#cite_tags! HA
#cite_tags Kerodon
'''
(T/'Fixture.lean').write_text(positive)
def run(name,text,expect,flags=()):
 p=T/(name+'.lean');p.write_text(text);r=subprocess.run([lean,*flags,p.name],cwd=T,env=env,text=True,capture_output=True);(T/(name+'.log')).write_text(r.stdout+r.stderr);assert (r.returncode==0)==expect,(name,r.stdout,r.stderr);results.append({'case':name,'rc':r.returncode});return r.stdout
out=run('Fixture',positive,True,('-o','Fixture.olean'));records=[json.loads(x) for x in out.splitlines() if x.startswith('{')];assert len([r for r in records if r['key']=='HTT'])==1;assert {r['relation'] for r in records if r['key']=='HA'}=={'special','direction','stronger-hyp'};assert any(r['key']=='Kerodon' for r in records);assert all(r['line'] and r['module']=='Fixture' for r in records)
imported=run('Imported','import Fixture\n#cite_tags HTT\n#cite_tags BS19\n',True);assert 'Fixture.exactValue' in imported and '"relation":"component"' in imported
for name,attr in [('unknown','cite UNKNOWN "1"'),('empty','cite HA ""'),('partial_missing','cite HA "1" (partial := special)'),('partial_blank','cite HA "1" (partial := special) "  "'),('native_cite','cite Kerodon "0000"')]:run(name,'import SerrePositivity.Util.Citation\n@['+attr+'] theorem exampleResult : True := trivial\n',False)
run('conflict','import Fixture\nattribute [cite HTT "5.5.2.9" (partial := special) "conflict"] Fixture.exactValue\n',False)
run('local','import Fixture\nattribute [local cite HTT "5.5.2.9"] Fixture.exactValue\n',False)
run('ModuleMode', 'module\npublic meta import SerrePositivity.Util.Citation\n@[expose] public section\n@[cite HTT "1.2.3.4"] theorem moduleResult : True := trivial\nattribute [cite HA "1.1.1.1"] moduleResult\n#cite_tags HTT\n#cite_tags HA\n', True)
(T/'receipt.json').write_text(json.dumps({'seconds':round(time.monotonic()-start,3),'cases':results,'pass':True},indent=2)+'\n');print('Citation tests passed',len(results))

out=run('Inspect','''import Fixture
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.UniverseLiftAnodyne
#cite_check Fixture.exactValue
#cite_check SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.anodyneQ_map_isIso_of_weakEquivalence
''',True)
rs=[json.loads(x) for x in out.splitlines() if x.startswith('{')]
assert len(rs)==2 and rs[0]['module']=='Fixture' and not rs[0]['requires_explicit_sset_model']
assert 'Nat' in rs[0]['type_constants']
assert rs[1]['requires_explicit_sset_model'] and 'sorryAx' not in rs[1]['axioms'],rs
(T/'inspection-receipt.json').write_text(json.dumps(rs,ensure_ascii=False,indent=2))
results.append({'case':'inspection','rc':0})
(T/'receipt.json').write_text(json.dumps({'seconds':round(time.monotonic()-start,3),'cases':results,'pass':True},indent=2)+'\n')
print('Inspection tests passed')
