from pathlib import Path
import json,sys,re
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import code_only
D=R/'formalization-plans/stage-ii/bulk-b3prime';closure=json.loads((D/'stage0-import-closure.json').read_text())['reverse_closure'];refs=set(json.loads((W/'reference-files.json').read_text()));skip=[];modules=[]
for m in closure:
 p=R/(m.replace('.','/')+'.lean');text=code_only(p.read_text());body=re.sub(r'(?m)^\s*(?:(?:public|private|meta)\s+)*import[^\n]*','',text);body=re.sub(r'(?m)^\s*module\s*$','',body)
 if not body.strip():skip.append({'module':m,'reason':'static source contains only module/import commands; imports checked separately, no owned Lean declarations','source':p.relative_to(R).as_posix()});refs.discard(p.relative_to(R).as_posix())
 else:modules.append(m)
refs.update(['SerrePositivity/Inputs/Perfectoidization.lean','SerrePositivity/BhattScholze/Perfectoidization/Finite.lean'])
# Split sources first; native and semantic collection remain in original environment.
priority={r['old_path'][:-5].replace('/','.') for r in json.loads((D/'split-plan.proposed.json').read_text())['rows']};modules.sort(key=lambda m:(m not in priority,m));groups=[modules[i:i+8] for i in range(0,len(modules),8)]
plan={'baseline':'32d364b53','modules':modules,'groups':groups,'reference_files':sorted(refs),'import_only_modules':skip,'no_scope_weakening':'All source-bearing affected modules snapshotted. Import-only aggregates have no owned declarations and remain covered by import/static/root validation.'};(W/'before-manifest.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2));print(len(modules),'snapshot modules',len(refs),'semantic files',len(skip),'import-only aggregates')
