from pathlib import Path
import json,re,sys,hashlib
R=Path.cwd();D=R/'formalization-plans/stage-ii/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import code_only
s=(R/'formalization-plans/stage-ii/bulk-5inf0/inventory.py').read_text();ns={'R':R,'re':re,'hashlib':hashlib,'code_only':code_only};exec(s[s.index('DECL='):s.index('main={};')],ns);scan=ns['scan']
rows=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];changing={x['old']:x['new'] for x in rows};targets={x['new'] for x in rows if x['new']!=x['old']};collisions=[];files=0
for p in (R/'SerrePositivity').rglob('*.lean'):
 files+=1
 for d in scan(p)['declarations']:
  name=d['name']
  if name in targets and not d['private']:
   projected=changing.get(name,name)
   if projected==name:collisions.append({'name':name,'existing_path':str(p.relative_to(R)),'line':d['line']})
splits=json.loads((D/'split-plan.proposed.json').read_text())['rows'];out={'status':'syntactic target-name check only; native generated/private constants checked during preparation','files_scanned':files,'public_target_name_collisions':collisions,'split_output_path_collisions':[r['new_path'] for r in splits if (R/r['new_path']).exists()]};(D/'stage0-target-collisions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print(files,'files;',len(collisions),'name collisions;',len(out['split_output_path_collisions']),'split path collisions');print(collisions[:12])
