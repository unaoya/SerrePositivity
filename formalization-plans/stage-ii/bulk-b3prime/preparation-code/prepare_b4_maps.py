from pathlib import Path
import json,sys
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'formalization-plans/stage-ii/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));import klw1_namespace as K
assert json.loads((W/'preservation/complete.json').read_text())['unexplained']==0
source=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];moves=json.loads((D/'module-map.proposed.json').read_text())['rows'];actual={}
for p in (W/'preservation').glob('[0-9][0-9][0-9]/after.json'):
 for row in json.loads(p.read_text())['declarations']:
  if not row['is_private']:actual[row['module'],row['name']]=row
missing=[r for r in source if (r['new_module'],r['new']) not in actual];assert not missing,missing[:8]
indexed={(r['module'],r['old']):r for r in json.loads((W/'namespace-rewrite-plan.json').read_text())['rows'] if not r['old'].startswith('_private.')};rename={}
for r in source:
 if r['old']==r['new']:continue
 row={'module':r['old_module'],'old':r['old'],'new':r['new'],'new_module':r['new_module']}
 if (hint:=indexed.get((r['old_module'],r['old']),{}).get('field_namespace')):row['field_namespace']=hint
 rename[row['module'],row['old']]=row
# Native generated public correspondences are useful only when the intended
# concrete destination really exists; keep unmatched compiler inventories for review.
compiler_review=[]
for r in json.loads((W/'before-kernel-disposition.json').read_text())['rows']:
 if r['is_private'] or r['old_user_name']==r['intended_new_user_name']:continue
 old=r['old_user_name'];new=r['intended_new_user_name'];owner=r['old_module'];target=r['new_module']
 if (target,new) not in actual:compiler_review.append(r);continue
 key=owner,old
 if key not in rename:rename[key]={'module':owner,'old':old,'new':new,'new_module':target}
plan={'modules':{r['old_module']:r['new_module'] for r in moves},'rows':sorted(rename.values(),key=lambda r:(r['module'],r['old'])),'namespaces':{},'opens':{},'module_opens':{},'policy':'Use original native namespace/open bindings; qualify moved references. Never infer a namespace from a module path. Wrapper deletion/call redirect is separate, not a signature-identical rename.'}
from collections import defaultdict
by_dest=defaultdict(list)
for row in plan['rows']:by_dest[row['new']].append(row)
duplicates={n:rs for n,rs in by_dest.items() if len(rs)>1}
(W/'b4-duplicate-native-destinations.json').write_text(json.dumps(duplicates,ensure_ascii=False,indent=2))
source_keys={(r['old_module'],r['old']) for r in source if r['old']!=r['new']}
for dest,rows in duplicates.items():
 assert all((r['module'],r['old']) not in source_keys for r in rows),('source API collision',dest,rows)
 for row in rows:
  compiler_review.append({'correspondence':row,'reason':'Same generated equation theorem name is created on demand in multiple native module environments; retain full owner evidence, do not invent a unique CLI ownership row.'})
plan['rows']=[r for r in plan['rows'] if r['new'] not in duplicates]

K.Migration(plan)
out=W/'B4';out.mkdir(exist_ok=True)
(out/'module-map.json').write_text(json.dumps(plan['modules'],ensure_ascii=False,indent=2)+'\n');(out/'namespace-rewrite-map.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n');(out/'public-owner-map.json').write_text(json.dumps({'rows':source,'native_destination_missing':missing},ensure_ascii=False,indent=2)+'\n');(out/'compiler-inventory-review.json').write_text(json.dumps(compiler_review,ensure_ascii=False,indent=2)+'\n');(out/'redirects-and-deletions.json').write_bytes((D/'redirects-and-deletions.json').read_bytes());(out/'map-summary.json').write_text(json.dumps({'whole_module_moves':len(moves),'all_public_source_rows':len(source),'changed_public_source_names':sum(r['old']!=r['new'] for r in source),'concrete_native_validated_rewrite_rows':len(plan['rows']),'native_source_destination_missing':0,'unpaired_compiler_names_not_autorewritten':len(compiler_review),'wrapper':'Approved removal/redirect, explicitly retain original finite-presentation parameter telescope in choosing definitions. Do not treat its weaker target as an identical-signature alias.'},ensure_ascii=False,indent=2));print('B4 maps',len(moves),len(source),len(plan['rows']),'compiler review',len(compiler_review))
