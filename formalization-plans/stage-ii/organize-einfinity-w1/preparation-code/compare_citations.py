"""Compare actual metadata against transported baseline plus the two reviewed additions."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,sys
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--before',type=Path,required=True);p.add_argument('--after',type=Path,required=True);p.add_argument('--name-map',type=Path,required=True);p.add_argument('--module-map',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();sys.path.insert(0,str(root/'scripts/refactor'));from compare_snapshots import rename
load=lambda p:json.loads(p.read_text());rules=load(a.name_map);plan=load(a.module_map);left=load(a.before);right=load(a.after);fields=['key','number','declaration','module','relation','comment','edition'];before=[];after=[]
def target_module(module,name):return plan.get('declarations',{}).get(module,{}).get(name,plan['modules'].get(module,module))
for record in left['records']:
 row={k:record[k] for k in fields};row['module']=target_module(row['module'],row['declaration']);row['declaration']=rename(row['declaration'],rules);before.append(row)
for record in right['records']:
 row={k:record[k] for k in fields};row['declaration']=rename(row['declaration'],rules);after.append(row)
review=load(root/'formalization-plans/stage-ii/organize-einfinity-w1/preparation/citation-review-all-native.json')['records'];editions={r['key']:r['edition'] for r in load(root/'research/bibliography.json')['references']};additions=[]
for item in review:
 if item['existing_source_attribute']:continue
 assert item['key']=='kerodon' and item['status']=='partial'
 old_matches=[r for r in left['records'] if r['key']=='Kerodon' and r['number']==item['tag'] and r['declaration']==item['declaration']];assert not old_matches,'The proposed new tag is already registered in the actual baseline'
 additions.append(dict(key='Kerodon',number=item['tag'],declaration=rename(item['declaration'],rules),module=target_module(item['old_module'],item['declaration']),relation='native',comment=item['planned_comment'],edition=editions['Kerodon']))
assert len(additions)==2
key=lambda row:json.dumps(row,ensure_ascii=False,sort_keys=True);expected=Counter(map(key,before+additions));actual=Counter(map(key,after));missing=[json.loads(row) for row,n in (expected-actual).items() for _ in range(n)];extra=[json.loads(row) for row,n in (actual-expected).items() for _ in range(n)];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();result=dict(status='PASS' if not missing and not extra else 'FAIL',baseline=len(before),reviewed_additions=additions,expected=len(before)+len(additions),actual=len(after),missing=missing,extra=extra,checked_fields=fields,before_sha256=sha(a.before),after_sha256=sha(a.after),name_map_sha256=sha(a.name_map),module_plan_sha256=sha(a.module_map),policy='Exact metadata multiplicities after ownership/name transport and independently specified additions. Actual path/line remain in native capture receipts.')
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','baseline','expected','actual']}|dict(missing=len(missing),extra=len(extra))));raise SystemExit(bool(missing or extra))
