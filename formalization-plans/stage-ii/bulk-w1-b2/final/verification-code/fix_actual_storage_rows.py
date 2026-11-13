from pathlib import Path
import json,hashlib
w=Path('/tmp/bulk-w1-b2');plan=json.load(open(w/'preservation-module-plan.json'));mm=plan['modules'];base='SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.'
wanted={base+'UniverseZeroTriangle':[base+'ZeroTriangle.'+s for s in ['down','down_vertex','isCofiber_down','isFiber_down','ulift_down_square']],base+'ZeroHomotopy':[base+'IsZeroVertex.isZeroHo']}
rows=[]
for owner,names in wanted.items():
 receipt=next(p for p in (w/'preservation').glob('*.receipt.json') if owner in json.load(open(p)).get('modules',[]))
 d=receipt.with_name(receipt.name.removesuffix('.receipt.json'));before=json.load(open(d/'before.json'));after=json.load(open(d/'after.json'));b={(r['module'],r['name']):r for r in before['declarations']};a={(r['module'],r['name']):r for r in after['declarations']};dest=mm.get(owner,owner)
 for name in names:
  left=b[owner,name];right=a[dest,name]
  for field in ['kind','type_hash','body_hash','axioms','attributes']:assert left[field]==right[field],(name,field)
  parent=name.rpartition('.')[0]
  receiver=parent.replace(base,'SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.',1)
  rows.append({'module':owner,'old':name,'new_module':dest,'new':name,'field_namespace':receiver,'evidence':'Actual before/after native declarations match in kind/type/body/axioms/kernel attributes. The stored method stays at its original full name; a weak export attaches it to the moved receiver.','comparison_receipt':receipt.name})
(w/'actual-storage-name-corrections.json').write_text(json.dumps({'status':'PASS','rows':rows,'semantic_changes':False,'capture_inputs_unchanged':True},ensure_ascii=False,indent=2))
p=w/'namespace-plan-field-reviewed.json';d=json.load(open(p));existing={(r['module'],r['old']) for r in d['rows']}
for row in rows:
 assert (row['module'],row['old']) not in existing
 d['rows'].append({k:row[k] for k in ['module','old','new_module','new','field_namespace']})
p.write_text(json.dumps(d,ensure_ascii=False,indent=2))
print('six actual method storage names verified; distribution map corrected, frozen comparison map unchanged')
