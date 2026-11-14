from pathlib import Path
import json,collections,hashlib
W=Path('/tmp/bulk-b3prime');by=collections.defaultdict(set);exact=set()
for p in (W/'actual-preservation').glob('[0-9][0-9][0-9]/after.json'):
 for r in json.loads(p.read_text())['declarations']:
  if not r['is_private']:by[r['name']].add(r['module']);exact.add((r['module'],r['name']))
rows={};unresolved=[];observed=[]
for r in json.loads((W/'before-kernel-disposition.json').read_text())['rows']:
 if r['is_private'] or r['old_module']==r['new_module']:continue
 owner=r['new_module'];name=r['intended_new_user_name'];policy='declared owner confirmed in actual after snapshot'
 if (owner,name) not in exact:
  candidates=by[name]
  if len(candidates)!=1:unresolved.append({'old_module':r['old_module'],'old':r['old_kernel_name'],'new':name,'actual_candidate_owners':sorted(candidates)});continue
  owner=next(iter(candidates));policy='generated on-demand helper: one actual after-snapshot provider; never guessed from a namespace';observed.append({'old_module':r['old_module'],'old':r['old_kernel_name'],'planned_owner':r['new_module'],'actual_provider':owner,'new':name})
 rows[r['old_module'],r['old_kernel_name']]={'module':r['old_module'],'old':r['old_kernel_name'],'new':name,'new_module':owner,'evidence':policy}
for r in json.loads((W/'B4/public-owner-map.json').read_text())['rows']:
 if r['old_module']==r['new_module']:continue
 assert (r['new_module'],r['new']) in exact,r
 key=r['old_module'],r['old'];new={'module':r['old_module'],'old':r['old'],'new':r['new'],'new_module':r['new_module'],'evidence':'public source declaration, exact actual after-snapshot owner'}
 if key in rows:assert rows[key]['new_module']==new['new_module'] and rows[key]['new']==new['new'],(key,rows[key],new)
 rows[key]=new
result={'scope':'Import providers only, including identity names whose defining module moved. Core shared rename plan still excludes identity renames. Private names are not inferred. Actual project-native after snapshots used, not module-path-to-namespace heuristics.','rows':sorted(rows.values(),key=lambda r:(r['module'],r['old'])),'generated_provider_observations':observed,'unresolved':unresolved};(W/'B4/declaration-import-owners.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));assert not unresolved,unresolved;print('B4 actual import providers',len(rows),'same-name',sum(r['old']==r['new'] for r in rows.values()),'generated observed providers',len(observed))
