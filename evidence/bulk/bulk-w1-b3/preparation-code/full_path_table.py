from pathlib import Path
import json,subprocess,hashlib,collections
w=Path('/tmp/bulk-w1-b3');b=w/'before';r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');p=json.load(open(w/'preservation-module-plan.json'));rows=[];missing=[];destinations=collections.defaultdict(list)
paths=subprocess.check_output(['git','ls-files','-z','--','SerrePositivity/**/*.lean','SerrePositivity.lean','scripts/**/*.lean'],cwd=b).decode().split('\0')
for rel in sorted(set(paths)):
 if not rel:continue
 m=rel[:-5].replace('/','.');target=p['modules'].get(m,m);outputs=sorted({target}|set(p.get('declarations',{}).get(m,{}).values()));after=[t.replace('.','/')+'.lean' for t in outputs]
 for a in after:
  if not (r/a).exists():missing.append({'before':rel,'after':a})
  destinations[a].append(rel)
 rows.append({'source':rel,'module':m,'primary_target':target.replace('.','/')+'.lean','outputs':after,'source_sha256':hashlib.sha256((b/rel).read_bytes()).hexdigest(),'status':'unchanged-path' if after==[rel] else 'split' if len(after)>1 else 'moved'})
summary={'source_files':len(rows),'moved':sum(x['status']=='moved' for x in rows),'split':sum(x['status']=='split' for x in rows),'missing_outputs':missing,'multi_owner_outputs':{a:owners for a,owners in destinations.items() if len(owners)>1},'frozen_main':json.load(open(w/'baseline.json'))['frozen_main']};(w/'full-path-table.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2));(w/'full-path-summary.json').write_text(json.dumps(summary,indent=2));print({k:v for k,v in summary.items() if k!='multi_owner_outputs'});assert not missing,missing[:5]
