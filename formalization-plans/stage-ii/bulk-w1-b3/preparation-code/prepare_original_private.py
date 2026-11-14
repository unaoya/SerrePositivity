from pathlib import Path
import json,re
w=Path('/tmp/bulk-w1-b3');b=w/'before';modules=json.load(open(w/'preservation-original-modules.json'));rows=[];missing=[];duplicates=[]
for m in modules:
 p=b/'.lake/build/lib/lean'/(m.replace('.','/')+'.ilean')
 if not p.exists():missing.append(m);continue
 seen={}
 for name,rng in json.load(open(p))['decls'].items():
  if not name.startswith('_private.'):continue
  user=re.sub(r'^_private\.'+re.escape(m)+r'\.\d+\.','',name)
  if user in seen:duplicates.append({'module':m,'name':user,'raw':[seen[user],name]})
  seen[user]=name;rows.append({'module':m,'kernel_name':name,'user_name':user,'range':rng})
(w/'original-private-names.json').write_text(json.dumps({'private_source_declarations':len(rows),'canonical_collisions':duplicates,'missing_modules':missing,'rows':rows},separators=(',',':')));print('private',len(rows),'missing',len(missing),'collisions',len(duplicates));print('missing examples',missing[:12])
