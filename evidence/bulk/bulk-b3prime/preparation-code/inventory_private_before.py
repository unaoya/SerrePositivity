from pathlib import Path
import json,re,sys,collections,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');D=R/'evidence/bulk/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));from compare_snapshots import normalize_generated_name
G={m:set(v) for m,v in json.loads((W/'tracked-import-graph.json').read_text()).items()};todo=list(json.loads((W/'before-manifest.json').read_text())['modules']);closure=set()
while todo:
 m=todo.pop()
 if m in closure:continue
 closure.add(m);todo.extend(G.get(m,set())&G.keys())
k=json.loads((W/'before-kernel-disposition.json').read_text());native={(r['old_module'],r['old_kernel_name']):r for r in k['rows']};pub=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];prv=json.loads((D/'source-private-map.proposed.json').read_text())['rows'];scope={}
for row in pub+prv:scope.setdefault(row['old_module'],{})[row['old']]=row
moves={r['old_module']:r['new_module'] for r in json.loads((D/'module-map.proposed.json').read_text())['rows']};rows=[];missing=[];collisions=[];foreign=[];sources={};unchanged_modules=0
for m in sorted(closure):
 p=R/'.lake/build/lib/lean'/(m.replace('.','/')+'.ilean')
 if not p.exists():missing.append(m);continue
 data=json.loads(p.read_bytes());seen={}
 for raw,rng in data.get('decls',{}).items():
  if not raw.startswith('_private.'):continue
  match=re.match(r'^_private\.'+re.escape(m)+r'\.\d+\.(.+)$',raw)
  if not match:foreign.append({'seen_in_module':m,'raw':raw});continue
  user=match[1]
  if user in seen:collisions.append({'module':m,'user':user,'raw':[seen[user],raw]})
  seen[user]=raw
  candidates=[x for n,x in scope.get(m,{}).items() if user==n or user.startswith(n+'.')];base=max(candidates,key=lambda x:len(x['old'])) if candidates else None;expected=native.get((m,raw));dest=expected['new_module'] if expected else base['new_module'] if base else moves.get(m,m);new=expected['intended_new_user_name'] if expected else base['new']+user[len(base['old']):] if base else user
  if m not in sources:sources[m]=(R/(m.replace('.','/')+'.lean')).read_text().splitlines()
  line=rng[0]+1;code=sources[m][rng[0]] if rng[0]<len(sources[m]) else '';notation=bool(re.match(r'\s*(?:(?:local|scoped)\s+)?(?:notation\d*|infixl?|infixr|prefix|postfix|syntax|macro_rules)\b',code));parser=bool(expected and expected.get('private_parser_descr'));compiler_aux=('macroRules' in user or '___unexpand_' in user) and notation
  if compiler_aux:new=normalize_generated_name(new,{m:dest})
  rows.append({'old_module':m,'old_raw':raw,'old_user':user,'new_module':dest,'intended_new_user':new,'source_line':line,'verified_notation_source':notation,'private_parser_descr':parser,'notation_auxiliary':compiler_aux,'source_range':rng})
result={'status':'before-side source-private inventory; after actual bindings and notation payload groups still required','project_prerequisites':len(closure),'private_bindings':len(rows),'canonical_collisions':collisions,'missing_ilean_modules':missing,'foreign_private_entries':foreign,'rows':rows};(W/'before-private-inventory.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));print('project prerequisites',len(closure),'private bindings',len(rows),'missing ilean',len(missing),'collisions',len(collisions),'foreign',len(foreign));print('notation source bindings',sum(r['verified_notation_source'] for r in rows))
