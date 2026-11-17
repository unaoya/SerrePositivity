from pathlib import Path
import json,re,sys,collections,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');A=Path('/tmp/bulk-b3prime-preview');W=Path('/tmp/bulk-b3prime');sys.path.insert(0,str(R/'scripts/refactor'));from klw1_namespace import private_user_name
plan=json.loads((W/'preservation-module-plan.json').read_text());rules=json.loads((W/'public-comparison-name-map.json').read_text());before=json.loads((W/'before-private-inventory.json').read_text());manifest=json.loads((W/'before-manifest.json').read_text());targets=set(json.loads((W/'final-bundle/manifest.json').read_text())['files']);after={};actual_rows=[];collisions=[];missing_files=[]
def add(raw,value):
 if raw in rules and rules[raw]!=value:raise ValueError('conflicting raw rule '+raw)
 rules[raw]=value
for m in sorted(targets):
 path=A/'.lake/build/lib/lean'/(m.replace('.','/')+'.ilean')
 if not path.exists():missing_files.append(m);continue
 for raw,rng in json.loads(path.read_bytes()).get('decls',{}).items():
  if not raw.startswith('_private.'):continue
  user=private_user_name(m,raw)
  if (m,user) in after:collisions.append({'module':m,'user':user,'raw':[after[m,user],raw]})
  after[m,user]=raw;actual_rows.append({'module':m,'raw':raw,'user':user,'source_range':rng});add(raw,'@owned-private['+m+']:'+user)
ordinary_missing=[];notation_unpaired=[]
for row in before['rows']:
 m=row['old_module'];dest=row['new_module'];user=row['intended_new_user'];raw=row['old_raw'];add(raw,'@owned-private['+dest+']:'+user)
 if dest not in targets:
  # Unchanged prerequisites retain their actual defining-module identity.
  assert dest==m and row['old_user']==user,(m,user)
  continue
 if (dest,user) not in after:
  entry={k:row[k] for k in ['old_module','old_raw','old_user','new_module','intended_new_user','source_line']}
  if row['verified_notation_source'] or row['private_parser_descr'] or row['notation_auxiliary']:notation_unpaired.append(entry)
  else:ordinary_missing.append(entry)
for root in ['Init','Lean','Std','Mathlib','Batteries','Aesop','Qq','ProofWidgets','LeanSearchClient','ImportGraph','Plausible']:add('_private.'+root,'@fixed-external-private['+root+']')
summary={'ordinary_private_missing':ordinary_missing,'notation_unpaired_for_native_companion':notation_unpaired,'after_private_collisions':collisions,'missing_after_ilean':missing_files,'before_source_private_bindings':before['private_bindings'],'after_source_private_bindings':len(actual_rows),'raw_private_rules':sum(k.startswith('_private.') for k in rules),'policy':'Ordinary source private declarations require actual module+user binding. Verified notation compiler ordinals are not paired; existing source-verified native ParserDescr companion and raw inventories remain mandatory in v3b.'};(W/'owned-private-rules-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));(W/'after-private-inventory.json').write_text(json.dumps(actual_rows,ensure_ascii=False,indent=2));(W/'owned-comparison-name-map.json').write_text(json.dumps(rules,ensure_ascii=False,indent=2));print('ordinary missing',len(ordinary_missing),'notation unpaired',len(notation_unpaired),'collisions',len(collisions),'missing ilean',len(missing_files));print(ordinary_missing[:5]);raise SystemExit(bool(ordinary_missing or collisions or missing_files))
