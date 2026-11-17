from pathlib import Path
import json,sys,re,hashlib,collections
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');D=R/'evidence/bulk/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));from lean_source import declaration_owner;from compare_snapshots import normalize_generated_name
pub=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];prv=json.loads((D/'source-private-map.proposed.json').read_text())['rows'];moves={r['old_module']:r['new_module'] for r in json.loads((D/'module-map.proposed.json').read_text())['rows']};inventory={f['path'][:-5].replace('/','.'):f for f in json.loads((D/'source-inventory.json').read_text())['files']};public={r['old']:r for r in pub};own={};private={}
for row in pub:own.setdefault(row['old_module'],{})[row['old']]=row
for row in prv:private.setdefault(row['old_module'],{})[row['old']]=row
split=json.loads((W/'split-bundle/plan.json').read_text());ranges={}
for record in split['records']:
 m=record['old_module'];text=(R/(m.replace('.','/')+'.lean')).read_text()
 for a,b in record.get('source_spans',[]):ranges.setdefault(m,[]).append((text.count('\n',0,a)+1,text.count('\n',0,b)+1,record['new_modules'][0]))
def prefix(name,table):
 keys=[n for n in table if name==n or name.startswith(n+'.')]
 return table[max(keys,key=len)] if keys else None
name_rules={r['old']:r['new'] for r in pub if r['old']!=r['new']};declarations={};private_normalization={};kernel_rows=[];loaded=[];missing_primary=[];unassociated=[]
for file in sorted((W/'before').glob('group-*.json')):
 if not file.with_name(file.stem+'.complete.json').exists():continue
 data=json.loads(file.read_text())
 for m in data['modules']:
  loaded.append(m);rows=[r for r in data['declarations'] if r['module']==m];byname={r['name']:r for r in rows};source_names={r['name'] for r in inventory.get(m,{}).get('declarations',[]) if r['name']};source_names.update(own.get(m,{}));source_names.update(private.get(m,{}));known=set(byname)
  for user in own.get(m,{}):
   if user not in known:missing_primary.append({'module':m,'name':user})
  for user,row in (own.get(m,{})|private.get(m,{})).items():private_normalization.setdefault(m,{})[user]=row['new']
  for r in rows:
   user=r['name'];raw=r.get('kernel_name',user);is_private=r.get('is_private',False);owner=declaration_owner(r,source_names,byname);base=(private.get(m,{}).get(owner) if owner else None) or (own.get(m,{}).get(owner) if owner else None);dest=base['new_module'] if base else moves.get(m,m)
   if base is None and (position:=r.get('source_range')):
    line=position['selection_start_line']
    for a,b,target in ranges.get(m,[]):
     if a<=line<b:dest=target;break
   table=(private.get(m,{})|own.get(m,{})) if is_private else public
   rule=prefix(user,table);new=rule['new']+user[len(rule['old']):] if rule else user
   if not is_private and new==user:new=normalize_generated_name(new,{m:dest})
   declarations.setdefault(m,{})[user]=dest
   if not is_private and new!=user:
    if user in name_rules:assert name_rules[user]==new,(user,name_rules[user],new)
    name_rules[user]=new
   if is_private:private_normalization.setdefault(m,{})[user]=new
   kernel_rows.append({'old_module':m,'old_kernel_name':raw,'old_user_name':user,'new_module':dest,'intended_new_user_name':new,'is_private':is_private,'source_parent':owner,'reference_kind':r.get('reference_kind'),'private_parser_descr':r.get('private_parser_descr',False),'environment_parent':r.get('environment_parent'),'parent_module':r.get('parent_module'),'source_range':r.get('source_range')})
   if owner is None:unassociated.append({'module':m,'name':user,'private_parser_descr':r.get('private_parser_descr',False),'reference_kind':r.get('reference_kind'),'parent_module':r.get('parent_module')})
plan={'modules':moves,'declarations':declarations,'private_normalization':private_normalization};(W/'preservation-module-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2));(W/'public-comparison-name-map.json').write_text(json.dumps(name_rules,ensure_ascii=False,indent=2));(W/'before-kernel-disposition.json').write_text(json.dumps({'status':'partial before-side intended disposition; actual after kernel names and ordinary private ownership still need reconciliation','loaded_modules':len(loaded),'rows':kernel_rows,'missing_source_public_rows':missing_primary,'unassociated':unassociated},ensure_ascii=False,indent=2));print('loaded',len(loaded),'kernel rows',len(kernel_rows),'public rules',len(name_rules),'missing source public',len(missing_primary));print(missing_primary[:8])
