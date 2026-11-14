from pathlib import Path
import json,sys
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(r/'scripts/refactor'))
import klw1_namespace as K

def refine():
 p=json.load(open(w/'namespace-rewrite-map.json'));migration=K.Migration(p);decisions=[]
 for index in sorted((w/'delta-captures').glob('*/files.json')):
  if index.parent.name.endswith('-pending'):continue
  for name in json.load(open(index)):
   d=json.load(open(index.parent/(name[:-5].replace('/','.')+'.json')))
   for row in d['commands']:
    if row['kind']!='open' or len(row.get('names',[]))!=1:continue
    old=row['names'][0];mode=row['mode'];new=None;reason=None
    if mode=='only':
     guard=row['command'];lo,hi=guard.get('start'),guard.get('stop')
     if lo is None or hi is None:continue
     members=[ref for ref in d['refs'] if lo<=ref.get('start',-1) and ref.get('stop',hi+1)<=hi and ref.get('name')]
     prefixes=set()
     for ref in members:
      if not ref['name'].startswith(old+'.'):break
      suffix=ref['name'][len(old):];actual=(migration.target(ref) or {}).get('new',ref['name'])
      if not actual.endswith(suffix):break
      prefixes.add(actual[:-len(suffix)])
     else:
      if len(prefixes)==1:new=prefixes.pop();reason='all compiler-resolved restricted members retain their exact suffix under this actual destination namespace'
    elif mode in ('simple','scoped') and old not in p['opens'] and any(K.under(old,origin) for origin in migration.namespace_origins):
     new=old;reason='retain actual original namespace binding and qualify moved term references individually; do not add destination namespace opens'
    if new is None:continue
    policies=p.setdefault('module_opens',{}).setdefault(d['module'],{})
    existing=policies.get(old,p['opens'].get(old,old))
    if existing!=new or old not in policies and old not in p['opens']:
     # Conflicting restricted uses stay under review; do not guess a combined scope.
     if old in policies and policies[old]!=new:continue
     policies[old]=new;decisions.append({'module':d['module'],'old':old,'new':new,'mode':mode,'reason':reason})
 if decisions:
  previous=json.load(open(w/'delta-open-decisions.json')) if (w/'delta-open-decisions.json').exists() else []
  (w/'delta-open-decisions.json').write_text(json.dumps(previous+decisions,ensure_ascii=False,indent=2))
  for fn in ['namespace-rewrite-map.json','namespace-map.json']:
   file=w/fn;data=json.load(open(file));data['module_opens']=p['module_opens'];tmp=file.with_suffix('.tmp');tmp.write_text(json.dumps(data,ensure_ascii=False,indent=2));tmp.replace(file)
 return len(decisions)
if __name__=='__main__':print(refine())
