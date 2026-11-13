"""Prepare verification rules from actual source private kernel names."""
from pathlib import Path
from collections import defaultdict
import json,sys,hashlib,re
W=Path('/tmp/bulk-w1-b3');R=W/'before';V=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(V/'scripts/refactor'));from klw1_namespace import private_user_name;from compare_snapshots import rename,normalize_generated_name
plan=json.load(open(W/'preservation-module-plan.json'));private=json.load(open(W/'original-private-names.json'))['rows'];byrow={(r['module'],r['old']):r for r in plan['rows']};owned=defaultdict(dict);expected={};rawrules=json.load(open(W/'comparison-name-map.json'))
for m,mapping in plan.get('namespaces',{}).items():owned[m].update(mapping)
for row in plan['rows']:owned[row['module']][private_user_name(row['module'],row['old']) if row['old'].startswith('_private.') else row['old']]=row['new']
def destination(module,name):
 split=plan.get('declarations',{}).get(module,{})
 current=name
 while current:
  if current in split:return split[current]
  current=current.rpartition('.')[0]
 return plan['modules'].get(module,module)
def identity(owner,name):return '@owned-private['+owner+']:'+name
def normalize_verified_notation(name,old,new):
 encoded_old=re.escape(old.replace('.','_'));encoded_new=new.replace('.','_')
 pattern=r'((?:^|\.)(?:«)?_aux_)'+encoded_old+r'(___(?=macroRules_|unexpand_))'
 name,count=re.subn(pattern,lambda m:m[1]+encoded_new+m[2],name)
 assert count==1,(old,name,count)
 return re.sub(r'_private_'+encoded_old+r'_(?=\d+_)',lambda m:'_private_'+encoded_new+'_',name)
def rule(raw,target):
 if raw in rawrules:assert rawrules[raw]==target,(raw,rawrules[raw],target)
 rawrules[raw]=target
source_lines={};notation_generated=[]
for r in private:
 explicit=byrow.get((r['module'],r['kernel_name']));name=explicit['new'] if explicit else rename(r['user_name'],plan.get('namespaces',{}).get(r['module'],{}));module=destination(r['module'],r['user_name'])
 if 'macroRules' in r['user_name']:
  if r['module'] not in source_lines:source_lines[r['module']]=(R/(r['module'].replace('.','/')+'.lean')).read_text().splitlines()
  line=source_lines[r['module']][r['range'][0]]
  assert re.match(r'\s*(?:(?:local|scoped)\s+)?(?:notation\d*|infixl?|infixr|prefix|postfix|syntax|macro_rules)\b',line),(r,line)
  name=normalize_verified_notation(name,r['module'],module)
  notation_generated.append({'old_module':r['module'],'old':r['user_name'],'new_module':module,'new':name,'source_line':r['range'][0]+1,'classification':'Compiler auxiliary at a verified notation source command; no ordinal pairing.'})
 owned[r['module']][r['user_name']]=name;expected[r['module'],r['kernel_name']]=module,name;rule(r['kernel_name'],identity(module,name))
external_roots=['Init','Lean','Std','Mathlib','Batteries','Aesop','Qq','ProofWidgets','LeanSearchClient','ImportGraph','Plausible']
for root in external_roots:rule('_private.'+root,'@fixed-external-private['+root+']')
old=[p[:-5].replace('/','.') for p in json.load(open(W/'comparison-files.json'))];targets=sorted({plan['modules'].get(m,m) for m in old}|{d for m in old for d in plan.get('declarations',{}).get(m,{}).values()});actual={};after_private=0
for m in targets:
 p=V/'.lake/build/lib/lean'/(m.replace('.','/')+'.ilean')
 for raw in json.load(open(p))['decls']:
  if raw.startswith('_private.'):
   name=private_user_name(m,raw);assert (m,name) not in actual,(m,name);actual[m,name]=raw;after_private+=1;rule(raw,identity(m,name))
missing=[{'old_module':m,'old_kernel_name':n,'expected':list(dest)} for (m,n),dest in expected.items() if dest not in actual]
(W/'private-notation-owned-names.json').write_text(json.dumps(notation_generated,ensure_ascii=False,indent=2));plan['private_normalization']=dict(owned);(W/'preservation-module-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2));(W/'owned-comparison-name-map.json').write_text(json.dumps(rawrules,ensure_ascii=False,indent=2));(W/'owned-private-rules-summary.json').write_text(json.dumps({'before_source_private_bindings':len(private),'after_source_private_bindings':after_private,'raw_kernel_rules':sum(k.startswith('_private.') for k in rawrules),'unchanged_external_private_roots':external_roots,'missing_private_source_bindings':missing,'normalization':'Actual raw private kernel name -> intended/actual defining module + user name; public rules remain the reviewed v3b rules. Scope-specific normalization of private declaration rows avoids cross-module user-name collisions.'},ensure_ascii=False,indent=2));print('owned source-private rules',len(private),after_private,'missing',len(missing),flush=True)
if missing:raise SystemExit(1)
