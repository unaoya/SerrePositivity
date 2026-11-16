"""Prepare existing v3b inputs from observed native owners on both sides.
No expression hashing/comparison logic is changed. No ordinal pairing is used.
"""
from pathlib import Path
from collections import defaultdict
import argparse,json,sys,hashlib,re
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--before',type=Path,required=True);p.add_argument('--after',type=Path,required=True);p.add_argument('--before-root',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();base=root/'formalization-plans/stage-ii/organize-einfinity-w1';a.output.mkdir(parents=True,exist_ok=True);plan=json.loads((base/'namespace-rewrite-map.json').read_text());sys.path.insert(0,str(root/'scripts/refactor'));from klw1_namespace import rename_prefix
before=json.loads(a.before.read_text());after=json.loads(a.after.read_text());mm={m:plan['modules'].get(m,m) for m in before['modules']};assert set(mm.values())==set(after['modules']);assert len(mm)==len(set(mm.values()))
actual={};duplicates=[]
for row in after['declarations']:
 key=row['module'],row['name'],row['is_private']
 if key in actual:duplicates.append(key)
 actual[key]=row
assert not duplicates,duplicates
rules={};private=defaultdict(dict);rows=[];missing=[];used=set()
public_targets={r['old']:r['new'] for r in plan['rows'] if not r['old'].startswith('_private.')}
source_declarations={}
def rule(old,new):
 if old in rules:assert rules[old]==new,(old,rules[old],new)
 rules[old]=new
for old in before['declarations']:
 module=old['module'];name=old['name'];new=rename_prefix(name,plan['namespaces'].get(module,{}))
 if not old['is_private']:
  if name in public_targets:new=public_targets[name]
  elif re.search(r'\.(?:congr_simp|eq_\d+)$',name):
   if module not in source_declarations:source_declarations[module]=json.loads((a.before_root/'.lake/build/lib/lean'/(module.replace('.','/')+'.ilean')).read_text())['decls']
   if old['kernel_name'] not in source_declarations[module]:new=rename_prefix(name,public_targets)
 target=mm[module];key=target,new,old['is_private']
 if key not in actual:missing.append(dict(old_module=module,old=name,expected_module=target,expected_name=new,private=old['is_private']));continue
 seen=actual[key];assert key not in used;used.add(key)
 if old['is_private']:
  private[module][name]=new;identity='@owned-private['+target+']:'+new;rule(old['kernel_name'],identity);rule(seen['kernel_name'],identity)
 elif name!=new:rule(name,new)
 rows.append(dict(old_module=module,old=name,old_kernel_name=old['kernel_name'],new_module=target,new=new,new_kernel_name=seen['kernel_name'],private=old['is_private']))
extra=[dict(module=k[0],name=k[1],private=k[2]) for k in actual if k not in used]
summary=dict(before_modules=len(before['modules']),after_modules=len(after['modules']),before_declarations=len(before['declarations']),after_declarations=len(after['declarations']),paired=len(rows),private=sum(r['private'] for r in rows),missing=missing,extra=extra,policy='Observed canonical names and actual native owners; no source-line or ordinal pairing. Existing v3b snapshot and comparator remain unchanged.',before_capture_sha256=hashlib.sha256(a.before.read_bytes()).hexdigest(),after_capture_sha256=hashlib.sha256(a.after.read_bytes()).hexdigest());(a.output/'owner-pairing-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
if missing or extra:print('Unpaired native declarations',len(missing),len(extra));raise SystemExit(1)
for name in ['Init','Lean','Std','Mathlib','Batteries','Aesop','Qq','ProofWidgets','LeanSearchClient','ImportGraph','Plausible']:rule('_private.'+name,'@fixed-external-private['+name+']')
(a.output/'comparison-name-map.json').write_text(json.dumps(rules,ensure_ascii=False,indent=2)+'\n');(a.output/'preservation-module-plan.json').write_text(json.dumps(dict(modules=mm,namespaces=plan['namespaces'],private_normalization=dict(private)),ensure_ascii=False,indent=2)+'\n');(a.output/'actual-owner-pairs.json').write_text(json.dumps(dict(rows=rows),ensure_ascii=False,indent=2)+'\n');print('Observed pairs',len(rows),'private',sum(r['private'] for r in rows))
