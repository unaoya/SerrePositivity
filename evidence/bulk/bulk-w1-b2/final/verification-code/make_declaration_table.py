"""Exact owned names from current PASS snapshots, retaining unpaired compiler inventories."""
from pathlib import Path
from collections import ChainMap,Counter,defaultdict
import json,gzip,sys,hashlib,re
W=Path('/tmp/bulk-w1-b2');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');V=W/'preview';sys.path.insert(0,str(W));import bulk_compare as B
C=B.C;plan=json.load(open(W/'preservation-module-plan.json'));mm=plan['modules'];rules=json.load(open(W/'owned-comparison-name-map.json'));groups=json.load(open(W/'preservation-groups.json'));out=W/'preservation';splits=json.load(open(out/'splits.json')) if (out/'splits.json').exists() else {};before={};after={};sources={};checked=[];aux=[];compiler_parsers=set()
allold=[m for g in groups for m in g];allnew=sorted({mm.get(m,m) for m in allold}|{d for m in allold for d in plan.get('declarations',{}).get(m,{}).values()});globalhash=hashlib.sha256(json.dumps({m:hashlib.sha256((V/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in allnew},sort_keys=True).encode()).hexdigest()
binary_hash=hashlib.sha256((W/'private-snapshot/snapshot').read_bytes()).hexdigest();module_plan_hash=hashlib.sha256((W/'preservation-module-plan.json').read_bytes()).hexdigest()
def expected_signature(modules):
 targets=sorted({mm.get(m,m) for m in modules}|{d for m in modules for d in plan.get('declarations',{}).get(m,{}).values()})
 return hashlib.sha256(json.dumps({'module_plan_sha256':module_plan_hash,'snapshot_binary_sha256':binary_hash,'global_after_sources':globalhash,'modules':modules,'name_map':hashlib.sha256((W/'owned-comparison-name-map.json').read_bytes()).hexdigest(),'comparator_sha256':hashlib.sha256((W/'bulk_compare.py').read_bytes()).hexdigest(),'before_sources':{m:hashlib.sha256((R/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in modules},'after_sources':{m:hashlib.sha256((V/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in targets},**({'strict_term_structure':True} if modules and all('.Project.Compatibility.' in m for m in modules) else {})},sort_keys=True).encode()).hexdigest()
def consume(modules,label):
 if label in splits:
  n=len(modules)//2;consume(modules[:n],label+'a');consume(modules[n:],label+'b');return
 receipt=json.load(open(out/(label+'.receipt.json')));assert receipt['status']=='PASS' and receipt['comparison_rc']==0 and receipt['signature']==expected_signature(modules),label;checked.extend(modules);directory=out/label
 for side,index in [('before',before),('after',after)]:
  data=json.load(open(directory/(side+'.json')))
  if side=='before':
   _,parsers=B.parser_self_projection(data);compiler_parsers.update((r['module'],r['name']) for r in parsers)
  for source in data['sources']:sources[side,source['module']]=source['source']
  for row in data['declarations']:
   key=row['module'],row['name']
   if key in index:assert index[key]==row,key
   index[key]=row
 aux.append({'group':label,'auxiliary_groups':json.load(open(directory/'comparison.json')).get('auxiliary_groups',{}),'parser_self_identity_companions':json.load(open(directory/'comparison.json')).get('parser_self_identity_companions',{})})
for i,modules in enumerate(groups):consume(modules,f'{i:04}')
assert set(checked)==set(allold) and len(checked)==len(allold)
by_module=defaultdict(list)
for (m,n),r in before.items():by_module[m].append(r)
authored={};parents={};transients={}
for m,rs in by_module.items():
 try:ns=set(C.parse_source(C.declaration_source(sources['before',m]),snapshot={'declarations':rs},module=m).declarations)
 except C.Unsupported:ns=set()
 authored[m]=ns;transients[m]=set(C.transient_names({'sources':[{'module':m,'source':C.declaration_source(sources['before',m])}],'declarations':rs}));by_name={r['name']:r for r in rs}
 for r in rs:parents[m,r['name']]=(C.declaration_owner(r,ns,by_name) if ns else None) or r['parent']
raw_private={}
for side,modules,root in [('before',allold,W/'baseline-build/lib/lean'),('after',allnew,V/'.lake/build/lib/lean')]:
 for m in modules:
  data=json.load(open(root/(m.replace('.','/')+'.ilean')))
  for n,rng in data['decls'].items():
   if n.startswith('_private.'):
    canonical=re.sub(r'^_private\.'+re.escape(m)+r'\.\d+\.','',n);raw_private[side,m,canonical]=n
actual_storage={(r['module'],r['old']):r for r in json.load(open(W/'actual-storage-name-corrections.json'))['rows']}
rows=[];unmatched=[];mappedafter=set();unexpected=[]
for (owner,name),row in sorted(before.items()):
 parent=parents[owner,name];dest=plan.get('declarations',{}).get(owner,{});new_owner=dest.get(name,dest.get(parent,mm.get(owner,owner)));preferred=C.normalize_generated_name(C.rename(name,plan.get('private_normalization',{}).get(owner,{}) if row.get('is_private',False) else rules),ChainMap({owner:new_owner},mm));inventory_only=(owner,name) in compiler_parsers or name in transients[owner] or C.notation_auxiliary(name,owner,authored[owner]) or (name not in authored[owner] and parent!=name and row['reference_kind'] in ['proof','generated']);preferred=actual_storage.get((owner,name),{}).get('new',preferred);target=preferred if not inventory_only and (new_owner,preferred) in after else None
 if target is None:
  permitted=inventory_only
  if not permitted:unexpected.append({'module':owner,'name':name,'parent':parent,'reference_kind':row['reference_kind']})
  status='compiler-inventory-only';unmatched.append({'module':owner,'name':name,'parent':parent,'reference_kind':row['reference_kind']})
 else:
  mappedafter.add((new_owner,target));status='name-renamed' if name!=target else 'module-moved' if owner!=new_owner else 'identity'
 rows.append({'old_module':owner,'old':name,'new_module':new_owner,'new':target,'status':status,'old_kernel_name':row.get('kernel_name',raw_private.get(('before',owner,name),name)),'new_kernel_name':after[new_owner,target].get('kernel_name',raw_private.get(('after',new_owner,target),target)) if target else None,'private':row.get('is_private',False),'source_private':('before',owner,name) in raw_private,'compiler_parser_descriptor':(owner,name) in compiler_parsers,'kind':row['kind'],'reference_kind':row['reference_kind'],'old_source_range':row.get('source_range'),'new_source_range':after[new_owner,target].get('source_range') if target else None})
assert not unexpected,unexpected[:20]
def gzwrite(path,records):
 with path.open('wb') as raw:
  with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as stream:
   for row in records:stream.write((json.dumps(row,ensure_ascii=False,separators=(',',':'))+'\n').encode())
output=W/'declaration-names.jsonl.gz';gzwrite(output,rows)
for side,index in [('before',before),('after',after)]:gzwrite(W/('declaration-inventory-'+side+'.jsonl.gz'),[{'module':m,'name':n,'kernel_name':r.get('kernel_name',raw_private.get((side,m,n),n)),'kind':r['kind'],'reference_kind':r['reference_kind'],'is_private':r.get('is_private',False),'source_range':r.get('source_range')} for (m,n),r in sorted(index.items())])
gzwrite(W/'declaration-generated-groups.jsonl.gz',aux)
summary={'before_declaration_records':len(before),'after_declaration_records':len(after),'source_modules':len(checked),'statuses':dict(Counter(r['status'] for r in rows)),'private_source_declarations':sum(r['source_private'] for r in rows),'unmatched_authored':len(unexpected),'unmatched_compiler_inventory':len(unmatched),'unpaired_after_inventory':len(set(after)-mappedafter),'sha256':hashlib.sha256(output.read_bytes()).hexdigest(),'pairing_policy':'Actual canonical owned names only; compiler-sharing groups retained separately, never ordinal-paired'};(W/'declaration-table-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print('declaration table',len(rows),'authored unmatched',len(unexpected),'compiler inventory',len(unmatched),flush=True)
