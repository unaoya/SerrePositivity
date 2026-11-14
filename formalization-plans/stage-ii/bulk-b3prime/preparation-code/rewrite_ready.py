from pathlib import Path
import json,sys,hashlib,inspect
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');D=R/'formalization-plans/stage-ii/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));import klw1_namespace as K;import bulk_namespace as B
public=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];privates=json.loads((D/'source-private-map.proposed.json').read_text())['rows'];module_rows=json.loads((D/'module-map.proposed.json').read_text())['rows'];modules={r['old_module']:r['new_module'] for r in module_rows};byold={r['old']:r for r in public if r['old']!=r['new']};privby={(r['old_module'],r['old']):r for r in privates};captured=[]
byold['SerrePositivity.Inputs.exists_perfectoidization_of_finite']={'old':'SerrePositivity.Inputs.exists_perfectoidization_of_finite','new':'SerrePositivity.BhattScholze.exists_perfectoidization_of_finite','old_module':'SerrePositivity.Inputs.Perfectoidization','new_module':'SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence'}
for idx in sorted((W/'before').glob('refs-*/files.json')):
 for path,data in K.captures(R,K.file_list(idx),idx.parent):captured.append((path,data))
native={}
for file in (W/'before').glob('group-*.json'):
 if not file.with_name(file.stem+'.complete.json').exists():continue
 snap=json.loads(file.read_text())
 for row in snap['declarations']:
  native[(row['module'],row.get('kernel_name',row['name']))]=row
verified_binders=set()
for path,data in captured:
 raw=data['source'].encode()
 for ref in data['refs']:
  if ref['kind']!='binder' or ref['module']!=data['module']:continue
  row=native.get((ref['module'],ref['name']))
  if row is None:continue
  pos=row.get('source_range') or {};line=raw[:ref['start']].count(b'\n')+1
  literal=raw[ref['start']:ref['stop']].decode().removeprefix('_root_.');user=K.private_user_name(ref['module'],ref['name'])
  if pos.get('selection_start_line')==line and (user==literal or user.endswith('.'+literal)):
   verified_binders.add((ref['module'],ref['start'],ref['stop']))
rows={(r['old_module'],r['old']):{'module':r['old_module'],'old':r['old'],'new':r['new'],'new_module':r['new_module']} for r in byold.values()}
def disposition(ref):
 old=ref['name'];owner=ref['module'];user=K.private_user_name(owner,old)
 if old.startswith('_private.'):
  matches=[r for (m,n),r in privby.items() if m==owner and (user==n or user.startswith(n+'.'))]
 else:matches=[r for n,r in byold.items() if old==n or old.startswith(n+'.')]
 if not matches:return None
 base=max(matches,key=lambda r:len(r['old']));new=base['new']+user[len(base['old']):]
 return {'module':owner,'old':old,'new':new,'new_module':base['new_module']}
for path,data in captured:
 for ref in data['refs']:
  if not ref.get('name') or not ref.get('module'):continue
  row=disposition(ref)
  if row is None or row['old']==row['new']:continue
  # Keep dot syntax only through the actual receiver namespace. Do not invent opens from module paths.
  if (ref['kind']=='field' or ref.get('start',0)>0 and data['source'].encode()[ref['start']-1:ref['start']]==b'.') and not row['old'].startswith('_private.'):
   old_parent=row['old'].rpartition('.')[0];mapped=byold.get(old_parent,{}).get('new',old_parent)
   if mapped!=row['new'].rpartition('.')[0]:row['field_namespace']=old_parent
  key=row['module'],row['old']
  if key in rows:
   assert rows[key]['new']==row['new'];rows[key].update({k:v for k,v in row.items() if k=='field_namespace'})
  else:rows[key]=row
declaration_contexts={}
for path,data in captured:
 raw=data['source'].encode();starts=[0]
 for match in __import__('re').finditer(b'\n',raw):starts.append(match.end())
 for ref in data['refs']:
  if ref['kind']!='binder' or ref['module']!=data['module'] or (ref['module'],ref['start'],ref['stop']) not in verified_binders:continue
  target=rows.get((ref['module'],ref['name']));original=native.get((ref['module'],ref['name']))
  if not target or not original:continue
  old=K.private_user_name(ref['module'],ref['name']);new=target['new'];pos=original.get('source_range') or {}
  if old==new or not pos:continue
  lo=starts[pos['start_line']-1];hi=starts[pos['end_line']] if pos['end_line']<len(starts) else len(raw)
  declaration_contexts.setdefault(data['module'],[]).append((lo,hi,old,new))
def declaration_namespace(module,a,b,curr):
 matches=[x for x in declaration_contexts.get(module,[]) if x[0]<=a and b<=x[1]]
 if not matches:return curr
 lo,hi,old,new=min(matches,key=lambda x:x[1]-x[0])
 if curr==old or curr.startswith(old+'.'):return new+curr[len(old):]
 parent=old.rpartition('.')[0];dest=new.rpartition('.')[0]
 if parent and (curr==parent or curr.startswith(parent+'.')):return dest+curr[len(parent):]
 return curr
plan={'modules':modules,'rows':sorted(rows.values(),key=lambda r:(r['module'],r['old'])),'namespaces':{},'opens':{},'module_opens':{},'policy':'Preserve all original namespace/open bindings; fully qualify moved uses. Field exports only for actual indexed dot uses; no namespace inferred from module paths.'};migration=K.Migration(plan);(W/'namespace-rewrite-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2))
# Instrument only the unchanged rewriter return to retain its exact byte edits for split projection.
source=inspect.getsource(K.rewrite);assert source.count(B.OLD)==1;source=source.replace(B.OLD,B.NEW)
# Lean also emits a synthetic LocalInfo at a global declaration name. Require both
# its own-module global binder and the captured declaration-command range; never
# suppress locals at arbitrary term spans.
anchor='        for ref in candidates:\n            # The command elaborator'
assert source.count(anchor)==1
source=source.replace(anchor,'''        declaration_binder = (any(ref["kind"] == "binder" and ref["module"] == module and migration.target(ref) for ref in candidates)
                              and ((module,a,b) in _verified_binders or any(cmd["kind"] == "declaration-command" and "start" in cmd and cmd["start"] <= a and b <= cmd["stop"] for cmd in data["commands"])))
        for ref in candidates:
            # The command elaborator''')
source=source.replace('if field_binder and ref["kind"] == "local":','if (field_binder or declaration_binder) and ref["kind"] == "local":')
anchor='            new_curr = rename_prefix(curr, ns_map)'
assert source.count(anchor)==1
source=source.replace(anchor,anchor+'''
            if ref["kind"] == "term" and source[max(0,a-1):a] != b".":
                new_curr = _declaration_namespace(module,a,b,new_curr)''')
anchor='                if normal == old or (row.get("field_namespace") and old.endswith("." + normal)):'
assert source.count(anchor)==1
source=source.replace(anchor,'''                if (module,a,b) in _verified_binders and "." in normal and old.endswith("."+normal):
                    replacements.add("_root_."+name)
                elif normal == old or (row.get("field_namespace") and old.endswith("." + normal)):''')

# Preserve the exact original open binding even if a newly introduced namespace
# shadows its short spelling. Names come from the original native command capture,
# never from a moved module path; add no new namespace to the environment.
anchor='            if new_names == names and not ns_map:\n                continue'
assert source.count(anchor)==1
source=source.replace(anchor,"""            if new_names == names and not ns_map:
                if len(names) == 1 and mode in ("simple", "scoped"):
                    edit(row, "_root_." + names[0])
                continue""")

needle='    return (None if diagnostics else bytes(result)), diagnostics';assert source.count(needle)==1;scope=dict(vars(K));scope['_captured_edits']={};scope['_verified_binders']=verified_binders;scope['_declaration_namespace']=declaration_namespace;source=source.replace(needle,'    _captured_edits[data["module"]] = edits\n'+needle);exec(compile(source,'<B3prime verified rewrite instrumentation>','exec'),scope);rewrite=scope['rewrite'];out=W/'rewritten';out.mkdir(exist_ok=True);done={};review={}
for path,data in captured:
 preview,issues=rewrite(data,migration)
 if issues:review[path]=issues;continue
 mod=modules.get(data['module'],data['module']);target=mod.replace('.','/')+'.lean';p=out/target;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(preview);edits=scope['_captured_edits'][data['module']];(out/(data['module']+'.edits.json')).write_text(json.dumps([{'start':a,'stop':b,'replacement':v} for (a,b),v in sorted(edits.items())],ensure_ascii=False));done[path]={'target':target,'edits':len(edits),'source_sha256':hashlib.sha256(data['source'].encode()).hexdigest(),'preview_sha256':hashlib.sha256(preview).hexdigest()}
status={'captured':len(captured),'rewritten':len(done),'symbol_rows':len(rows),'field_exports':sum('field_namespace' in r for r in rows.values()),'review':review,'files':done,'plan_sha256':hashlib.sha256((W/'namespace-rewrite-plan.json').read_bytes()).hexdigest()};(W/'rewrite-status.json').write_text(json.dumps(status,ensure_ascii=False,indent=2));print('captured',len(captured),'rewritten',len(done),'review files',len(review),'symbol rows',len(rows));print([(k,len(v)) for k,v in review.items()][:20])
