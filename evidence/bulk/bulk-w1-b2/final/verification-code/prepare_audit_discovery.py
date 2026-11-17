from pathlib import Path
import json,gzip,hashlib,ast,os
w=Path('/tmp/bulk-w1-b2');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');v=w/'preview';t=w/'replay-tree';rel='scripts/refactor/verify.sh';old=(r/rel).read_text();needle="Path('scripts/audit').glob('*.lean')";assert old.count(needle)==1;new=old.replace(needle,"Path('scripts/audit').rglob('*.lean')");assert (v/rel).read_text() in [old,new] and (t/rel).read_text() in [old,new]
for root in [v,t]:(root/rel).write_text(new)
# Execute only the two real discovery AST statements, without running verify,
# touching preparation outputs, invoking Lean, or requesting another lease.
code=new.split("python3 - <<'PY'\n",1)[1].split('\nPY\n',1)[0];nodes=[]
for node in ast.walk(ast.parse(code)):
 if isinstance(node,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='audits' for x in node.targets):nodes.append(node)
 if isinstance(node,ast.AugAssign) and isinstance(node.target,ast.Name) and node.target.id=='audits':nodes.append(node)
nodes=sorted(nodes,key=lambda x:x.lineno)[:2];assert len(nodes)==2
scope={'Path':Path};os.chdir(v);exec(compile(ast.Module(body=nodes,type_ignores=[]),'<actual verify discovery statements>','exec'),scope);discovered=set(scope['audits']);manifest={s.strip() for s in (v/'scripts/refactor/audit_manifest.txt').read_text().splitlines() if s.strip() and not s.startswith('#')};nested={str(p.relative_to(v)) for p in (v/'scripts/audit/bs_power_root_envelope').glob('*.lean')};assert len(nested)==4 and nested<=discovered and not manifest-discovered,(manifest-discovered,nested-discovered)
manifest_rel='scripts/refactor/audit_manifest.txt';saved=w/'audit-discovery-original-manifest.txt'
if not saved.exists():
 assert (v/manifest_rel).read_bytes()==(t/manifest_rel).read_bytes();saved.write_bytes((v/manifest_rel).read_bytes())
old_manifest=saved.read_text();assert 'scripts/audit_bhatt_scholze_stage2.lean' not in old_manifest.splitlines();new_manifest=old_manifest.rstrip()+'\nscripts/audit_bhatt_scholze_stage2.lean\n'
for root in [v,t]:
 assert (root/manifest_rel).read_text() in [old_manifest,new_manifest];(root/manifest_rel).write_text(new_manifest)
manifest.add('scripts/audit_bhatt_scholze_stage2.lean');assert discovered==manifest
bundle={'schema_version':1,'math_base':'B2 preview after the move bundle; changes only nested audit discovery','sources':{rel:hashlib.sha256(old.encode()).hexdigest(),manifest_rel:hashlib.sha256(old_manifest.encode()).hexdigest()},'outputs':[{'source':rel,'target':rel,'sha256':hashlib.sha256(new.encode()).hexdigest(),'edits':[{'start':0,'stop':len(old.encode()),'text':new}]}],'deletions':[]}
bundle['outputs'].append({'source':manifest_rel,'target':manifest_rel,'sha256':hashlib.sha256(new_manifest.encode()).hexdigest(),'edits':[{'start':0,'stop':len(old_manifest.encode()),'text':new_manifest}]})
with (w/'audit-discovery-preview-edits.json.gz').open('wb') as raw:
 with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as f:f.write(json.dumps(bundle,separators=(',',':')).encode())
result={'status':'PASS','scope':'Prospective isolated verification script only; production shared verifier is unchanged. Root/full audits/verify not executed in B2.','change':'Recursive discovery of registered scripts/audit/bs_power_root_envelope/*.lean','actual_discovery_count':len(discovered),'manifest_count':len(manifest),'missing_manifest_entries':sorted(manifest-discovered),'unregistered_discovered':sorted(discovered-manifest),'new_nested_audits':sorted(nested),'original_script_sha256':hashlib.sha256(old.encode()).hexdigest(),'prospective_script_sha256':hashlib.sha256(new.encode()).hexdigest()};(w/'audit-discovery-check.json').write_text(json.dumps(result,indent=2));print(result)
