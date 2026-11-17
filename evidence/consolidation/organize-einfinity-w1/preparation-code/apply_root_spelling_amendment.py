"""Apply only authenticated insertions of `_root_.` before HomotopicalAlgebra.
The initial whole-file application and its receipt are retained unchanged.
"""
from pathlib import Path
import argparse,hashlib,json,os
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--before',type=Path,required=True);p.add_argument('--preview',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--apply',action='store_true');a=p.parse_args();root=a.root.resolve();before=a.before.resolve();base=root/'evidence/consolidation/organize-einfinity-w1';read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest();initial=read(a.output/'application.json');assert initial['applied'];manifest=read(a.preview/'manifest.json');assert read(a.preview/'review.json')=={};assert read(a.preview/'summary.json')['plan_sha256']==initial['plan_sha256'];overlay=read(a.preview/'metadata-overlay.manifest.json');global_records=read(base/'reviewed-global-root-spellings.json');assert not global_records['pending'];auth={r['source']:r for r in global_records['records']};changed={};details=[];normalize=lambda b:b.replace(b'_root_.HomotopicalAlgebra',b'HomotopicalAlgebra')
for r in manifest:
 old,new=r['old_path'],r['new_path'];original=(before/old).read_bytes();assert sha(original)==r['source_sha256'];current=(root/new).read_bytes();expected=initial['paths_to_write'].get(new,r['source_sha256']);assert sha(current)==expected,new
 data=(a.preview/new).read_bytes();digest=r['preview_sha256']
 if new in overlay:assert overlay[new]['before_sha256']==digest;digest=overlay[new]['after_sha256']
 assert sha(data)==digest,new
 assert normalize(current)==normalize(data),('Not solely an absolute-root spelling insertion',new)
 additions=data.count(b'_root_.HomotopicalAlgebra')-current.count(b'_root_.HomotopicalAlgebra');assert additions>=0
 if data!=current:
  assert old in auth and additions>0;changed[new]=data;details.append(dict(old_path=old,new_path=new,before_sha256=sha(current),after_sha256=sha(data),root_qualifiers_added=additions))
for path,digest in initial['paths_to_write'].items():assert sha((root/path).read_bytes())==digest,path
for path in initial['paths_to_delete']:assert not (root/path).exists()
stable=read(base/'preparation/unchanged-scope-files.json');captured={r['old_path'] for r in manifest}
for path,digest in stable.items():
 if path not in captured:assert sha((root/path).read_bytes())==digest
record=dict(applied=False,initial_application_sha256=sha((a.output/'application.json').read_bytes()),source_changes=details,changed_files=len(changed),root_qualifiers_added=sum(r['root_qualifiers_added'] for r in details),global_records_sha256=sha((base/'reviewed-global-root-spellings.json').read_bytes()),preview_manifest_sha256=sha((a.preview/'manifest.json').read_bytes()),policy='Only `_root_.` insertions; every edited original span has an actual compiler namespace/constant resolution. No statement or proof modification; native v3b remains required.')
if a.apply:
 for path,data in changed.items():
  target=root/path;temp=target.with_name(target.name+'.oe-root-new');assert not temp.exists();temp.write_bytes(data);os.replace(temp,target)
 record['applied']=True
 combined=dict(initial);combined['paths_to_write']={**initial['paths_to_write'],**{path:sha(data) for path,data in changed.items()}};combined['root_spelling_amendment']=record;(a.output/'application-amended.json').write_text(json.dumps(combined,ensure_ascii=False,indent=2)+'\n')
(a.output/('root-spelling-amendment.json' if a.apply else 'root-spelling-amendment-dry-run.json')).write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n');(a.output/'root-spelling-paths-to-stage.nul').write_bytes(b''.join(path.encode()+b'\0' for path in sorted(changed)));print(json.dumps({k:record[k] for k in ['applied','changed_files','root_qualifiers_added']}))
