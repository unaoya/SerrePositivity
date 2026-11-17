"""COW-copy only absent, byte-identical-source project caches; Lake must revalidate.
Run within a shared build ticket. Never overwrite any existing cache file.
This is an optimization, not a build receipt or a preservation check.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--donor',type=Path,action='append',required=True);p.add_argument('--graph',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();graph=json.load(gzip.open(a.graph));rows=[];skipped=0
for donor in a.donor:
 donor=donor.resolve();assert donor!=root;assert (donor/'.lake/build').resolve()!=(root/'.lake/build').resolve()
 for rel in ['lean-toolchain','lake-manifest.json','SerrePositivity/Util/Citation.lean']:assert sha(root/rel)==sha(donor/rel),(donor,rel)
 for module in sorted(graph):
  rel=module.replace('.','/');cache=Path('.lake/build/lib/lean')/rel;target=root/(str(cache)+'.olean');source=root/(rel+'.lean');other=donor/(rel+'.lean');original=donor/(str(cache)+'.olean')
  if target.exists() or not original.exists() or not source.exists() or not other.exists() or sha(source)!=sha(other):continue
  digest=sha(source);files=list(original.parent.glob(original.stem+'.*'));ir=donor/('.lake/build/ir/'+rel)
  files+=list(ir.parent.glob(ir.name+'.*'));material={p.relative_to(donor).as_posix():sha(p) for p in sorted(files) if p.is_file() and not p.name.endswith('.setup.json')};assert original.relative_to(donor).as_posix() in material
  if any((root/name).exists() and sha(root/name)!=h for name,h in material.items()):skipped+=1;continue
  copied=[name for name in material if not (root/name).exists()];by_parent={}
  for name in copied:by_parent.setdefault(str(Path(name).parent),[]).append(name)
  for parent,names in by_parent.items():
   dest=root/parent;dest.mkdir(parents=True,exist_ok=True);subprocess.run(['cp','-c','-n',*[str(donor/name) for name in names],str(dest)],check=True)
  for name,h in material.items():assert sha(root/name)==h,(module,name)
  assert sha(source)==sha(other)==digest
  rows.append(dict(module=module,donor=str(donor),source_sha256=digest,files=material,copied=copied))
result=dict(count=len(rows),skipped_existing_conflicts=skipped,rows=rows,policy='COW absent cache files only. Source, toolchain, manifest and Citation identical. No existing file overwritten. Ordinary Lake builds must validate dependency hashes; no check result reused.',time=time.time());a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(modules=len(rows),files=sum(len(r['copied']) for r in rows),skipped_existing_conflicts=skipped)))
