from pathlib import Path
import json,hashlib,shutil,os,time
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');A=Path('/tmp/bulk-b3prime-preview');manifest=json.loads((W/'final-bundle/manifest.json').read_text());copied=[];skipped=[];removed=[]
assert (W/'actual-application.json').exists()
for m,sha in manifest['files'].items():
 rel=m.replace('.','/');source=R/(rel+'.lean')
 if hashlib.sha256(source.read_bytes()).hexdigest()!=sha:skipped.append(m);continue
 assert hashlib.sha256((A/(rel+'.lean')).read_bytes()).hexdigest()==sha
 for folder in ['lib/lean','ir']:
  base=A/'.lake/build'/folder/rel;targetbase=R/'.lake/build'/folder/rel
  for file in base.parent.glob(base.name+'.*'):
   if file.name.endswith('.setup.json'):continue
   suffix=file.name[len(base.name):]
   if folder=='ir' and suffix not in ['.c','.c.hash']:continue
   target=targetbase.parent/file.name;target.parent.mkdir(parents=True,exist_ok=True);temp=target.with_name(target.name+'.bulk-copy-'+str(os.getpid()));shutil.copy2(file,temp);os.replace(temp,target);copied.append(str(target.relative_to(R)))
for path in manifest['delete_paths']:
 rel=path[:-5]
 for folder in ['lib/lean','ir']:
  base=R/'.lake/build'/folder/rel
  if not base.parent.exists():continue
  for file in base.parent.glob(base.name+'.*'):
   if file.is_file():file.unlink();removed.append(str(file.relative_to(R)))
(W/'verified-cache-install.json').write_text(json.dumps({'copied_files':len(copied),'module_sources_identical':len(manifest['files'])-len(skipped),'different_aggregate_sources_not_reused':skipped,'obsolete_artifact_files_removed':len(removed),'policy':'Copy only native artifacts from validated source-identical modules; atomic replace breaks cache hardlinks, no setup paths copied; normal Lake build still validates dependency traces.','time':time.time()},indent=2));print('cache files',len(copied),'source-identical modules',len(manifest['files'])-len(skipped),'skipped',skipped,'old artifacts removed',len(removed))
