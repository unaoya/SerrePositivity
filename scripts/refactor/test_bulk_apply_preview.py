from pathlib import Path
import argparse
import subprocess,tempfile,hashlib,gzip,json
parser=argparse.ArgumentParser();parser.add_argument('--script',type=Path,default=Path(__file__).with_name('bulk_apply_preview.py'));parser.add_argument('--output',type=Path);args=parser.parse_args();SCRIPT=args.script.resolve();results=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def write_bundle(path,sources,outputs,deletions=()):
 with gzip.open(path,'wt') as f:json.dump({'schema_version':1,'sources':{k:sha(v) for k,v in sources.items()},'outputs':[{'source':s,'target':t,'sha256':sha(data),'edits':[{'start':0,'stop':len(sources[s]) if s else 0,'text':data.decode()}]} for s,t,data in outputs],'deletions':list(deletions)},f)
def call(root,bundle,ok,apply=False):
 r=subprocess.run(['python3','-B',str(SCRIPT),'--root',str(root),'--bundle',str(bundle),*(['--apply'] if apply else [])],text=True,capture_output=True);assert (r.returncode==0)==ok,(r.stdout,r.stderr);return r
with tempfile.TemporaryDirectory(prefix='bulk-apply-check-',dir='/tmp') as directory:
 w=Path(directory);root=w/'tree';root.mkdir();subprocess.run(['git','init','-q','-b','codex/fixture',str(root)],check=True);(root/'a.txt').write_bytes(b'original');(root/'c.txt').write_bytes(b'delete me');p=w/'bundle.gz';sources={'a.txt':b'original','c.txt':b'delete me'};write_bundle(p,sources,[('a.txt','new/b.txt',b'moved original'),('a.txt','a.txt',b'compatibility'),('c.txt','new/d.txt',b'rehomed')],['c.txt'])
 call(root,p,True);assert (root/'a.txt').read_bytes()==b'original' and not (root/'new').exists();results.append('read-only preflight')
 library_bundle=w/'library.gz';write_bundle(library_bundle,sources,[('a.txt','new/b.txt',b'moved original')]);
 with gzip.open(library_bundle,'rt') as f: library_data=json.load(f)
 library_data['library_sha256']=sha(b'reviewed implementation')
 with gzip.open(library_bundle,'wt') as f: json.dump(library_data,f)
 call(root,library_bundle,False,True);assert (root/'a.txt').read_bytes()==b'original';results.append('missing reviewed citation implementation rejected')
 (root/'new').mkdir();(root/'new/b.txt').write_bytes(b'collision');call(root,p,False,True);assert (root/'a.txt').read_bytes()==b'original' and (root/'c.txt').exists();(root/'new/b.txt').unlink();results.append('collision rejected before mutation')
 (root/'a.txt.bulk-preview-tmp').write_bytes(b'existing temporary file');call(root,p,False,True);assert (root/'a.txt').read_bytes()==b'original';(root/'a.txt.bulk-preview-tmp').unlink();results.append('temporary destination rejected before mutation')
 subprocess.run(['git','symbolic-ref','HEAD','refs/heads/main'],cwd=root,check=True);call(root,p,False,True);assert (root/'a.txt').read_bytes()==b'original';subprocess.run(['git','symbolic-ref','HEAD','refs/heads/codex/fixture'],cwd=root,check=True);results.append('main apply refused')
 call(root,p,True,True);assert (root/'a.txt').read_bytes()==b'compatibility' and (root/'new/b.txt').read_bytes()==b'moved original' and (root/'new/d.txt').read_bytes()==b'rehomed' and not (root/'c.txt').exists();results.append('move and old-path shim share the original safely')
 call(root,p,False,True);assert (root/'a.txt').read_bytes()==b'compatibility';results.append('stale original rejected')
 unsafe=w/'unsafe.gz';write_bundle(unsafe,{},[(None,'../escape.txt',b'bad')]);call(root,unsafe,False,True);assert not (w/'escape.txt').exists();results.append('parent traversal rejected')
 outside=w/'outside';outside.mkdir();(root/'link').symlink_to(outside,target_is_directory=True);write_bundle(unsafe,{},[(None,'link/escape.txt',b'bad')]);call(root,unsafe,False,True);assert not (outside/'escape.txt').exists();results.append('symlink escape rejected')
if args.output:args.output.write_text(json.dumps({'passed':len(results),'cases':results},indent=2))
print('apply-tool checks passed',len(results))
