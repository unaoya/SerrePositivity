"""Collect an original formal audit at night, with the same unchanged frontend setup.
Audits execute their original checks; they are not treated as small daytime sources.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,sys,tempfile,time,zoneinfo
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--tools',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--file',required=True,choices=['scripts/audit_einfinity.lean','scripts/audit_bhatt_scholze_stage2.lean']);p.add_argument('--budget',type=int,default=1600);a=p.parse_args();now=datetime.datetime.now(zoneinfo.ZoneInfo('Asia/Tokyo'));assert now.hour>=23 or now.hour<8,'Original formal audit capture is night-only';assert 0<a.budget<=1650;root=a.root.resolve();tools=a.tools.resolve();assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()=='30ae8948f339beec42d9340feb02f2031c22c72b';out=a.output.resolve();caps=out/'captures';caps.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(tools));import bulk_collect as B;from klw1_namespace import checked_capture,module_name
sha=lambda b:hashlib.sha256(b).hexdigest();source_sha=sha((root/a.file).read_bytes());helper_sha=sha(B.patched_helper((tools/'klw1_collect_refs.lean').read_text()).encode());module=module_name(a.file);target=caps/(module+'.json');receipt=caps/(module+'.receipt.json')
if receipt.exists() and target.exists():
 r=json.loads(receipt.read_text())
 if r['source_sha256']==source_sha and r['helper_sha']==helper_sha and r['capture_sha256']==sha(target.read_bytes()) and r['returncode']==0:
  checked_capture(root,a.file,target);print('Validated existing successful audit capture',a.file);raise SystemExit(0)
os.environ['LEAN_NUM_THREADS']='1';start=time.monotonic()
with tempfile.TemporaryDirectory(prefix='oe-audit-original-') as td:
 td=Path(td);(td/'files.json').write_text(json.dumps([a.file]));dest=td/'output';cmd=[sys.executable,str(tools/'bulk_namespace.py'),'collect','--root',str(root),'--files',str(td/'files.json'),'--output',str(dest)]
 with (caps/(module+'.log')).open('w') as log:r=subprocess.run(['gtimeout','--kill-after=3s',str(a.budget),*cmd],cwd=root,stdout=log,stderr=subprocess.STDOUT)
 rec=dict(policy='Original formal audit executed at night; not a small daytime mathematical-source capture',source=a.file,source_sha256=source_sha,helper_sha=helper_sha,returncode=r.returncode,seconds=time.monotonic()-start,started_jst=now.isoformat(),budget=a.budget,command=cmd)
 if r.returncode==0:
  data=checked_capture(root,a.file,dest/(module+'.json'));assert data['elaboration']['collector_sha256']==helper_sha;target.write_bytes((dest/(module+'.json')).read_bytes());rec.update(capture_sha256=sha(target.read_bytes()),refs=len(data['refs']),commands=len(data['commands']));receipt.write_text(json.dumps(rec,ensure_ascii=False,indent=2)+'\n')
 (out/('audit-'+module+'-attempt.json')).write_text(json.dumps(rec,ensure_ascii=False,indent=2)+'\n');print(json.dumps(rec),flush=True);raise SystemExit(r.returncode)
