"""Ordinary Lake build for every dependency of every official audit."""
from pathlib import Path
import argparse,hashlib,json,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--root-receipt',type=Path,required=True);p.add_argument('--targets',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();a.output.mkdir(parents=True,exist_ok=True);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();b=json.loads(a.root_receipt.read_text());assert b['returncode']==0
for path,h in b['source_sha256'].items():assert sha(root/path)==h,path
mods=json.loads(a.targets.read_text());assert len(mods)==len(set(mods));assert all((root/(m.replace('.','/')+'.lean')).exists() for m in mods);t=time.monotonic();r=subprocess.run(['lake','build',*mods],cwd=root)
for path,h in b['source_sha256'].items():assert sha(root/path)==h,path
record=dict(returncode=r.returncode,targets=len(mods),target_list_sha256=sha(a.targets),root_receipt_sha256=sha(a.root_receipt),seconds=time.monotonic()-t,policy='All official audit imports, ordinary Lake build, no selections or skipped dependencies');(a.output/('complete.json' if r.returncode==0 else 'failed.json')).write_text(json.dumps(record,indent=2)+'\n');raise SystemExit(r.returncode)
