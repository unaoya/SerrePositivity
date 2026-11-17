"""One ordinary root-build attempt; invoke under the bounded night bulk guard."""
from pathlib import Path
import argparse,hashlib,json,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--warm-donor',type=Path,action='append',default=[]);p.add_argument('--graph',type=Path);a=p.parse_args();root=a.root.resolve();a.output.mkdir(parents=True,exist_ok=True);start=time.monotonic()
if a.warm_donor:
 assert a.graph
 cmd=['python3',str(root/'evidence/consolidation/organize-einfinity-w1/preparation-code/warm_missing_cache.py'),'--root',str(root),'--graph',str(a.graph),'--output',str(a.output/'cache-warm-receipt.json')]
 for donor in a.warm_donor:cmd+=['--donor',str(donor)]
 subprocess.run(cmd,cwd=root,check=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();paths=[root/'SerrePositivity.lean',*(root/'SerrePositivity').rglob('*.lean'),root/'lean-toolchain',root/'lakefile.toml',root/'lake-manifest.json'];sources={p.relative_to(root).as_posix():sha(p) for p in paths};signature=hashlib.sha256(json.dumps(sources,sort_keys=True).encode()).hexdigest();cmd=['lake','build','SerrePositivity'];r=subprocess.run(cmd,cwd=root);assert all(sha(root/p)==h for p,h in sources.items()),'sources changed during root build';record=dict(command=cmd,returncode=r.returncode,seconds=time.monotonic()-start,signature=signature,source_sha256=sources,policy='Ordinary complete root build, no skipped dependencies or synthetic pass')
(a.output/('complete.json' if r.returncode==0 else 'failed.json')).write_text(json.dumps(record,indent=2)+'\n');raise SystemExit(r.returncode)
