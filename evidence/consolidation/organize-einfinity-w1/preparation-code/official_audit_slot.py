"""Run every official audit, with source-pinned resumable receipts, in one bounded lease.
This is the separate formal-audit gate, not a replacement for normal full verify.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,sys,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--budget',type=int,required=True);p.add_argument('--first-audit');a=p.parse_args();root=a.root.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);start=time.monotonic();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=sorted({p.relative_to(root).as_posix() for p in (root/'scripts').glob('audit_*.lean')}|{p.relative_to(root).as_posix() for p in (root/'scripts/audit').rglob('*.lean')});manifest=[s.strip() for s in (root/'scripts/refactor/audit_manifest.txt').read_text().splitlines() if s.strip() and not s.startswith('#')];assert len(manifest)==len(set(manifest)) and set(paths)==set(manifest);assert len(paths)==106
sys.path.insert(0,str(root/'scripts/refactor'));from audit_imports import audit_build_targets
targets=audit_build_targets((root/p).read_text() for p in paths);(out/'inventory.json').write_text(json.dumps(dict(audits=paths,count=len(paths),build_targets=targets,policy='Every official audit, exact manifest equality, no selection or exclusions'),indent=2)+'\n')
inputs=[root/'SerrePositivity.lean',*(root/'SerrePositivity').rglob('*.lean'),root/'lakefile.toml',root/'lake-manifest.json',root/'lean-toolchain',root/'research/bibliography.json',*(root/'scripts/refactor').glob('*.py'),*(root/p for p in paths)];hashes={p.relative_to(root).as_posix():sha(p) for p in sorted(inputs)};signature=hashlib.sha256(json.dumps(hashes,sort_keys=True).encode()).hexdigest();results=[];resumed_legacy=[]
equivalence_path=out/'input-equivalence.json';equivalence=json.loads(equivalence_path.read_text()) if equivalence_path.exists() else {};equivalence_sha256=sha(equivalence_path) if equivalence else None
order=list(range(len(paths)))
if a.first_audit:
 assert a.first_audit in paths
 first=paths.index(a.first_audit);order.remove(first);order.insert(0,first)
for i in order:
 path=paths[i]
 receipt=out/f'{i:03}.json';old=json.loads(receipt.read_text()) if receipt.exists() else {}
 reviewed=equivalence.get('valid_legacy_receipts',{}).get(path,{})
 equivalent=(equivalence.get('current_signature')==signature and reviewed.get('receipt_sha256')==sha(receipt) and reviewed.get('source_sha256')==hashes[path] and reviewed.get('legacy_signature')==old.get('signature')) if receipt.exists() else False
 if (old.get('signature')==signature or equivalent) and old.get('returncode')==0:
  assert old['source_sha256']==hashes[path]
  if equivalent:old={**old,'unchanged_inputs_equivalence_sha256':equivalence_sha256};resumed_legacy.append(path)
  results.append(old);continue
 left=int(a.budget-(time.monotonic()-start)-15)
 if left<100:break
 log=out/f'{i:03}.log'
 if log.exists():log.rename(out/f'{i:03}.history-{time.time_ns()}.log')
 t=time.monotonic();timing=out/f'{i:03}.time'
 with log.open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(left),'/usr/bin/time','-l','-o',str(timing),'lake','env','lean',path],cwd=root,env=os.environ|{'LEAN_NUM_THREADS':'1'},stdout=f,stderr=subprocess.STDOUT)
 rss_match=re.search(r'(?m)^\s*(\d+)\s+maximum resident set size\s*$',timing.read_text()) if timing.exists() else None
 row=dict(path=path,source_sha256=hashes[path],signature=signature,returncode=r.returncode,seconds=time.monotonic()-t,log=str(log),max_rss_bytes=int(rss_match[1]) if rss_match else None,measured_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),time_log=str(timing));(out/f'{i:03}.attempt.json').write_text(json.dumps(row,indent=2)+'\n');print(i+1,len(paths),path,r.returncode,round(row['seconds'],2),flush=True)
 if r.returncode in (124,137):break
 if r.returncode:raise SystemExit(1)
 receipt.write_text(json.dumps(row,indent=2)+'\n');results.append(row)
assert all(sha(root/p)==h for p,h in hashes.items()),'Inputs changed during audit gate'
summary=dict(resumed_legacy_audits=resumed_legacy,input_equivalence_sha256=equivalence_sha256,count=len(paths),success=len(results),complete=len(results)==len(paths),failed=[],results=results,signature=signature,input_sha256=hashes,seconds=time.monotonic()-start,policy='All formal audits serially, actual execution rc0; full verify remains separate');(out/'progress.json').write_text(json.dumps(summary,indent=2)+'\n')
if summary['complete']:(out/'complete.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['count','success','complete','seconds']}));raise SystemExit(0 if summary['complete'] else 75)
