"""Normal, uncached, full verify after the independent OE-W1 gates.
Invoke inside the bounded NIGHT bulk guard. The coordinator asked us to retain
base 30ae8948f until the stopping point; do not merge the Citation update here.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,os,subprocess,sys,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--v3b',type=Path,required=True);p.add_argument('--citation',type=Path,required=True);p.add_argument('--root-receipt',type=Path,required=True);p.add_argument('--audits',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();a.output.mkdir(parents=True,exist_ok=True);(root/'.lake/verify').mkdir(parents=True,exist_ok=True);load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();v=load(a.v3b);c=load(a.citation);b=load(a.root_receipt);audits=load(a.audits)
assert v['complete'] and v['completed_modules']==v['total_modules']==1071 and not v['failure'];assert c['status']=='PASS' and not c['missing'] and not c['extra'];assert b['returncode']==0;assert audits['complete'] and audits['success']==audits['count']==106 and not audits['failed']
for record,field in [(b,'source_sha256'),(audits,'input_sha256')]:
 for path,digest in record[field].items():assert sha(root/path)==digest,path
source_roots=['SerrePositivity','SerrePositivity.lean','scripts','lakefile.toml','lake-manifest.json','lean-toolchain']
assert not subprocess.check_output(['git','diff','HEAD','--name-only','--',*source_roots],cwd=root,text=True).strip(),'uncommitted sources'
assert not subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','SerrePositivity','scripts'],cwd=root,text=True).strip(),'untracked sources'
for key in ['VERIFY_BASELINE','VERIFY_SKIP_BUILD','VERIFY_ONLY_AUDITS','VERIFY_EXTRA_AUDITS','SORRY_AUDIT_ROOT','SORRY_AUDIT_ALLOWED']:assert key not in os.environ,(key,'must use normal full verify')
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();sys.path.insert(0,str(root/'scripts/refactor'));from verify_runner import read_stats,save_stat
stats=read_stats(root);before={k:dict(v) for k,v in stats.items()};exclusive={'scripts/audit_axioms.lean','scripts/audit_einfinity.lean','scripts/audit_infinity_core.lean','scripts/audit_infinity_f1.lean','scripts/audit_infinity_f1b.lean','scripts/audit_infinity_presentable_localization.lean','scripts/audit_kst_s_construction.lean'}
for row in audits['results']:
 assert row['returncode']==0 and row['max_rss_bytes'] is not None
 measured=max(row['max_rss_bytes'],stats.get(row['path'],{}).get('max_rss_bytes',0));save_stat(root,dict(name=row['path'],cached=False,seconds=row['seconds'],max_rss_bytes=measured,measured_at=row['measured_at']),stats,commit)
 if measured>=10_000_000_000:exclusive.add(row['path'])
settings={'VERIFY_JOBS':'4','VERIFY_MEMORY_GB':'32','VERIFY_CACHE':'0','VERIFY_EXCLUSIVE_AUDITS':' '.join(sorted(exclusive))};(a.output/'scheduling-telemetry.json').write_text(json.dumps(dict(before=before,after=stats,policy='RSS/duration scheduling estimates only, no reused check results'),indent=2)+'\n');(a.output/'resource-plan.json').write_text(json.dumps(dict(settings=settings,base='30ae8948f339beec42d9340feb02f2031c22c72b',main_merge='deliberately deferred by user',all_audits=106),indent=2)+'\n')
t=time.monotonic();r=subprocess.run(['zsh','scripts/refactor/verify.sh'],cwd=root,env=os.environ|settings);assert r.returncode==0,('full verify failed',r.returncode)
s=load(root/'.lake/verify/summary.json');assert s['gate'] is True and s['status']=='PASS' and not s['failures'];assert s['commit']==commit;assert s['counts']['audit']==dict(success=106,failure=0,known=0) and s['counts']['sorry']==dict(success=1,failure=0,known=0) and s['counts']['build']==dict(success=2,failure=0,known=0);assert s['runner']['jobs']==4 and s['runner']['cache_enabled'] is False
sc=s['runner']['scheduling'];assert sc['max_concurrent']<=4 and sc['memory_budget_bytes']==32_000_000_000 and sc['max_exclusive_concurrent']<=1
raw=(root/'.lake/verify/summary.json').read_bytes()
with gzip.open(a.output/'summary.json.gz','wb') as f:f.write(raw)
result=dict(status='PASS',commit=commit,seconds=time.monotonic()-t,summary_sha256=hashlib.sha256(raw).hexdigest(),counts=s['counts'],settings=settings,gate_receipt_sha256={str(p):sha(p) for p in [a.v3b,a.citation,a.root_receipt,a.audits]});(a.output/'complete.json').write_text(json.dumps(result,indent=2)+'\n');print('OE-W1 FULL VERIFY PASS',flush=True)
