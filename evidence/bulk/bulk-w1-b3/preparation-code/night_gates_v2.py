from pathlib import Path
import subprocess,json,os,time,datetime
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout')
from check_frozen_main import check as check_frozen_main
check_frozen_main()
assert (w/'preservation-complete.json').exists()
if not (w/'verified-source-checkpoint.json').exists():subprocess.run(['python3','-B',str(w/'verified_checkpoint.py')],check=True)
# No gate is selected out and no known-failure baseline is edited here.
def run(label,cmd,seconds=28800,env=None):
 check_frozen_main()
 log=w/(label+'.log');p=subprocess.run(['python3','-B',str(w/'guard.py'),'--cwd',str(r),'--log',str(log),'--night-only','--seconds',str(seconds),'--',*cmd],env=env,stdout=subprocess.DEVNULL);print(label,p.returncode,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 return json.load(open(str(log)+'.json'))
root=run('root-build',['lake','build','SerrePositivity']);(w/'root-build-complete.json').write_text(json.dumps(root,indent=2))
import sys
sys.path.insert(0,str(r/'scripts/refactor'));from audit_imports import audit_build_targets
paths=sorted({str(p.relative_to(r)) for p in (r/'scripts').glob('audit_*.lean')}|{str(p.relative_to(r)) for p in (r/'scripts/audit').rglob('*.lean')});manifest={line.strip() for line in (r/'scripts/refactor/audit_manifest.txt').read_text().splitlines() if line.strip() and not line.startswith('#')};assert set(paths)==manifest,{'unregistered':sorted(set(paths)-manifest),'missing':sorted(manifest-set(paths))}
(w/'all-audit-inventory.json').write_text(json.dumps({'audits':paths,'count':len(paths),'discovery':'all top-level audit_*.lean plus recursive scripts/audit/**/*.lean, exact manifest match'},indent=2));targets=sorted(audit_build_targets((r/path).read_text() for path in paths))
if targets:run('all-audit-prerequisites',['lake','build',*targets])
out=w/'all-audits';out.mkdir(exist_ok=True);results=[];failed=[]
for index,path in enumerate(paths):
 check_frozen_main()
 if 8<=datetime.datetime.now().hour<23:raise SystemExit('Night audit boundary')
 log=out/f'{index:03}.log';env=dict(os.environ,LEAN_NUM_THREADS='1');p=subprocess.run(['python3','-B',str(w/'guard.py'),'--cwd',str(r),'--log',str(log),'--night-only','--seconds','2400','--','env','LEAN_NUM_THREADS=1','lake','env','lean',path],env=env,stdout=subprocess.DEVNULL);record={'path':path,**json.load(open(str(log)+'.json'))};results.append(record);(w/'all-audits-progress.json').write_text(json.dumps(results,indent=2));print('audit',index+1,len(paths),p.returncode,path,flush=True)
 if p.returncode:failed.append(record)
 if record['reason']:raise SystemExit(p.returncode)
summary={'audits':len(paths),'success':sum(x['rc']==0 for x in results),'failed':failed,'results':results,'scheduling':'strictly serial, including every large audit','finished':time.time()};(w/'all-audits-results.json').write_text(json.dumps(summary,indent=2))
if failed:raise SystemExit(1)
(w/'all-audits-complete.json').write_text(json.dumps(summary,indent=2))
settings=json.load(open('/tmp/bulk-w1-b2/b3-heavy-audit-plan.json'));env=dict(os.environ)
for key in ['VERIFY_ONLY_AUDITS','VERIFY_SKIP_BUILD','VERIFY_EXTRA_AUDITS','VERIFY_BASELINE','SORRY_AUDIT_ROOT','SORRY_AUDIT_ALLOWED']:env.pop(key,None)
# Resource estimates only: never read or manufacture successful verification results.
stat_path=r/'.lake/verify/audit-stats.json';stat_path.parent.mkdir(parents=True,exist_ok=True)
try: measured_stats=json.load(open(stat_path))
except (OSError,ValueError):measured_stats={}
if not isinstance(measured_stats,dict):measured_stats={}
for result in results:
 previous=measured_stats.get(result['path'],{})
 if not isinstance(previous,dict):previous={}
 old_peak=previous.get('max_rss_bytes',0);old_seconds=previous.get('seconds',0)
 if not isinstance(old_peak,int) or old_peak<0:old_peak=0
 if not isinstance(old_seconds,(int,float)) or old_seconds<0:old_seconds=0
 measured_stats[result['path']]={**previous,'max_rss_bytes':max(old_peak,result['peak_process_tree_rss_bytes']),'seconds':max(old_seconds,result['seconds']),'resource_measurement':'current standalone PASS audit, resource scheduling only'}
stat_path.write_text(json.dumps(measured_stats,indent=2))
observed_large={x['path'] for x in results if x['peak_process_tree_rss_bytes']>=10_000_000_000}
exclusive=set(settings['VERIFY_EXCLUSIVE_AUDITS'].split())|observed_large
# audit_axioms is already run after the parallel pool by verify_runner; retaining
# it in the requested group also documents the measured size conservatively.
(w/'verify-resource-plan.json').write_text(json.dumps({'VERIFY_JOBS':4,'VERIFY_MEMORY_GB':32,'memory_budget_bytes':32_000_000_000,'VERIFY_CACHE':0,'exclusive_audits':sorted(exclusive),'observed_large_audits':sorted(observed_large),'scope':'Scheduling only; no audit removed, no cached result reused'},indent=2))
env.update(VERIFY_JOBS='4',VERIFY_MEMORY_GB='32',VERIFY_CACHE='0',VERIFY_EXCLUSIVE_AUDITS=' '.join(sorted(exclusive)))
record=run('full-verify',['zsh','scripts/refactor/verify.sh'],env=env);(w/'full-verify-complete.json').write_text(json.dumps(record,indent=2))
