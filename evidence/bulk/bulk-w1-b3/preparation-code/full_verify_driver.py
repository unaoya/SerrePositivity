from pathlib import Path
import subprocess,json,os,time,datetime,math
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout')
from check_frozen_main import check as check_frozen_main
check_frozen_main()
summary=json.load(open(w/'all-audits-complete.json'));results=summary['results'];assert summary['success']==summary['audits']==len(results)==106 and not summary['failed'] and all(x['rc']==0 and x['reason'] is None for x in results)
subprocess.run(['python3','-B',str(w/'check_source_scope.py')],check=True)
subprocess.run(['python3','-B',str(w/'check_target_coverage.py')],check=True)
watcher=subprocess.Popen(['python3','-B',str(w/'live_budget_watch.py'),'--root-pid',str(os.getpid()),'--output','full-verify-aggregate-budget.json'])
idle=subprocess.Popen(['caffeinate','-i','-w',str(os.getpid())])
def run(label,cmd,seconds=43200,env=None,jobs=1,threads=1):
 check_frozen_main()
 log=w/(label+'.log');p=subprocess.run(['python3','-B',str(w/'guard.py'),'--cwd',str(r),'--log',str(log),'--seconds',str(seconds),'--jobs',str(jobs),'--threads',str(threads),'--',*cmd],env=env,stdout=subprocess.DEVNULL);print(label,p.returncode,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 return json.load(open(str(log)+'.json'))
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
 if not isinstance(old_seconds,(int,float)) or not math.isfinite(old_seconds) or old_seconds<0:old_seconds=0
 measured_stats[result['path']]={**previous,'max_rss_bytes':max(old_peak,result['peak_process_tree_rss_bytes']),'seconds':max(old_seconds,result['seconds']),'resource_measurement':'current standalone PASS audit, resource scheduling only'}
stat_path.write_text(json.dumps(measured_stats,indent=2))
observed_large={x['path'] for x in results if x['peak_process_tree_rss_bytes']>=10_000_000_000}
exclusive=set(settings['VERIFY_EXCLUSIVE_AUDITS'].split())|observed_large
# audit_axioms is already run after the parallel pool by verify_runner; retaining
# it in the requested group also documents the measured size conservatively.
verify_jobs,verify_memory=((3,24) if 8<=datetime.datetime.now().hour<23 else (4,32))
(w/'verify-resource-plan.json').write_text(json.dumps({'VERIFY_JOBS':verify_jobs,'VERIFY_MEMORY_GB':verify_memory,'memory_budget_bytes':verify_memory*1_000_000_000,'authorization':'11-14 morning: serial audits allowed during daytime; full verify 3 jobs/24 GB during day, 4/32 optional at night','VERIFY_CACHE':0,'exclusive_audits':sorted(exclusive),'observed_large_audits':sorted(observed_large),'scope':'Scheduling only; no audit removed, no cached result reused'},indent=2))
env.update(VERIFY_JOBS=str(verify_jobs),VERIFY_MEMORY_GB=str(verify_memory),VERIFY_CACHE='0',VERIFY_EXCLUSIVE_AUDITS=' '.join(sorted(exclusive)))
record=run('full-verify',['zsh','scripts/refactor/verify.sh'],env=env,jobs=verify_jobs,threads=verify_jobs);(w/'full-verify-complete.json').write_text(json.dumps(record,indent=2))
