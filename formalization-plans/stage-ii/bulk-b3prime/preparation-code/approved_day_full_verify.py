from pathlib import Path
import json,subprocess,os,datetime,hashlib,time
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout')
required=['root-build-complete.json','actual-preservation/complete.json','actual-citation-comparison.json','all-audits-complete.json']
for name in required:assert (W/name).exists(),name
all_audits=json.loads((W/'all-audits-complete.json').read_text());assert all_audits['success']==all_audits['count']==106 and not all_audits['failed']
application=json.loads((W/'actual-application.json').read_text())
for path,sha in application['paths_written'].items():assert hashlib.sha256((R/path).read_bytes()).hexdigest()==sha,path
source_roots=['SerrePositivity','SerrePositivity.lean','scripts','lakefile.toml','lake-manifest.json','lean-toolchain']
assert not subprocess.check_output(['git','diff','HEAD','--name-only','--',*source_roots],cwd=R,text=True).strip(),'uncommitted source changes'
assert not subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','SerrePositivity','scripts'],cwd=R,text=True).strip(),'untracked source changes'
main_increment=subprocess.check_output(['git','diff',application['main'],'main','--name-only','--',*source_roots],cwd=R,text=True).splitlines()
assert not main_increment,('main code increment needs capture/merge and revalidation before full verify',main_increment)
approval='2026-11-15 morning coordinator/user: one daytime full verify without shared key or time limit, VERIFY_JOBS=3 VERIFY_MEMORY_GB=24, large audits serial.'
old=json.loads(Path('/tmp/bulk-w1-b3/verify-resource-plan.json').read_text());exclusive=set(old['exclusive_audits'])|{r['path'] for r in all_audits['results'] if r['peak_process_tree_rss_bytes']>=10_000_000_000}
# Scheduling telemetry only: never reuse an audit result or verification cache.
import sys
sys.path.insert(0,str(R/'scripts/refactor'))
from verify_runner import read_stats,save_stat
stats=read_stats(R);stats_before={k:dict(v) for k,v in stats.items()};commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
for row in all_audits['results']:
 measured=max(row['peak_process_tree_rss_bytes'],stats.get(row['path'],{}).get('max_rss_bytes',0))
 save_stat(R,{'name':row['path'],'cached':False,'seconds':row['seconds'],'max_rss_bytes':measured,'measured_at':row['finished_local']},stats,commit)
(W/'verify-scheduling-telemetry.json').write_text(json.dumps({'scope':'Scheduling RSS/duration estimates only, no reused check result. Serial guard tree RSS conservatively includes Lake launcher; retain greater previous RSS.','before':stats_before,'after':stats,'source':'all-audits-complete.json'},indent=2))
settings={'VERIFY_JOBS':'3','VERIFY_MEMORY_GB':'24','VERIFY_CACHE':'0','VERIFY_EXCLUSIVE_AUDITS':' '.join(sorted(exclusive))}
for key in ['VERIFY_BASELINE','VERIFY_SKIP_BUILD','VERIFY_ONLY_AUDITS','VERIFY_EXTRA_AUDITS','SORRY_AUDIT_ROOT','SORRY_AUDIT_ALLOWED']:assert key not in os.environ,(key,'must use normal full verify')
(W/'verify-resource-plan.json').write_text(json.dumps({'settings':settings,'approval':approval,'night_only':False,'shared_key':False,'time_limit_seconds':None,'all_audits':106,'actual_process_tree_guard_bytes':32000000000,'note':'Official24GB scheduler with conservative observed RSS; an individually oversize audit runs alone. Existing32GB emergency guard retained. No result cache or omitted check.'},ensure_ascii=False,indent=2))
log=W/'full-verify.log';cmd=['env',*[k+'='+v for k,v in settings.items()],'python3',str(W/'approved_day_guard.py'),'--cwd',str(R),'--log',str(log),'--jobs','3','--threads','3','--','zsh','scripts/refactor/verify.sh']
with (W/'full-verify.approved.launcher.log').open('w') as out:p=subprocess.run(cmd,cwd=R,stdout=out,stderr=subprocess.STDOUT)
receipt=json.loads(log.with_suffix('.log.json').read_text());(W/'full-verify-attempt.json').write_text(json.dumps(receipt,indent=2));assert p.returncode==0 and receipt['rc']==0 and receipt['reason'] is None,receipt
summary=json.loads((R/'.lake/verify/summary.json').read_text());assert summary['gate'] is True and summary['status']=='PASS' and not summary['failures'],summary
assert summary['commit']==subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),summary['commit']
assert summary['counts']['audit']=={'success':106,'failure':0,'known':0} and summary['counts']['sorry']=={'success':1,'failure':0,'known':0} and summary['counts']['build']=={'success':2,'failure':0,'known':0},summary['counts']
assert summary['runner']['jobs']==3 and summary['runner']['cache_enabled'] is False,summary['runner']
scheduling=summary['runner']['scheduling'];assert scheduling['max_concurrent']<=3 and scheduling['memory_budget_bytes']==24_000_000_000 and scheduling['max_exclusive_concurrent']<=1,scheduling
assert exclusive<=set(scheduling['exclusive_audits'])|{'scripts/audit_axioms.lean'},scheduling['exclusive_audits']
import gzip
raw=(R/'.lake/verify/summary.json').read_bytes()
with gzip.open(W/'full-verify-summary.json.gz','wb') as target:target.write(raw)
compact={k:summary[k] for k in ['status','gate','summary','commit','seconds','audit_count','executed_audit_count','counts','failures','retried','new_audits']}
compact['runner']={k:summary['runner'][k] for k in ['jobs','cache_enabled','audit_pool_wall_seconds','audit_wall_seconds','retried','measurement_missing']}
compact['scheduling']={k:scheduling[k] for k in ['max_concurrent','memory_budget_bytes','max_reserved_rss_bytes','max_exclusive_concurrent','exclusive_audits']}
(W/'full-verify-complete.json').write_text(json.dumps({'execution':receipt,'summary':compact,'full_summary_sha256':hashlib.sha256(raw).hexdigest(),'full_summary':'full-verify-summary.json.gz','head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'settings':settings,'approval':approval,'shared_key':False,'time_limit_seconds':None,'time':time.time()},indent=2));print('FULL VERIFY PASS',flush=True)
