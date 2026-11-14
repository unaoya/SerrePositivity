from pathlib import Path
import json,subprocess,os,datetime,hashlib,time
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout')
required=['root-build-complete.json','actual-preservation/complete.json','actual-citation-comparison.json','all-audits-complete.json']
for name in required:assert (W/name).exists(),name
all_audits=json.loads((W/'all-audits-complete.json').read_text());assert all_audits['success']==all_audits['count']==106 and not all_audits['failed']
application=json.loads((W/'actual-application.json').read_text())
for path,sha in application['paths_written'].items():assert hashlib.sha256((R/path).read_bytes()).hexdigest()==sha,path
now=datetime.datetime.now();assert now.hour>=23 or now.hour<8,'night-only'
budget=1750
if now.hour<8:budget=min(budget,int((now.replace(hour=8,minute=0,second=0,microsecond=0)-now).total_seconds())-20)
assert budget>=60
old=json.loads(Path('/tmp/bulk-w1-b3/verify-resource-plan.json').read_text());exclusive=set(old['exclusive_audits'])|{r['path'] for r in all_audits['results'] if r['peak_process_tree_rss_bytes']>=10_000_000_000}
settings={'VERIFY_JOBS':'4','VERIFY_MEMORY_GB':'32','VERIFY_CACHE':'0','VERIFY_EXCLUSIVE_AUDITS':' '.join(sorted(exclusive))}
for key in ['VERIFY_BASELINE','VERIFY_SKIP_BUILD','VERIFY_ONLY_AUDITS','VERIFY_EXTRA_AUDITS']:assert key not in os.environ,(key,'must use normal full verify')
(W/'verify-resource-plan.json').write_text(json.dumps({'settings':settings,'night_only':True,'shared_ticket_class':'bulk','max_ticket_seconds':budget,'all_audits':106,'prior_B3_seconds_jobs3':2968.3724,'note':'No previous KL-W1 exemption; hard stop before30minutes. A timeout is not a full verify pass. No audit or check removed.'},ensure_ascii=False,indent=2))
log=W/'full-verify.log';cmd=['zsh',str(R/'scripts/refactor/with_build_lock.sh'),'--wait','3600','--class','bulk','--','env',*[k+'='+v for k,v in settings.items()],'python3',str(W/'guard.py'),'--cwd',str(R),'--log',str(log),'--night-only','--seconds',str(budget),'--jobs','4','--threads','4','--','zsh','scripts/refactor/verify.sh']
with (W/'full-verify.lease.log').open('w') as out:p=subprocess.run(cmd,cwd=R,stdout=out,stderr=subprocess.STDOUT)
receipt=json.loads(log.with_suffix('.log.json').read_text());(W/'full-verify-attempt.json').write_text(json.dumps(receipt,indent=2));assert p.returncode==0 and receipt['rc']==0 and receipt['reason'] is None,receipt
summary=json.loads((R/'.lake/verify/summary.json').read_text());assert summary['gate'] is True and summary['status']=='PASS' and not summary['failures'],summary
(W/'full-verify-complete.json').write_text(json.dumps({'execution':receipt,'summary':summary,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'settings':settings,'time':time.time()},indent=2));print('FULL VERIFY PASS',flush=True)
