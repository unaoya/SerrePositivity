"""One authorized second-night batch; daytime waiting starts no builds or audits."""
from pathlib import Path
from zoneinfo import ZoneInfo
import datetime,subprocess,json,time,os
os.environ['TZ']='Asia/Tokyo';time.tzset()
W=Path('/tmp/bulk-w1-b3');tz=ZoneInfo('Asia/Tokyo');scheduled=datetime.datetime(2026,11,14,23,tzinfo=tz);deadline=datetime.datetime(2026,11,15,8,tzinfo=tz);state=W/'second-night-worker-status.json'
def status(stage,**extra):
 state.write_text(json.dumps({'pid':os.getpid(),'stage':stage,'scheduled':scheduled.isoformat(),'deadline':deadline.isoformat(),'now':datetime.datetime.now(tz).isoformat(),**extra},ensure_ascii=False,indent=2))
status('waiting until authorized night')
while datetime.datetime.now(tz)<scheduled:
 status('waiting until authorized night');time.sleep(30)
if datetime.datetime.now(tz)>=deadline:status('deadline passed; no heavy work started');raise SystemExit(75)
watch=subprocess.Popen(['python3','-B',str(W/'live_budget_watch.py'),'--root-pid',str(os.getpid()),'--output','second-night-budget-watch.json'])
idle=subprocess.Popen(['caffeinate','-i','-w',str(os.getpid())]);rc=1
try:
 status('revalidating unchanged inputs')
 for name in ['check_frozen_main.py','check_target_coverage.py','check_source_scope.py','independent_delta_replay.py','make_declaration_table.py']:
  cmd=['python3','-B',str(W/'guard.py'),'--cwd','/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout','--log',str(W/('second-night-'+name+'.log')),'--night-only','--seconds','1780','--','python3','-B',str(W/name)]
  r=subprocess.run(cmd)
  if r.returncode:rc=r.returncode;break
 else:
  status('root, all formal audits, full uncached verify')
  rc=subprocess.run(['python3','-B',str(W/'night_gates_v2.py')]).returncode
 status('gates terminal',rc=rc)
finally:
 watch.terminate();watch.wait()
 # The watcher handles SIGTERM by writing its final aggregate receipt.
 try:idle.terminate()
 except ProcessLookupError:pass
status('publishing observed result',rc=rc)
pub=subprocess.run(['python3','-B',str(W/'publish_second_night.py')]).returncode
status('finished',gates_rc=rc,publication_rc=pub)
raise SystemExit(rc or pub)
