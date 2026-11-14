"""Choose the limit after acquisition, so queueing across 08:00 cannot use a night lease."""
from pathlib import Path
import datetime,subprocess,sys,os,json,time
now=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=9)))
day=8<=now.hour<23 or (now.hour==7 and now.minute>=50)
outer=280 if day else 580
inner=outer-30
print(json.dumps({'slot_started':now.isoformat(),'outer_limit_seconds':outer,'worker_budget_seconds':inner,'day_rule':day,'script':sys.argv[1]}),flush=True)
r=subprocess.run(['gtimeout','--kill-after=3s',str(outer),sys.executable,'-B',sys.argv[1]],env=dict(os.environ,BULK_SLOT_SECONDS=str(inner)))
raise SystemExit(r.returncode)
