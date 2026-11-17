"""Choose a compiler-reference chunk at actual lease acquisition time (JST)."""
from pathlib import Path
import datetime,subprocess,sys,zoneinfo
now=datetime.datetime.now(zoneinfo.ZoneInfo('Asia/Tokyo'));night=now.hour>=23 or now.hour<8
seconds=1680 if night else 280
if now.hour<8:seconds=min(seconds,int((now.replace(hour=8,minute=0,second=0,microsecond=0)-now).total_seconds())-15)
if seconds<100:
 print('Near 08:00: release the lease and resume outside this night chunk',flush=True);raise SystemExit(77)
print('Actual lease chunk',dict(jst=now.isoformat(),guard_seconds=seconds,collector_budget=seconds-15,per_file_timeout_ceiling=190),flush=True)
leaf=Path(__file__).with_name('collect_reference_parallel_slot.py');command=['gtimeout','--kill-after=5s',str(seconds),sys.executable,str(leaf),*sys.argv[1:],'--budget',str(seconds-15)]
raise SystemExit(subprocess.run(command).returncode)
