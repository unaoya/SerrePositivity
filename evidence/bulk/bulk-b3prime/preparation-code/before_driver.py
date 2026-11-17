from pathlib import Path
import subprocess,datetime,time,json
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');i=0
while not (W/'before/complete.json').exists():
 now=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=9)));budget=1650 if now.hour>=23 or now.hour<8 else 270
 with (W/f'before-slot-{i:03}.log').open('a') as f:
  r=subprocess.run(['zsh',str(R/'scripts/refactor/with_build_lock.sh'),'--wait','3600','--class','bulk','--','gtimeout','--kill-after=5s',str(budget+5),'python3',str(W/'before_slot.py'),str(budget)],cwd=R,stdout=f,stderr=subprocess.STDOUT)
 print('slot',i,'rc',r.returncode,'budget',budget,flush=True);(W/'before-driver-progress.json').write_text(json.dumps({'slot':i,'rc':r.returncode,'budget':budget,'time':now.isoformat()}));i+=1
 if r.returncode not in [0,75]:raise SystemExit(r.returncode)
print('all before preparation complete',flush=True)
