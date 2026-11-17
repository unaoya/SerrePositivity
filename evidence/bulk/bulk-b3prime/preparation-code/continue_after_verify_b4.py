from pathlib import Path
import datetime,time,subprocess,json
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout')
print('Waiting without a ticket for full verify completion before the B4 regression.',flush=True)
while not (W/'full-verify-complete.json').exists():
 if 8<=datetime.datetime.now().hour<23:raise SystemExit(75)
 time.sleep(5)
cmd=['zsh',str(R/'scripts/refactor/with_build_lock.sh'),'--wait','3600','--class','bulk','--','python3',str(W/'guard.py'),'--cwd',str(R),'--log',str(W/'B4-native-regression.log'),'--night-only','--seconds','1650','--jobs','1','--threads','1','--','python3',str(W/'test_b4_native_after.py')]
p=subprocess.run(cmd,cwd=R);raise SystemExit(p.returncode)
