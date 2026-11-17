from pathlib import Path
import subprocess,json,time
w=Path('/tmp/bulk-w1-b3')
while not (w/'delta-follow-complete.json').exists() or not (w/'collect-guarded.log.json').exists():time.sleep(10)
guard=json.load(open(w/'collect-guarded.log.json'))
if guard['rc'] or guard['reason']:raise SystemExit('Collector has not finished successfully; inspect guard before building')
for script in ['build_before_missing.py','prepare_validation.py','target_build.py']:
 result=subprocess.run(['python3','-B',str(w/script)])
 if result.returncode:raise SystemExit(result.returncode)
