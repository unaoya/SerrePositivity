from pathlib import Path
import json,subprocess,time,datetime
W=Path('/tmp/bulk-b3prime')
print('Waiting without a build ticket for all106 formal audits; then one normally locked, bounded full verify.',flush=True)
while not (W/'all-audits-complete.json').exists():
 now=datetime.datetime.now()
 if 8<=now.hour<23:
  (W/'night-continuation-stop.json').write_text(json.dumps({'reason':'formal audits not complete by daytime boundary','time':now.isoformat()}));raise SystemExit(75)
 time.sleep(5)
d=json.loads((W/'all-audits-complete.json').read_text());assert d['count']==d['success']==106 and not d['failed']
print('All formal audits complete: starting normal full verify,4jobs32GB, shared bulk key, hard limit1750s.',flush=True)
p=subprocess.run(['python3',str(W/'full_verify_driver.py')]);print('Full verify driver exit',p.returncode,flush=True);raise SystemExit(p.returncode)
