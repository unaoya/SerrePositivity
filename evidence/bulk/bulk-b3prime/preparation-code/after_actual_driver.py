from pathlib import Path
import subprocess
W=Path('/tmp/bulk-b3prime');assert (W/'actual-preservation/complete.json').exists()
for script,args in [('run_leased_stage.py',['citations-actual']),('compare_actual_citations.py',[]),('formal_audit_driver.py',[])]:
 print('start actual stage',script,*args,flush=True);p=subprocess.run(['python3',str(W/script),*args])
 if p.returncode:raise SystemExit(p.returncode)
