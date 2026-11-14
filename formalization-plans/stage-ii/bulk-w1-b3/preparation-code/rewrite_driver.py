from pathlib import Path
import subprocess,json,time
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');last=-1
while True:
 complete=len([p for p in (w/'delta-captures').glob('*/files.json') if not p.parent.name.endswith('-pending')])
 if complete!=last:
  p=subprocess.run(['python3','-B',str(w/'rewrite_ready_groups.py')],cwd=r)
  if p.returncode:raise SystemExit(p.returncode)
  s=json.load(open(w/'delta-rewrite-status.json'));print('capture groups',complete,'rewritten',s['files'],'review',len(s['review']),flush=True);last=complete
  if complete==58:
   if s['review']:raise SystemExit('Review items saved; resolve before target builds')
   assert s['files']==686;s['status']='PASS: exact original-environment sources collected and rewritten';(w/'delta-follow-complete.json').write_text(json.dumps(s,ensure_ascii=False,indent=2));break
 time.sleep(10)
