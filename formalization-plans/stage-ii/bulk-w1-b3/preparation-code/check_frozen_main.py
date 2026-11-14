"""Allow only ordinary Markdown documentation updates under the approved roots."""
from pathlib import Path
import subprocess,json,datetime
W=Path('/tmp/bulk-w1-b3');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout')
def check():
 baseline=json.load(open(W/'baseline.json'))['frozen_main']
 head=subprocess.check_output(['git','rev-parse','main'],cwd=R,text=True).strip()
 paths=subprocess.check_output(['git','diff','--name-only','--no-renames',baseline,head],cwd=R,text=True).splitlines()
 forbidden=[]
 for path in paths:
  doc=path.startswith(('formalization-plans/','research/')) and path.endswith('.md')
  for ref in [baseline,head]:
   row=subprocess.check_output(['git','ls-tree',ref,'--',path],cwd=R,text=True).strip()
   if row and not row.startswith('100644 blob '):doc=False
  if not doc:forbidden.append(path)
 result={'status':'PASS' if not forbidden else 'FAIL','frozen_mathematical_main':'c5c4436c0','frozen_document_main':baseline,'observed_main':head,'allowed_document_paths':[p for p in paths if p not in forbidden],'forbidden_changes':forbidden,'authorization':'11-14 coordinator reply: documentation-only formalization-plans/research changes allowed; build/audit changes stop','checked_at':datetime.datetime.now().isoformat()}
 (W/'main-compatibility-check.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
 assert not forbidden,result
 return result
if __name__=='__main__':print(json.dumps(check(),ensure_ascii=False))
