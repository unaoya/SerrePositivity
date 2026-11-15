from pathlib import Path
import json,time
W=Path('/tmp/bulk-b3prime');p=W/'before-manifest.json';plan=json.loads(p.read_text());extra=json.loads((W/'additional-doc-modules.json').read_text());added=sorted(set(extra)-set(plan['modules']));plan['modules']+=added;plan['groups']+=[added[i:i+8] for i in range(0,len(added),8)];plan['comment_only_extension']={'modules':extra,'reason':'Approved R7-7/R8-9/R10-7 and CompletedTensor §10 shared core documentation; code-token equality guarded; full unchanged v3b still required'};p.write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
if added:
 done=W/'before/complete.json';assert done.exists();done.rename(done.with_name('complete.before-doc-extension-'+str(time.time_ns())+'.json'))
print('appended original snapshot modules',len(added),'full',len(plan['modules']),'semantic reference files unchanged',len(plan['reference_files']))
