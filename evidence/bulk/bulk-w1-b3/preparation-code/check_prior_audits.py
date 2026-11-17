"""Bind first-night successful audit receipts to unchanged committed sources."""
from pathlib import Path
import json,subprocess,tarfile,hashlib,datetime
W=Path('/tmp/bulk-w1-b3');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'evidence/bulk/bulk-w1-b3';head=json.load(open(W/'verified-source-checkpoint.json'))['head'];critical=['SerrePositivity','SerrePositivity.lean','scripts','research','lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain']
subprocess.run(['git','diff','--exit-code',head,'HEAD','--',*critical],cwd=R,check=True,stdout=subprocess.DEVNULL)
assert not subprocess.check_output(['git','status','--porcelain','--',*critical],cwd=R,text=True).strip()
saved=json.load(open(D/'all-audits-progress.json'));assert len(saved)==32 and saved==json.load(open(W/'all-audits-progress.json'))
proof=[]
with tarfile.open(D/'first-night-audit-logs.tar.gz') as archive:
 for i,row in enumerate(saved):
  assert row['rc']==0 and row['reason'] is None and row['command']==['env','LEAN_NUM_THREADS=1','lake','env','lean',row['path']]
  receipt=json.load(open(W/'all-audits'/f'{i:03}.log.json'));assert row=={'path':row['path'],**receipt}
  for suffix in ['.log','.log.json']:
   name=f'{i:03}'+suffix;current=(W/'all-audits'/name).read_bytes();old=archive.extractfile('all-audits/'+name).read();assert old==current
  proof.append({'path':row['path'],'source_sha256':hashlib.sha256((R/row['path']).read_bytes()).hexdigest(),'log_sha256':hashlib.sha256((W/'all-audits'/f'{i:03}.log').read_bytes()).hexdigest(),'rc':0})
result={'status':'PASS','retained_successful_audits':32,'unchanged_source_checkpoint':head,'critical_paths':critical,'proof':proof,'checked_at':datetime.datetime.now().isoformat(),'policy':'Retain actual successful checks on byte-identical committed inputs; no audit omitted; remaining 74 run once each, all full verify audits uncached.'};(W/'prior-audit-evidence-check.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));print('prior 32 audit receipts and logs identical; all critical sources unchanged',flush=True)
