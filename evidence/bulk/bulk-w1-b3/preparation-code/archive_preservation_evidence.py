"""Archive comparison receipts and validate saved snapshot byte hashes; no Lean runs."""
from pathlib import Path
import hashlib,json,tarfile,io
W=Path('/tmp/bulk-w1-b3');P=W/'preservation';R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'evidence/bulk/bulk-w1-b3';manifest=[];count=0;labels=[];members=[]
for receipt in sorted(P.glob('*.receipt.json')):
 data=json.load(open(receipt));assert data['status']=='PASS' and data['comparison_rc']==0 and not data['changes'],receipt
 label=receipt.name.removesuffix('.receipt.json');directory=P/label;count+=len(data['modules']);labels.append(label);members.append(receipt)
 for side in ['before','after']:
  capture=directory/(side+'.capture.json');c=json.load(open(capture));snapshot=directory/(side+'.json');digest=hashlib.sha256(snapshot.read_bytes()).hexdigest();assert digest==c['sha256'],snapshot
  manifest.append({'group':label,'side':side,'snapshot_sha256':digest,'snapshot_bytes':snapshot.stat().st_size,'capture_signature':c['signature'],'comparison_signature':data['signature']})
 for name in ['comparison.json','compare.log','before.capture.json','after.capture.json','before.resources','after.resources','before.log','after.log']:
  path=directory/name
  if path.exists():members.append(path)
assert count==10195,count
obj={'source_modules':count,'leaf_groups':len(labels),'raw_snapshot_hashes_verified':len(manifest),'snapshots':manifest,'policy':'Comparison receipts, reports, capture signatures and process resources; full snapshot bodies remain in the independent local before/after workspace, hashes retained here.'};(W/'preservation-evidence-manifest.json').write_text(json.dumps(obj,ensure_ascii=False,indent=2))
with tarfile.open(D/'preservation-evidence.tar.gz','w:gz') as archive:
 for path in members:archive.add(path,arcname='preservation/'+str(path.relative_to(P)))
 archive.add(W/'preservation-evidence-manifest.json',arcname='preservation-evidence-manifest.json')
(D/'preservation-evidence-summary.json').write_text(json.dumps({k:v for k,v in obj.items() if k!='snapshots'},ensure_ascii=False,indent=2));print({k:v for k,v in obj.items() if k!='snapshots'})
