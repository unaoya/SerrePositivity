from pathlib import Path
import json,subprocess,sys,re,tempfile,time
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');b=w/'before';plan=json.load(open(w/'namespace-rewrite-map.json'));sys.path.insert(0,str(r/'scripts/refactor'));import bulk_namespace as B;import klw1_namespace as K
migration=K.Migration(plan);out=w/'rewritten-delta';out.mkdir(exist_ok=True);done={};review={}
for index in sorted((w/'delta-captures').glob('*/files.json')):
 group=index.parent
 if group.name.endswith('-pending'):continue
 for rel,data in K.captures(b,K.file_list(index),group):
  preview,issues=B.rewrite(data,migration)
  if issues:review[rel]=issues;continue
  target=plan['modules'].get(data['module'],data['module']).replace('.','/')+'.lean'
  desired=r/target;current=desired.read_bytes() if desired.exists() else b''
  original=(b/rel).read_bytes()
  if current==original:merged=preview
  elif current==preview:merged=current
  else:
   with tempfile.TemporaryDirectory() as tmp:
    tmp=Path(tmp);(tmp/'current').write_bytes(current);(tmp/'original').write_bytes(original);(tmp/'rewrite').write_bytes(preview)
    p=subprocess.run(['git','merge-file','-p',str(tmp/'current'),str(tmp/'original'),str(tmp/'rewrite')],capture_output=True)
    if p.returncode:
     review[rel]=[{'kind':'overlapping-frozen-delta-rewrite','preview':str(out/target)}];f=out/target;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(p.stdout);continue
    merged=p.stdout
  f=out/target;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(merged)
  if merged!=current:desired.parent.mkdir(parents=True,exist_ok=True);desired.write_bytes(merged)
  done[rel]={'target':target,'changed':original!=merged}
(w/'delta-rewrite-status.json').write_text(json.dumps({'files':len(done),'changed':sum(x['changed'] for x in done.values()),'review':review,'rows':done},ensure_ascii=False,indent=2));print('rewritten',len(done),'review',len(review))
