"""Reconstruct indexed edits from frozen inputs, never from the current worktree."""
from pathlib import Path
import sys,json,gzip,subprocess,tempfile,re,hashlib
w=Path('/tmp/bulk-w1-b3');b=w/'before';r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(r/'scripts/refactor'));import bulk_namespace as B;import klw1_namespace as K
from bulk_apply_preview import replay
bundle=json.loads(gzip.decompress((w/'initial-rebased-bundle.json.gz').read_bytes()));plan=json.load(open(w/'namespace-rewrite-map.json'));migration=K.Migration(plan);status=json.load(open(w/'delta-rewrite-status.json'));targets={row['target'] for row in status['rows'].values()};initial={};sha=lambda data:hashlib.sha256(data).hexdigest()
fingerprints={'bundle':sha((w/'initial-rebased-bundle.json.gz').read_bytes()),'namespace_map':sha((w/'namespace-rewrite-map.json').read_bytes()),'helper':sha(Path(__file__).read_bytes()),'tools':{n:sha((r/'scripts/refactor'/n).read_bytes()) for n in ['bulk_namespace.py','klw1_namespace.py','bulk_apply_preview.py']},'before_delta':{rel:sha((b/rel).read_bytes()) for rel in status['rows']},'captures':{str(p.relative_to(w/'delta-captures')):sha(p.read_bytes()) for index in (w/'delta-captures').glob('*/files.json') if not index.parent.name.endswith('-pending') for p in index.parent.glob('*.json')}}
input_signature=sha(json.dumps(fingerprints,sort_keys=True).encode());receipt=w/'independent-delta-replay-check.json'
if receipt.exists():
 cached=json.load(open(receipt))
 if cached.get('input_signature')==input_signature and cached.get('status')=='PASS':
  rows=cached['output_rows'];assert len(rows)==686 and {row['source'] for row in rows}==set(status['rows'])
  for row in rows:
   assert all(sha((root/row['target']).read_bytes())==row['sha256'] for root in [w/'independent-replayed-delta',w/'rewritten-delta',r]),row['target']
  print('Independent replay input and current-output integrity PASS (reuse)',len(rows),flush=True);raise SystemExit(0)
for row in bundle['outputs']:
 if row['target'] not in targets:continue
 payload=replay((b/row['source']).read_bytes() if row['source'] else b'',row['edits']);assert sha(payload)==row['sha256'];initial[row['target']]=payload
out=w/'independent-replayed-delta';out.mkdir(exist_ok=True);results=[];root_spelling_resolutions=[];pat=re.compile(rb'^<<<<<<<[^\n]*\n(.*?)^=======\n(.*?)^>>>>>>>[^\n]*\n',re.M|re.S)
for index in sorted((w/'delta-captures').glob('*/files.json')):
 if index.parent.name.endswith('-pending'):continue
 for rel,data in K.captures(b,K.file_list(index),index.parent):
  target=status['rows'][rel]['target'];original=(b/rel).read_bytes();approved=initial.get(target,original);preview,issues=B.rewrite(data,migration);assert not issues,(rel,issues)
  if approved==original:merged=preview
  elif approved==preview:merged=approved
  else:
   with tempfile.TemporaryDirectory(prefix='b3-replay-') as tmp:
    tmp=Path(tmp)
    for name,content in [('approved',approved),('original',original),('indexed',preview)]:(tmp/name).write_bytes(content)
    result=subprocess.run(['git','merge-file','-p',str(tmp/'approved'),str(tmp/'original'),str(tmp/'indexed')],capture_output=True);assert 0<=result.returncode<=127,(rel,result.returncode);merged=result.stdout
   if result.returncode:
    assert rel=='scripts/audit_derived_infinity.lean',rel
    def resolve(match):
     left,right=match[1],match[2];assert left.replace(b'_root_.SerrePositivity.',b'SerrePositivity.')==right.replace(b'_root_.SerrePositivity.',b'SerrePositivity.');assert all(not line.strip() or line.startswith((b'#print axioms ',b'example ',b'    ')) for line in left.splitlines());return right
    merged,n=pat.subn(resolve,merged);assert n==9,n;assert not re.search(rb'^(<<<<<<<|=======|>>>>>>>)',merged,re.M);root_spelling_resolutions.append({'path':rel,'groups':n,'policy':'Only explicit _root_.SerrePositivity spelling; every other byte agrees.'})
  saved=(w/'rewritten-delta'/target).read_bytes();actual=(r/target).read_bytes();assert merged==saved==actual,('Independent delta differs',rel,target)
  dest=out/target;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(merged);results.append({'source':rel,'target':target,'sha256':sha(merged)})
assert len(results)==686 and {x['source'] for x in results}==set(status['rows']);summary={'status':'PASS','input_signature':input_signature,'files':len(results),'root_spelling_resolutions':root_spelling_resolutions,'unexplained':0,'input_bundle_sha256':sha((w/'initial-rebased-bundle.json.gz').read_bytes()),'output_rows':results,'policy':'Reconstruct exclusively from the frozen before tree, rebased approved bundle, compiler capture and final namespace map. No current-worktree content is used to derive expected bytes.'};(w/'independent-delta-replay-check.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print('Independent delta replay PASS',len(results),flush=True)
