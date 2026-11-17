"""Reconstruct reviewed edits against exact B2 inputs, then three-way with frozen main."""
from pathlib import Path
import json,gzip,hashlib,subprocess,sys,tempfile,collections,re
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');d=r/'evidence/bulk/bulk-w1-b2/final';sys.path.insert(0,str(r/'scripts/refactor'));from bulk_apply_preview import replay
bundle=json.load(gzip.open(d/'preview-edits.json.gz','rt'));orig={};changed={};outputs={};conflicts=[];ledger=[];sha=lambda b:hashlib.sha256(b).hexdigest()
for source,h in bundle['sources'].items():
 current=(r/source).read_bytes() if (r/source).exists() else None
 if current is not None and sha(current)==h:old=current
 else:
  old=subprocess.check_output(['git','show','0e8c854208151bc054e15ba3ba183a931b630b1c:'+source],cwd=r)
 assert sha(old)==h,source;orig[source]=old
 if current!=old:changed[source]=current
for row in bundle['outputs']:
 source=row['source'];old=orig[source] if source else b'';after=replay(old,row['edits']);assert sha(after)==row['sha256']
 if source in changed:
  assert changed[source] is not None,('deleted frozen source',source)
  with tempfile.TemporaryDirectory() as tmp:
   tmp=Path(tmp);(tmp/'after').write_bytes(after);(tmp/'base').write_bytes(old);(tmp/'main').write_bytes(changed[source])
   p=subprocess.run(['git','merge-file','-p',str(tmp/'after'),str(tmp/'base'),str(tmp/'main')],capture_output=True)
   if p.returncode:conflicts.append({'source':source,'target':row['target'],'code':p.returncode});(w/('conflict-'+str(len(conflicts))+'.txt')).write_bytes(p.stdout)
   after=p.stdout
  ledger.append({'source':source,'target':row['target'],'mode':'three-way frozen-main rebase','conflict':bool(p.returncode)})
 outputs[row['target']]=after
# The two reviewed supplements are applied to reconstructed output, never to main.
for name in ['bounded-doc-preview-edits.json.gz','audit-discovery-preview-edits.json.gz']:
 b=json.load(gzip.open(d/name,'rt'))
 for row in b['outputs']:
  current=outputs.get(row['source'],(r/row['source']).read_bytes() if (r/row['source']).exists() else b'')
  if sha(current)!=b['sources'][row['source']]:conflicts.append({'source':row['source'],'target':row['target'],'supplement':name});continue
  after=replay(current,row['edits']);assert sha(after)==row['sha256'];outputs[row['target']]=after
# Explicit B3 scope exception: keep IntegralExistence at its old location.
old='SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence';new='SerrePositivity.BhattScholze.IntegralPerfectoidization.Existence.IntegralExistence';oldpath=old.replace('.','/')+'.lean';newpath=new.replace('.','/')+'.lean'
assert newpath in outputs;outputs[oldpath]=outputs.pop(newpath)
for path,content in list(outputs.items()):
 if new.encode() in content:outputs[path]=content.replace(new.encode(),old.encode())
deletions=set(bundle['deletions']);deletions.discard(oldpath)
# No @cite Prop 7.11 is permitted on IntegralExistence; report all citation lines.
integral=outputs[oldpath].decode();assert not re.search(r'attribute\s*\[cite\s+BS19\s+"(?:Prop(?:osition)?\s*)?7\.11"',integral)
stage=w/'rendered';stage.mkdir(exist_ok=True)
for path,data in outputs.items():
 p=stage/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
(w/'rebase-summary.json').write_text(json.dumps({'outputs':len(outputs),'deletions':len(deletions),'changed_original_sources':len(changed),'three_way_outputs':ledger,'conflicts':conflicts,'scope_exception':{'IntegralExistence':{'from':new,'kept':old}},'integral_citation_lines':[line for line in integral.splitlines() if '[cite' in line]},ensure_ascii=False,indent=2));(w/'deletions.json').write_text(json.dumps(sorted(deletions),indent=2));print('reconstructed',len(outputs),'conflicts',len(conflicts),'changed sources',len(changed))
