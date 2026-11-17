"""Authenticate absolute spellings of existing Mathlib-root opens and references.
Only `_root_.` is inserted; no declaration name, expression or assumption is added.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,hashlib,json,sys
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--before',type=Path,required=True);p.add_argument('--captures',type=Path,nargs='+',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();sys.path.insert(0,str(root/'scripts/refactor'));import klw1_namespace as K
base=root/'evidence/consolidation/organize-einfinity-w1';plan=K.Migration(json.loads((base/'namespace-rewrite-map.json').read_text()));records=[];pending=[];seen=set();sha=lambda b:hashlib.sha256(b).hexdigest()
for folder in a.captures:
 for rp in sorted(folder.glob('*.receipt.json')):
  receipt=json.loads(rp.read_text());assert receipt['returncode']==0;path=receipt['source'];assert path not in seen;seen.add(path);cap=rp.with_name(rp.name.removesuffix('.receipt.json')+'.json');assert sha(cap.read_bytes())==receipt['capture_sha256'];data=K.checked_capture(a.before,path,cap);source=data['source'].encode();edits={}
  for cmd in data['commands']:
   if cmd['kind']!='open' or len(cmd.get('names',[]))!=1:continue
   old=source[cmd['start']:cmd['stop']].decode();resolved=cmd['names'][0]
   if not (old=='HomotopicalAlgebra' or old.startswith('HomotopicalAlgebra.')) or resolved!=old:continue
   if cmd['mode'] not in ['simple','local-simple']:pending.append(dict(source=path,command=cmd,reason='Inspect non-simple original Mathlib-root open'));continue
   edits[cmd['start'],cmd['stop']]=dict(kind='open',start=cmd['start'],stop=cmd['stop'],old=old,new='_root_.'+old,mode=cmd['mode'],resolved_namespace=resolved)
  groups=defaultdict(list)
  for ref in data['refs']:groups[ref['start'],ref['stop']].append(ref)
  for (lo,hi),refs in groups.items():
   old=source[lo:hi].decode()
   if not old.startswith('HomotopicalAlgebra.') or not K.IDENT.fullmatch(old) or source[max(0,lo-1):lo]==b'.':continue
   matching=[r for r in refs if r['kind']=='term' and r['name']==old and plan.target(r) is None]
   if not matching:continue
   if not all(r['name']==old and r['kind'] in ['term','syntax'] and plan.target(r) is None for r in refs):pending.append(dict(source=path,start=lo,stop=hi,reason='Inspect multiple resolutions before anchoring a qualified constant'));continue
   edits[lo,hi]=dict(kind='term',start=lo,stop=hi,old=old,new='_root_.'+old,resolutions=sorted({(r['module'],r['name'],r['kind']) for r in refs}))
  if edits:records.append(dict(source=path,module=data['module'],source_sha256=sha(source),capture_sha256=receipt['capture_sha256'],rows=[edits[k] for k in sorted(edits)]))
a.output.write_text(json.dumps(dict(policy='Original compiler namespace/constant resolutions; exact source bytes; insertion of root qualifier only. Does not weaken type or proof. Final native v3b required.',records=records,pending=pending),ensure_ascii=False,indent=2)+'\n');print(json.dumps(dict(files=len(records),edits=sum(len(r['rows']) for r in records),kinds=dict(Counter(e['kind'] for r in records for e in r['rows'])),pending=len(pending))));raise SystemExit(bool(pending))
