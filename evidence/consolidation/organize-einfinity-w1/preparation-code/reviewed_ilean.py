"""Individually reviewed ILean edits, explicitly distinct from InfoTree captures."""
from pathlib import Path
import hashlib,json
BASE=Path(__file__).resolve().parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def previews(root):
 records=json.loads((BASE/'reviewed-ilean-previews.json').read_text());result={}
 for r in records:
  assert r['kind']=='individually-reviewed-original-ilean-spans'
  assert sha((BASE/'namespace-rewrite-map.json').read_bytes())==r['plan_sha256']
  source=(root/r['source']).read_bytes();assert sha(source)==r['source_sha256']
  assert sha((root/r['ilean_path']).read_bytes())==r['ilean_sha256']
  text=source.decode()
  for e in sorted(r['edits'],key=lambda e:e['start'],reverse=True):
   assert text[e['start']:e['end']]==e['old'];text=text[:e['start']]+e['new']+text[e['end']:]
  data=text.encode();assert sha(data)==r['preview_sha256'];result[r['source']]=(data,r)
 return result
