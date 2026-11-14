"""Update only actual after positions following the separately preserved doc-only overlay."""
from pathlib import Path
import json,gzip,hashlib
w=Path('/tmp/bulk-w1-b2');d=json.load(open(w/'bounded-doc-check/after.json'));b=json.load(open(w/'bounded-doc-check/before.json'));after={(r['module'],r['name']):r for r in d['declarations']};before={(r['module'],r['name']):r for r in b['declarations']};assert set(before)==set(after)
for k,x in before.items():
 y=after[k]
 for field in ['kernel_name','kind','reference_kind','is_private','type_hash','body_hash','axioms','attributes']:assert x.get(field)==y.get(field),(k,field)
modules=set(d['modules']);changes={}
def rewrite(filename,convert):
 p=w/filename;rows=[]
 with gzip.open(p,'rt') as f:
  for line in f:rows.append(convert(json.loads(line)))
 with p.open('wb') as raw:
  with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as out:
   for r in rows:out.write((json.dumps(r,ensure_ascii=False,separators=(',',':'))+'\n').encode())
 return len(rows)
count=0
def names(row):
 global count
 key=row['new_module'],row['new']
 if row['new_module'] in modules and row['new'] is not None:
  actual=after[key];assert row['new_kernel_name']==actual.get('kernel_name',actual['name']),key
  if row['new_source_range']!=actual.get('source_range'):count+=1
  row['new_source_range']=actual.get('source_range')
 return row
rewrite('declaration-names.jsonl.gz',names)
changed_inventory=0
def inventory(row):
 global changed_inventory
 key=row['module'],row['name']
 if row['module'] in modules:
  assert key in after,key
  value=after[key].get('source_range');changed_inventory+=row.get('source_range')!=value;row['source_range']=value
 return row
rewrite('declaration-inventory-after.jsonl.gz',inventory)
p=w/'declaration-table-summary.json';s=json.load(open(p));s['sha256']=hashlib.sha256((w/'declaration-names.jsonl.gz').read_bytes()).hexdigest();s['after_source_range_policy']='Actual V ranges, updated from the separately preserved 14-file V -> replay-tree comment-only supplement';s['doc_supplement_range_updates']=s.get('doc_supplement_range_updates',count);p.write_text(json.dumps(s,ensure_ascii=False,indent=2));(w/'bounded-doc-range-update.json').write_text(json.dumps({'status':'PASS','actual_module_declaration_keys_identical':len(after),'kernel_hashes_attributes_axioms_identical':True,'updated_name_rows':count,'updated_inventory_rows':changed_inventory,'modules':sorted(modules)},indent=2));print('actual doc supplement ranges updated',count)
