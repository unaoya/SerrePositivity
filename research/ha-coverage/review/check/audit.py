#!/usr/bin/env python3
"""HA 照合表と保存済み証拠を監査する（Lean の実行・ビルドはしない）。"""
import argparse
import csv
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
import subprocess

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root',type=Path,default=Path.cwd())
parser.add_argument('--pdf',type=Path,help='任意：段0の原典PDFもSHA-256を検証する')
parser.add_argument('--mathlib',type=Path,help='ソースハッシュも検証する場合の Mathlib checkout')
args=parser.parse_args();repo=args.root.resolve();base=repo/'research/ha-coverage';check=base/'review/check'
if args.pdf:
 assert hashlib.sha256(args.pdf.read_bytes()).hexdigest()=='112b145a95a62daefb8275851cac9ab6430004cfc8f751a33a8d981fd7ad68c3'
items=list(csv.DictReader((base/'items.csv').open()));catalog={r['number']:r for r in items}
assert len(items)==len(catalog)==2866
statuses={'own','mathlib','both','partial','none'};kinds={'special','direction','stronger-hyp','component'}
rows={};counts={}
for chapter in ['0','1','2','3','4','5','6','7','A','B']:
 table=list(csv.DictReader((base/f'review/ch{chapter}.csv').open()))
 expected={n for n in catalog if n.split('.')[0]==chapter};actual={r['number'] for r in table}
 assert len(table)==len(actual) and actual==expected,(chapter,len(table),len(expected))
 for r in table:
  n=r['number'];assert n not in rows;rows[n]=r
  assert r['status'] in statuses and r['reason'],n
  assert (r['status']=='partial')==(r.get('partial_kind','') in kinds),n
  if r['status']!='none':
   assert r['check'] in {'found','renamed'} and r['declarations'],n
   assert '仮定：' in r['reason'] and '結論：' in r['reason'],n
  else:assert r['check']=='not_found' and not r['declarations'],n
 counts[chapter]=dict(Counter(r['status'] for r in table))
assert set(rows)==set(catalog)
positive={};negative={};source_checks={};typed={};provenances=defaultdict(set)
for path in sorted(check.glob('ch*-*.json')):
 assert path.stat().st_size<2_000_000,path
 data=json.loads(path.read_text());assert data['ha_pdf_sha256']=='112b145a95a62daefb8275851cac9ab6430004cfc8f751a33a8d981fd7ad68c3';source_commit=data.get('worktree_commit');mathlib_commit=data.get('mathlib_commit')
 if path.name.endswith('-kernel-evidence.json'):
  for n,value in data.get('items',{}).items():
   assert n not in positive,n;positive[n]=value
   names=[s.strip().split(' @ ')[0] for s in rows[n]['declarations'].split(' | ')]
   assert names==value['declarations'],n
   for name in names:
    d=data['declarations'][name]
    assert d['type'] and d['name']==name and d['line']>0,(n,name)
    assert set(d['axioms'])<={'propext','Classical.choice','Quot.sound'},(n,name,d['axioms'])
    typed[(name,d['source_sha256'])]=d
    key=(source_commit,mathlib_commit,d['path'],d['source_sha256']);source_checks[key]=True
 elif path.name.endswith('-none-search.json'):
  for n,value in data.get('items',{}).items():
   assert n not in negative,n;negative[n]=value
   assert value['reason']==rows[n]['reason'],n
   assert set(value['search'])=={'SerrePositivity','Mathlib'} and value['sources_read'],n
   assert 'exact' in value['citation_scan'] and any(k in value['citation_scan'] for k in ['neighbors','neighbor_subsections']),n
   for d in value['sources_read']:source_checks[(source_commit,mathlib_commit,d['path'],d['sha256'])]=True
 provenances[path.name.split('-')[0]].add(source_commit)
assert set(positive)=={n for n,r in rows.items() if r['status']!='none'}
assert set(negative)=={n for n,r in rows.items() if r['status']=='none'}
missing_refs={}
for filename in ['citations.csv','plan-citations.csv']:
 missing_refs[filename]=sorted({r['number'] for r in csv.DictReader((base/filename).open()) if r['number'] not in catalog and not any(n.startswith(r['number']+'.') for n in catalog)})
 assert not missing_refs[filename],(filename,missing_refs[filename])
# 目録の引用数は、採取済みCSVの同じ番号の行数に一致する。
for filename,column in [('citations.csv','lean_citations'),('plan-citations.csv','plan_citations')]:
 cite_counts=Counter(r['number'] for r in csv.DictReader((base/filename).open()))
 for n,r in catalog.items():assert int(r[column])==cite_counts[n],(n,column)
# 第1章の分割証拠への目次も実ファイルの件数と一致する。
manifest=json.loads((check/'ch1-kernel-evidence.json').read_text())
for group,entry in manifest['sections'].items():
 assert len(json.loads((check/entry['path']).read_text())['items'])==entry['item_count'],group
verified_hashes=0
if args.mathlib:
 raw_cache={}
 for source_commit,mathlib_commit,path,wanted in source_checks:
  gitroot=args.mathlib if path.startswith('Mathlib/') else repo
  commit=mathlib_commit if path.startswith('Mathlib/') else source_commit
  key=(str(gitroot),commit,path)
  if key not in raw_cache:
   result=subprocess.run(['git','-C',str(gitroot),'show',f'{commit}:{path}'],capture_output=True,check=True)
   raw_cache[key]=hashlib.sha256(result.stdout).hexdigest()
  assert raw_cache[key]==wanted,(commit,path,'source hash mismatch')
  verified_hashes+=1
 # 段4は記録時と現ソースの一致も確認する。既存段は各記録コミットを使う。
 for path in sorted(check.glob('ch*-*.json')):
  if path.name.split('-')[0] not in {'ch0','ch5','ch6','chA','chB'} and not path.name.startswith('ch1-stage4-'):continue
  data=json.loads(path.read_text())
  sources=[(d['path'],d['source_sha256']) for d in data.get('declarations',{}).values()]
  sources += [(s['path'],s['sha256']) for item in data.get('items',{}).values() for s in item.get('sources_read',[])]
  for source,wanted in sources:
   p=(args.mathlib/source) if source.startswith('Mathlib/') else repo/source
   assert hashlib.sha256(p.read_bytes()).hexdigest()==wanted,source
result={'items':len(rows),'counts':counts,'total':dict(Counter(r['status'] for r in rows.values())),
        'unsure':0,'partial_kind':dict(Counter(r['partial_kind'] for r in rows.values() if r['status']=='partial')),
        'typed_declaration_versions':len(typed),'positive_items':len(positive),'none_items':len(negative),'verified_source_hash_records':verified_hashes,
        'kerodon_items':sum(bool(r['kerodon']) for r in items),
        'e_infinity_items':sum('E∞' in r['goal'].split(';') for r in items),'missing_citations':missing_refs}
print(json.dumps(result,ensure_ascii=False,indent=2))
