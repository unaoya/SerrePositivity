#!/usr/bin/env python3
"""Read-only structural/source audit for DAG XIII and NS coverage. Does not run Lean.
This checks evidence consistency, not mathematical completeness of negative judgments.
"""
import collections,csv,hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
FIELDS='number,kind,title,section,status,declarations,reason,confidence,lean_citations,plan_citations,kerodon,goal'.split(',')
BASE='55f6cfbea'

def rows(p):
    with p.open(newline='') as f:return list(csv.DictReader(f))
def run():
    for book,count in [('dag13',290),('ns',253)]:
        folder=ROOT/'research'/f'{book}-coverage'
        items=rows(folder/'items.csv');assert list(items[0])==FIELDS
        index={r['number']:r for r in items};assert len(index)==len(items)==count
        assert all(r['title'] and r['section'] and not any(r[k] for k in ['status','declarations','reason']) for r in items)
        reviewed=[r for p in sorted((folder/'review').glob('*.csv')) for r in rows(p)]
        reviews={r['number']:r for r in reviewed};assert len(reviews)==len(reviewed)==count and reviews.keys()==index.keys()
        source=rows(folder/'review/check/source-items.csv');assert {r['number']:r['kind'] for r in source}=={n:r['kind'] for n,r in index.items()}
        evidence=json.loads((folder/'review/check/claim-evidence.json').read_text());ev={r['number']:r for r in evidence};assert ev.keys()==index.keys()
        searches=json.loads((folder/'review/check/search-evidence.json').read_text())
        types=json.loads((folder/'review/check/source-types.json').read_text())
        priority={'dag13':{'1.1','2.1','2.2'},'ns':{'I.1','I.3','III.1','IV.1'}}[book]
        porder=[ev[n]['review_order'] for n,i in index.items() if i['section'] in priority]
        rest=[ev[n]['review_order'] for n,i in index.items() if i['section'] not in priority]
        assert max(porder)<min(rest)
        for r in reviewed:
            n=r['number'];assert r['status'] in ['own','mathlib','both','partial','none'] and r['reason']
            assert r['reason']==ev[n]['comparison'] and ev[n]['search_group'] in searches
            assert r['axioms']=='','No kernel axiom audit was run'
            if r['status']=='none':assert not r['declarations'] and not r['partial_kind'] and r['check']=='not_found'
            else:
                assert r['declarations'] and '仮定：' in r['reason'] and '結論：' in r['reason'] and r['check']=='found'
                for part in r['declarations'].split(' | '):
                    name,loc=part.split(' @ ');file,line=loc.rsplit(':',1)
                    assert name in types and file==types[name]['file'] and int(line)==types[name]['line']
                if r['status']=='partial':assert r['partial_kind'] in ['component','special','direction','stronger-hyp']
                else:assert not r['partial_kind']
        for d in types.values():
            p=ROOT/('.lake/packages/mathlib/'+d['file'] if d['file'].startswith('Mathlib/') else d['file'])
            s=p.read_text();assert hashlib.sha256(s.encode()).hexdigest()==d['source_sha256'],str(p)
            assert d['source_excerpt'].startswith(s.splitlines()[d['line']-1])
            assert d['source_excerpt'].startswith(d['source_signature'])
        for group in searches.values():
            assert group['exit_code'] in [0,1] and group['inspected_candidates']
            for d in group['inspected_candidates']:
                p=ROOT/('.lake/packages/mathlib/'+d['file'] if d['file'].startswith('Mathlib/') else d['file'])
                assert hashlib.sha256(p.read_bytes()).hexdigest()==d['sha256']
        for filename,field in [('citations.csv','lean_citations'),('plan-citations.csv','plan_citations')]:
            cs=rows(folder/filename);c=collections.Counter(r['number'] for r in cs)
            assert set(c)<=set(index),set(c)-set(index)
            assert all(int(i[field])==c[n] for n,i in index.items())
        # Exact section ranges, including the deliberately irregular chapter introductions.
        if book=='dag13':
            expected={'1.0':range(1,4),'1.1':range(1,17),'1.2':range(1,22),'1.3':range(1,7),'1.4':range(1,16),'1.5':range(1,5),'2.0':range(5,8),'2.1':range(1,26),'2.2':range(1,19),'2.3':range(1,26),'2.4':range(1,27),'2.5':range(1,13),'2.6':range(1,18),'3.0':[18],'3.1':range(1,18),'3.2':range(1,30),'3.3':range(1,16),'3.4':range(1,16),'3.5':range(1,16),'3.6':range(1,8)}
        else:
            maxima={'I.1':13,'I.2':9,'I.3':9,'I.4':4,'II.1':9,'II.2':16,'II.3':8,'II.4':11,'II.5':13,'II.6':10,'III.1':10,'III.2':3,'III.3':8,'III.4':7,'III.5':6,'III.6':8,'IV.1':21,'IV.2':4,'IV.3':7,'IV.4':17,'A':17,'B':22,'C':14}
            expected={s:range(1,m+1) for s,m in maxima.items()};expected['Introduction']=range(1,8)
        assert set(expected)=={i['section'] for i in items}
        for sec,ns in expected.items():assert {int(i['number'].rsplit('.',1)[1]) for i in items if i['section']==sec}==set(ns),sec
        assert (folder/'toc.md').read_text().find(json.loads((folder/'review/check/edition.json').read_text())['sha'])>=0
        print(book,count,dict(collections.Counter(r['status'] for r in reviewed)))
    subprocess.run(['python3','scripts/refactor/bulk_citation_registry.py','--check'],cwd=ROOT,check=True)
    changed=subprocess.check_output(['git','diff',BASE,'--name-only','--','*.lean'],cwd=ROOT,text=True).splitlines()
    assert changed==['SerrePositivity/Util/Citation.lean'],changed
    for folder in ['research/ha-coverage','research/htt-coverage','research/kerodon-coverage']:
        assert not subprocess.check_output(['git','diff',BASE,'--name-only','--',folder],cwd=ROOT,text=True)
    def strip(s):return re.sub(r'-- BEGIN GENERATED REGISTRY\n.*?-- END GENERATED REGISTRY','REGISTRY',s,flags=re.S)
    old=subprocess.check_output(['git','show',BASE+':SerrePositivity/Util/Citation.lean'],cwd=ROOT,text=True)
    assert strip(old)==strip((ROOT/'SerrePositivity/Util/Citation.lean').read_text())
    print('PASS: 543 unique items, canonical reviews, references, evidence, ranges, registry and edit scope')
if __name__=='__main__':run()
