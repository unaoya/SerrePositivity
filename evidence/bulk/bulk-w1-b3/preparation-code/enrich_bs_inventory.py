from pathlib import Path
import json,collections
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');old=json.load(open('/tmp/bulk-w1-b2/bs-section-order-check.json'));current=json.load(open(w/'bs-section-order-check.json'));retained='SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence';proposed=json.load(open('/tmp/bulk-w1-b2/preservation-module-plan.json'))['modules'][retained]
norm=lambda m:retained if m==proposed else m
approved={(norm(e['from']),norm(e['to'])):e for e in old['paper_section_reverse_edges']};actual={(e['from'],e['to']) for e in current['paper_section_reverse_edges']};assert actual==approved.keys(),{'added':sorted(actual-approved.keys()),'missing':sorted(approved.keys()-actual)}
for edge in current['paper_section_reverse_edges']:
 before=approved[edge['from'],edge['to']];edge['approved_reason']=before['proposed_reason'];edge['approval']='Approved B3 inventory only; no exemption added to the dependency-tier checker.';index=r/'.lake/build/lib/lean'/(edge['from'].replace('.','/')+'.ilean');used=collections.Counter()
 for key,value in json.load(open(index))['references'].items():
  ref=json.loads(key).get('c',{})
  if ref.get('m')==edge['to']:used[ref.get('n','')]+=len(value.get('usages',[]))
 edge['actual_compiler_reference_names']=[{'name':name,'usages':count} for name,count in sorted(used.items()) if count];edge['classification']='direct declaration reference' if used else 'import visibility only; no direct declaration reference in the actual after index'
current['retained_path_primary_subject_override']={'module':retained,'paper_section':'§10','reason':'Retained original path per B3 directive; module docstring identifies author Theorem 10.11. The path does not change the paper subject.'};current['approved_edge_count']=len(approved);current['edge_set_matches_approved']=True;(w/'bs-section-order-check.json').write_text(json.dumps(current,ensure_ascii=False,indent=2));print('BS inventory approved-edge match',len(actual),flush=True)
