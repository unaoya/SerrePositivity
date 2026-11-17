from pathlib import Path
import json,sys,re,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');A=Path('/tmp/bulk-b3prime-preview');W=Path('/tmp/bulk-b3prime');D=R/'evidence/bulk/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));from lean_source import doc_start
plan=json.loads((W/'namespace-rewrite-plan.json').read_text());status=json.loads((W/'rewrite-status.json').read_text());source_names=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];splits=json.loads((D/'split-plan.proposed.json').read_text())['rows'];allrows=[]
for p in (W/'before').glob('group-*.json'):
 if p.with_name(p.stem+'.complete.json').exists():allrows+=json.loads(p.read_text())['declarations']

def project(text,edits,a,b):
 raw=text.encode();lo=len(text[:a].encode());hi=len(text[:b].encode());chosen=[]
 for e in edits:
  x,y=e['start'],e['stop']
  if x==y:
   if lo<x<=hi or lo==0 and x==0:chosen.append(e)
  elif lo<=x and y<=hi:chosen.append(e)
  elif x<hi and lo<y:raise ValueError('edit crosses split boundary: '+str(e))
 result=bytearray();at=lo
 for e in chosen:
  assert e['start']>=at;result.extend(raw[at:e['start']]);result.extend(e['replacement'].encode());at=e['stop']
 result.extend(raw[at:hi]);return result.decode()

def section(text,label):
 marker='@[expose] public noncomputable section '+label;s=text.index(marker);start=text.rfind('/-!',0,s);assert start>=0;end=text.index('end '+label,s)+len('end '+label)
 if text[end:end+1]=='\n':end+=1
 return start,end
records=[]
for split in splits:
 label=split.get('source_section');oldmod=split['old_path'][:-5].replace('/','.');newmod=split['new_path'][:-5].replace('/','.')
 if label not in ['InitialLimit','IteratedPDH0Reflection'] and not split['new_path'].endswith('/AdjoinResidue.lean'):continue
 assert split['old_path'] in status['files'],(split['old_path'],status['review'].get(split['old_path']))
 text=(R/split['old_path']).read_text();edits=json.loads((W/'rewritten'/(oldmod+'.edits.json')).read_text());names=set(split.get('declarations',[])) or {n['old'] for n in source_names if n['old_module']==oldmod and n['new_module']==newmod};selected=[r for r in allrows if r['module']==oldmod and any(r['name']==n or r['name'].startswith(n+'.') for n in names)];assert names<={r['name'] for r in selected}
 imports=sorted({m for r in selected for m in r['used_modules'] if m.startswith(('Mathlib.','SerrePositivity.')) and m!=oldmod})
 if label in ['InitialLimit','IteratedPDH0Reflection']:assert not any('BhattScholze' in m for m in imports),imports
 else:assert not any('.Andre.' in m for m in imports),imports
 spans=[section(text,label)] if label else [section(text,s) for s in ['DeltaAdjoinDivisionResiduePresentation','DeltaDivisionSourceResidueTensor']]
 body='\n'.join(project(text,edits,a,b) for a,b in spans)
 title={'InitialLimit':'始対象の値から指定極限錐を計算する','IteratedPDH0Reflection':'二つの主元完備化の H⁰ と PD 完備化の比較'}.get(label,'δ 除算添加環の剰余とテンソル表示')
 universe='u v w' if label=='InitialLimit' else 'u v' if label is None else 'u'
 header='module\n'+''.join('public import '+m+'\n' for m in imports)+'\n/-!\n# '+title+'\n\n概要：一般の構成とその比較をまとめる。\n方針：元の宣言とその局所的な文脈を、機械的な名前の追従だけで保存する。\n規約：特殊な包絡の存在や追加の仮定を導入しない。\n使われ方：Bhatt–Scholze の包絡または perfectoid 化の比較。\n-/\n\nuniverse '+universe+'\n\n'
 content=header+body;target=A/split['new_path'];receiptfile=W/('projected-'+newmod+'.json')
 if target.exists():
  assert receiptfile.exists();previous=json.loads(receiptfile.read_text());assert hashlib.sha256(target.read_bytes()).hexdigest()==previous['sha256']
 target.parent.mkdir(parents=True,exist_ok=True);target.write_text(content);record={'old_module':oldmod,'new_module':newmod,'source_declarations':sorted(names),'source_spans':spans,'imports':imports,'sha256':hashlib.sha256(content.encode()).hexdigest(),'status':'isolated generated file only; target build and full original-owner v3b still required'};receiptfile.write_text(json.dumps(record,ensure_ascii=False,indent=2));records.append(record);print(newmod,len(names),'imports',len(imports))
(W/'projected-generic-plan.json').write_text(json.dumps(records,ensure_ascii=False,indent=2))
