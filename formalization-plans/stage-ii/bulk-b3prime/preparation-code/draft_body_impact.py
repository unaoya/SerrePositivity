from pathlib import Path
import json,re
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'formalization-plans/stage-ii/bulk-b3prime';moves=json.loads((D/'module-map.proposed.json').read_text())['rows'];names=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];terms={r['old_module']:r['new_module'] for r in moves}|{r['old']:r['new'] for r in names if r['old']!=r['new']};terms['SerrePositivity.Inputs.Perfectoidization']='SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence';rx=re.compile(r'(?<![\w.])(?:'+'|'.join(re.escape(n) for n in sorted(terms,key=len,reverse=True))+r")(?![\w'])");rows=[]
for p in sorted((R/'formalization-plans/bhatt-scholze/drafts').rglob('*.lean')):
 text=p.read_text();hits=[]
 for m in rx.finditer(text):
  line=text.count('\n',0,m.start())+1
  if line==1 and text.startswith('-- 将来の置き場所：'):continue
  hits.append({'line':line,'old':m[0],'new':terms[m[0]]})
 if hits:rows.append({'path':p.relative_to(R).as_posix(),'literal_occurrences':hits,'protected_A4_P0_review':p.relative_to(R/'formalization-plans/bhatt-scholze/drafts').parts[0]=='A4'})
result={'status':'B4/draft followup text-only impact; no draft body/import/type/proof changed, no elaboration claim. B3prime approves future-destination comment lines, not wholesale protected P0 migration. Includes comments/strings and may need native review before changing code.','files':len(rows),'occurrences':sum(len(r['literal_occurrences']) for r in rows),'rows':rows};(W/'draft-body-b4-impact.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));print('draft body text impact files',len(rows),'occurrences',result['occurrences'])
