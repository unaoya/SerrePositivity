from pathlib import Path
import json,hashlib,re
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');root=R/'formalization-plans/bhatt-scholze/drafts';out=W/'draft-header-bundle';old='SerrePositivity.BhattScholze.Perfectoidization.Derived.';section={'A4':'Construction','A5':'Descent','A6':'Arc','A7':'Construction','A8':'Almost','A9':'Interface'};rows=[]
for p in sorted(root.rglob('*.lean')):
 text=p.read_text();first,sep,body=text.partition('\n')
 if not first.startswith('-- 将来の置き場所：'+old):continue
 group=p.relative_to(root).parts[0];assert group in section
 dest='SerrePositivity.BhattScholze.'+('Almost.' if group=='A8' else 'Perfectoidization.'+section[group]+'.')
 new=first.replace(old,dest,1)
 if group=='A9':new=new.replace('Inputs/PerfectoidizationInterface.lean','SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean')
 result=new+sep+body;assert result.partition('\n')[2]==body
 rel=p.relative_to(R);target=out/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(result)
 rows.append({'path':rel.as_posix(),'line':1,'old':first,'new':new,'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'preview_sha256':hashlib.sha256(result.encode()).hexdigest(),'authority':'R8-8: future destination comment only; A4 P0 body/import/name/type/proof byte-identical; hypothetical destinations remain marked 仮'})
(W/'draft-header-plan.json').write_text(json.dumps({'status':'isolated comment-only proposal; no actual worktree drafts modified','files':len(rows),'rows':rows},ensure_ascii=False,indent=2));print('draft future-destination comment headers',len(rows))
