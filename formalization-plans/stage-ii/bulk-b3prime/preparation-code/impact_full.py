from pathlib import Path
import subprocess,json,re
R=Path.cwd();D=R/'formalization-plans/stage-ii/bulk-b3prime';mods=json.loads((D/'module-map.proposed.json').read_text())['rows'];names=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];branches=['math/bs-impl','math/bs-m15','math/inf-supply','math/inf-supply-b','math/scheme','research/kerodon-review-c'];wts={}
for line in subprocess.check_output(['git','worktree','list','--porcelain'],text=True).splitlines():
 if line.startswith('worktree '):w=line[9:]
 if line.startswith('branch refs/heads/'):wts[line[18:]]=w
terms={m[k] for m in mods for k in ['old_module','old_path']};terms.update(n['old'] for n in names);pattern=re.compile('|'.join(re.escape(x)+r"(?![\w'])" for x in sorted(terms,key=len,reverse=True)))
leafs={}
for x in names:
 ns,leaf=x['old'].rsplit('.',1)
 if len(leaf)<3:continue
 leafs.setdefault(leaf,set()).add(ns)
leafpat=re.compile(r"(?<![\w'])"+'(?:'+'|'.join(re.escape(x) for x in sorted(leafs,key=len,reverse=True))+')'+r"(?![\w'])")
rows=[]
for b in branches:
 base=subprocess.check_output(['git','merge-base','main',b],text=True).strip();paths=set(subprocess.check_output(['git','diff','--name-only','--diff-filter=ACMR',base,b],text=True).splitlines());wt=Path(wts[b]);paths.update(subprocess.check_output(['git','-C',str(wt),'ls-files','--modified','--others','--exclude-standard'],text=True).splitlines());hits=[];possible=[];binary=0
 for p in sorted(paths):
  f=wt/p
  if not f.is_file():continue
  try:s=f.read_text()
  except (UnicodeError,OSError):binary+=1;continue
  if '\0' in s:binary+=1;continue
  found=sorted(set(m.group() for m in pattern.finditer(s)))
  if found:hits.append({'path':p,'matches':found,'kind':'Lean' if p.endswith('.lean') else 'script' if p.endswith(('.py','.sh')) else 'document_or_data'});continue
  if p.endswith('.lean'):
   found=sorted({m.group() for m in leafpat.finditer(s) if any(ns in s for ns in leafs[m.group()])})
   if found:possible.append({'path':p,'unqualified_candidates':found,'note':'lexical candidate only; must resolve binding with native collector'})
 collisions=[m['new_path'] for m in mods if (wt/m['new_path']).exists() and not (R/m['new_path']).exists()]
 rows.append({'branch':b,'head':subprocess.check_output(['git','rev-parse',b],text=True).strip(),'merge_base':base,'files_scanned':len(paths),'nontext_files_skipped':binary,'literal_hits':hits,'literal_count':len(hits),'possible_unqualified':possible,'possible_count':len(possible),'new_path_collisions':collisions})
result={'status':'source-text stage0 branch impact, includes documents/data; no other lane writes','baseline':'32d364b53','method':'Read live branch worktrees for committed branch changes relative to merge-base(main, branch), plus tracked modifications and untracked files. Full old module/path strings and full names whose name or owning module changes; candidate unqualified identifiers reported separately. Binary files skipped. Current branch heads captured.','branches':rows,'literal_branch_file_count':sum(x['literal_count'] for x in rows),'conservative_with_unqualified_branch_file_count':sum(x['literal_count']+x['possible_count'] for x in rows),'new_path_collision_count':sum(len(x['new_path_collisions']) for x in rows)}
(D/'branch-impact-stage0.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print([(x['branch'],x['literal_count'],x['possible_count']) for x in rows]);print('totals',result['literal_branch_file_count'],result['conservative_with_unqualified_branch_file_count'],'collisions',result['new_path_collision_count'])
