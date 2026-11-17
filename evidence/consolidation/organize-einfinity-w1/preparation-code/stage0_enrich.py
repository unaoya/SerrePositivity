from pathlib import Path
import csv,json,re,subprocess,hashlib
out=Path('evidence/consolidation/organize-einfinity-w1');rows=list(csv.DictReader((out/'stage1-modules.csv').open()))
from source_names import declarations
names=[]
for r in rows:
 for n,p,line in declarations(Path(r['old_path']).read_text(),r['old_path']):
  old=r['old_namespace'];nn=r['new_namespace']+n[len(old):] if r['action']=='move' and (n==old or n.startswith(old+'.')) else n
  names.append(dict(old=n,new=nn,owner=r['old_module'],new_owner=r['new_module'],line=line,status='source candidate; native generated/private ownership pending'))
with (out/'source-declaration-map.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(names[0]),lineterminator='\n');w.writeheader();w.writerows(names)
oldnames={r['old'] for r in names};review=[]
for f in Path('research/kerodon-coverage/review').glob('ch[0-9]*.csv'):
 for r in csv.DictReader(f.open()):
  if r['status_new'] not in ['own','both','partial']:continue
  hit=sorted(set(re.findall(r'SerrePositivity\.[\w.]+',r['declarations_new']))&oldnames)
  if hit:review.append(dict(review=str(f),number=r['number'],status=r['status_new'],declarations=hit))
(out/'citation-review-candidates.json').write_text(json.dumps(review,ensure_ascii=False,indent=2)+'\n')
s=json.loads((out/'stage0-summary.json').read_text());s.update(source_declaration_candidates=len(names),source_declarations_renamed=sum(r['old']!=r['new'] for r in names),citation_review_rows=len(review));(out/'stage0-summary.json').write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n')
impact=json.loads((out/'branch-impact.json').read_text());n=set(r['old_module'] for r in rows if r['action']=='move')
for d in ['FrameHom','HomotopyWeight','SimplicialLocalization']:n.update(['SerrePositivity.EInfinity.'+d,'EInfinity.'+d,d+'.'])
n.update(r['old_module'].split('.')[-1] for r in rows if r['id']=='OE05')
rx=re.compile('|'.join(map(re.escape,sorted(n,key=len,reverse=True))))
worktrees={}
for line in subprocess.check_output(['git','worktree','list','--porcelain'],text=True).splitlines():
 if line.startswith('worktree '):wd=Path(line[9:])
 if line.startswith('branch refs/heads/'):worktrees[line[18:]]=wd
for branch,b in impact['branches'].items():
 wd=worktrees.get(branch);b['worktree']=str(wd) if wd else None;hits=[]
 if wd:
  files=subprocess.check_output(['git','-C',str(wd),'ls-files','--modified','--others','--exclude-standard'],text=True).splitlines()
  for p in files:
   path=wd/p
   if path.suffix!='.lean' or not path.is_file():continue
   text=path.read_text();hs=sorted(set(rx.findall(text)))
   if hs:hits.append(dict(path=p,matches=hs,source_sha256=hashlib.sha256(text.encode()).hexdigest()))
 b['uncommitted_matches']=hits;b['affected_files_with_worktree']=len({x['path'] for x in b['files']}|{x['path'] for x in hits})
impact['total_affected_files_with_worktree']=sum(b['affected_files_with_worktree'] for b in impact['branches'].values());(out/'branch-impact.json').write_text(json.dumps(impact,ensure_ascii=False,indent=2)+'\n');s['branch_affected_with_worktree']=impact['total_affected_files_with_worktree'];(out/'stage0-summary.json').write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n')
print('impact including uncommitted',impact['total_affected_files_with_worktree']);print('source names',len(names),'renamed',s['source_declarations_renamed'])
