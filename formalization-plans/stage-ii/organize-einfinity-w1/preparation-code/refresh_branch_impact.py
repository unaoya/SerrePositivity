"""Read other lane refs/worktrees without changing them; refresh literal B4 impact."""
from pathlib import Path
import argparse,csv,json,re,subprocess,hashlib
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--include-active-worktrees',action='store_true');a=p.parse_args();root=a.root.resolve();base=root/'formalization-plans/stage-ii/organize-einfinity-w1';old=json.loads((base/'branch-impact.json').read_text());rows=list(csv.DictReader((base/'stage1-modules.csv').open()));needles={r['old_module'] for r in rows if r['action']=='move'};needles.update(r['old_namespace'] for r in rows if r['action']=='move');needles.update(r['old_module'].rsplit('.',1)[-1] for r in rows if r['id']=='OE05')
regex=re.compile('|'.join(re.escape(s) for s in sorted(needles,key=len,reverse=True))+r'|\b(?:FrameHom|FrameArrows|HomotopyWeight|SimplicialLocalization|AnodyneWeakDetection)\b|(?<![\w.])HomotopicalAlgebra\b');results={}
def git(where,*args):return subprocess.check_output(['git',*args],cwd=where,text=True).strip()
branches=dict(old['branches'])
if a.include_active_worktrees:
 current=git(root,'branch','--show-current')
 for block in git(root,'worktree','list','--porcelain').split('\n\n'):
  fields=dict(line.split(' ',1) for line in block.splitlines() if ' ' in line)
  branch=fields.get('branch','').removeprefix('refs/heads/')
  if branch and branch not in ('main',current):branches.setdefault(branch,dict(worktree=fields['worktree']))
removed_branches={}
for branch,prev in branches.items():
 resolved=subprocess.run(['git','rev-parse','--verify',branch],cwd=root,capture_output=True,text=True)
 if resolved.returncode:
  removed_branches[branch]=dict(previous_head=prev.get('head'),previous_worktree=prev.get('worktree'),reason='Reference no longer exists; active renamed worktrees are scanned separately')
  continue
 head=resolved.stdout.strip();paths=set(git(root,'log','--format=','--name-only','--diff-filter=AM',old['base']+'..'+head,'--','*.lean').splitlines());hits=[]
 for path in sorted(paths):
  if not path:continue
  r=subprocess.run(['git','show',head+':'+path],cwd=root,capture_output=True,text=True)
  if r.returncode:continue
  matches=sorted(set(regex.findall(r.stdout)))
  if matches:hits.append(dict(path=path,matches=matches,source_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),is_draft=path.startswith('drafts/')))
 worktree=Path(prev['worktree']) if prev.get('worktree') else None;dirty=[];checked=0
 if worktree and worktree.exists():
  changed=set(git(worktree,'diff','--name-only','HEAD','--','*.lean').splitlines())|set(git(worktree,'ls-files','--others','--exclude-standard','--','*.lean').splitlines())
  for path in sorted(changed):
   if not path or not (worktree/path).is_file():continue
   source=(worktree/path).read_text();checked+=1;matches=sorted(set(regex.findall(source)))
   if matches:dirty.append(dict(path=path,matches=matches,source_sha256=hashlib.sha256(source.encode()).hexdigest(),is_draft=path.startswith('drafts/')))
 results[branch]=dict(head=head,touched_lean_files=len(paths),affected_files=len(hits),files=hits,worktree=str(worktree) if worktree else None,uncommitted_checked=checked,uncommitted_matches=dirty,affected_files_with_worktree=len({r['path'] for r in hits+dirty}))
summary=dict(base=old['base'],removed_branches=removed_branches,includes_active_worktrees=a.include_active_worktrees,policy='Exact old module/namespace strings, BE module basenames, plus bare namespace tokens and unrooted Mathlib HomotopicalAlgebra candidates; original branch HEAD and dirty/untracked Lean sources read-only, drafts included. Candidate matches are conservative; compiler checks determine actual bindings.',branches=results,total_affected_files=sum(x['affected_files'] for x in results.values()),total_affected_with_worktree=sum(x['affected_files_with_worktree'] for x in results.values()));a.output.write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n');print(json.dumps({k:v['affected_files_with_worktree'] for k,v in results.items()}));raise SystemExit(1 if summary['total_affected_with_worktree']>30 else 0)
