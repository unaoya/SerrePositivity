from pathlib import Path
import subprocess,json,re,hashlib,datetime
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');base=json.load(open(w/'baseline.json'))['frozen_main'];mm=json.load(open(w/'module-map.json'));ns=json.load(open(w/'namespace-rewrite-map.json'))
# This inventory reads immutable git objects only; it never opens a lane worktree.
def git(*a):return subprocess.check_output(['git',*a],cwd=r).decode()
rows=ns['rows'];print('name row keys',list(rows[0]))
names={x['old']:x['new'] for x in rows if x['old']!=x['new']};changed_modules={a:b for a,b in mm.items() if a!=b}
patterns=[('modules',changed_modules),('names',names)];regexes={k:re.compile(r'(?<![\w.])(?:'+'|'.join(re.escape(n) for n in sorted(d,key=len,reverse=True))+r')(?![\w.])') for k,d in patterns};out={}
for branch in ['math/inf-supply','math/inf-supply-b','math/bs-impl','math/scheme']:
 head=git('rev-parse',branch).strip();paths=sorted(set(git('log','--format=','--name-only','--diff-filter=AM',base+'..'+head,'--','*.lean').splitlines()));affected=[];drafts=[];missing=[];collect_files=[]
 for path in paths:
  if not path:continue
  p=subprocess.run(['git','show',head+':'+path],cwd=r,capture_output=True)
  if p.returncode:missing.append(path);continue
  
  if not path.startswith('formalization-plans/') and '/drafts/' not in path:collect_files.append(path)
  source=p.stdout.decode();hits={k:sorted(set(pattern.findall(source))) for k,pattern in regexes.items()}
  if not any(hits.values()):continue
  row={'path':path,'source_sha256':hashlib.sha256(p.stdout).hexdigest(),**hits}
  if path.startswith('formalization-plans/') or '/drafts/' in path:drafts.append(row)
  else:affected.append(row)
 (w/('b4-'+branch.replace('/','-')+'-files.json')).write_text(json.dumps(collect_files,indent=2))
 out[branch]={'head':head,'collect_files':collect_files,'collect_file_count':len(collect_files),'candidate_files':len(paths),'files':affected,'files_count':len(affected),'nonbuild_drafts_excluded':drafts,'deleted_since_commits':missing,'observation':'static exact text references in branch HEAD files touched by commits not reachable from frozen main; unqualified names require original-environment collect for authoritative rewrite'}
 print(branch,len(paths),len(affected),'drafts',len(drafts),flush=True)
(w/'b4-branch-impact.json').write_text(json.dumps({'frozen_main':base,'observed_local':datetime.datetime.now().isoformat(),'branches':out,'policy':'git references and objects only; no other lane worktree reads or writes'},ensure_ascii=False,indent=2))
