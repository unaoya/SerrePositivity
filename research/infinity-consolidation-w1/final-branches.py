"""Pin read-only lane observation; no branch/worktree writes."""
from pathlib import Path
import json,subprocess,sys,re,hashlib
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'scripts/refactor'));from layer_check import imports,code_only
import csv,pickle
move={r['old_module'] for r in csv.DictReader((OUT/'moves.csv').open())}
prefixes=json.loads((OUT/'namespace-prefix-proposal.json').read_text())
def git(*a,cwd=ROOT):return subprocess.check_output(['git',*a],cwd=cwd,text=True).strip()
def fast(s):
 matches=list(re.finditer(r'(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import[^\n]*',s))
 if not matches:return set()
 # include continuation lines; full source fallback if a comment is incomplete
 end=s.find('\n',matches[-1].end());end=len(s) if end<0 else end+1
 while end<len(s) and re.match(r'[ \t]+[\w]+\.',s[end:]):
  n=s.find('\n',end);end=len(s) if n<0 else n+1
 try:return imports(s[:end])
 except ValueError:return imports(s)
a={}
for b,d in [('math/inf-supply','SerrePositivity-bs-classical'),('math/scheme','SerrePositivity-scheme')]:
 wt=ROOT.parent/d;head=git('rev-parse',b)
 touched=set(git('log','--format=','--name-only','main..'+head,'--','*.lean').splitlines())|set(git('diff','--name-only','main...'+head,'--','*.lean').splitlines())
 dirty=set(git('diff','HEAD','--name-only','--','*.lean',cwd=wt).splitlines())|set(git('ls-files','--others','--exclude-standard','*.lean',cwd=wt).splitlines())
 touched|=dirty;touched.discard('');dirty.discard('');hits=[];kst=[];sources={}
 for p in sorted(touched):
  f=wt/p
  if not f.exists():continue
  s=f.read_text();sources[p]=hashlib.sha256(s.encode()).hexdigest();ds=fast(s);im=sorted(ds&move)
  # Names qualified with any EInfinity scope, not just longest family prefix.
  ns=sorted(set(re.findall(r'SerrePositivity\.EInfinity(?:\.[\w\u0080-\uffff]+)*',s)))
  if im or ns:hits.append({'path':p,'imports':im,'qualified_einfinity_mentions':ns})
  ks=sorted(x for x in ds if x.startswith('SerrePositivity.KST'))
  if ks:kst.append({'path':p,'imports':ks})
 a[b]=dict(head=head,head_after=git('rev-parse',b),worktree=str(wt),touched_lean=len(touched),readable_touched=len(sources),dirty_lean=sorted(dirty),touched_paths=sorted(touched),affected_files=len(hits),affected_imports=sum(len(r['imports']) for r in hits),hits=hits,kst_importers=kst,source_inventory_sha256=hashlib.sha256(json.dumps(sources,sort_keys=True).encode()).hexdigest())
(OUT/'branch-impact.json').write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({b:{k:v for k,v in l.items() if k not in ('dirty_lean','touched_paths','kst_importers','hits')} for b,l in a.items()},indent=2))
