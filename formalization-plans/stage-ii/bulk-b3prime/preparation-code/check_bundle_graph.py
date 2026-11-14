from pathlib import Path
import json,re,sys,collections,hashlib,subprocess
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');A=Path('/tmp/bulk-b3prime-preview');sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import code_only
rx=re.compile(r'(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(SerrePositivity(?:\.[\w\']+)*)')
def graph(root):
 return {p.relative_to(root).as_posix()[:-5].replace('/','.'):set(rx.findall(code_only(p.read_text()))) for p in [root/'SerrePositivity.lean',*(root/'SerrePositivity').rglob('*.lean')]}
def reach(g,seeds):
 seen=set(seeds);q=collections.deque(seen)
 while q:
  for c in g.get(q.popleft(),set()):
   if c not in seen:seen.add(c);q.append(c)
 return seen
def cycles(g):
 # Kahn elimination is enough for the no-cycle gate; preserve all residual edges on failure.
 deg={n:len(v & g.keys()) for n,v in g.items()};rev=collections.defaultdict(set)
 for n,vs in g.items():
  for v in vs:rev[v].add(n)
 q=collections.deque(n for n in g if not deg[n]);removed=set()
 while q:
  n=q.popleft();removed.add(n)
  for m in rev[n]:
   deg[m]-=1
   if not deg[m]:q.append(m)
 return sorted(set(g)-removed)
manifest=json.loads((W/'final-bundle/manifest.json').read_text());before={m:{d for d in ds if d.startswith('SerrePositivity.')} for m,ds in json.loads((W/'tracked-import-graph.json').read_text()).items()};after={m:set(ds) for m,ds in before.items()};allowed=set(manifest['delete_paths'])|{m.replace('.','/')+'.lean' for m in manifest['files']};changed=set(subprocess.check_output(['git','diff','HEAD','--no-renames','--name-only','--','SerrePositivity','SerrePositivity.lean'],cwd=A,text=True).splitlines());assert changed<=allowed,sorted(changed-allowed)
assert not subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','SerrePositivity','SerrePositivity.lean'],cwd=A,text=True).strip(),'unstaged untracked Lean outside indexed bundle'
assert not subprocess.check_output(['git','diff','32d364b53','HEAD','--name-only','--','SerrePositivity','SerrePositivity.lean'],cwd=A,text=True).strip(),'preview HEAD differs from before mathematical baseline'
for p in manifest['delete_paths']:after.pop(p[:-5].replace('/','.'),None);assert not (A/p).exists(),p
for m,sha in manifest['files'].items():
 p=A/(m.replace('.','/')+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==sha,m;after[m]=set(rx.findall(code_only(p.read_text())))
missing=[{'module':m,'import':d} for m,ds in after.items() for d in ds if d not in after];core_prefix='SerrePositivity.EInfinity';bs='SerrePositivity.BhattScholze';edges=lambda g:[{'module':m,'import':d} for m,ds in g.items() if m==core_prefix or m.startswith(core_prefix+'.') for d in ds if d==bs or d.startswith(bs+'.')];reached=reach(after,['SerrePositivity']);plan=json.loads((R/'formalization-plans/stage-ii/bulk-b3prime/stage0-import-closure.json').read_text());mapping=json.loads((W/'namespace-rewrite-plan.json').read_text())['modules'];pub=[{'module':mapping.get(r['module'],r['module']),'root_reachable':mapping.get(r['module'],r['module']) in reached} for r in plan['publication_targets']];residual=cycles(after);result={'scope':'All active modules; cached baseline graph with final actual-source overlay and git-diff/source-SHA coverage guards. Archive remains excluded as in the original layer source graph.','baseline_modules':len(before),'preview_modules':len(after),'missing_project_imports':missing,'cycle_residual':residual,'EInfinity_to_BS_before':edges(before),'EInfinity_to_BS_after':edges(after),'EInfinity_transitively_reaches_BS':sorted(m for m in reach(after,[core_prefix]) if m==bs or m.startswith(bs+'.')),'publication_targets':pub,'source_manifest_sha256':hashlib.sha256((W/'final-bundle/manifest.json').read_bytes()).hexdigest()};(W/'full-preview-import-graph.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));print({k:len(v) if isinstance(v,list) else v for k,v in result.items()});raise SystemExit(bool(missing or residual or result['EInfinity_to_BS_after'] or result['EInfinity_transitively_reaches_BS'] or not all(r['root_reachable'] for r in pub)))
